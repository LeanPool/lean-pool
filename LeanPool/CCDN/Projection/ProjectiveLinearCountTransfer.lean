/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IntegerLinearForms
public import LeanPool.CCDN.Algebra.ProjectiveSection
public import LeanPool.CCDN.Height.ProjectiveZeroLocus
import LeanPool.CCDN.Algebra.ProjectiveFiniteFibers
import LeanPool.CCDN.Determinant.PolynomialMapDeterminant
import LeanPool.CCDN.Projection.BoundedLinearProjection

/-! Height and cardinality transport through an integer linear
projection with uniformly bounded affine fibers. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

private def integerProjectiveLinearImage {m n : ℕ}
    (P : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ) (x : ProjectivePoint n) :
    ProjectivePoint m :=
  if h : (P.map (Int.castRingHom ℚ)) *ᵥ x.rep ≠ 0 then
    Projectivization.mk ℚ ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) h
  else
    Projectivization.mk ℚ (fun _ : Fin (m + 1) => 1) (by
      intro hz
      have hh := congrFun hz 0
      exact one_ne_zero hh)

/-- Let `P` be an integer matrix with entries of absolute value at most `H` whose linear forms
satisfy the homogeneous relation `f` modulo `I`. If every affine fiber of the induced map on the
zero locus of `I` has at most `M` points, then the projective rational points of height at most `B`
on the zero locus of `I` number at most `M` times those of height at most `(n + 1) * H * B` on the
projective hypersurface `f = 0`. -/
theorem projective_integer_linear_count_transfer
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (P : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (f : MvPolynomial (Fin (m + 1)) ℚ) (hf : f.IsHomogeneous f.totalDegree)
    (hrelation : aeval (fun i => integerLinearForm (P i)) f ∈ I)
    (M : ℕ)
    (hfinite : ∀ z : Fin (m + 1) → ℚ, ∀ s : Finset (Fin (n + 1) → ℚ),
      (∀ x ∈ s, x ∈ idealZeroLocus I) →
      (∀ x ∈ s, ∀ i, eval x (integerLinearForm (P i)) = z i) → s.card ≤ M)
    (H B : ℝ) (hH : 0 ≤ H)
    (hP : ∀ i j, |(P i j : ℝ)| ≤ H) :
    projectiveCount (projectiveIdealZeroLocus I) B ≤
      M * projectiveCount (projectiveZeroLocus f) ((n + 1 : ℕ) * H * B) := by
  classical
  let L := (P.map (Int.castRingHom ℚ)).mulVecLin
  let π := integerProjectiveLinearImage P
  let s := projectivePoints (projectiveIdealZeroLocus I) B
  let t := projectivePoints (projectiveZeroLocus f) ((n + 1 : ℕ) * H * B)
  have hLapply (x : Fin (n + 1) → ℚ) (i) :
      L x i = eval x (integerLinearForm (P i)) := by
    simp only [L, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Int.coe_castRingHom, eval_linearForm]
  have hfiniteL (z : Fin (m + 1) → ℚ) (u : Finset (Fin (n + 1) → ℚ))
      (hu : ∀ x ∈ u, x ∈ idealZeroLocus I) (huz : ∀ x ∈ u, L x = z) :
      u.card ≤ M := by
    apply hfinite z u hu
    intro x hx i
    rw [← hLapply, huz x hx]
  have hnon (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) :
      L x.rep ≠ 0 :=
    projective_linear_image_ne_zero_of_finite_zero_fiber I L M (hfiniteL 0) x hx
  have hπ (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) :
      π x = Projectivization.mk ℚ (L x.rep) (hnon x hx) := by
    exact dite_eq_left (hnon x hx)
  have himage : s.image π ⊆ t := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxB, hxI⟩ := mem_projectivePoints.mp hx
    rw [hπ x hxI]
    apply mem_projectivePoints.mpr
    constructor
    · exact (projective_linear_map_height P hH hP x (hnon x hxI)).trans
        (mul_le_mul_of_nonneg_left hxB (by positivity))
    · rw [mem_projectiveZeroLocus_mk hf]
      have hz := projectiveIdealZeroLocus_rep hxI _ hrelation
      rw [eval_polynomial_coordinate_map] at hz
      have hev : L x.rep = fun i => eval x.rep (integerLinearForm (P i)) :=
        funext (hLapply x.rep)
      rwa [hev]
  have hfib (y : ProjectivePoint m) :
      (s.filter (fun x => π x = y)).card ≤ M := by
    let u := s.filter (fun x => π x = y)
    have hu (x) (hx : x ∈ u) : x ∈ projectiveIdealZeroLocus I :=
      (mem_projectivePoints.mp (Finset.mem_filter.mp hx).1).2
    apply projective_linear_fiber_card_le I L u hu (fun x hx => hnon x (hu x hx))
      y _ M (hfiniteL y.rep)
    intro x hx
    rw [← hπ x (hu x hx)]
    exact (Finset.mem_filter.mp hx).2
  change s.card ≤ M * t.card
  rw [Finset.card_eq_sum_card_image π s]
  calc
    _ ≤ ∑ _y ∈ s.image π, M := Finset.sum_le_sum (fun y _ => hfib y)
    _ = M * (s.image π).card := by simp [Nat.mul_comm]
    _ ≤ M * t.card := Nat.mul_le_mul_left M (Finset.card_le_card himage)

end
end CCDN
