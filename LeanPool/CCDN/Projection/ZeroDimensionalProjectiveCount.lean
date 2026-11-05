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
public import LeanPool.CCDN.Height.ProjectiveBox
public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
import LeanPool.CCDN.Algebra.ProjectiveFiniteFibers
import LeanPool.CCDN.Projection.BoundedDegreeNormalizationFiber
import LeanPool.CCDN.Projection.BoundedIntegerNormalization

/-! The zero-dimensional case of projective dimension growth. A
one-parameter normalization sends every projective point to the unique
point of projective zero-space; its affine fiber bound controls
the whole source, independently of height. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

private theorem exists_integer_linear_normalization_of_le (m n : ℕ) (hmn : m + 1 ≤ n)
    (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime] (d : ℕ)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ a : Fin (m + 1) → Fin n → ℤ,
      (projectionCoordinateMap I (fun i => integerLinearForm (a i))).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I (fun i => integerLinearForm (a i))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨a, _, hint, hi⟩ := exists_bounded_integer_normalization m k I d hdimdeg
  exact ⟨a, hint, hi⟩

/-- If a prime ideal `I` in `n + 1` variables has Hilbert dimension one (projective dimension
zero) and degree `d`, its projective zero locus has at most `d ^ (n + 1)` rational points of any
height. -/
theorem zero_dimensional_projective_count_le
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = d) (B : ℝ) :
    projectiveCount (projectiveIdealZeroLocus I) B ≤ d ^ (n + 1) := by
  classical
  obtain ⟨a, hint, hi⟩ := exists_integer_linear_normalization_of_le 0 (n + 1)
    (by omega) I d ⟨hdim, by simpa using hdegree⟩
  let L := (Matrix.map a (Int.castRingHom ℚ)).mulVecLin
  have hLapply (x : Fin (n + 1) → ℚ) (i : Fin 1) :
      L x i = eval x (integerLinearForm (a i)) := by
    simp only [L, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Int.coe_castRingHom, eval_linearForm]
    rfl
  have hfinite (z : Fin 1 → ℚ) (s : Finset (Fin (n + 1) → ℚ))
      (hs : ∀ x ∈ s, x ∈ idealZeroLocus I) (hz : ∀ x ∈ s, L x = z) :
      s.card ≤ d ^ (n + 1) := by
    refine (linear_normalization_fiber_card_le I (fun i => integerLinearForm (a i))
      (fun i => linearForm_totalDegree_le _) hi hint d ⟨hdim, by simpa using hdegree⟩ z s hs
      ?_).trans (Nat.le_self_pow (Nat.succ_ne_zero n) d)
    intro x hx i
    rw [← hLapply, hz x hx]
  let s := projectivePoints (projectiveIdealZeroLocus I) B
  have hs (x) (hx : x ∈ s) : x ∈ projectiveIdealZeroLocus I :=
    (mem_projectivePoints.mp hx).2
  have hnon (x) (hx : x ∈ s) : L x.rep ≠ 0 :=
    projective_linear_image_ne_zero_of_finite_zero_fiber I L (d ^ (n + 1))
      (hfinite 0) x (hs x hx)
  let y : ProjectivePoint 0 :=
    Projectivization.mk ℚ (fun _ : Fin 1 => 1) (by
      intro h
      exact one_ne_zero (congrFun h 0))
  apply projective_linear_fiber_card_le I L s hs hnon y _ (d ^ (n + 1)) (hfinite y.rep)
  intro x hx
  change Projectivization.mk ℚ (L x.rep) (hnon x hx) =
    Projectivization.mk ℚ (fun _ : Fin 1 => 1) _
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨L x.rep 0, ?_⟩
  funext i
  have hi0 : i = 0 := by apply Fin.ext; have := i.isLt; omega
  simp [hi0]

end
end CCDN
