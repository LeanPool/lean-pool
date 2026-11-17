/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Projection.ProjectivePlaneProjection
import LeanPool.CCDN.Algebra.ScaledHypersurfaceModel
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Height.ProjectiveIntegerHeight
import LeanPool.CCDN.LowerBound.GridCurveConstruction
import LeanPool.CCDN.LowerBound.IntegerGridLowerBound

/-! The integer grid gives distinct bounded-height rational points on the
irreducible projective closure. This is the geometric input to CCDN
Proposition 5, including the stated degree and the exact grid size. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma affineProjectivePoint_integer_height_le {n : ℕ} (z : IntPoint n)
    {B : ℝ} (hB : 1 ≤ B) (hz : InBox z B) :
    (affineProjectivePoint (rationalPoint z)).mulHeight ≤ B := by
  let w : IntPoint (n + 1) := Fin.cons 1 z
  have hw0 : w 0 ≠ 0 := one_ne_zero
  have he : affineProjectivePoint (rationalPoint z) =
      Projectivization.mk ℚ (rationalPoint w)
        (rationalPoint_ne_zero (fun h => hw0 (congrFun h 0))) := by
    convert affineProjectivePoint_eq_integer w hw0 using 1
    congr 1
    funext j
    simp [w, rationalPoint]
  rw [he]
  apply projective_integer_height_le w (fun h => hw0 (congrFun h 0))
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa [w] using hB
  · exact hz i

/-- A finite integral grid injects into projective space by z↦[1:z]. -/
theorem integer_grid_le_projective_count {n d : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (hd : f.totalDegree ≤ d)
    (s : Finset ℤ) {B : ℝ} (hB : 1 ≤ B)
    (hsB : ∀ a ∈ s, |(a : ℝ)| ≤ B)
    (hfzero : ∀ z : IntPoint n, (∀ j, z j ∈ s) → eval (rationalPoint z) f = 0) :
    s.card ^ n ≤ projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f)) B := by
  classical
  let S : Finset (IntPoint n) := Fintype.piFinset (fun _ => s)
  have hScard : S.card = s.card ^ n := by simp [S, Fintype.card_piFinset]
  rw [← hScard]
  apply Finset.card_le_card_of_injOn (fun z => affineProjectivePoint (rationalPoint z))
  · intro z hz
    have hz' : ∀ j, z j ∈ s := Fintype.mem_piFinset.mp hz
    apply mem_projectivePoints.mpr
    refine ⟨affineProjectivePoint_integer_height_le z hB (fun j => hsB (z j) (hz' j)), ?_⟩
    unfold affineProjectivePoint
    rw [mem_projectiveZeroLocus_mk (scaledHomogenize_homogeneous 1 f hd),
      ← affineChart_eval, affineChart_scaledHomogenize_one]
    exact hfzero z hz'
  · intro x _ y _ he
    have hh := affineProjectivePoint_injective n he
    funext j
    exact Int.cast_injective (congrFun hh j)

/-- The homogenization of an absolutely irreducible rational polynomial of total degree `d` is a
form of degree `d` that is again absolutely irreducible. -/
lemma projective_closure_absolute_irreducible {n d : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (hd : f.totalDegree = d)
    (hf : AbsolutelyIrreducibleRat f) :
    (scaledHomogenize d 1 f).IsHomogeneous d ∧
      (scaledHomogenize d 1 f).totalDegree = d ∧
        AbsolutelyIrreducibleRat (scaledHomogenize d 1 f) := by
  have hhom := scaledHomogenize_homogeneous 1 f hd.le
  have h0 : scaledHomogenize d 1 f ≠ 0 := by
    intro h
    have hh := affineChart_scaledHomogenize_one d f
    rw [h, map_zero] at hh
    exact hf.ne_zero (by rw [← hh, map_zero])
  refine ⟨hhom, hhom.totalDegree h0, ?_⟩
  dsimp only [AbsolutelyIrreducibleRat]
  rw [scaledHomogenize_map, map_one]
  have hdeg : (map (algebraMap ℚ (AlgebraicClosure ℚ)) f).totalDegree = d :=
    (totalDegree_map_of_injective (algebraMap ℚ (AlgebraicClosure ℚ)).injective _).trans hd
  simpa only [hdeg] using scaledHomogenize_irreducible _ hf one_ne_zero

/-- For d≥4, the precise asymmetric integer grid used in Section 6 supplies
(floor((d−1)/2)+1)² distinct projective points at the paper's chosen height. -/
theorem exists_projective_grid_lower_bound (d : ℕ) (hd : 4 ≤ d) :
    ∃ F : MvPolynomial (Fin 3) ℚ,
      F.IsHomogeneous d ∧ F.totalDegree = d ∧
        AbsolutelyIrreducibleRat F ∧
          ((d - 1) / 2 + 1) ^ 2 ≤
            projectiveCount (projectiveZeroLocus F)
              (((d - 1) / 2 - (d - 1) / 4 : ℕ) : ℝ) := by
  classical
  let q := (d - 1) / 2
  let r := (d - 1) / 4
  let B := q - r
  have hrq : r ≤ q := by dsimp [q, r]; omega
  have hB : 1 ≤ B := by dsimp [B, q, r]; omega
  have hrB : r ≤ B := by dsimp [B, q, r]; omega
  let s : Finset ℤ := Finset.Icc (-(B : ℤ)) (r : ℤ)
  have hs : s.card = q + 1 := by
    rw [Int.card_Icc]
    omega
  let t : Finset ℚ := s.image (Int.castRingHom ℚ)
  have ht : t.card = q + 1 := by
    change (s.image (fun x : ℤ => (x : ℚ))).card = _
    rw [Finset.card_image_of_injective _ Int.cast_injective, hs]
  obtain ⟨f, hfdeg, hfir, hfzero⟩ := exists_absolutely_irreducible_plane_grid
    (algebraMap ℚ (AlgebraicClosure ℚ)) t (by rw [ht]; omega) d
    (by rw [ht]; dsimp [q]; omega) (by rw [ht]; dsimp [q]; omega)
  obtain ⟨hhom, hdeg, hir⟩ := projective_closure_absolute_irreducible f hfdeg hfir
  refine ⟨scaledHomogenize d 1 f, hhom, hdeg, hir, ?_⟩
  change (q + 1) ^ 2 ≤ projectiveCount _ (B : ℝ)
  rw [← hs]
  apply integer_grid_le_projective_count f hfdeg.le s (by exact_mod_cast hB)
  · intro a ha
    have hab := Finset.mem_Icc.mp ha
    have har : a ≤ (B : ℤ) := hab.2.trans (by exact_mod_cast hrB)
    exact_mod_cast abs_le.mpr ⟨hab.1, har⟩
  · intro z hz
    apply hfzero
    intro j
    exact Finset.mem_image.mpr ⟨z j, hz j, rfl⟩

/-- Every positive degree has an absolutely irreducible projective model
with at least two rational points of height one. This covers d=1,2,3 in
Proposition 5. -/
theorem exists_projective_two_point_lower_bound (d : ℕ) (hd : 0 < d) :
    ∃ F : MvPolynomial (Fin 3) ℚ,
      F.IsHomogeneous d ∧ F.totalDegree = d ∧
        AbsolutelyIrreducibleRat F ∧
          2 ≤ projectiveCount (projectiveZeroLocus F) 1 := by
  classical
  obtain ⟨f, hfdeg, hfir, hfzero, hfone⟩ := exists_irreducible_zero_one_equation
    (algebraMap ℚ (AlgebraicClosure ℚ)) d 2 hd (by decide)
  obtain ⟨hhom, hdeg, hir⟩ := projective_closure_absolute_irreducible f hfdeg hfir
  refine ⟨scaledHomogenize d 1 f, hhom, hdeg, hir, ?_⟩
  have hc : ({(0 : ℤ), 1} : Finset ℤ).card = 2 := by decide
  conv_lhs => rw [← hc]
  apply Finset.card_le_card_of_injOn (fun a : ℤ => affineProjectivePoint
    (rationalPoint (fun _ : Fin 2 => a)))
  · intro a ha
    have ha' : a = 0 ∨ a = 1 := by simpa using ha
    apply mem_projectivePoints.mpr
    refine ⟨affineProjectivePoint_integer_height_le _ le_rfl ?_, ?_⟩
    · intro j
      rcases ha' with rfl | rfl <;> norm_num
    · unfold affineProjectivePoint
      rw [mem_projectiveZeroLocus_mk hhom,
        ← affineChart_eval, affineChart_scaledHomogenize_one]
      rcases ha' with rfl | rfl
      · change eval (0 : Fin 2 → ℚ) f = 0
        exact hfzero
      · change eval (fun _ => (1 : ℚ)) f = 0
        exact hfone
  · intro a _ b _ he
    have hh := affineProjectivePoint_injective 2 he
    have h := congrFun hh 0
    exact Int.cast_injective h

end
end CCDN
