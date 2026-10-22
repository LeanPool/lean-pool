/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Plane.ProjectivePlaneAbsoluteCount
import LeanPool.CCDN.Algebra.HomogeneousChartIrreducible
import LeanPool.CCDN.Algebra.ProjectiveAffineChart
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Plane.NonabsolutePlaneCount
import LeanPool.CCDN.Plane.ProjectivePlaneBezout

/-! Curves that are irreducible over the base field but split over an
extension have at most d^2+d projective base-field points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem nonabsolute_projective_plane_points_card_le {k K ι : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype ι] {d : ℕ}
    (f : MvPolynomial (Fin 3) k) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible f) (hred : ¬ Irreducible (map (algebraMap k K) f))
    (z : ι → Projectivization k (Fin 3 → k)) (hinj : Function.Injective z)
    (hz : ∀ i, z i ∈ projectiveZeroLocus f) :
    Fintype.card ι ≤ d ^ 2 + d := by
  classical
  have hX := variable_not_dvd_irreducible_homogeneous f hf hir hd 0
  have hdeg := affineChart_degree_of_not_variable_dvd f hf hX
  have hchart := affineChart_irreducible_of_not_variable_dvd f hf hir hX
  have hchartred : ¬ Irreducible (map (algebraMap k K) (affineChart 2 f)) := by
    intro hi
    apply hred
    apply irreducible_of_affineChart_irreducible
    · rw [affineChart_map]
      have hmapdegree (q : MvPolynomial (Fin 2) k) :
          (map (algebraMap k K) q).totalDegree = q.totalDegree :=
          totalDegree_map_of_injective (algebraMap k K).injective _
      rw [hmapdegree, hdeg, (hf.map _).totalDegree]
      exact fun h => hir.ne_zero
        ((map_injective (algebraMap k K) (algebraMap k K).injective) (by simpa using h))
    · rwa [affineChart_map]
  let S := Finset.univ.filter (fun i : ι => (z i).rep 0 ≠ 0)
  let T := Finset.univ.filter (fun i : ι => ¬ (z i).rep 0 ≠ 0)
  have hs := nonabsolute_plane_points_card_le (affineChart 2 f) hchart
    (by omega : 0 < (affineChart 2 f).totalDegree) hchartred
    (fun i : S => projectiveAffineCoordinates (z i.val)) ?_ ?_
  · have ht := projective_plane_common_zeros_card_le f (X 0) hf hir (isHomogeneous_X _ _)
      (irreducible_homogeneous_not_dvd_variable f hf hir hd 0)
      (fun i : T => z i.val) (hinj.comp Subtype.val_injective) (fun i => hz i.val) ?_
    · have hsum := Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (p := fun i : ι => (z i).rep 0 ≠ 0)
      simp only [Fintype.card_coe, hdeg] at hs
      simp only [Fintype.card_coe, mul_one] at ht
      change S.card + T.card = Finset.univ.card at hsum
      rw [Finset.card_univ] at hsum
      omega
    · intro i
      change eval (z i.val).rep (X 0) = 0
      simpa using (Finset.mem_filter.mp i.property).2
  · intro i j he
    apply Subtype.ext
    apply hinj
    exact projectiveAffineCoordinates_injective
      (Finset.mem_filter.mp i.property).2 (Finset.mem_filter.mp j.property).2 he
  · intro i
    exact projectiveAffineCoordinates_zero f hf (z i.val)
      (Finset.mem_filter.mp i.property).2 (hz i.val)

private theorem projectiveCount_nonabsolute_plane_le
    {K : Type*} [Field K] [Algebra ℚ K] {d : ℕ}
    (f : MvPolynomial (Fin 3) ℚ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible f) (hred : ¬ Irreducible (map (algebraMap ℚ K) f)) (B : ℝ) :
    projectiveCount (projectiveZeroLocus f) B ≤ d ^ 2 + d := by
  classical
  let S := projectivePoints (projectiveZeroLocus f) B
  have h := nonabsolute_projective_plane_points_card_le f hf hd hir hred
    (fun x : S => x.val) Subtype.val_injective (fun x => (mem_projectivePoints.mp x.property).2)
  simpa only [Fintype.card_coe, S, projectiveCount] using h

/-- The uniform plane bound for every rational irreducible homogeneous
equation of degree at least two, whether or not geometrically irreducible. -/
theorem projective_plane_rational_count {d : ℕ}
    (f : MvPolynomial (Fin 3) ℚ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible f) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
  by_cases habs : AbsolutelyIrreducibleRat f
  · exact projective_plane_rational_absolute_count f hf hd habs hB
  · have h := projectiveCount_nonabsolute_plane_le f hf hd hir habs B
    have hR : (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤ (d : ℝ) ^ 2 + d := by
      exact_mod_cast h
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hd4 : (d : ℝ) ^ 2 + d ≤ 2 * (d : ℝ) ^ 4 := by nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)]
    have hC : 2 ≤ projectivePlaneAbsoluteConstant := by
      unfold projectivePlaneAbsoluteConstant
      have hpos := Real.exp_pos
        (heightDeterminantError projectivePlaneDeterminantConstant + 20)
      have hpos' : 0 ≤
          2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) *
            Real.exp 14 * Real.exp 2 := by positivity
      linarith
    have hQ : 1 ≤ B ^ (2 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
    calc
      _ ≤ (d : ℝ) ^ 2 + d := hR
      _ ≤ 2 * (d : ℝ) ^ 4 := hd4
      _ ≤ projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ _ := le_mul_of_one_le_right
        (mul_nonneg projectivePlaneAbsoluteConstant_pos.le (by positivity)) hQ

end
end CCDN
