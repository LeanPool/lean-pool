/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.ProjectivePlaneAbsoluteCount
public import LeanPool.CCDN.Projection.ScaleAbsorption
import LeanPool.CCDN.Algebra.ProjectivePermutation
import LeanPool.CCDN.Plane.ProjectivePlaneLinearCount
import LeanPool.CCDN.Projection.ProjectiveProjectionCount

/-! The projective curve count of Theorem 2 with an explicit constant. In a chart where the
curve is not contained in the hyperplane at infinity, a bounded projection to the plane and the
projective plane count give the bound (`projective_curve_count_of_proper_chart`); a coordinate
permutation, which costs no height, chooses such a chart (`projective_curve_count`). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The explicit constant `projectivePlaneAbsoluteConstant * exp (2 * projectionLogConstant n) + 1`
of the projective curve count in `ℙⁿ`: the plane-curve constant, enlarged by the height loss of a
bounded projection to the plane, plus one to absorb the `d²` error term of the projection. -/
def projectiveCurveConstant (n : ℕ) : ℝ :=
  projectivePlaneAbsoluteConstant * Real.exp (2 * projectionLogConstant n) + 1

/-- The constant `projectiveCurveConstant n` is positive. -/
lemma projectiveCurveConstant_pos (n : ℕ) : 0 < projectiveCurveConstant n := by
  unfold projectiveCurveConstant
  have := projectivePlaneAbsoluteConstant_pos
  positivity

private theorem projectiveCurveEstimate_scale (n : ℕ) {d : ℕ} (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    projectiveCurveEstimate d (projectionBoxFactor n d * B) ≤
      Real.exp (2 * projectionLogConstant n) * projectiveCurveEstimate d B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : 0 < projectionBoxFactor n d :=
    lt_of_lt_of_le (by norm_num) (projectionBoxFactor_one_le n d)
  have hpow : (projectionBoxFactor n d) ^ (2 / (d : ℝ)) ≤
      Real.exp (2 * projectionLogConstant n) := by
    rw [Real.rpow_def_of_pos hA, Real.exp_le_exp, ← mul_div_assoc]
    apply (div_le_iff₀ hd0).mpr
    have hlog := projectionBoxFactor_log_le n hd
    linarith
  unfold projectiveCurveEstimate
  rw [Real.mul_rpow hA.le (by linarith)]
  have h := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) by positivity)
  convert h using 1 <;> ring

/-- Let `I` be the homogeneous prime ideal of a projective curve of degree `d > 0` in `ℙⁿ` that is
not contained in the hyperplane `X 0 = 0` (that is, `X 0 ∉ I`). For `B ≥ 1`, the number of rational
points of height at most `B` on the curve is at most `projectiveCurveConstant n * d⁴ B^(2/d)`. -/
theorem projective_curve_count_of_proper_chart {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime] (hX : X 0 ∉ I)
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCurveConstant n * projectiveCurveEstimate d B := by
  obtain ⟨f, hf, hir, hreduce⟩ := exists_projective_plane_count_reduction I hX hd hdegree
  have hAB := one_le_mul_of_one_le_of_one_le (projectionBoxFactor_one_le n d) hB
  have hplane := projective_plane_equation_bound f hf hd hir hAB
  have hR : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) + (d : ℝ) ^ 2 := by
    exact_mod_cast hreduce B hB
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : 1 ≤ B ^ (2 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  have herr : (d : ℝ) ^ 2 ≤ projectiveCurveEstimate d B :=
    (pow_le_pow_right₀ hd1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) hQ)
  calc
    _ ≤ projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) +
        (d : ℝ) ^ 2 := hR
    _ ≤ projectivePlaneAbsoluteConstant *
          projectiveCurveEstimate d (projectionBoxFactor n d * B) +
        projectiveCurveEstimate d B := by
      rw [projectiveCurveEstimate, ← mul_assoc]
      exact add_le_add hplane herr
    _ ≤ projectivePlaneAbsoluteConstant *
          (Real.exp (2 * projectionLogConstant n) * projectiveCurveEstimate d B) +
        projectiveCurveEstimate d B := by
      gcongr
      exacts [projectivePlaneAbsoluteConstant_pos.le, projectiveCurveEstimate_scale n hd hB]
    _ = projectiveCurveConstant n * projectiveCurveEstimate d B := by
      unfold projectiveCurveConstant
      ring

/-- Let `I` be the homogeneous prime ideal of a projective curve of degree `d > 0` in `ℙⁿ`. For
`B ≥ 1`, the number of rational points of height at most `B` on the curve is at most
`projectiveCurveConstant n * d⁴ B^(2/d)`. -/
theorem projective_curve_count {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime]
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCurveConstant n * projectiveCurveEstimate d B := by
  classical
  by_cases hS : (projectivePoints (projectiveIdealZeroLocus I) B).Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hxI := (mem_projectivePoints.mp hx).2
    obtain ⟨j, hj⟩ := Function.ne_iff.mp x.rep_nonzero
    change x.rep j ≠ 0 at hj
    let e := Equiv.swap (0 : Fin (n + 1)) j
    let J := projectivePermutedIdeal I e
    have hX : X 0 ∉ J := by
      intro h
      have hh := (mem_projectivePermutedIdeal I e (X 0)).mp h
      have hXj : X j ∈ I := by simpa [e] using hh
      have hz := projectiveIdealZeroLocus_rep hxI (X j) hXj
      exact hj (by simpa using hz)
    have hJ := projectiveCurveDegree_permuted I e hdegree
    have h := projective_curve_count_of_proper_chart J hX hd hJ hB
    have hc : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        projectiveCount (projectiveIdealZeroLocus J) B := by
      exact_mod_cast projectiveCount_le_permuted I e B
    exact hc.trans h
  · have he := Finset.not_nonempty_iff_eq_empty.mp hS
    unfold projectiveCount
    rw [he, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (projectiveCurveConstant_pos n).le
      (by unfold projectiveCurveEstimate; positivity)

end
end CCDN
