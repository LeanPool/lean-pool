/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Second moments of the genuine Gaussian measures used in the paper

These are probability-measure ingredients for the Gaussian computations in
Section 3.2. They do not identify the projected diffusion with an OU process.
-/

public section

open MeasureTheory ProbabilityTheory

namespace CutoffRigidity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The centered second moment of a multivariate Gaussian is the trace of its
covariance matrix. This concerns Mathlib's probability measure, not a scalar profile. -/
theorem gaussian_centered_second_moment (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) :
    ∫ x, ‖x - m‖ ^ 2 ∂multivariateGaussian m S = Matrix.trace S := by
  have hmean (i : ι) :
      ∫ x : EuclideanSpace ℝ ι, x i ∂multivariateGaussian m S = m i := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
      (IsGaussian.integrable_id (μ := multivariateGaussian m S))
  have hcoord (i : ι) :
      ∫ x : EuclideanSpace ℝ ι, (x i - m i) ^ 2 ∂multivariateGaussian m S = S i i := by
    rw [← hmean i, ← variance_eq_integral (by fun_prop)]
    exact variance_eval_multivariateGaussian hS i
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simpa [Matrix.trace] using Finset.sum_congr rfl (fun i _ => hcoord i)
  · intro i hi
    have hm : MemLp (fun x : EuclideanSpace ℝ ι => x i) 2 (multivariateGaussian m S) := by
      simpa using IsGaussian.memLp_dual (multivariateGaussian m S) (EuclideanSpace.proj i)
        2 (by norm_num)
    simpa using (hm.sub (memLp_const (m i))).integrable_sq

omit [DecidableEq ι] in
/-- The standard Gaussian in dimension `card ι` has squared norm expectation `card ι`. -/
theorem standard_gaussian_second_moment :
    ∫ x : EuclideanSpace ℝ ι, ‖x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) =
      Fintype.card ι := by
  classical
  simpa using gaussian_centered_second_moment (0 : EuclideanSpace ℝ ι)
    (1 : Matrix ι ι ℝ) Matrix.PosSemidef.one

/-- Squared distance from a fixed point splits into squared mean displacement
and covariance trace, as used in the Gaussian distance calculations. -/
theorem gaussian_second_moment_about (m a : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) :
    ∫ x, ‖x - a‖ ^ 2 ∂multivariateGaussian m S = ‖m - a‖ ^ 2 + Matrix.trace S := by
  have hm (i : ι) : MemLp (fun x : EuclideanSpace ℝ ι => x i) 2
      (multivariateGaussian m S) := by
    simpa using IsGaussian.memLp_dual (multivariateGaussian m S) (EuclideanSpace.proj i)
      2 (by norm_num)
  have hmean (i : ι) :
      ∫ x : EuclideanSpace ℝ ι, x i ∂multivariateGaussian m S = m i := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
      (IsGaussian.integrable_id (μ := multivariateGaussian m S))
  have hcoord (i : ι) :
      ∫ x : EuclideanSpace ℝ ι, (x i - a i) ^ 2 ∂multivariateGaussian m S =
        (m i - a i) ^ 2 + S i i := by
    have hv := variance_eq_sub ((hm i).sub (memLp_const (a i)))
    change Var[fun x : EuclideanSpace ℝ ι => x i - a i; multivariateGaussian m S] =
      (∫ x : EuclideanSpace ℝ ι, (x i - a i) ^ 2 ∂multivariateGaussian m S) -
        (∫ x : EuclideanSpace ℝ ι, x i - a i ∂multivariateGaussian m S) ^ 2 at hv
    rw [variance_sub_const (hm i).aestronglyMeasurable,
      variance_eval_multivariateGaussian hS i] at hv
    have hma : ∫ x : EuclideanSpace ℝ ι, (x i - a i) ∂multivariateGaussian m S =
        m i - a i := by
      rw [integral_sub ((hm i).integrable (by norm_num)) (integrable_const _),
        hmean i, integral_const]
      simp
    rw [hma] at hv
    change S i i = (∫ x : EuclideanSpace ℝ ι, (x i - a i) ^ 2
      ∂multivariateGaussian m S) - (m i - a i) ^ 2 at hv
    linarith
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp_rw [show ∀ x : EuclideanSpace ℝ ι, (x - a).ofLp = fun i => x i - a i
        from fun _ => rfl, hcoord]
    simp [Finset.sum_add_distrib, Matrix.trace]
  · intro i hi
    simpa using ((hm i).sub (memLp_const (a i))).integrable_sq

end CutoffRigidity
