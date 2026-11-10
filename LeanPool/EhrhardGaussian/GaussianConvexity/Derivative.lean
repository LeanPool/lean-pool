/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.GaussianConvexity.Normal
public import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Linarith

/-!
# The derivative at zero of the normalized log MGF

The removable quotient is handled as the divided slope of the analytic cumulant
function. Its derivative is exactly half the variance. This justifies the
parameter-zero calculation in KPZ Lemma 3.2 without a formal Taylor remainder.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace EhrhardGaussian.GaussianConvexity

/-- Differentiating the removable divided slope divides the second derivative by two. -/
theorem hasDerivAt_dslope_zero {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    HasDerivAt (dslope f 0) (iteratedDeriv 2 f 0 / 2) 0 := by
  obtain ⟨p, hp⟩ := hf
  have hg : AnalyticAt ℝ (dslope f 0) 0 := ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have heq : f = fun x => x * dslope f 0 x + f 0 := by
    funext x
    have h := sub_smul_dslope f 0 x
    simp only [sub_zero, smul_eq_mul] at h
    linarith only [h]
  have hsecond : iteratedDeriv 2 f 0 = 2 * deriv (dslope f 0) 0 := by
    calc
      iteratedDeriv 2 f 0 = iteratedDeriv 2 (fun x => x * dslope f 0 x + f 0) 0 :=
        congrArg (fun k : ℝ → ℝ => iteratedDeriv 2 k 0) heq
      _ = iteratedDeriv 2 (fun x => x * dslope f 0 x) 0 +
          iteratedDeriv 2 (fun _ : ℝ => f 0) 0 :=
        iteratedDeriv_add (contDiffAt_id.mul hg.contDiffAt) contDiffAt_const
      _ = _ := by
        rw [iteratedDeriv_fun_mul (f := fun x : ℝ => x) (g := dslope f 0)
          (n := 2) (x := 0) contDiffAt_id hg.contDiffAt]
        norm_num [Finset.sum_range_succ, iteratedDeriv_fun_id, iteratedDeriv_const,
          iteratedDeriv_one]
  have hderiv := hg.differentiableAt.hasDerivAt
  convert hderiv using 1
  linarith only [hsecond]

/-- The normalized log MGF is the analytic divided slope of its cumulant at zero. -/
theorem logMGFRatio_eq_dslope {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (h0 : 0 ∈ interior (integrableExpSet X μ)) :
    logMGFRatio μ X = dslope (cgf X μ) 0 := by
  funext q
  by_cases hq : q = 0
  · subst q
    simp only [logMGFRatio, ite_true, dslope_same, deriv_cgf_zero h0, probReal_univ, div_one]
  · rw [dslope_of_ne _ hq]
    simp only [logMGFRatio, hq, ite_false, slope_def_field, cgf_zero, sub_zero]
    rw [cgf, div_eq_inv_mul]
    rfl

/-- Half the variance is the derivative at zero of the normalized log MGF. -/
theorem hasDerivAt_logMGFRatio_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (h0 : 0 ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (logMGFRatio μ X) (Var[X; μ] / 2) 0 := by
  rw [logMGFRatio_eq_dslope μ X h0]
  have h := hasDerivAt_dslope_zero (analyticAt_cgf h0)
  have hmem : MemLp X 2 μ := memLp_of_mem_interior_integrableExpSet h0 2
  have hsecond : iteratedDeriv 2 (cgf X μ) 0 = Var[X; μ] := by
    rw [iteratedDeriv_two_cgf h0, variance_eq_sub hmem, deriv_cgf_zero h0]
    simp only [zero_mul, Real.exp_zero, mul_one, mgf_zero, div_one, probReal_univ, Pi.pow_apply]
  rw [hsecond] at h
  exact h

end EhrhardGaussian.GaussianConvexity
