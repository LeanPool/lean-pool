/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee, Scott Armstrong
-/

/-
Modified for EhrhardGaussian, 2026.

Product-Fubini pattern adapted from Lattice-Probability,
LatticeProb/Prob/CdfDifferenceFourier.lean; real exponential integrability is new.
-/
module

public import LeanPool.EhrhardGaussian.GaussianConvexity.WeightedCDF
public import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.Linarith

/-!
# The weighted CDF difference identity on probability laws

Both exponential moments at the parameter suffice. The argument works
for negative parameters and for atomic laws without separate tail formulas.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter

namespace EhrhardGaussian.GaussianConvexity

variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The difference of two CDFs is the expectation of the coupled indicator difference. -/
theorem cdf_sub_eq_integral_cdfIndDiff (t : ℝ) :
    cdf μ t - cdf ν t = ∫ z : ℝ × ℝ, cdfIndDiff z.1 z.2 t ∂(μ.prod ν) := by
  have hI : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      Integrable ((Iic t).indicator (fun _ => (1 : ℝ))) ρ := fun ρ _ =>
    (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  unfold cdfIndDiff
  rw [integral_sub ((hI μ).comp_fst ν) ((hI ν).comp_snd μ),
    integral_fun_fst (fun x => (Iic t).indicator (fun _ => (1 : ℝ)) x),
    integral_fun_snd (fun x => (Iic t).indicator (fun _ => (1 : ℝ)) x),
    integral_indicator_const _ measurableSet_Iic, integral_indicator_const _ measurableSet_Iic]
  simp only [cdf_eq_real, probReal_univ, smul_eq_mul, mul_one, one_mul]

/-- Exponential moments of both marginals dominate the coupled weighted indicator in `L¹`. -/
theorem integrable_cdfIndDiff_exp_prod {p : ℝ} (hp : p ≠ 0)
    (hμ : Integrable (fun x => Real.exp (p * x)) μ)
    (hν : Integrable (fun x => Real.exp (p * x)) ν) :
    Integrable (fun q : ℝ × (ℝ × ℝ) =>
      cdfIndDiff q.2.1 q.2.2 q.1 * Real.exp (p * q.1)) (volume.prod (μ.prod ν)) := by
  have hmeas : Measurable (fun q : ℝ × (ℝ × ℝ) =>
      cdfIndDiff q.2.1 q.2.2 q.1 * Real.exp (p * q.1)) :=
    measurable_cdfIndDiff.mul (by fun_prop)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ (fun z => integrable_cdfIndDiff_exp z.1 z.2 p), ?_⟩
  simp_rw [integral_norm_cdfIndDiff_exp _ _ hp]
  apply (((hμ.comp_fst ν).add (hν.comp_snd μ)).div_const |p|).mono' (by fun_prop)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_abs, abs_div]
  have h := abs_sub (Real.exp (p * z.2)) (Real.exp (p * z.1))
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)] at h
  exact div_le_div_of_nonneg_right (h.trans_eq (add_comm _ _)) (abs_nonneg p)

/-- Integrability of a weighted CDF difference, even when neither weighted tail is integrable. -/
theorem integrable_cdf_sub_mul_exp {p : ℝ} (hp : p ≠ 0)
    (hμ : Integrable (fun x => Real.exp (p * x)) μ)
    (hν : Integrable (fun x => Real.exp (p * x)) ν) :
    Integrable (fun t => (cdf μ t - cdf ν t) * Real.exp (p * t)) := by
  have hi := (integrable_cdfIndDiff_exp_prod hp hμ hν).integral_prod_left
  apply hi.congr
  apply ae_of_all
  intro t
  change (∫ z : ℝ × ℝ, cdfIndDiff z.1 z.2 t * Real.exp (p * t) ∂(μ.prod ν)) = _
  rw [integral_mul_const, ← cdf_sub_eq_integral_cdfIndDiff]

/-- The signed weighted-CDF identity: the same formula holds for both signs of `p ≠ 0`. -/
theorem integral_cdf_sub_mul_exp {p : ℝ} (hp : p ≠ 0)
    (hμ : Integrable (fun x => Real.exp (p * x)) μ)
    (hν : Integrable (fun x => Real.exp (p * x)) ν) :
    ∫ t, (cdf μ t - cdf ν t) * Real.exp (p * t) =
      (mgf id ν p - mgf id μ p) / p := by
  let f : ℝ → ℝ × ℝ → ℝ := fun t z => cdfIndDiff z.1 z.2 t * Real.exp (p * t)
  have hint : Integrable (Function.uncurry f) (volume.prod (μ.prod ν)) :=
    integrable_cdfIndDiff_exp_prod hp hμ hν
  have hswap := integral_integral_swap hint
  have hL : ∀ t, ∫ z : ℝ × ℝ, f t z ∂(μ.prod ν) =
      (cdf μ t - cdf ν t) * Real.exp (p * t) := by
    intro t
    dsimp [f]
    rw [integral_mul_const, ← cdf_sub_eq_integral_cdfIndDiff]
  have hR : ∀ z : ℝ × ℝ, ∫ t, f t z =
      (Real.exp (p * z.2) - Real.exp (p * z.1)) / p :=
    fun z => integral_cdfIndDiff_exp z.1 z.2 hp
  simp_rw [hL, hR] at hswap
  rw [hswap, integral_div, integral_sub (hν.comp_snd μ) (hμ.comp_fst ν),
    integral_fun_snd (fun y => Real.exp (p * y)),
    integral_fun_fst (fun x => Real.exp (p * x))]
  simp only [mgf, id_eq, probReal_univ, one_smul]

end EhrhardGaussian.GaussianConvexity
