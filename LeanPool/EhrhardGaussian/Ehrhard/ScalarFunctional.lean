/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.CorrelatedFunctional

/-! # Scalar functional Ehrhard inequality after the correlation limit -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- A pointwise correlated scalar comparison yields the corresponding inequality between Gaussian
mean quantiles. -/
theorem correlated_functional_comparison_explicit {u v w : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (hutail : Tendsto u (cocompact ℝ) atBot) (hvtail : Tendsto v (cocompact ℝ) atBot)
    (hwtail : Tendsto w (cocompact ℝ) atBot)
    {p q ρ σ U V : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1)
    (hρ : |ρ| < 1) (hσ : 0 < σ) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (huU : ∀ x, u x ≤ U) (hvV : ∀ y, v y ≤ V)
    (horiginal : ∀ x y, p * u x + q * v y ≤ σ * w (p * x + q * y)) :
    p * gaussianCDFChart.symm (scaledGaussianMean (fun x => gaussianCDF (u x)) 1) +
      q * gaussianCDFChart.symm (scaledGaussianMean (fun x => gaussianCDF (v x)) 1) ≤
        σ * gaussianCDFChart.symm (scaledGaussianMean (fun x => gaussianCDF (w x)) σ) := by
  have h := correlated_functional_comparison hu hv hw hutail hvtail hwtail hp hq hsum hρ hσ hvar huU
    hvV horiginal
  rw [quantileLinear_tripleTheta] at h
  simpa only [tripleLinearForm, quantileVector, tripleScales, Matrix.cons_val] using sub_nonpos.mp h

/-- The scalar functional Ehrhard inequality follows from a pointwise convex combination bound and
decay at infinity. -/
theorem scalar_functional_ehrhard {u v w : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (hutail : Tendsto u (cocompact ℝ) atBot) (hvtail : Tendsto v (cocompact ℝ) atBot)
    (hwtail : Tendsto w (cocompact ℝ) atBot)
    {p q U V : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1)
    (huU : ∀ x, u x ≤ U) (hvV : ∀ y, v y ≤ V)
    (horiginal : ∀ x y, p * u x + q * v y ≤ w (p * x + q * y)) :
    p * gaussianCDFChart.symm (scaledGaussianMean (fun x => gaussianCDF (u x)) 1) +
      q * gaussianCDFChart.symm (scaledGaussianMean (fun x => gaussianCDF (v x)) 1) ≤
        gaussianCDFChart.symm (scaledGaussianMean (fun x => gaussianCDF (w x)) 1) := by
  let ρ := fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)
  let σ := fun n : ℕ => Real.sqrt (p ^ 2 + q ^ 2 + 2 * p * q * ρ n)
  have hρnonneg (n) : 0 ≤ ρ n := by
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one hden).mpr (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith only [hn])
    exact sub_nonneg.mpr hle
  have hρ (n) : |ρ n| < 1 := by
    rw [abs_of_nonneg (hρnonneg n)]
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    dsimp only [ρ]
    linarith only [hpos]
  have hrad (n) : 0 < p ^ 2 + q ^ 2 + 2 * p * q * ρ n := by
    have hc := mul_nonneg (by positivity : 0 ≤ 2 * p * q) (hρnonneg n)
    have hp₂ := sq_pos_of_pos hp
    nlinarith only [hp₂, sq_nonneg q, hc]
  have hσ (n) : 0 < σ n := Real.sqrt_pos.mpr (hrad n)
  have hvar (n) : σ n ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ n := Real.sq_sqrt (hrad n).le
  have hρlim : Tendsto ρ atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hradlim : Tendsto (fun n => p ^ 2 + q ^ 2 + 2 * p * q * ρ n) atTop (𝓝 (1 : ℝ)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => p ^ 2 + q ^ 2) atTop (𝓝 (p ^ 2 + q ^
      2))).add
      (hρlim.const_mul (2 * p * q))
    have hsq := congrArg (fun z : ℝ => z ^ 2) hsum
    have hvalue : p ^ 2 + q ^ 2 + 2 * p * q * 1 = 1 := by nlinarith only [hsq]
    simpa only [hvalue] using h
  have hσlim : Tendsto σ atTop (𝓝 1) := by simpa only [σ, Real.sqrt_one] using hradlim.sqrt
  let m := fun n => ∫ z, gaussianCDF (w (σ n * z) / σ n) ∂gaussianReal 0 1
  have hmlim : Tendsto m atTop (𝓝 (scaledGaussianMean (fun x => gaussianCDF (w x)) 1)) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 1)
      (l := (atTop : Filter ℕ)) (F := fun n z => gaussianCDF (w (σ n * z) / σ n))
      (f := fun z => gaussianCDF (w z)) (fun _ => (1 : ℝ))
      (Eventually.of_forall fun n =>
        (continuous_gaussianCDF.comp ((hw.comp
          (by fun_prop : Continuous (fun z : ℝ => σ n * z))).div_const (σ n))).aestronglyMeasurable)
      (Eventually.of_forall fun n => ae_of_all _ fun z => by
        simpa only [Function.comp_def, Real.norm_eq_abs, abs_of_pos (gaussianCDF_pos _)] using
          (gaussianCDF_lt_one (w (σ n * z) / σ n)).le)
      (integrable_const 1) (ae_of_all _ fun z => ?_)
    · simpa only [m, scaledGaussianMean, one_mul] using h
    · have hz : Tendsto (fun n => σ n * z) atTop (𝓝 z) := by
        simpa only [one_mul] using hσlim.mul_const z
      have hwlim := (hw.tendsto z).comp hz
      have hdlim := hwlim.div hσlim one_ne_zero
      have hlim := continuous_gaussianCDF.continuousAt.tendsto.comp hdlim
      simpa only [Function.comp_def, Pi.div_def, one_mul, div_one] using hlim
  have hm : scaledGaussianMean (fun x => gaussianCDF (w x)) 1 ∈ Ioo (0 : ℝ) 1 :=
    integral_gaussianCDF_mem_Ioo (gaussianReal 0 1) (hw.measurable.comp (by fun_prop))
  have hchart := (contDiffAt_gaussianCDFChart_symm hm).continuousAt.tendsto.comp hmlim
  have hright := hσlim.mul hchart
  have hcomparison (n) := correlated_functional_comparison_explicit hu hv (hw.div_const (σ n))
    hutail hvtail (hwtail.atBot_div_const (hσ n)) hp hq hsum (hρ n) (hσ n) (hvar n) huU hvV
    (fun x y => by simpa only [mul_div_cancel₀ _ (hσ n).ne'] using horiginal x y)
  have hle := ge_of_tendsto hright (Eventually.of_forall hcomparison)
  simpa only [one_mul] using hle

end EhrhardGaussian.Ehrhard

end
