/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Gaussian.Moments
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives
public import LeanPool.KLS.FunctionalInequalities.Probability.Product
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Basic
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Testing
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments

/-! # Moments and covariance under Gaussian smoothing -/

@[expose] public section

section

/-!
# Moments and covariance of Gaussian-smoothed laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5), regular approximation: the Gaussian
noise `γ_s` (kernel `e^{-s‖y‖²}`, variance `ε = 1/(2s)`) has mean zero and `∫⟪v,y⟫² = ‖v‖²/(2s)`;
the smoothed law `μ * γ_s` of a law with finite second moment keeps the mean and has covariance
`Cov μ + ε·Id`, with `∫‖y‖²` increased by `n ε`. As `s → ∞` the means, raw second moments and
covariance operators converge to those of `μ`. The weak convergence of the smoothed laws is in
`Approximation`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

open FunctionalInequalities.Probability.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


omit [CompleteSpace E] in
/-- The smoothed law `μ * γ_s` has a finite second moment when `μ` does. -/
theorem smoothedLaw_memLp_two (μ : Measure E) [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ)
    {s : ℝ} (hs : 0 < s) : MemLp id 2 (smoothedLaw μ s) := by
  let _ : IsProbabilityMeasure (Probability.Gaussian.law (V := E) s) :=
    Probability.Gaussian.law_probability hs
  unfold smoothedLaw Measure.conv
  apply
    (memLp_map_measure_iff continuous_id.aestronglyMeasurable
        (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)).2
  exact
    (hμ2.comp_fst (Probability.Gaussian.law s)).add
      ((Probability.Gaussian.memLp_two hs).comp_snd μ)


/-- Gaussian smoothing preserves the mean. -/
theorem smoothedLaw_mean (μ : Measure E) [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) {s : ℝ}
    (hs : 0 < s) : (∫ y : E, y ∂(smoothedLaw μ s)) = ∫ y : E, y ∂μ := by
  let _ : IsProbabilityMeasure (Probability.Gaussian.law (V := E) s) :=
    Probability.Gaussian.law_probability hs
  have hfirst : Integrable (fun p : E × E => p.1) (μ.prod (Probability.Gaussian.law s)) :=
    (hμ2.comp_fst (Probability.Gaussian.law s)).integrable one_le_two
  have hsecond : Integrable (fun p : E × E => p.2) (μ.prod (Probability.Gaussian.law s)) :=
    ((Probability.Gaussian.memLp_two hs).comp_snd μ).integrable one_le_two
  unfold smoothedLaw Measure.conv
  change
    (∫ y,
        id
          y ∂(Measure.map (fun p : E × E => p.1 + p.2) (μ.prod (Probability.Gaussian.law s)))) =
      _
  rw [integral_map (by fun_prop) continuous_id.aestronglyMeasurable]
  change (∫ p : E × E, p.1 + p.2 ∂(μ.prod (Probability.Gaussian.law s))) = _
  rw [integral_add hfirst hsecond, integral_fun_fst (fun y : E => y),
    integral_fun_snd (fun y : E => y), Probability.Gaussian.mean_zero hs]
  simp

-- Retain the existing CompleteSpace binder in this public interface.
/-- Variances add under smoothing: `Var_{μ*γ_s}⟪v,·⟫ = Var_μ⟪v,·⟫ + ‖v‖²/(2s)`. -/
theorem smoothedLaw_variance (μ : Measure E) [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ)
    {s : ℝ} (hs : 0 < s) (v : E) :
    variance (fun y : E => ⟪v, y⟫) (smoothedLaw μ s) =
      variance (fun y : E => ⟪v, y⟫) μ + ‖v‖ ^ 2 / (2 * s) := by
  let _ : IsProbabilityMeasure (Probability.Gaussian.law (V := E) s) :=
    Probability.Gaussian.law_probability hs
  have hX : MemLp (fun y : E => ⟪v, y⟫) 2 μ := by
    simpa only [id_eq, innerSL_apply_apply] using hμ2.continuousLinearMap_comp (innerSL ℝ v)
  have hY : MemLp (fun y : E => ⟪v, y⟫) 2 (Probability.Gaussian.law s) := by
    simpa only [id_eq, innerSL_apply_apply] using
      (Probability.Gaussian.memLp_two hs).continuousLinearMap_comp (innerSL ℝ v)
  have h := variance_add_prod hX hY
  rw [Probability.Gaussian.variance_inner hs] at h
  unfold smoothedLaw Measure.conv
  rw [variance_map (by fun_prop : AEMeasurable (fun y : E => ⟪v, y⟫) _)
      (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)]
  simpa only [Function.comp_def, inner_add_right] using h


/-- The covariance form of the smoothed law is `Cov_μ + ⟪·,·⟫/(2s)`. -/
theorem smoothedLaw_covarianceBilin (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v w : E) :
    covarianceBilin (smoothedLaw μ s) v w = covarianceBilin μ v w + ⟪v, w⟫ / (2 * s) := by
  let _ : IsProbabilityMeasure (smoothedLaw μ s) := smoothedLaw_probability hs
  have hsm2 := smoothedLaw_memLp_two μ hμ2 hs
  have hdiag (u : E) : covarianceBilin (smoothedLaw μ s) u u =
      covarianceBilin μ u u + ‖u‖ ^ 2 / (2 * s) := by
    rw [covarianceBilin_self hsm2, covarianceBilin_self hμ2]
    exact smoothedLaw_variance μ hμ2 hs u
  have hv := hdiag v
  have hw := hdiag w
  have hsum := hdiag (v + w)
  simp only [map_add, add_apply] at hsum
  rw [covarianceBilin_comm (μ := smoothedLaw μ s) w v, covarianceBilin_comm (μ := μ) w v,
    norm_add_sq_real] at hsum
  field_simp [hs.ne'] at hv hw hsum ⊢
  nlinarith

/--
**Covariance of the smoothed law**: `Cov(μ * γ_s) = Cov μ + (1/(2s)) · Id` (BKL Section 2, p. 5). -/
theorem smoothedLaw_covariance_operator (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
    Covariance.operator (smoothedLaw μ s) =
      Covariance.operator μ + (1 / (2 * s)) • (1 : E →L[ℝ] E) := by
  ext v
  apply ext_inner_right ℝ
  intro w
  rw [Covariance.operator_inner]
  simp only [add_apply, smul_apply, inner_add_left, real_inner_smul_left,
    Covariance.operator_inner]
  have hone : (1 : E →L[ℝ] E) v = v := rfl
  rw [hone]
  simpa only [one_div, one_mul, div_eq_mul_inv, mul_comm] using
    smoothedLaw_covarianceBilin μ hμ2 hs v w


/-- Raw directional second moments increase by `‖v‖²/(2s)`. -/
theorem smoothedLaw_inner_sq (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v : E) :
    (∫ y : E, ⟪v, y⟫ ^ 2 ∂(smoothedLaw μ s)) =
      (∫ y : E, ⟪v, y⟫ ^ 2 ∂μ) + ‖v‖ ^ 2 / (2 * s) := by
  let _ : IsProbabilityMeasure (smoothedLaw μ s) := smoothedLaw_probability hs
  have hsm2 := smoothedLaw_memLp_two μ hμ2 hs
  have hX : MemLp (fun y : E => ⟪v, y⟫) 2 μ := by
    simpa only [id_eq, innerSL_apply_apply] using hμ2.continuousLinearMap_comp (innerSL ℝ v)
  have hY : MemLp (fun y : E => ⟪v, y⟫) 2 (smoothedLaw μ s) := by
    simpa only [id_eq, innerSL_apply_apply] using hsm2.continuousLinearMap_comp (innerSL ℝ v)
  have hm : (∫ y : E, ⟪v, y⟫ ∂(smoothedLaw μ s)) = ∫ y : E, ⟪v, y⟫ ∂μ := by
    change (∫ y, (innerSL ℝ v) (id y) ∂(smoothedLaw μ s)) = ∫ y, (innerSL ℝ v) (id y) ∂μ
    rw [(innerSL ℝ v).integral_comp_comm (hsm2.integrable one_le_two),
      (innerSL ℝ v).integral_comp_comm (hμ2.integrable one_le_two)]
    congr 1
    simpa only [id_eq] using smoothedLaw_mean μ hμ2 hs
  have hv := smoothedLaw_variance μ hμ2 hs v
  rw [variance_eq_sub hY, variance_eq_sub hX, hm] at hv
  simp only [Pi.pow_apply] at hv
  linarith

/-- `∫ ‖y‖² d(μ*γ_s) = ∫ ‖y‖² dμ + n/(2s)`. -/
theorem smoothedLaw_norm_sq (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
    (∫ y : E, ‖y‖ ^ 2 ∂(smoothedLaw μ s)) =
      (∫ y : E, ‖y‖ ^ 2 ∂μ) + (Module.finrank ℝ E : ℝ) / (2 * s) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hsm2 := smoothedLaw_memLp_two μ hμ2 hs
  have hi (ν : Measure E) (hν : MemLp id 2 ν) (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun y : E => ⟪b i, y⟫ ^ 2) ν := by
    have h : MemLp (fun y : E => ⟪b i, y⟫) 2 ν := by
      simpa only [id_eq, innerSL_apply_apply] using hν.continuousLinearMap_comp (innerSL ℝ (b i))
    exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).1 h
  have heq : (fun y : E => ‖y‖ ^ 2) = fun y => ∑ i, ⟪b i, y⟫ ^ 2 := by
    funext y
    exact (b.sum_sq_inner_right y).symm
  rw [heq, integral_finsetSum Finset.univ (fun i _ => hi _ hsm2 i),
    integral_finsetSum Finset.univ (fun i _ => hi _ hμ2 i)]
  simp_rw [smoothedLaw_inner_sq μ hμ2 hs]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [b.norm_eq_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

private theorem epsilon_tendsto_zero :
    Tendsto (fun s : ℝ => 1 / (2 * s)) atTop (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (fun s : ℝ => 2 * s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  simpa only [Function.comp_def, one_div] using (tendsto_inv_atTop_zero.comp ht)

/-- The means of the smoothed laws converge (they are constant) as `s → ∞`. -/
theorem smoothedLaw_mean_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => ∫ y : E, y ∂(smoothedLaw μ s)) atTop (𝓝 (∫ y : E, y ∂μ)) := by
  apply (tendsto_const_nhds (x := ∫ y : E, y ∂μ)).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_mean μ hμ2 hs).symm

/-- The raw second moments of the smoothed laws converge as `s → ∞`. -/
theorem smoothedLaw_norm_sq_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => ∫ y : E, ‖y‖ ^ 2 ∂(smoothedLaw μ s)) atTop (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂μ)) := by
  have ht : Tendsto (fun s : ℝ => (∫ y : E, ‖y‖ ^ 2 ∂μ) + (Module.finrank ℝ E : ℝ) / (2 * s))
      atTop (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂μ)) := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_zero, add_zero] using
      (tendsto_const_nhds (x := ∫ y : E, ‖y‖ ^ 2 ∂μ)).add
        (epsilon_tendsto_zero.const_mul (Module.finrank ℝ E : ℝ))
  apply ht.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_norm_sq μ hμ2 hs).symm

/-- The covariance operators of the smoothed laws converge in operator norm as `s → ∞`. -/
theorem smoothedLaw_covariance_operator_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => Covariance.operator (smoothedLaw μ s)) atTop
      (𝓝 (Covariance.operator μ)) := by
  have ht :
    Tendsto (fun s : ℝ => Covariance.operator μ + (1 / (2 * s)) • (1 : E →L[ℝ] E)) atTop
      (𝓝 (Covariance.operator μ)) := by
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds (x := Covariance.operator μ)).add
        (epsilon_tendsto_zero.smul (tendsto_const_nhds (x := (1 : E →L[ℝ] E))))
  apply ht.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_covariance_operator μ hμ2 hs).symm

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing


end

/-! ### Fourth moments of Gaussian, smoothed and linear-image laws; translated Gaussian identity

`Probability.Gaussian.law s` has a fourth moment; fourth moments pass to smoothed laws and linear
images; the Gaussian directional identity for bounded Lipschitz `C¹` tests holds after a
translation. -/

section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem smoothedLaw_memLp_four (μ : Measure E) [IsProbabilityMeasure μ] (hμ4 : MemLp id 4 μ)
    {s : ℝ} (hs : 0 < s) : MemLp id 4 (smoothedLaw μ s) := by
  let _ : IsProbabilityMeasure (Probability.Gaussian.law (V := E) s) :=
    Probability.Gaussian.law_probability hs
  unfold smoothedLaw Measure.conv
  apply
    (memLp_map_measure_iff continuous_id.aestronglyMeasurable
        (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)).2
  exact
    (hμ4.comp_fst (Probability.Gaussian.law s)).add
      ((Probability.Gaussian.memLp_four hs).comp_snd μ)

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end
