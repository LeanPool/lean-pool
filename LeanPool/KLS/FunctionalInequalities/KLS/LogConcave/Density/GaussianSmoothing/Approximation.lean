/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Pointwise approximation by normalized Gaussian smoothing

The normalized Gaussian kernel forms a peak function. At every continuity
point of an actual Borell density, the smoothed density converges to the
source value as inverse variance tends to infinity. This is a pointwise
statement; convergence of laws and geometric/Poincare stability are separate.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter Topology Bornology
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

open FunctionalInequalities.Probability.Gaussian
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem normalizedKernel_scale (c : ℝ) (hc : 0 < c) (z : V) :
    normalizedKernel (c ^ 2) z = c ^ Module.finrank ℝ V * normalizedKernel 1 (c • z) := by
  unfold normalizedKernel kernel mass
  have hpow :
    (Real.pi / c ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) =
      Real.pi ^ ((Module.finrank ℝ V : ℝ) / 2) / c ^ Module.finrank ℝ V := by
    rw [Real.div_rpow Real.pi_nonneg (sq_nonneg _)]
    have hd : (c ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) = c ^ Module.finrank ℝ V := by
      calc
        (c ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) =
            (c ^ (2 : ℝ)) ^ ((Module.finrank ℝ V : ℝ) / 2) :=
          congrArg (fun x : ℝ => x ^ ((Module.finrank ℝ V : ℝ) / 2))
            (Real.rpow_natCast c 2).symm
        _ = c ^ ((2 : ℝ) * ((Module.finrank ℝ V : ℝ) / 2)) := (Real.rpow_mul hc.le _ _).symm
        _ = c ^ (Module.finrank ℝ V : ℝ) := by congr 1; ring
        _ = c ^ Module.finrank ℝ V := Real.rpow_natCast c _
    rw [hd]
  rw [hpow]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow]
  have he : -c ^ 2 * ‖z‖ ^ 2 = -(c * ‖z‖) ^ 2 := by ring
  rw [he]
  field_simp

private theorem source_integrable {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ) :
    Integrable ρ (volume : Measure V) := by
  apply (lintegral_ofReal_ne_top_iff_integrable hρ.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hρ.nonneg x)).mp
  have hmass : (∫⁻ x : V, ENNReal.ofReal (ρ x)) = 1 := by
    have h : ν univ = 1 := measure_univ
    rw [← hρ.withDensity_eq, withDensity_apply _ MeasurableSet.univ] at h
    simpa only [Measure.restrict_univ] using h
  rw [hmass]
  simp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem tendsto_norm_pow_normalizedKernel_one :
    Tendsto (fun z : V => ‖z‖ ^ Module.finrank ℝ V * normalizedKernel 1 z)
      (cobounded V) (𝓝 0) := by
  have A : Tendsto (fun z : V => ‖z‖ ^ 2) (cobounded V) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
  have B := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((Module.finrank ℝ V : ℝ) / 2) 1 zero_lt_one).comp A
  have C := B.const_mul (mass (V := V) 1)⁻¹
  rw [mul_zero] at C
  convert C using 2 with z
  simp only [normalizedKernel, kernel, mass, div_one, Function.comp_apply]
  have hnorm : (‖z‖ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) =
      ‖z‖ ^ Module.finrank ℝ V := by
    calc
      (‖z‖ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) =
          (‖z‖ ^ (2 : ℝ)) ^ ((Module.finrank ℝ V : ℝ) / 2) :=
            congrArg (fun x : ℝ => x ^ ((Module.finrank ℝ V : ℝ) / 2))
              (Real.rpow_natCast ‖z‖ 2).symm
      _ = ‖z‖ ^ ((2 : ℝ) * ((Module.finrank ℝ V : ℝ) / 2)) :=
        (Real.rpow_mul (norm_nonneg z) _ _).symm
      _ = ‖z‖ ^ (Module.finrank ℝ V : ℝ) := by congr 1; ring
      _ = ‖z‖ ^ Module.finrank ℝ V := Real.rpow_natCast ‖z‖ _
  rw [hnorm]
  ring

/-- At each continuity point of the source Borell density, Gaussian smoothing
recovers that density as its inverse length scale tends to infinity. -/
private theorem normalizedDensity_tendsto_at_continuity_sq {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {x : V} (hx : ContinuousAt ρ x) :
    Tendsto (fun c : ℝ => normalizedDensity ρ (c ^ 2) x) atTop (𝓝 (ρ x)) := by
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable'
    (μ := (volume : Measure V)) (φ := normalizedKernel (V := V) 1)
    (fun z => (normalizedKernel_pos one_pos z).le)
    (integral_normalizedKernel (V := V) one_pos)
    (tendsto_norm_pow_normalizedKernel_one (V := V))
    (source_integrable hρ) hx
  apply hpeak.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  rw [normalizedDensity_eq_integral hρ (sq_pos_of_pos hc) x]
  rw [← hρ.withDensity_eq]
  rw [integral_withDensity_eq_integral_toReal_smul
    hρ.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (hρ.nonneg y), normalizedKernel_scale c hc (x - y)]
  simp only [smul_eq_mul]
  ring

/-- The normalized Gaussian smoothing density tends to the source Borell
density at every continuity point as the inverse variance tends to infinity. -/
theorem normalizedDensity_tendsto_at_continuity {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {x : V} (hx : ContinuousAt ρ x) :
    Tendsto (fun s : ℝ => normalizedDensity ρ s x) atTop (𝓝 (ρ x)) := by
  have h := (normalizedDensity_tendsto_at_continuity_sq hρ hx).comp
    Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [Ici_mem_atTop (0 : ℝ)] with s hs
  change normalizedDensity ρ ((√s) ^ 2) x = normalizedDensity ρ s x
  rw [Real.sq_sqrt hs]

/-- The actual normalized Gaussian density converges to the source Borell
density Haar-almost everywhere. This statement does not yet give convergence
of the associated probability measures. -/
theorem normalizedDensity_ae_tendsto {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) :
    ∀ᵐ x ∂(volume : Measure V),
      Tendsto (fun s : ℝ => normalizedDensity ρ s x) atTop (𝓝 (ρ x)) :=
  (hρ.ae_continuous).mono fun _ hx => normalizedDensity_tendsto_at_continuity hρ hx

private theorem tendsto_integral_min {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) :
    Tendsto (fun s : ℝ => ∫ x : V, min (normalizedDensity ρ s x) (ρ x))
      atTop (𝓝 (∫ x : V, ρ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound := ρ)
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
    exact ((normalizedDensity_measurable hρ.measurable hs).min hρ.measurable).aestronglyMeasurable
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
    exact Filter.Eventually.of_forall fun x => by
      have h0 : 0 ≤ min (normalizedDensity ρ s x) (ρ x) :=
        le_min (normalizedDensity_pos hρ hs x).le (hρ.nonneg x)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact min_le_right _ _
  · apply (lintegral_ofReal_ne_top_iff_integrable hρ.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hρ.nonneg x)).mp
    have hmass : (∫⁻ x : V, ENNReal.ofReal (ρ x)) = 1 := by
      have h : ν univ = 1 := measure_univ
      rw [← hρ.withDensity_eq, withDensity_apply _ MeasurableSet.univ] at h
      simpa only [Measure.restrict_univ] using h
    rw [hmass]
    simp
  · filter_upwards [normalizedDensity_ae_tendsto hρ] with x hx
    simpa only [min_self] using hx.min (tendsto_const_nhds (x := ρ x))


private theorem source_integral_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) :
    ∫ x : V, ρ x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => hρ.nonneg x)
    hρ.measurable.aestronglyMeasurable]
  have h : ν univ = 1 := measure_univ
  rw [← hρ.withDensity_eq, withDensity_apply _ MeasurableSet.univ] at h
  simpa only [Measure.restrict_univ, ENNReal.toReal_one] using congrArg ENNReal.toReal h

private theorem integrable_min {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : V => min (normalizedDensity ρ s x) (ρ x)) volume := by
  apply (source_integrable hρ).mono'
  · exact ((normalizedDensity_measurable hρ.measurable hs).min hρ.measurable).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (normalizedDensity_pos hρ hs x).le (hρ.nonneg x))]
      exact min_le_right _ _

/-- Normalized Gaussian smoothing converges to the source Borell density
in `L¹(volume)` as inverse variance tends to infinity. The proof uses
unit mass and dominated convergence for the pointwise minimum. -/
theorem normalizedDensity_tendsto_L1 {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) :
    Tendsto (fun s : ℝ => ∫ x : V, |normalizedDensity ρ s x - ρ x|)
      atTop (𝓝 0) := by
  have heq (s : ℝ) (hs : 0 < s) :
      (∫ x : V, |normalizedDensity ρ s x - ρ x|) =
        (∫ x : V, normalizedDensity ρ s x) + (∫ x : V, ρ x) -
          2 * (∫ x : V, min (normalizedDensity ρ s x) (ρ x)) := by
    have hp (x : V) : |normalizedDensity ρ s x - ρ x| =
        normalizedDensity ρ s x + ρ x - 2 * min (normalizedDensity ρ s x) (ρ x) := by
      rcases le_total (normalizedDensity ρ s x) (ρ x) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    simp_rw [hp]
    calc
      (∫ x : V, normalizedDensity ρ s x + ρ x -
          2 * min (normalizedDensity ρ s x) (ρ x)) =
          (∫ x : V, normalizedDensity ρ s x + ρ x) -
            (∫ x : V, 2 * min (normalizedDensity ρ s x) (ρ x)) :=
        integral_sub ((integrable_normalizedDensity hρ hs).add (source_integrable hρ))
          ((integrable_min hρ hs).const_mul 2)
      _ = _ := by rw [integral_add (integrable_normalizedDensity hρ hs)
        (source_integrable hρ), integral_const_mul]
  have hlim : Tendsto (fun s : ℝ =>
      (2 : ℝ) - 2 * (∫ x : V, min (normalizedDensity ρ s x) (ρ x)))
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).sub
      ((tendsto_integral_min hρ).const_mul 2)
    simpa [source_integral_eq_one hρ] using h
  apply hlim.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  rw [heq s hs, integral_normalizedDensity_eq_one hρ hs, source_integral_eq_one hρ]
  norm_num

/-- `L¹` convergence gives convergence of the density integral on every set. -/
theorem normalizedDensity_setIntegral_tendsto {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) (D : Set V) :
    Tendsto (fun s : ℝ => ∫ x in D, normalizedDensity ρ s x)
      atTop (𝓝 (∫ x in D, ρ x)) := by
  have hbound (s : ℝ) (hs : 0 < s) :
      |(∫ x in D, normalizedDensity ρ s x) - (∫ x in D, ρ x)| ≤
        ∫ x : V, |normalizedDensity ρ s x - ρ x| := by
    rw [← integral_sub (μ := (volume : Measure V).restrict D)
      (integrable_normalizedDensity hρ hs).integrableOn
      (source_integrable hρ).integrableOn]
    exact (abs_integral_le_integral_abs).trans
      (setIntegral_le_integral
        ((integrable_normalizedDensity hρ hs).sub (source_integrable hρ)).abs
        (Filter.Eventually.of_forall fun x => abs_nonneg _))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (Filter.Eventually.of_forall fun s => norm_nonneg
    ((∫ x in D, normalizedDensity ρ s x) - (∫ x in D, ρ x))) ?_
    (normalizedDensity_tendsto_L1 hρ)
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  simpa only [Real.norm_eq_abs] using hbound s hs


/-- The actual normalized Gaussian convolution laws converge setwise to the
source law on every measurable set. -/
theorem smoothedLaw_set_tendsto {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {D : Set V} (hD : MeasurableSet D) :
    Tendsto (fun s : ℝ => (smoothedLaw ν s) D) atTop (𝓝 (ν D)) := by
  have hsource : ν D = ENNReal.ofReal (∫ x in D, ρ x) := by
    rw [← hρ.withDensity_eq, withDensity_apply _ hD]
    exact (ofReal_integral_eq_lintegral_ofReal
      (source_integrable hρ).integrableOn
      (Filter.Eventually.of_forall fun x => hρ.nonneg x)).symm
  have hsmooth (s : ℝ) (hs : 0 < s) :
      (smoothedLaw ν s) D =
        ENNReal.ofReal (∫ x in D, normalizedDensity ρ s x) := by
    rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs, withDensity_apply _ hD]
    exact (ofReal_integral_eq_lintegral_ofReal
      (integrable_normalizedDensity hρ hs).integrableOn
      (Filter.Eventually.of_forall fun x => (normalizedDensity_pos hρ hs x).le)).symm
  rw [hsource]
  apply (ENNReal.tendsto_ofReal (normalizedDensity_setIntegral_tendsto hρ D)).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (hsmooth s hs).symm

section WeakConvergence

open Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem density_integral (g : E → ℝ) (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y)
    (f : BoundedContinuousFunction E ℝ) :
    (∫ y, f y ∂(volume.withDensity (fun y => ENNReal.ofReal (g y)))) = ∫ y : E, g y * f y := by
  rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
      (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (hg0 y), smul_eq_mul]

private theorem bounded_density_integrable {g : E → ℝ} (hg : Integrable g volume)
    (f : BoundedContinuousFunction E ℝ) : Integrable (fun y => g y * f y) volume := by
  refine (hg.norm.mul_const ‖f‖).mono'
    (hg.aestronglyMeasurable.mul f.continuous.measurable.aestronglyMeasurable) ?_
  filter_upwards [] with y
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg _)

/--
Integrals of bounded continuous functions against the smoothed laws converge to those against `μ`
(`L¹` convergence of the normalized densities). -/
theorem smoothedLaw_integral_bounded_tendsto {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) (f : BoundedContinuousFunction E ℝ) :
    Tendsto (fun s : ℝ => ∫ y, f y ∂(smoothedLaw μ s)) atTop (𝓝 (∫ y, f y ∂μ)) := by
  have hρi := source_integrable hρ
  have hlim :
    Tendsto (fun s : ℝ => ‖f‖ * ∫ y : E, |normalizedDensity ρ s y - ρ y|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (normalizedDensity_tendsto_L1 hρ).const_mul ‖f‖
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hlim
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  have hFi := integrable_normalizedDensity hρ hs
  have hFd := bounded_density_integrable hFi f
  have hρd := bounded_density_integrable hρi f
  have hdiff := hFi.sub hρi
  have hD := bounded_density_integrable hdiff f
  have hEq :
    (∫ y, f y ∂(smoothedLaw μ s)) - (∫ y, f y ∂μ) =
      ∫ y : E, (normalizedDensity ρ s y - ρ y) * f y := by
    rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs, ← hρ.withDensity_eq,
      density_integral _ (normalizedDensity_measurable hρ.measurable hs)
        (fun y => (normalizedDensity_pos hρ hs y).le),
      density_integral _ hρ.measurable hρ.nonneg, ← integral_sub hFd hρd]
    congr 1
    funext y
    ring
  rw [hEq]
  calc
    ‖∫ y : E, (normalizedDensity ρ s y - ρ y) * f y‖ ≤
        ∫ y : E, ‖(normalizedDensity ρ s y - ρ y) * f y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : E, |normalizedDensity ρ s y - ρ y| * ‖f‖ := by
      apply integral_mono hD.norm (hdiff.abs.mul_const ‖f‖)
      intro y
      change ‖(normalizedDensity ρ s y - ρ y) * f y‖ ≤ |normalizedDensity ρ s y - ρ y| * ‖f‖
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (abs_nonneg _)
    _ = ‖f‖ * ∫ y : E, |normalizedDensity ρ s y - ρ y| := by rw [integral_mul_const]; ring

/-- **Weak convergence of the Gaussian smoothing**: `μ * γ_{n+1} → μ` in the topology of weak
convergence of probability laws (BKL Section 2, p. 5). -/
theorem smoothedProbabilityLaw_tendsto {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) :
    Tendsto (fun n : ℕ => smoothedProbabilityLaw μ ((n : ℝ) + 1) (by positivity)) atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
  intro f
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact (smoothedLaw_integral_bounded_tendsto hρ f).comp hn

end WeakConvergence

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
