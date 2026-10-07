/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedTrace

/-!
# Real-valued version of the normalized trace limit

The nonnegative extended-real strip estimate transfers to a real set
integral. This is the form used by the absorbed Carleman inequality.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal

noncomputable section

namespace ESS

/-- A normalized extended-real strip limit transfers to a real set
integral when the integrand is nonnegative and measurable. -/
theorem bu_short_real_strip_of_lintegral_limit
    (B : Set Vec3) (σ τ : ℝ) (hτ : 0 < τ)
    (f : Vec3 × ℝ → ℝ)
    (hfmeas : AEStronglyMeasurable f
      ((volume.restrict B).prod (volume.restrict (Ioo σ (σ + τ)))))
    (hf0 : ∀ q, 0 ≤ f q)
    (hH : Tendsto (fun ε : ℝ =>
      (∫⁻ t in Ioc (σ + ε) (σ + 2 * ε),
        ∫⁻ x, ENNReal.ofReal (f (x, t)) ∂(volume.restrict B)) /
        ENNReal.ofReal ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε : ℝ =>
      (∫ q in B ×ˢ Ioc (σ + ε) (σ + 2 * ε), f q
        ∂(volume : Measure (Vec3 × ℝ))) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let μfull : Measure (Vec3 × ℝ) :=
    (volume.restrict B).prod (volume.restrict (Ioo σ (σ + τ)))
  let H : ℝ → ℝ≥0∞ := fun ε =>
    (∫⁻ t in Ioc (σ + ε) (σ + 2 * ε),
      ∫⁻ x, ENNReal.ofReal (f (x, t)) ∂(volume.restrict B)) /
      ENNReal.ofReal ε ^ 2
  have hH' : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 0) := hH
  have hReal : Tendsto (fun ε => (H ε).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hH'
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 2 * ε < τ := by
    have hcont : Continuous (fun ε : ℝ => 2 * ε) := by fun_prop
    have hlim : Tendsto (fun ε : ℝ => 2 * ε)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [mul_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact hlim.eventually (Iio_mem_nhds hτ)
  have hHfinite : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), H ε < ⊤ :=
    hH'.eventually (Iio_mem_nhds (by simp : (0 : ℝ≥0∞) < ⊤))
  apply hReal.congr'
  filter_upwards [self_mem_nhdsWithin, hsmall, hHfinite] with ε hε hετ hHfin
  let strip : Set ℝ := Ioc (σ + ε) (σ + 2 * ε)
  let μstrip : Measure (Vec3 × ℝ) :=
    (volume.restrict B).prod (volume.restrict strip)
  have hsub : strip ⊆ Ioo σ (σ + τ) := by
    intro t ht
    have hεpos : 0 < ε := hε
    constructor
    · linarith only [hεpos, ht.1]
    · linarith only [ht.2, hετ]
  have hmeasure : μstrip = μfull.restrict (Set.univ ×ˢ strip) := by
    dsimp [μstrip, μfull]
    calc
      (volume.restrict B).prod (volume.restrict strip) =
          (volume.restrict B).prod
            ((volume.restrict (Ioo σ (σ + τ))).restrict strip) := by
        rw [Measure.restrict_restrict_of_subset hsub]
      _ = ((volume.restrict B).prod (volume.restrict (Ioo σ (σ + τ)))).restrict
          (Set.univ ×ˢ strip) := by
        simpa only [Measure.restrict_univ] using
          (Measure.prod_restrict (μ := volume.restrict B)
            (ν := volume.restrict (Ioo σ (σ + τ))) Set.univ strip)
  have hfmeasStrip : AEStronglyMeasurable f μstrip := by
    rw [hmeasure]
    exact hfmeas.mono_measure Measure.restrict_le_self
  let mass : ℝ≥0∞ :=
    ∫⁻ t in strip,
      ∫⁻ x, ENNReal.ofReal (f (x, t)) ∂(volume.restrict B)
  have hTonelli : (∫⁻ q, ENNReal.ofReal (f q) ∂μstrip) = mass := by
    exact lintegral_prod_symm _
      (ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        hfmeasStrip.aemeasurable)
  have he : ENNReal.ofReal ε ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hε)
  have hefin : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
  have hden0 : ENNReal.ofReal ε ^ 2 ≠ 0 := pow_ne_zero _ he
  have hdenfin : ENNReal.ofReal ε ^ 2 ≠ ⊤ := by simp
  have hmassFin : mass < ⊤ := by
    have hcancel := ENNReal.div_mul_cancel hden0 hdenfin (b := mass)
    have hdenFin : ENNReal.ofReal ε ^ 2 < ⊤ := by simp
    rw [← hcancel]
    exact ENNReal.mul_lt_top hHfin hdenFin
  have hfInt : Integrable f μstrip := by
    apply (lintegral_ofReal_ne_top_iff_integrable hfmeasStrip
      (Filter.Eventually.of_forall (fun q => hf0 q))).1
    rw [hTonelli]
    exact ne_of_lt hmassFin
  have hInt0 : 0 ≤ ∫ q, f q ∂μstrip := by
    apply integral_nonneg_of_ae
    exact Filter.Eventually.of_forall hf0
  have hOfReal : ENNReal.ofReal (∫ q, f q ∂μstrip) = mass := by
    rw [← hTonelli]
    exact ofReal_integral_eq_lintegral_ofReal hfInt
      (Filter.Eventually.of_forall hf0)
  have hset : (∫ q in B ×ˢ strip, f q
      ∂(volume : Measure (Vec3 × ℝ))) = ∫ q, f q ∂μstrip := by
    dsimp [μstrip]
    rw [Measure.prod_restrict]
    rfl
  change (H ε).toReal =
    (∫ q in B ×ˢ strip, f q ∂(volume : Measure (Vec3 × ℝ))) / ε ^ 2
  rw [hset, show H ε = mass / ENNReal.ofReal ε ^ 2 from rfl,
    ← hOfReal, ENNReal.toReal_div,
    ENNReal.toReal_ofReal hInt0]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le]

/-- A sectionwise trace estimate and finite time-derivative mass imply
vanishing normalized real quadratic mass on a bounded spatial set. -/
theorem bu_short_real_trace_strip_tendsto_zero
    (B : Set Vec3) (τ : ℝ) (hτ : 0 < τ)
    (hBfinite : volume B < ⊤)
    (f : Vec3 × ℝ → ℝ)
    (hfmeas : AEStronglyMeasurable f
      ((volume.restrict B).prod (volume.restrict (Ioo 0 τ))))
    (hf0 : ∀ q, 0 ≤ f q)
    (g : Vec3 × ℝ → ℝ≥0∞)
    (hgmeas : AEMeasurable g
      ((volume.restrict B).prod (volume.restrict (Ioo 0 τ))))
    (hgfin : (∫⁻ q, g q ∂((volume.restrict B).prod
      (volume.restrict (Ioo 0 τ)))) < ⊤)
    (htrace : ∀ t, 0 < t → t < τ →
      (∫⁻ x, ENNReal.ofReal (f (x, t)) ∂(volume.restrict B)) ≤
        ENNReal.ofReal t *
          ∫⁻ x, ∫⁻ s, g (x, s) ∂(volume.restrict (Ioc 0 t))
            ∂(volume.restrict B)) :
    Tendsto (fun ε : ℝ =>
      (∫ q in B ×ˢ Ioc ε (2 * ε), f q
        ∂(volume : Measure (Vec3 × ℝ))) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hinput := bu_short_trace_strip_tendsto_zero B τ hτ hBfinite
    (fun q => ENNReal.ofReal (f q)) g hgmeas hgfin htrace
  have hmain := bu_short_real_strip_of_lintegral_limit B 0 τ hτ f
    (by simpa only [zero_add] using hfmeas) hf0
    (by simpa only [zero_add] using hinput)
  simpa only [zero_add] using hmain

end ESS
