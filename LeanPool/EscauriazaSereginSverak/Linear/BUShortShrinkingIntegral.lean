/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortFixedWeight
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Absolute continuity on shrinking time strips

An integrable nonnegative space-time function has vanishing integral on
bounded spatial sets as the time strip shrinks to the initial face.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal

noncomputable section

namespace ESS

/-- Product volume of a bounded spatial set and a shrinking initial-time
strip tends to zero. -/
theorem bu_short_product_measure_shrinking
    (B : Set Vec3) (τ : ℝ)
    (hBfinite : volume B < ⊤) :
    Tendsto (fun ε : ℝ =>
      ((volume.restrict B).prod (volume.restrict (Ioo 0 τ)))
        (Set.univ ×ˢ Ioc 0 (2 * ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let μB : Measure Vec3 := volume.restrict B
  let μT : Measure ℝ := volume.restrict (Ioo 0 τ)
  have hupper : Tendsto (fun ε : ℝ =>
      (volume B) * ENNReal.ofReal (2 * ε))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hreal : Tendsto (fun ε : ℝ => 2 * ε)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcon : Continuous (fun ε : ℝ => (2 : ℝ) * ε) := by fun_prop
      simpa only [mul_zero] using (hcon.tendsto 0).mono_left nhdsWithin_le_nhds
    have hofreal : Tendsto (fun ε : ℝ => ENNReal.ofReal (2 * ε))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hofreal (Or.inr (ne_of_lt hBfinite))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun _ => zero_le) (fun ε => ?_)
  change (μB.prod μT) (Set.univ ×ˢ Ioc 0 (2 * ε)) ≤
    volume B * ENNReal.ofReal (2 * ε)
  rw [Measure.prod_prod]
  have hμB : μB Set.univ = volume B := by
    simp only [μB, Measure.restrict_apply_univ]
  rw [hμB]
  apply mul_le_mul_of_nonneg_left
  · change volume.restrict (Ioo 0 τ) (Ioc 0 (2 * ε)) ≤
      ENNReal.ofReal (2 * ε)
    rw [Measure.restrict_apply measurableSet_Ioc]
    calc
      volume (Ioc 0 (2 * ε) ∩ Ioo 0 τ) ≤
          volume (Ioc 0 (2 * ε)) :=
        measure_mono (Set.inter_subset_left :
          Ioc 0 (2 * ε) ∩ Ioo 0 τ ⊆ Ioc 0 (2 * ε))
      _ = ENNReal.ofReal (2 * ε) := by
        rw [Real.volume_Ioc]
        simp
  · exact zero_le

/-- Finite product-space mass vanishes on the shrinking time strip. -/
theorem bu_short_product_lintegral_shrinking
    (B : Set Vec3) (τ : ℝ)
    (hBfinite : volume B < ⊤)
    (f : Vec3 × ℝ → ℝ≥0∞)
    (hf : (∫⁻ q, f q ∂((volume.restrict B).prod
      (volume.restrict (Ioo 0 τ)))) < ⊤) :
    Tendsto (fun ε : ℝ =>
      ∫⁻ q in (Set.univ ×ˢ Ioc 0 (2 * ε)), f q
        ∂((volume.restrict B).prod (volume.restrict (Ioo 0 τ))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact tendsto_setLIntegral_zero (ne_of_lt hf)
    (bu_short_product_measure_shrinking B τ hBfinite)

/-- Tonelli gives the same shrinking limit with space integrated outside
time, as in the small-time trace estimate. -/
theorem bu_short_nested_lintegral_shrinking
    (B : Set Vec3) (τ : ℝ) (hτ : 0 < τ)
    (hBfinite : volume B < ⊤)
    (f : Vec3 × ℝ → ℝ≥0∞)
    (hfmeas : AEMeasurable f
      ((volume.restrict B).prod (volume.restrict (Ioo 0 τ))))
    (hf : (∫⁻ q, f q ∂((volume.restrict B).prod
      (volume.restrict (Ioo 0 τ)))) < ⊤) :
    Tendsto (fun ε : ℝ =>
      ∫⁻ x, ∫⁻ s, f (x, s) ∂(volume.restrict (Ioc 0 (2 * ε)))
        ∂(volume.restrict B))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let μB : Measure Vec3 := volume.restrict B
  let μT : Measure ℝ := volume.restrict (Ioo 0 τ)
  have hbase := bu_short_product_lintegral_shrinking B τ hBfinite f hf
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 2 * ε < τ := by
    have hcont : Continuous (fun ε : ℝ => 2 * ε) := by fun_prop
    have hlim : Tendsto (fun ε : ℝ => 2 * ε)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [mul_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact hlim.eventually (Iio_mem_nhds hτ)
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hετ
  have hsub : Ioc 0 (2 * ε) ⊆ Ioo 0 τ := by
    intro s hs
    exact ⟨hs.1, hs.2.trans_lt hετ⟩
  have hmeasure :
      μB.prod (volume.restrict (Ioc 0 (2 * ε))) =
        (μB.prod μT).restrict (Set.univ ×ˢ Ioc 0 (2 * ε)) := by
    calc
      μB.prod (volume.restrict (Ioc 0 (2 * ε))) =
          μB.prod (μT.restrict (Ioc 0 (2 * ε))) := by
        rw [Measure.restrict_restrict_of_subset hsub]
      _ = (μB.prod μT).restrict (Set.univ ×ˢ Ioc 0 (2 * ε)) := by
        simpa only [Measure.restrict_univ] using
          (Measure.prod_restrict (μ := μB) (ν := μT)
            Set.univ (Ioc 0 (2 * ε)))
  have hfmeas' : AEMeasurable f
      (μB.prod (volume.restrict (Ioc 0 (2 * ε)))) := by
    rw [hmeasure]
    exact hfmeas.mono_measure (Measure.restrict_le_self)
  have htonelli := lintegral_lintegral (μ := μB)
    (ν := volume.restrict (Ioc 0 (2 * ε)))
    (f := fun x s => f (x, s)) hfmeas'
  rw [hmeasure] at htonelli
  exact htonelli.symm

end ESS
