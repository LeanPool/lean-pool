/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShrinkingIntegral
public import LeanPool.EscauriazaSereginSverak.Linear.SmallTimeTrace

/-!
# Vanishing normalized mass in the lower-time strip

The small-time trace estimate supplies two powers of the strip width.
Absolute continuity of the time derivative's quadratic integral then
removes the normalized lower-time cutoff error.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal

noncomputable section

namespace ESS

/-- A sectionwise trace inequality bounds the mass of a time strip by
its squared width times the derivative mass below the strip. -/
theorem bu_short_trace_strip_bound
    (B : Set Vec3) (τ ε : ℝ) (hε : 0 < ε) (hετ : 2 * ε < τ)
    (f g : Vec3 × ℝ → ℝ≥0∞)
    (htrace : ∀ t, 0 < t → t < τ →
      (∫⁻ x, f (x, t) ∂(volume.restrict B)) ≤
        ENNReal.ofReal t *
          ∫⁻ x, ∫⁻ s, g (x, s) ∂(volume.restrict (Ioc 0 t))
            ∂(volume.restrict B)) :
    (∫⁻ t in Ioc ε (2 * ε),
      ∫⁻ x, f (x, t) ∂(volume.restrict B)) ≤
      2 * ENNReal.ofReal ε ^ 2 *
        (∫⁻ x, ∫⁻ s, g (x, s) ∂(volume.restrict (Ioc 0 (2 * ε)))
          ∂(volume.restrict B)) := by
  let Q : ℝ≥0∞ :=
    ∫⁻ x, ∫⁻ s, g (x, s) ∂(volume.restrict (Ioc 0 (2 * ε)))
      ∂(volume.restrict B)
  have hpoint (t : ℝ) (ht : t ∈ Ioc ε (2 * ε)) :
      (∫⁻ x, f (x, t) ∂(volume.restrict B)) ≤
        ENNReal.ofReal (2 * ε) * Q := by
    have ht0 : 0 < t := hε.trans ht.1
    have htle : t ≤ 2 * ε := ht.2
    have htail :
        (∫⁻ x, ∫⁻ s, g (x, s) ∂(volume.restrict (Ioc 0 t))
          ∂(volume.restrict B)) ≤ Q := by
      apply lintegral_mono
      intro x
      exact lintegral_mono_set (fun s hs => ⟨hs.1, hs.2.trans htle⟩)
    have htime : ENNReal.ofReal t ≤ ENNReal.ofReal (2 * ε) :=
      ENNReal.ofReal_le_ofReal htle
    calc
      _ ≤ ENNReal.ofReal t *
          (∫⁻ x, ∫⁻ s, g (x, s) ∂(volume.restrict (Ioc 0 t))
            ∂(volume.restrict B)) := htrace t ht0 (htle.trans_lt hετ)
      _ ≤ ENNReal.ofReal (2 * ε) * Q := by gcongr
  have hmass :
      (∫⁻ t in Ioc ε (2 * ε),
        ∫⁻ x, f (x, t) ∂(volume.restrict B)) ≤
        ENNReal.ofReal (2 * ε) * Q *
          volume (Ioc ε (2 * ε)) := by
    calc
      _ ≤ ∫⁻ t in Ioc ε (2 * ε), ENNReal.ofReal (2 * ε) * Q := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpoint t ht
      _ = ENNReal.ofReal (2 * ε) * Q *
            volume (Ioc ε (2 * ε)) := by
        rw [lintegral_const, Measure.restrict_apply_univ]
  calc
    _ ≤ ENNReal.ofReal (2 * ε) * Q *
        volume (Ioc ε (2 * ε)) := hmass
    _ = 2 * ENNReal.ofReal ε ^ 2 * Q := by
      rw [Real.volume_Ioc]
      have hvol : ENNReal.ofReal (2 * ε - ε) = ENNReal.ofReal ε := by
        congr 1
        ring
      rw [hvol, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
      ring

/-- The normalized strip mass tends to zero when the time derivative has
finite quadratic mass on the fixed spatial cylinder. -/
theorem bu_short_trace_strip_tendsto_zero
    (B : Set Vec3) (τ : ℝ) (hτ : 0 < τ)
    (hBfinite : volume B < ⊤)
    (f g : Vec3 × ℝ → ℝ≥0∞)
    (hgmeas : AEMeasurable g
      ((volume.restrict B).prod (volume.restrict (Ioo 0 τ))))
    (hgfin : (∫⁻ q, g q ∂((volume.restrict B).prod
      (volume.restrict (Ioo 0 τ)))) < ⊤)
    (htrace : ∀ t, 0 < t → t < τ →
      (∫⁻ x, f (x, t) ∂(volume.restrict B)) ≤
        ENNReal.ofReal t *
          ∫⁻ x, ∫⁻ s, g (x, s) ∂(volume.restrict (Ioc 0 t))
            ∂(volume.restrict B)) :
    Tendsto (fun ε : ℝ =>
      (∫⁻ t in Ioc ε (2 * ε),
        ∫⁻ x, f (x, t) ∂(volume.restrict B)) /
          ENNReal.ofReal ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let Q : ℝ → ℝ≥0∞ := fun ε =>
    ∫⁻ x, ∫⁻ s, g (x, s) ∂(volume.restrict (Ioc 0 (2 * ε)))
      ∂(volume.restrict B)
  have hQ : Tendsto Q (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    bu_short_nested_lintegral_shrinking B τ hτ hBfinite g hgmeas hgfin
  have hupper : Tendsto (fun ε : ℝ => 2 * Q ε)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hQ (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 2 * ε < τ := by
    have hcont : Continuous (fun ε : ℝ => 2 * ε) := by fun_prop
    have hlim : Tendsto (fun ε : ℝ => 2 * ε)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [mul_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact hlim.eventually (Iio_mem_nhds hτ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hετ
    have hmass := bu_short_trace_strip_bound B τ ε hε hετ f g htrace
    have he : ENNReal.ofReal ε ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hε)
    have hefin : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
    have hden0 : ENNReal.ofReal ε ^ 2 ≠ 0 := pow_ne_zero _ he
    have hdenfin : ENNReal.ofReal ε ^ 2 ≠ ⊤ := by simp
    apply (ENNReal.div_le_iff hden0 hdenfin).2
    calc
      (∫⁻ t in Ioc ε (2 * ε),
        ∫⁻ x, f (x, t) ∂(volume.restrict B)) ≤
          2 * ENNReal.ofReal ε ^ 2 * Q ε := hmass
      _ = (2 * Q ε) * ENNReal.ofReal ε ^ 2 := by ring

end ESS
