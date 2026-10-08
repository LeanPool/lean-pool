/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTraceSupport
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedError

/-!
# Comparing the early cutoff error with trace mass

The time derivative of the lower cutoff contributes only on its
transition strip. A nonnegative majorant there is integrated over the
larger trace cylinder.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

/-- An integrable error supported on a measurable strip is bounded by a
nonnegative majorant integrated over the full strip. -/
theorem bu_short_early_integral_le_trace
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {K S : Set X} (hKmeas : MeasurableSet K) (hSmeas : MeasurableSet S)
    {f g : X → ℝ} (hf : IntegrableOn f S μ)
    (hg : IntegrableOn g K μ) (hf0 : ∀ z, 0 ≤ f z)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ K, g z ≤ C * S.indicator f z) :
    (∫ z in K, g z ∂μ) ≤ C * (∫ z in S, f z ∂μ) := by
  have hfInd : Integrable (S.indicator f) μ := hf.integrable_indicator hSmeas
  have hscaled : IntegrableOn (fun z => C * S.indicator f z) K μ :=
    (hfInd.const_mul C).integrableOn
  have hfirst := setIntegral_mono_on hg hscaled hKmeas hbound
  have hInd0 : 0 ≤ᵐ[μ] S.indicator f := by
    filter_upwards [] with z
    by_cases hz : z ∈ S <;> simp [Set.indicator, hz, hf0 z]
  have hsecond : (∫ z in K, S.indicator f z ∂μ) ≤
      ∫ z, S.indicator f z ∂μ :=
    setIntegral_le_integral hfInd hInd0
  have hsecond' : (∫ z in K, S.indicator f z ∂μ) ≤
      ∫ z in S, f z ∂μ := by
    calc
      _ ≤ ∫ z, S.indicator f z ∂μ := hsecond
      _ = ∫ z in S, f z ∂μ := by rw [integral_indicator hSmeas]
  rw [integral_const_mul] at hfirst
  exact hfirst.trans (mul_le_mul_of_nonneg_left hsecond' hC)

/-- Replacing the half-open shrinking strip by its closed version does
not change its integral, and a fixed coefficient preserves the trace
limit. -/
theorem bu_short_closed_strip_scaled_tendsto_zero
    (B : Set Vec3) (f : Vec3 × ℝ → ℝ) (C : ℝ)
    (htrace : Tendsto (fun ε : ℝ =>
      (∫ q in B ×ˢ Ioc (1 / 2 + ε) (1 / 2 + 2 * ε), f q
        ∂(volume : Measure (Vec3 × ℝ))) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε : ℝ =>
      C / ε ^ 2 *
        (∫ q in B ×ˢ Icc (1 / 2 + ε) (1 / 2 + 2 * ε), f q
          ∂(volume : Measure (Vec3 × ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hset (ε : ℝ) :
      (∫ q in B ×ˢ Icc (1 / 2 + ε) (1 / 2 + 2 * ε), f q
        ∂(volume : Measure (Vec3 × ℝ))) =
      (∫ q in B ×ˢ Ioc (1 / 2 + ε) (1 / 2 + 2 * ε), f q
        ∂(volume : Measure (Vec3 × ℝ))) := by
    apply setIntegral_congr_set
    exact (Measure.set_prod_ae_eq (ae_eq_refl B)
      (Ioc_ae_eq_Icc (a := 1 / 2 + ε) (b := 1 / 2 + 2 * ε))).symm
  have hlim : Tendsto (fun ε : ℝ => C *
      ((∫ q in B ×ˢ Ioc (1 / 2 + ε) (1 / 2 + 2 * ε), f q
        ∂(volume : Measure (Vec3 × ℝ))) / ε ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using htrace.const_mul C
  convert hlim using 1
  ext ε
  rw [hset]
  ring

end ESS
