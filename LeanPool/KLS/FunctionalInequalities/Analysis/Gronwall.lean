/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Integral Grönwall inequality

`φ(t) ≤ a + K ∫₀ᵗ φ` on `[0, T]` for a measurable bounded `φ` and `K ≥ 0` gives `φ(t) ≤ a e^{Kt}`,
any real
`a` (Mathlib has the differential and discrete forms).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace FunctionalInequalities.Analysis

/-- Integral Grönwall (real analysis; not in Mathlib in this form). -/
theorem le_mul_exp_of_le_add_integral {φ : ℝ → ℝ} {a K T : ℝ} (hK : 0 ≤ K)
    (hφm : Measurable φ) (hφb : ∃ B, ∀ t ∈ Set.Icc (0 : ℝ) T, |φ t| ≤ B)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ a + K * ∫ s in Set.Ioc (0 : ℝ) t, φ s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ a * Real.exp (K * t) := by
  classical
  obtain ⟨B, hB⟩ := hφb
  have hφi : IntegrableOn φ (Set.Icc (0 : ℝ) T) := by
    refine IntegrableOn.of_bound measure_Icc_lt_top hφm.aestronglyMeasurable B ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simpa only [Real.norm_eq_abs] using hB s hs
  let p : ℝ → ℝ := (Set.Icc (0 : ℝ) T).indicator φ
  have hpi : Integrable p := hφi.integrable_indicator measurableSet_Icc
  let g : ℝ → ℝ := fun t => a + K * ∫ s in (0 : ℝ)..t, p s
  have hgc : Continuous g :=
    continuous_const.add
      ((intervalIntegral.continuous_primitive
        (fun _ _ => hpi.intervalIntegrable) 0).const_mul K)
  have hpg : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ g t := by
    intro t ht
    have he :
        (∫ s in (0 : ℝ)..t, p s) = ∫ s in Set.Ioc (0 : ℝ) t, φ s := by
      rw [intervalIntegral.integral_of_le ht.1]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans ht.2⟩
      exact Set.indicator_of_mem hsT φ
    simpa only [g, he] using h t ht
  let u : ℝ → ℝ := fun t => a + K * ∫ s in (0 : ℝ)..t, g s
  have huc : Continuous u :=
    continuous_const.add
      ((intervalIntegral.continuous_primitive
        (fun c d => hgc.intervalIntegrable c d) 0).const_mul K)
  have hgu : ∀ t ∈ Set.Icc (0 : ℝ) T, g t ≤ u t := by
    intro t ht
    change a + K * (∫ s in (0 : ℝ)..t, p s) ≤
      a + K * (∫ s in (0 : ℝ)..t, g s)
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hK)
    apply intervalIntegral.integral_mono_on ht.1 hpi.intervalIntegrable
      (hgc.intervalIntegrable 0 t)
    intro s hs
    have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
    simpa only [p, Set.indicator_of_mem hsT] using hpg s hsT
  have hud : ∀ x, HasDerivAt u (K * g x) x := by
    intro x
    exact ((intervalIntegral.integral_hasDerivAt_right
      (hgc.intervalIntegrable 0 x)
      (hgc.stronglyMeasurableAtFilter volume (𝓝 x))
      hgc.continuousAt).const_mul K).const_add a
  have hu0 : u 0 ≤ a := by
    simp only [u, intervalIntegral.integral_same, mul_zero, add_zero, le_refl]
  have hub : ∀ t ∈ Set.Icc (0 : ℝ) T, u t ≤ a * Real.exp (K * t) := by
    have hb := le_gronwallBound_of_liminf_deriv_right_le
      (f := u) (f' := fun x => K * g x) (δ := a) (K := K) (ε := 0)
      huc.continuousOn
      (fun x _ r hr => (hud x).hasDerivWithinAt.liminf_right_slope_le hr)
      hu0
      (fun x hx => by
        simpa only [add_zero] using
          mul_le_mul_of_nonneg_left (hgu x ⟨hx.1, hx.2.le⟩) hK)
    intro t ht
    simpa only [gronwallBound_ε0, sub_zero] using hb t ht
  intro t ht
  exact (hpg t ht).trans ((hgu t ht).trans (hub t ht))

end FunctionalInequalities.Analysis
