/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import TauCeti.Probability.Martingale.MaximalInequality.Event

/-!
# Continuous-time Doob bound in real-valued notation

Convert Tau Ceti's extended nonnegative running supremum to a real one using
its almost-sure finiteness theorem.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

theorem maximal_ineq_norm (hM : Martingale M 𝓕 μ) (ε : ℝ) (T : ℝ≥0)
    (hcont : ∀ ω, IsRightContinuous (M · ω)) :
    ε • μ.real {ω | ε ≤ ⨆ i : Iic T, ‖M i ω‖} ≤
      ∫ ω in {ω | ε ≤ ⨆ i : Iic T, ‖M i ω‖}, ‖M T ω‖ ∂μ := by
  by_cases hε : 0 ≤ ε
  swap
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hε) measureReal_nonneg).trans
      (integral_nonneg fun _ ↦ norm_nonneg _)
  have hrc : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t :=
    ae_of_all _ fun ω t _ ↦ hcont ω t
  let c : ℝ≥0 := ⟨ε, hε⟩
  have hevent : {ω | ε ≤ ⨆ i : Iic T, ‖M i ω‖} =ᵐ[μ]
      {ω | (c : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal ‖M t ω‖} := by
    filter_upwards [hM.ae_iSup_eNorm_lt_top hrc] with ω hω
    let S : ℝ≥0∞ := ⨆ t ≤ T, ENNReal.ofReal ‖M t ω‖
    have hs : S ≠ ∞ := by simpa only [← ofReal_norm, S] using hω.ne
    have hle (i : Iic T) : ‖M i ω‖ ≤ S.toReal := by
      rw [← ENNReal.toReal_ofReal (norm_nonneg (M i ω))]
      exact ENNReal.toReal_mono hs (le_iSup₂_of_le i i.2 le_rfl)
    have hb : BddAbove (range fun i : Iic T ↦ ‖M i ω‖) :=
      ⟨S.toReal, fun _ ⟨i, hi⟩ ↦ hi ▸ hle i⟩
    have hsup : (⨆ i : Iic T, ‖M i ω‖) = S.toReal := by
      refine le_antisymm (ciSup_le hle) ?_
      have hnonneg := (norm_nonneg (M T ω)).trans (le_ciSup hb ⟨T, le_rfl⟩)
      refine ENNReal.toReal_le_of_le_ofReal hnonneg ?_
      exact iSup₂_le fun t ht ↦ ENNReal.ofReal_le_ofReal (le_ciSup hb ⟨t, ht⟩)
    change (ε ≤ ⨆ i : Iic T, ‖M i ω‖) ↔ (c : ℝ≥0∞) ≤ S
    rw [hsup, ← ENNReal.ofReal_coe_nnreal (p := c), ENNReal.ofReal_le_iff_le_toReal hs]
    rfl
  rw [measureReal_congr hevent, setIntegral_congr_set hevent]
  have h := hM.norm.mul_measure_le_iSup_le_setIntegral (fun _ _ ↦ norm_nonneg _)
    (hrc.mono fun _ h t ht ↦ (h t ht).norm) c
  have hc : (c : ℝ≥0∞).toReal = ε := ENNReal.coe_toReal c
  simpa only [ENNReal.toReal_mul, hc, smul_eq_mul, measureReal_def,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _), c]
    using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

end ProbabilityTheory
