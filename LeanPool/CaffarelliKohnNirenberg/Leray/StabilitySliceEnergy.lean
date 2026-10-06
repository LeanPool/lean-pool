/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilitySliceConvergence

/-!
# Stability Slice Energy

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- The essential-supremum slice energy bound persists under strong space-time
convergence (`thm:stability`). -/
theorem stability_essSup_slice_energy_lt_top
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E]
    (μ : Measure α) [SFinite μ] (ν : Measure β)
    (F : ℕ → β × α → E) (G : β × α → E)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) 3 (ν.prod μ)) atTop (nhds 0))
    (hF : ∀ n, ∀ᵐ t ∂ν,
      AEMeasurable (fun x => ‖F n (t, x)‖ₑ ^ (2 : ℝ)) μ)
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hbound : ∀ n,
      essSup (fun t => ∫⁻ x, ‖F n (t, x)‖ₑ ^ (2 : ℝ) ∂μ) ν ≤ M) :
    essSup (fun t => ∫⁻ x, ‖G (t, x)‖ₑ ^ (2 : ℝ) ∂μ) ν < ⊤ := by
  obtain ⟨σ, _hσ, hae⟩ :=
    stability_exists_subsequence_ae_slices_of_eLpNorm_tendsto
      μ ν 3 (by norm_num) F G hconv
  have henergy : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ,
      Tendsto (fun n => ‖F (σ n) (t, x)‖ₑ ^ (2 : ℝ)) atTop
        (nhds (‖G (t, x)‖ₑ ^ (2 : ℝ))) := by
    filter_upwards [hae] with t ht
    filter_upwards [ht] with x hx
    exact (ENNReal.continuous_rpow_const.tendsto _).comp hx.enorm
  have hslicebound (n : ℕ) :
      ∀ᵐ t ∂ν, (∫⁻ x, ‖F (σ n) (t, x)‖ₑ ^ (2 : ℝ) ∂μ) ≤ M := by
    filter_upwards [ENNReal.ae_le_essSup
      (fun t => ∫⁻ x, ‖F (σ n) (t, x)‖ₑ ^ (2 : ℝ) ∂μ)] with t ht
    exact ht.trans (hbound (σ n))
  have hle := stability_essSup_lintegral_le_of_ae_tendsto μ ν
    (fun n t x => ‖F (σ n) (t, x)‖ₑ ^ (2 : ℝ))
    (fun t x => ‖G (t, x)‖ₑ ^ (2 : ℝ)) M
    (fun n => hF (σ n)) henergy hslicebound
  exact lt_of_le_of_lt hle hM

end CKN
