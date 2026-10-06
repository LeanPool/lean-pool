/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.EssSup

/-!
# Stability Slice Bound

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- A uniform almost-everywhere bound on slice energies passes to an almost-everywhere
pointwise limit by Fatou's lemma (`thm:stability`). -/
theorem stability_essSup_lintegral_le_of_ae_tendsto
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (F : ℕ → β → α → ℝ≥0∞) (G : β → α → ℝ≥0∞) (M : ℝ≥0∞)
    (hF : ∀ n, ∀ᵐ t ∂ν, AEMeasurable (F n t) μ)
    (hconv : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, Tendsto (fun n => F n t x) atTop (nhds (G t x)))
    (hbound : ∀ n, ∀ᵐ t ∂ν, ∫⁻ x, F n t x ∂μ ≤ M) :
    essSup (fun t => ∫⁻ x, G t x ∂μ) ν ≤ M := by
  have hall : ∀ᵐ t ∂ν, ∀ n, ∫⁻ x, F n t x ∂μ ≤ M :=
    ae_all_iff.mpr hbound
  have hmeas : ∀ᵐ t ∂ν, ∀ n, AEMeasurable (F n t) μ :=
    ae_all_iff.mpr hF
  apply essSup_le_of_ae_le M
  filter_upwards [hconv, hall, hmeas] with t ht htbound htmeas
  have heq : (∫⁻ x, G t x ∂μ) =
      ∫⁻ x, liminf (fun n => F n t x) atTop ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [ht] with x hx
    exact hx.liminf_eq.symm
  rw [heq]
  calc
    (∫⁻ x, liminf (fun n => F n t x) atTop ∂μ) ≤
        liminf (fun n => ∫⁻ x, F n t x ∂μ) atTop :=
      lintegral_liminf_le' htmeas
    _ ≤ M := Filter.liminf_le_of_frequently_le
      (Filter.Frequently.of_forall htbound)

end CKN
