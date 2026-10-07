/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilitySliceBound
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Stability Slice Convergence

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- Strong space-time convergence has a subsequence converging on almost every
spatial slice for almost every time (`thm:stability`). -/
theorem stability_exists_subsequence_ae_slices_of_eLpNorm_tendsto
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E]
    (μ : Measure α) [SFinite μ] (ν : Measure β) (p : ℝ≥0∞) (hp : p ≠ 0)
    (F : ℕ → β × α → E) (G : β × α → E)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) p (ν.prod μ)) atTop (nhds 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ t ∂ν, ∀ᵐ x ∂μ,
        Tendsto (fun n => F (σ n) (t, x)) atTop (nhds (G (t, x))) := by
  obtain ⟨σ, hσ, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm hp hconv).exists_seq_tendsto_ae
  exact ⟨σ, hσ, Measure.ae_ae_of_ae_prod hae⟩

end CKN
