/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilitySliceEnergy

/-!
# Stability Product Swap

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- Strong convergence on a product measure is unchanged by interchanging the
space and time coordinates (`thm:stability`). -/
theorem stability_eLpNorm_tendsto_swap
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E]
    (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν]
    (p : ℝ≥0∞) (F : ℕ → α × β → E) (G : α × β → E)
    (hF : ∀ n, AEStronglyMeasurable (F n - G) (μ.prod ν))
    (hconv : Tendsto (fun n => eLpNorm (F n - G) p (μ.prod ν)) atTop (nhds 0)) :
    Tendsto
      (fun n => eLpNorm
        (fun z : β × α => F n (z.2, z.1) - G (z.2, z.1)) p (ν.prod μ))
      atTop (nhds 0) := by
  have heq (n : ℕ) :
      eLpNorm (fun z : β × α => F n (z.2, z.1) - G (z.2, z.1)) p (ν.prod μ) =
        eLpNorm (F n - G) p (μ.prod ν) := by
    change eLpNorm ((F n - G) ∘ Prod.swap) p (ν.prod μ) =
      eLpNorm (F n - G) p (μ.prod ν)
    exact eLpNorm_comp_measurePreserving (hF n)
      (Measure.measurePreserving_swap (μ := ν) (ν := μ))
  simpa only [heq] using hconv

end CKN
