/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Stability Finite Sum Integral

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
noncomputable section

namespace CKN

/-- A finite sum of integrable scalar pairings preserves convergence of its
integrals. -/
theorem stability_tendsto_integral_finsetSum
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (F : ℕ → ι → α → ℝ) (G : ι → α → ℝ)
    (hF : ∀ n i, i ∈ s → Integrable (F n i) μ)
    (hG : ∀ i, i ∈ s → Integrable (G i) μ)
    (hconv : ∀ i, i ∈ s → Tendsto (fun n => ∫ x, F n i x ∂μ)
      atTop (nhds (∫ x, G i x ∂μ))) :
    Tendsto (fun n => ∫ x, ∑ i ∈ s, F n i x ∂μ) atTop
      (nhds (∫ x, ∑ i ∈ s, G i x ∂μ)) := by
  have hsum := tendsto_finsetSum s (fun i hi => hconv i hi)
  have heqF (n : ℕ) :
      (∫ x, ∑ i ∈ s, F n i x ∂μ) =
        ∑ i ∈ s, ∫ x, F n i x ∂μ :=
    integral_finsetSum s (fun i hi => hF n i hi)
  have heqG :
      (∫ x, ∑ i ∈ s, G i x ∂μ) =
        ∑ i ∈ s, ∫ x, G i x ∂μ :=
    integral_finsetSum s (fun i hi => hG i hi)
  simpa only [heqF, heqG] using hsum

end CKN
