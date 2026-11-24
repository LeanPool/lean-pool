/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM11.RadialExists
import LeanPool.GraphMinor.GM11.Section64

/-!
# Choosing the metric of a respectful drawing tangle

The hypothesis in XII (4.3), page 249, names a respectful tangle,
whose metric is used throughout the proof. Choose a radial drawing
and its derived inside function. The associated distance supplies
the metric data used by the free-edge selection argument.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14

/-- The metric data associated to a respectful drawing tangle. -/
theorem exists_metric_of_respectful_drawing_tangle
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle Γ θ T) :
    ∃ d : Set S → Set S → ℕ, HasTangleMetric Γ θ T d := by
  obtain ⟨K, hK⟩ := exists_radialDrawing hS hT.1
  obtain ⟨ins, hins⟩ := exists_derivedSlope hS hT.2.2 hK.2.1
  exact ⟨tangleMetric Γ K ins θ, hT, K, ins, hK, hins, fun _ _ _ _ => rfl⟩

end GraphMinor.GM12
