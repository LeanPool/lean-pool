/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM12.Section4MetricExistence

/-!
# Metrics for the spans in Graph Minors XVI

A respectful tangle has a metric. Choose a radial drawing. Each short circuit of
that drawing is a normal circle meeting the original drawing in fewer than the
tangle order many vertices. Respectfulness chooses its inside disc. These choices
give the derived slope used in the definition of the tangle metric.
-/

public section

namespace GraphMinor.GM16

open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- The metric used in Graph Minors XVI, Section 4, page 52, exists for every
respectful tangle in a closed surface. It is obtained from a radial drawing and
the inside discs supplied by respectfulness, as in XI, Section 6, page 87. -/
theorem exists_tangleMetric (hS : IsClosedSurface S) {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle H θ T) :
    ∃ d, HasTangleMetric H θ T d :=
  GM12.exists_metric_of_respectful_drawing_tangle hS hT

end GraphMinor.GM16
