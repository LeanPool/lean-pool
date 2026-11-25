/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.DrawingPointConnectivity
import LeanPool.GraphMinor.GM12.Section4PathExists
import LeanPool.GraphMinor.GM11.PaintingRegions
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Paths in a two-cell drawing

The point set of a two-cell drawing in a connected closed surface does not
split into two disjoint nonempty closed sets. Partitioning it according to
which vertices can be reached by graph walks therefore shows that any two
vertices are joined by a walk. This supplies the paths chosen in XVI (8.3).
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- Two vertices of a two-cell drawing in a connected closed surface are joined
by a graph walk, as used in Graph Minors XVI, proof of (8.3), Claims (5) and (12). -/
theorem drawing_walk_of_twoCell (hS : IsClosedSurface S) {D : Drawing S}
    (hD : (PaintingOrDrawing.drawing D).IsTwoCell)
    {a b : S} (ha : a ∈ D.V) (hb : b ∈ D.V) : Nonempty (GraphWalk D.toGraph a b) := by
  let : ConnectedSpace S := hD.1
  exact GM12.exists_walk_of_open_disc_regions hS hD.2 ha hb

/-- A two-cell drawing with a tangle of order at least two has an edge. -/
theorem edges_nonempty_of_tangle (hS : IsClosedSurface S) {H : Drawing S}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GraphMinor.GM14.IsRespectfulDrawingTangle H θ T) (hθ : 2 ≤ θ) : H.E.Nonempty := by
  have hc : 2 ≤ H.V.ncard := hθ.trans hT.2.1.order_le_ncard_vertexSet
  obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard H.finite_V).mp (by omega : 1 < H.V.ncard)
  obtain ⟨W⟩ := drawing_walk_of_twoCell hS hT.1 hx hy
  cases W with
  | nil _ => exact (hxy rfl).elim
  | cons hl _ => exact ⟨_, hl.1⟩

end GraphMinor.GM16
