/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceExistence
import LeanPool.GraphMinor.GM12.Section2NonemptyEdges
import LeanPool.GraphMinor.GM12.Section2Zero

/-!
# Traces below a tangle order

In XII (2.1) and the proof of (3.2), pages 243--246, the normal
curve length is below the tangle order. A zero-length curve has its
one-vertex trace without an edge assumption. At positive length,
the tangle order is at least two and X (2.3) supplies a drawing edge,
so the full trace construction applies.
-/

public section

namespace GraphMinor.GM12

open Surface GM11

/-- Every normal finite-length curve below a tangle order has a trace,
including the case where the drawing has no edges. -/
theorem exists_trace_of_curveLength_lt_tangle_order
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {φ : C(Circle, S)} (hφ : IsNormalCurve Γ φ) (hlen : curveLength Γ φ < θ) :
    ∃ (u : S) (W : GraphWalk K.toGraph u u), IsTrace Γ K φ W := by
  by_cases hzero : curveLength Γ φ = 0
  · exact exists_trace_of_length_zero hK hφ hzero
  · have hθ : 2 ≤ θ := by omega
    have hE : Γ.E.Nonempty := edges_nonempty_of_tangle_order_two hT hθ
    exact exists_trace hS hK hE hφ

end GraphMinor.GM12
