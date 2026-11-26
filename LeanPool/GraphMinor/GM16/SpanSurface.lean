/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs

/-!
# The surface of a span is closed

A span is drawn in a surface with empty boundary. Every point is
therefore an interior point, so the surface is closed. This supplies
the surface condition when lifting the handle outcome in XVI (7.1).
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM15
universe u v w

/-- The surface underlying a span is a closed surface. -/
theorem span_isClosedSurface {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v} {G : Graph α β} {H : Drawing S} {η : GraphMinor.GM14.SpanEmbedding H
      G}
    {θ_star θ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h : IsSigmaSpan G H η θ_star θ T_star T) : IsClosedSurface S := by
  classical
  refine ⟨h.isSurface.1, h.isSurface.2.1, ?_⟩
  intro x
  by_contra hx
  have hb : x ∈ bd S := hx
  rw [h.bd_empty] at hb
  exact hb

end GraphMinor.GM16
