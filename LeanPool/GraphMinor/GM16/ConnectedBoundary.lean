/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# Connectivity through a connected boundary

In a connected graph, suppose a subgraph retains every edge incident
with one of its vertices away from a chosen boundary. Following any
ambient walk to the boundary gives a walk inside the subgraph up to
its first boundary vertex. If the boundary vertices are connected
inside the subgraph, the whole subgraph is connected. This is the
graph argument behind the connected annulus in XVI (8.1), Claim (14).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06
universe u v
variable {α : Type u} {β : Type v}

/-- A subgraph of a connected graph is connected when its boundary
is connected and all edges at its other vertices are retained. -/
theorem isGraphConnected_of_connected_boundary {G Q : Graph α β} {B : Set α}
    (hQG : Q ≤ G) (hG : IsGraphConnected G) (hB : B.Nonempty) (hBQ : B ⊆ V(Q))
    (hConn : ∀ x ∈ B, ∀ y ∈ B, Nonempty (GraphWalk Q x y))
    (hKeep : ∀ e x y, G.IsLink e x y → x ∈ V(Q) → x ∉ B → Q.IsLink e x y) :
    IsGraphConnected Q := by
  obtain ⟨b₀, hb₀⟩ := hB
  have hWalk : ∀ {x t}, (W : GraphWalk G x t) → t ∈ B → x ∈ V(Q) →
      ∃ b ∈ B, Nonempty (GraphWalk Q x b) := by
    intro x t W
    induction W with
    | nil _ => exact fun ht hx => ⟨_, ht, ⟨.nil hx⟩⟩
    | @cons x y z e hl W ih =>
      intro ht hx
      by_cases hxb : x ∈ B
      · exact ⟨x, hxb, ⟨.nil hx⟩⟩
      · have hlQ := hKeep e x y hl hx hxb
        obtain ⟨b, hb, ⟨R⟩⟩ := ih ht hlQ.right_mem
        exact ⟨b, hb, ⟨.cons hlQ R⟩⟩
  have hReach : ∀ {x}, x ∈ V(Q) → ∃ b ∈ B, Nonempty (GraphWalk Q x b) := by
    intro x hx
    obtain ⟨W⟩ := hG.2 x (hQG.vertexSet_mono hx) b₀ (hQG.vertexSet_mono (hBQ hb₀))
    exact hWalk W hb₀ hx
  refine ⟨⟨b₀, hBQ hb₀⟩, ?_⟩
  intro x hx y hy
  obtain ⟨b, hb, ⟨R⟩⟩ := hReach hx
  obtain ⟨c, hc, ⟨T⟩⟩ := hReach hy
  obtain ⟨U⟩ := hConn b hb c hc
  exact ⟨(R.append U).append T.reverse⟩

end GraphMinor.GM16
