/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section1
public import LeanPool.GraphMinor.GM12.Section4Separation
import LeanPool.GraphMinor.GM12.Section4WalkMetric
import LeanPool.GraphMinor.GM11.Walks

/-!
# A nonfree path edge lies inside a radial circuit of length two

Claim (1) in the proof of XII (4.3), pages 249--250, starts with
a nonfree edge with distinct ends. Its two ends lie on a tangle
small side of order at most one. Move the edge onto that side by
X (2.9), then apply XII (1.1). The resulting radial circuit has
at most one original vertex. Radial bipartiteness makes its length
at most two.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM10 GM11 GM14 Hypergraph

/-- The small-separation and radial-circuit step of claim (1) in
Graph Minors XII (4.3), pages 249--250. -/
theorem exists_short_radial_circuit_of_nonfree_edge
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle Γ θ T) (hθ : 2 ≤ θ)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {f : Set S} {u v : S} (hl : Γ.toGraph.IsLink f u v) (huv : u ≠ v)
    (hfree : ¬ IsFreeSet Γ.toHypergraph T θ {u, v}) :
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ ∧
      C.length ≤ 2 ∧ (C.V ∩ Γ.V).ncard ≤ 1 ∧ f ⊆ ins C := by
  have hpairV : ({u, v} : Set S) ⊆ Γ.V := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hl.2.1
    · exact hl.2.2.1
  have hpair : ({u, v} : Set S).ncard = 2 := Set.ncard_pair huv
  have hbad : ∃ A B : Hypergraph S (Set S), (A, B) ∈ T ∧ {u, v} ⊆ A.vertexSet ∧
      separationOrder A B ≤ 1 := by
    by_contra hno
    apply hfree
    refine ⟨hpairV, hpair ▸ hθ, ?_⟩
    intro A B hm hsub
    rw [hpair]
    by_contra hlt
    exact hno ⟨A, B, hm, hsub, by omega⟩
  obtain ⟨A, B, hm, hsub, hord⟩ := hbad
  let H := edgeHypergraph Γ.toHypergraph f
  have hHV : H.vertexSet ⊆ A.vertexSet := by
    intro x hx
    change Γ.toHypergraph.Inc f x at hx
    have hxends : x ∈ ({u, v} : Set S) := hl.2.2.2 ▸ ⟨hx.2.2, hx.2.1⟩
    exact hsub hxends
  have hmove := tangle_move_subhypergraph hT.2.1 hm (edgeHypergraph_le hl.1) hHV
  let A' := A ∪ H
  let B' := B.deleteEdges H.edgeSet
  have hm' : (A', B') ∈ T := hmove.1
  have ho' : separationOrder A' B' ≤ 1 := hmove.2 ▸ hord
  have hfA : f ∈ A'.edgeSet := Or.inr (mem_singleton f)
  obtain ⟨C, hC, hCs, hCl, hCV, hfC⟩ :=
    (theorem_1_1_proof hS hT ⟨f, hl.1⟩ hK hd (hT.2.1.isSeparation hm')
      (hT.2.1.order_lt hm')).mp hm' f hfA
  have hcount : (C.V ∩ Γ.V).ncard ≤ 1 :=
    (Set.ncard_le_ncard hCV (A' ∩ B').vertexSet_finite).trans ho'
  have hlen := (circuit_length_eq_two_mul_ncard hK.2.1 hC hCs).1
  refine ⟨C, hC, hCs, hCl, ?_, hcount, hfC⟩
  rw [hlen]
  exact Nat.mul_le_mul_left 2 hcount

end GraphMinor.GM12
