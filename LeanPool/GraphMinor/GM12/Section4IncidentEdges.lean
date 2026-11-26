/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.Walks
import Mathlib.Data.List.Chain

/-!
# Distances between successive path edges

XII (4.3), claims (2)--(4), page 250, uses the bound four for
two edges with a common end. Each edge is at distance at most two from
that end. The triangle inequality from XI (9.1) gives four. Applying
this at every vertex of a walk gives a chain of edge distances.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14

/-- Two edges incident with one vertex are at distance at most four,
as used in XII (4.3), page 250. -/
theorem incident_edges_distance_le_four
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    {e f : Set S} (he : e ∈ Γ.E) (hf : f ∈ Γ.E)
    {v : S} (hv : v ∈ Γ.V) (hve : v ∈ closure e) (hvf : v ∈ closure f) :
    d e f ≤ 4 := by
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  have hsym := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have hvebound := h91.2.2.2.2.2.2 v hv e he hve
  have hvfbound := h91.2.2.2.2.2.2 v hv f hf hvf
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have heA : e ∈ Γ.A := Or.inl (Or.inr he)
  have hfA : f ∈ Γ.A := Or.inl (Or.inr hf)
  have ht := htri e heA {v} hvA f hfA
  rw [hsym e heA {v} hvA] at ht
  exact ht.trans (Nat.add_le_add hvebound hvfbound)

/-- The initial edge and the edges of a walk form a chain with
successive distances at most four, as used in XII (4.3), claim (2). -/
theorem walk_edges_distance_chain
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    {x y : S} (W : GraphWalk Γ.toGraph x y)
    {e : Set S} (he : e ∈ Γ.E) (hx : x ∈ closure e) :
    (e :: W.edges).IsChain (fun a b => d a b ≤ 4) := by
  induction W generalizing e with
  | nil hv => exact List.IsChain.singleton e
  | @cons x z y f hl R ih =>
    rw [GraphWalk.edges_cons, List.isChain_cons_cons]
    refine ⟨?_, ih hl.edge_mem ?_⟩
    · apply incident_edges_distance_le_four hS hm he hl.edge_mem hl.left_mem hx
      have hx' : x ∈ closure f ∩ Γ.V := by rw [hl.2.2.2]; simp
      exact hx'.1
    · have hz : z ∈ closure f ∩ Γ.V := by rw [hl.2.2.2]; simp
      exact hz.1

/-- A nontrivial walk has a last edge incident with its terminal vertex. -/
theorem exists_walk_edge_at_end {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {x y : S} (W : GraphWalk Γ.toGraph x y)
    (hne : W.edges ≠ []) : ∃ e ∈ W.edges, y ∈ closure e := by
  induction W with
  | nil hv => exact False.elim (hne rfl)
  | @cons x z y e hl R ih =>
    by_cases hR : R.edges = []
    · have hzy : z = y := by
        cases R with
        | nil hv => rfl
        | cons h rest => simp only [GraphWalk.edges_cons, List.cons_ne_nil] at hR
      refine ⟨e, List.mem_cons_self, ?_⟩
      have hz : z ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; simp
      exact hzy ▸ hz.1
    · obtain ⟨f, hf, hy⟩ := ih hR
      exact ⟨f, List.mem_cons_of_mem e hf, hy⟩

end GraphMinor.GM12
