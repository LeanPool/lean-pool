/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM12.Section4IncidentEdges
import LeanPool.GraphMinor.GM12.Section4FirstThreshold
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.Walks
import Mathlib.Data.List.Chain

/-!
# First threshold edges on the chosen path

XII (4.3), page 250, first observes that the last edge of the
path is close to the second chosen edge. Thus the path reaches
all thresholds up to the distance of the chosen edges minus four.
The first-threshold argument then gives claim (2), including the
upper bound by the threshold plus three.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14

/-- XII (4.3), claim (2), page 250, with its threshold-existence
argument. The returned prefix contains only edges below the threshold. -/
theorem exists_first_path_threshold_edge
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    {x y : S} (W : GraphWalk Γ.toGraph x y)
    {g h : Set S} (hg : g ∈ Γ.E) (hh : h ∈ Γ.E)
    (hx : x ∈ closure g) (hy : y ∈ closure h)
    {i : ℕ} (hi : 1 ≤ i) (hfar : i + 4 ≤ d g h) :
    ∃ (p : List (Set S)) (f : Set S) (q : List (Set S)),
      W.edges = p ++ f :: q ∧ (∀ e ∈ p, d g e < i) ∧
        i ≤ d g f ∧ d g f ≤ i + 3 := by
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  have htri := h91.2.2.2.2.1
  have hgA : g ∈ Γ.A := Or.inl (Or.inr hg)
  have hhA : h ∈ Γ.A := Or.inl (Or.inr hh)
  have hmem : ∀ e ∈ W.edges, e ∈ Γ.E := by
    intro e he
    exact (walkDrawing_isSubdrawing Γ W).2 ((walkDrawing_E Γ W).symm ▸ he)
  have hchain := walk_edges_distance_chain hS hm W hg hx
  have hhead : ∀ e, W.edges.head? = some e → d g e ≤ 4 := by
    intro e he
    exact hchain.rel_head? (by rw [he]; rfl)
  have hstep : ∀ (p : List (Set S)) a b (q : List (Set S)),
      W.edges = p ++ a :: b :: q → d g b ≤ d g a + 4 := by
    intro p a b q heq
    have ha : a ∈ Γ.E := hmem a (heq ▸ List.mem_append_right p List.mem_cons_self)
    have hb : b ∈ Γ.E := hmem b (heq ▸ List.mem_append_right p
      (List.mem_cons_of_mem a List.mem_cons_self))
    have hab : d a b ≤ 4 :=
      List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain.tail heq
    exact (htri g hgA a (Or.inl (Or.inr ha)) b (Or.inl (Or.inr hb))).trans
      (Nat.add_le_add_left hab _)
  have hne : W.edges ≠ [] := by
    intro heq
    have hxy : x = y := by
      cases W with
      | nil hv => rfl
      | cons hl R => simp only [GraphWalk.edges_cons, List.cons_ne_nil] at heq
    have hclose := incident_edges_distance_le_four hS hm hg hh (W.mem_vertexSet_of_mem_support
      W.start_mem_support) hx (hxy ▸ hy)
    omega
  obtain ⟨e, he, hye⟩ := exists_walk_edge_at_end W hne
  have heE := hmem e he
  have heh := incident_edges_distance_le_four hS hm heE hh (W.mem_vertexSet_of_mem_support
    W.end_mem_support) hye hy
  have hlast := htri g hgA e (Or.inl (Or.inr heE)) h hhA
  have hex : ∃ e ∈ W.edges, i ≤ d g e := ⟨e, he, by omega⟩
  exact exists_first_threshold_edge_of_head_le_four (d g) hi W.edges hhead hstep hex

end GraphMinor.GM12
