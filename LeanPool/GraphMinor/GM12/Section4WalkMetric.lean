/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section1
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Length and distance for radial walks

In XII (4.1), page 248, the cost of a radial circuit is half its length,
which is the number of its original vertices. Bipartiteness gives this
identity. The distance bound follows by using a closed walk as a witness
in the definition of the tangle metric.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM14 Hypergraph

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]

omit [T1Space S] in
/-- Every closed walk of a pre-radial drawing `K` of `H` has even length, equal to twice the number
of visits to `V(H)`. -/
theorem closed_walk_length_eq_two_mul {H K : Drawing S}
    (hP : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K) {u : S}
    (W : GraphWalk K.toGraph u u) :
    by classical exact W.length = 2 * (W.support.tail.countP (· ∈ H.V)) := by
  classical
  have hb₁ : ∀ e x y, K.toGraph.IsLink e x y → (x ∈ H.V ↔ y ∉ H.V) :=
    bipartite_of_preRadial hP
  have hb₂ : ∀ e x y, K.toGraph.IsLink e x y → (x ∈ H.Vᶜ ↔ y ∉ H.Vᶜ) := by
    intro e x y hl
    simp only [mem_compl_iff, not_not]
    exact ⟨fun hx => not_not.mp ((hb₁ e x y hl).not.mp hx),
      fun hy hx => (hb₁ e x y hl).mp hx hy⟩
  have hle₁ := two_mul_count_le H.V hb₁ W
  have hle₂ := two_mul_count_le H.Vᶜ hb₂ W
  have hsum_list : ∀ l : List S, l.countP (· ∈ H.V) + l.countP (· ∈ H.Vᶜ) = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.length_cons, ← ih]
      by_cases hx : x ∈ H.V <;> (simp [hx]; omega)
  have hsum : W.support.tail.countP (· ∈ H.V) + W.support.tail.countP (· ∈ H.Vᶜ) = W.length := by
    rw [hsum_list, List.length_tail, length_support]
    rfl
  omega

omit [T1Space S] in
/-- Every circuit `D` of a pre-radial drawing `K` of `H` has length `2 * |V(D) ∩ V(H)|` and
contains a vertex of `H`. -/
theorem circuit_length_eq_two_mul_ncard {H K D : Drawing S}
    (hP : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K)
    (hD : D.IsCircuit) (hDs : D.IsSubdrawing K) :
    D.length = 2 * (D.V ∩ H.V).ncard ∧ (D.V ∩ H.V).Nonempty := by
  classical
  obtain ⟨u, W_D, ⟨hnd, hed⟩, hpos, hDV, hDE⟩ := hD
  obtain ⟨W, hs, he⟩ := hDs.exists_walk_up W_D
  have hDlen : D.length = W.length := by
    rw [Drawing.length, hDE, ← he]
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by ext; simp
    rw [h, ncard_coe_finset, List.toFinset_card_of_nodup (he ▸ hed)]
    rfl
  have heven := closed_walk_length_eq_two_mul hP W
  have htail_mem : ∀ x, x ∈ W.support.tail ↔ x ∈ D.V := by
    intro x
    rw [hDV, hs, mem_ofPred_eq]
    cases W_D with
    | nil _ => exact absurd hpos (Nat.lt_irrefl 0)
    | cons _ r =>
      change x ∈ r.support ↔ x ∈ _ :: r.support
      constructor
      · exact fun hx => List.mem_cons_of_mem _ hx
      · intro hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact r.end_mem_support
        · exact hx
  have hset_eq : ((W.support.tail.filter (· ∈ H.V)).toFinset : Set S) = D.V ∩ H.V := by
    ext x
    simp [htail_mem]
  have hcard : W.support.tail.countP (· ∈ H.V) = (D.V ∩ H.V).ncard := by
    rw [← hset_eq, ncard_coe_finset,
      List.toFinset_card_of_nodup ((hs ▸ hnd).filter _), List.countP_eq_length_filter]
  have hlen_eq : D.length = 2 * (D.V ∩ H.V).ncard := by
    rw [hDlen, heven, hcard]
  refine ⟨hlen_eq, ?_⟩
  have hWlen : W.length = W_D.length := by
    change W.edges.length = W_D.edges.length
    rw [he]
  have hpos' : 0 < (D.V ∩ H.V).ncard := by omega
  exact (ncard_pos (D.finite_V.subset inter_subset_left)).mp hpos'

/-- A radial closed walk of length `2k < 2θ` containing the two corresponding
atoms witnesses distance at most `k`, as used in XII (4.1), page 248. -/
theorem tangleMetric_le_of_walk {H K : Drawing S} {ins : Drawing S → Set S}
    {θ k : ℕ} {x y x' y' : Set S}
    (hx : IsCorrespondingAtom H K x x') (hy : IsCorrespondingAtom H K y y')
    {u : S} (W : GraphWalk K.toGraph u u) (hW : W.length < 2 * θ)
    (hlen : W.length = 2 * k)
    (hxW : x' ⊆ insWalk ins K W) (hyW : y' ⊆ insWalk ins K W) :
    tangleMetric H K ins θ x y ≤ k := by
  classical
  unfold tangleMetric
  split_ifs with heq hex
  · exact Nat.zero_le _
  · exact Nat.sInf_le ⟨u, W, x', y', hx, hy, hW, hlen, hxW, hyW⟩
  · exact (hex ⟨u, W, x', y', hx, hy, hW, hxW, hyW⟩).elim

/-- The tangle metric is bounded by the order. If a short witness exists,
its even length gives a smaller bound. Otherwise the metric is the order. -/
theorem tangleMetric_le_order {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (ins : Drawing S → Set S) (θ : ℕ) (x y : Set S) :
    tangleMetric H K ins θ x y ≤ θ := by
  classical
  by_cases heq : x = y
  · simp only [tangleMetric, heq, ↓reduceIte, Nat.zero_le]
  by_cases hex : ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
      IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
      W.length < 2 * θ ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W
  · obtain ⟨u, W, x', y', hx, hy, hlen, hxW, hyW⟩ := hex
    have heven := closed_walk_length_eq_two_mul hK.2.1 W
    exact (tangleMetric_le_of_walk hx hy W hlen heven hxW hyW).trans (by omega)
  · simp only [tangleMetric, heq, hex, ↓reduceIte, le_refl]

section EdgeSeparations

open GM10

variable {X : Type u} [TopologicalSpace X]

/-- An edge of a drawing has at most two ends in its hypergraph. -/
theorem drawing_edge_ends_ncard_le_two {H : Drawing X} {e : Set X} (he : e ∈ H.E) :
    (H.toHypergraph.ends e).ncard ≤ 2 := by
  obtain ⟨a, b, hl⟩ := H.toGraph.exists_isLink_of_mem_edgeSet he
  have hends : H.toHypergraph.ends e ⊆ {a, b} := by
    intro x hx
    rw [← hl.2.2.2]
    exact ⟨hx.2.2, hx.2.1⟩
  exact (ncard_le_ncard hends (toFinite _)).trans ((ncard_insert_le a {b}).trans (by simp))

/-- Separating one drawing edge from the rest has order at most two. -/
theorem drawing_edge_separation_order_le_two {H : Drawing X} {e : Set X} (he : e ∈ H.E) :
    separationOrder (edgeHypergraph H.toHypergraph e) (H.toHypergraph.deleteEdges {e}) ≤ 2 := by
  rw [separationOrder_edgeHypergraph_deleteEdges]
  exact drawing_edge_ends_ncard_le_two he

/-- A tangle of order at least three selects the one-edge side as its small side. -/
theorem drawing_edge_small_side_mem_of_order_three {H : Drawing X} {θ : ℕ}
    {T : Set (Hypergraph X (Set X) × Hypergraph X (Set X))}
    (hT : IsTangle H.toHypergraph θ T) (hθ : 2 < θ) {e : Set X} (he : e ∈ H.E) :
    (edgeHypergraph H.toHypergraph e, H.toHypergraph.deleteEdges {e}) ∈ T :=
  (hT.axiom1 (isSeparation_edgeHypergraph_deleteEdges (G := H.toHypergraph) he)
    ((drawing_edge_separation_order_le_two he).trans_lt hθ)).resolve_right
    fun h => hT.axiom3 h rfl

end EdgeSeparations

end GraphMinor.GM12
