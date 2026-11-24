/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CircuitSplice
import LeanPool.GraphMinor.GM11.EvenCircuit
import LeanPool.GraphMinor.GM11.CircuitRegions

/-!
# The circuit obtained by splicing the retained path

For XII (7.3), Claim (1), page 262, close the retained simple
path through the old region hubs. If the hubs agree, two old
spokes suffice. Otherwise four old spokes close it through the
deleted vertex. Record the exact vertices, edges, and length of
the resulting old circuit.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

private theorem walkDrawing_length_of_nodup
    {S : Type*} [TopologicalSpace S] [T1Space S] (K : Drawing S)
    {x y : S} (W : GraphWalk K.toGraph x y) (hW : W.edges.Nodup) :
    (walkDrawing K W).length = W.length := by
  classical
  rw [Drawing.length, walkDrawing_E]
  have hset : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by ext e; simp
  rw [hset, ncard_coe_finset, List.toFinset_card_of_nodup hW]
  rfl

/-- The old circuit in XII (7.3), Claim (1), page 262, formed
from a retained path and two or four spokes. Its length increases
by two precisely when the old middle vertices differ. -/
theorem exists_spliced_circuit
    {S : Type*} [TopologicalSpace S] [T1Space S] {K : Drawing S}
    {x y v p q : S} {a b c d : Set S}
    (ha : K.toGraph.IsLink a v p) (hb : K.toGraph.IsLink b p x)
    (hc : K.toGraph.IsLink c y q) (hd : K.toGraph.IsLink d q v)
    (P : GraphWalk K.toGraph x y) (hP : P.IsSimple)
    (hp : p ∉ P.support) (hq : q ∉ P.support) (hv : v ∉ P.support)
    (hpv : p ≠ v) (hqv : q ≠ v) (hbc : b ≠ c) :
    open scoped Classical in
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing K ∧
      C.length = P.length + (if p = q then 2 else 4) ∧
      C.V = ({z | z ∈ P.support} ∪ {p, q}) ∪ (if p = q then ∅ else {v}) ∧
      C.E = if p = q then insert b (insert c {e | e ∈ P.edges})
        else insert a (insert b (insert c (insert d {e | e ∈ P.edges}))) := by
  classical
  by_cases hpq : p = q
  · subst q
    let W : GraphWalk K.toGraph p p := .cons hb (P.append (.cons hc (.nil hc.right_mem)))
    have hsc := isSimpleClosed_close_path hb hc P hP hp hbc
    have hlen : W.length = P.length + 2 := by
      dsimp only [W]
      rw [GraphWalk.length_cons, GraphWalk.length_append]
      simp only [GraphWalk.length_cons, GraphWalk.length_nil]
    refine ⟨walkDrawing K W, isCircuit_walkDrawing K hsc (by rw [hlen]; omega),
      walkDrawing_isSubdrawing K W, ?_, ?_, ?_⟩
    · rw [walkDrawing_length_of_nodup K W hsc.2, hlen, ite_eq_left (rfl : p = p)]
    · rw [walkDrawing_V]
      dsimp only [W]
      rw [GraphWalk.support_cons, GraphWalk.support_append]
      ext z
      simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.tail_cons,
        List.mem_cons, List.mem_append, mem_ofPred_eq, mem_union, mem_insert_iff,
        mem_singleton_iff]
      tauto
    · rw [walkDrawing_E, ite_eq_left rfl]
      dsimp only [W]
      rw [GraphWalk.edges_cons, GraphWalk.edges_append]
      ext e
      simp only [GraphWalk.edges_cons, GraphWalk.edges_nil, List.mem_cons, List.mem_append,
        mem_ofPred_eq, mem_insert_iff, List.not_mem_nil, or_false]
      tauto
  · obtain ⟨W, hsc, hlen, hE, hV⟩ := exists_simpleClosed_four_edge_splice ha hb hc hd P hP
      hp hq hv hpq hpv hqv
    refine ⟨walkDrawing K W, isCircuit_walkDrawing K hsc (by rw [hlen]; omega),
      walkDrawing_isSubdrawing K W, ?_, ?_, ?_⟩
    · rw [walkDrawing_length_of_nodup K W hsc.2, hlen, ite_eq_right hpq]
    · rw [walkDrawing_V, hV]
      ext z
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
        mem_ofPred_eq, mem_union, mem_insert_iff, mem_singleton_iff, ite_eq_right hpq]
      tauto
    · rw [walkDrawing_E, hE, ite_eq_right hpq]
      ext e
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
        mem_ofPred_eq, mem_insert_iff]
      tauto

/-- The spliced circuit lies in any old subdrawing containing the
retained path and its replacement spokes. This is the containment
in the lifted walk used in XII (7.3), Claim (1), page 262. -/
theorem exists_spliced_circuit_in_subdrawing
    {S : Type*} [TopologicalSpace S] [T2Space S] {K N : Drawing S}
    (hNK : N.IsSubdrawing K)
    {x y v p q : S} {a b c d : Set S}
    (ha : K.toGraph.IsLink a v p) (hb : K.toGraph.IsLink b p x)
    (hc : K.toGraph.IsLink c y q) (hd : K.toGraph.IsLink d q v)
    (P : GraphWalk K.toGraph x y) (hP : P.IsSimple)
    (hp : p ∉ P.support) (hq : q ∉ P.support) (hv : v ∉ P.support)
    (hpv : p ≠ v) (hqv : q ≠ v) (hbc : b ≠ c)
    (haN : a ∈ N.E) (hbN : b ∈ N.E) (hcN : c ∈ N.E) (hdN : d ∈ N.E)
    (hPN : ∀ e ∈ P.edges, e ∈ N.E) :
    open scoped Classical in
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing N ∧
      C.length = P.length + (if p = q then 2 else 4) ∧
      C.V = ({z | z ∈ P.support} ∪ {p, q}) ∪ (if p = q then ∅ else {v}) ∧
      C.E = if p = q then insert b (insert c {e | e ∈ P.edges})
        else insert a (insert b (insert c (insert d {e | e ∈ P.edges}))) := by
  classical
  obtain ⟨C, hC, hCK, hlen, hV, hE⟩ := exists_spliced_circuit ha hb hc hd P hP
    hp hq hv hpv hqv hbc
  refine ⟨C, hC, circuit_isSubdrawing_of_E hC hCK hNK ?_, hlen, hV, hE⟩
  intro e he
  rw [hE] at he
  by_cases hpq : p = q
  · rw [ite_eq_left hpq] at he
    rcases he with rfl | rfl | he
    · exact hbN
    · exact hcN
    · exact hPN e he
  · rw [ite_eq_right hpq] at he
    rcases he with rfl | rfl | rfl | rfl | he
    · exact haN
    · exact hbN
    · exact hcN
    · exact hdN
    · exact hPN e he

end GraphMinor.GM12
