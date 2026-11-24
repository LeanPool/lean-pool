/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CircuitWalks

/-!
# Removing one vertex from a circuit

For XII (7.3), Claim (1), page 262, separate the two edges at
the merged hub from the remaining path of the circuit. Rotate a
simple closed walk to that hub and remove its first and last
edges. The remaining path is simple and omits the hub. A circuit
with two parallel edges leaves a path of length zero.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A loopless circuit at a chosen vertex consists of two distinct
edges at that vertex and a simple path avoiding it. This gives
the path denoted by `C'` with its hub removed in XII (7.3),
Claim (1), page 262, including the parallel-edge case. -/
theorem exists_circuit_path_at_vertex
    {S : Type*} [TopologicalSpace S] {C : Drawing S}
    (hC : C.IsCircuit)
    (hloop : ∀ e x y, C.toGraph.IsLink e x y → x ≠ y)
    {v : S} (hv : v ∈ C.V) :
    ∃ (x y : S) (e f : Set S) (_he : C.toGraph.IsLink e v x)
      (_hf : C.toGraph.IsLink f y v) (P : GraphWalk C.toGraph x y),
      P.IsSimple ∧ v ∉ P.support ∧ e ≠ f ∧ e ∉ P.edges ∧ f ∉ P.edges ∧
      C.V = insert v {z | z ∈ P.support} ∧
      C.E = insert e (insert f {g | g ∈ P.edges}) ∧ C.length = P.length + 2 := by
  obtain ⟨u, W, hW, hpos, hV, hE⟩ := hC
  have hvW : v ∈ W.support := by simpa only [hV, mem_ofPred_eq] using hv
  obtain ⟨R, hR, hlen, hmemV, hmemE⟩ := exists_simpleClosed_walk_at_vertex W hW hvW
  have hClen : C.length = W.length := by
    change C.E.ncard = W.edges.length
    rw [hE]
    have hset : {g | g ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by ext g; simp
    rw [hset, ncard_coe_finset, List.toFinset_card_of_nodup hW.2]
  have hRpos : 0 < R.length := hlen.symm ▸ hpos
  cases hcase : R with
  | nil h => rw [hcase] at hRpos; exact (Nat.lt_irrefl 0 hRpos).elim
  | @cons _ x _ e he rest =>
    have hrestpos : 0 < rest.length := by
      by_contra hnot
      have hz : rest.length = 0 := Nat.eq_zero_of_not_pos hnot
      have hxv := GraphWalk.eq_of_length_eq_zero hz
      exact hloop e v x he hxv.symm
    obtain ⟨y, f, hf, P, hlast⟩ := exists_walk_last_edge rest hrestpos
    have hnd : (P.support ++ [v]).Nodup := by
      have hh := hR.1
      rw [hcase, GraphWalk.support_cons, List.tail_cons, hlast, GraphWalk.support_append] at hh
      exact hh
    have hP : P.IsSimple := (List.nodup_append.mp hnd).1
    have hvP : v ∉ P.support := by
      intro hvm
      exact (List.nodup_append.mp hnd).2.2 v hvm v (by simp) rfl
    have hEd : (e :: (P.edges ++ [f])).Nodup := by
      have hh := hR.2
      rw [hcase, GraphWalk.edges_cons, hlast, GraphWalk.edges_append] at hh
      exact hh
    have heP : e ∉ P.edges := fun hem => (List.nodup_cons.mp hEd).1 (List.mem_append_left _ hem)
    have hef : e ≠ f := by
      intro hef
      exact (List.nodup_cons.mp hEd).1 (List.mem_append_right _ (by simp [hef]))
    have hfP : f ∉ P.edges := by
      intro hfm
      exact (List.nodup_append.mp (List.nodup_cons.mp hEd).2).2.2 f hfm f (by simp) rfl
    refine ⟨x, y, e, f, he, hf, P, hP, hvP, hef, heP, hfP, ?_, ?_, ?_⟩
    · ext z
      rw [hV]
      change z ∈ W.support ↔ _
      rw [← hmemV z, hcase, GraphWalk.support_cons, hlast, GraphWalk.support_append]
      simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.tail_cons, List.mem_cons,
        List.mem_append, mem_insert_iff, mem_ofPred_eq]
      tauto
    · ext g
      rw [hE]
      change g ∈ W.edges ↔ _
      rw [← hmemE g, hcase, GraphWalk.edges_cons, hlast, GraphWalk.edges_append]
      simp only [GraphWalk.edges_cons, GraphWalk.edges_nil, List.mem_cons, List.mem_append,
        mem_insert_iff, mem_ofPred_eq]
      tauto
    · rw [hClen, ← hlen, hcase, GraphWalk.length_cons, hlast, GraphWalk.length_append]
      simp only [GraphWalk.length_cons, GraphWalk.length_nil]

/-- Read the circuit path in its ambient drawing rather than in
the circuit's own graph. This is the form used for the two new
spokes and the retained path in XII (7.3), Claim (1), page 262. -/
theorem exists_circuit_path_in_drawing
    {S : Type*} [TopologicalSpace S] {J C : Drawing S}
    (hC : C.IsCircuit) (hCJ : C.IsSubdrawing J)
    (hloop : ∀ e x y, J.toGraph.IsLink e x y → x ≠ y)
    {v : S} (hv : v ∈ C.V) :
    ∃ (x y : S) (e f : Set S) (_he : J.toGraph.IsLink e v x)
      (_hf : J.toGraph.IsLink f y v) (P : GraphWalk J.toGraph x y),
      P.IsSimple ∧ v ∉ P.support ∧ e ≠ f ∧ e ∉ P.edges ∧ f ∉ P.edges ∧
      C.V = insert v {z | z ∈ P.support} ∧
      C.E = insert e (insert f {g | g ∈ P.edges}) ∧ C.length = P.length + 2 := by
  have hloopC : ∀ e x y, C.toGraph.IsLink e x y → x ≠ y :=
    fun e x y h => hloop e x y ((hCJ.isLink_iff h.1).mp h)
  obtain ⟨x, y, e, f, he, hf, P₀, hP₀, hvP₀, hef, heP₀, hfP₀, hV, hE, hlen⟩ :=
    exists_circuit_path_at_vertex hC hloopC hv
  obtain ⟨P, hPS, hPE⟩ := hCJ.exists_walk_up P₀
  have hPlen : P.length = P₀.length := congrArg List.length hPE
  refine ⟨x, y, e, f, (hCJ.isLink_iff he.1).mp he, (hCJ.isLink_iff hf.1).mp hf,
    P, ?_, ?_, hef, ?_, ?_, ?_, ?_, ?_⟩
  · change P.support.Nodup
    rw [hPS]
    exact hP₀
  · rwa [hPS]
  · rwa [hPE]
  · rwa [hPE]
  · rwa [hPS]
  · rwa [hPE]
  · rwa [hPlen]

end GraphMinor.GM12
