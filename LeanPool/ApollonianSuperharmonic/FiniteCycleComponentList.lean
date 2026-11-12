/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import LeanPool.ApollonianSuperharmonic.Preamble

/-!
# FiniteCycleComponentList

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open scoped Sym2

-- [TABLET NODE: FiniteCycleComponentList]
theorem FiniteCycleComponentList
    {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsCycles)
    (c : G.ConnectedComponent) (v : V) (hv : v ∈ c.supp)
    (hn : (G.neighborSet v).Nonempty) :
    ∃ (p : List V) (x y : V),
      p.Nodup ∧ 3 ≤ p.length ∧
      p.head? = some x ∧ p.getLast? = some y ∧
      (p.toFinset : Set V) = c.supp ∧
      G.Adj y x ∧ List.IsChain G.Adj p ∧
      ∀ a b, a ∈ c.supp →
        (G.Adj a b ↔
          s(a, b) = s(y, x) ∨
            s(a, b) ∈ List.zipWith (s(·, ·)) p p.tail) := by
-- BODY
  classical
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨w, hwcycle, hwverts⟩ :=
    hG.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hn
  cases w with
  | nil => exact (hwcycle.not_nil .nil).elim
  | @cons u w x hadj q =>
      refine ⟨q.support, w, v, hwcycle.support_nodup, ?_, ?_, ?_, ?_, hadj, ?_, ?_⟩
      · simpa using hwcycle.three_le_length
      · cases q <;> simp
      · exact List.getLast?_eq_some_iff.2
          ⟨q.support.dropLast, q.dropLast_support_concat.symm⟩
      · ext z
        simp only [Finset.mem_coe, List.mem_toFinset]
        rw [← hwverts, SimpleGraph.Walk.mem_verts_toSubgraph]
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
        constructor
        · exact Or.inr
        · intro hz
          rcases hz with rfl | hz
          · exact q.end_mem_support
          · exact hz
      · exact q.isChain_adj_support
      · intro a b ha
        have ha' : a ∈ (SimpleGraph.Walk.cons hadj q).toSubgraph.verts := by
          rw [hwverts]
          exact ha
        rw [← hwcycle.adj_toSubgraph_iff_of_isCycles hG ha' b]
        rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        rw [q.edges_eq_zipWith_support]

end ApollonianSuperharmonic

end
