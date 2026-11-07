/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Bound.Init

public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Vertex Sets of Adjoined Trees

Shared facts from Wesley Pegden's Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12, generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Adjoining an edge to a fresh endpoint inserts exactly that endpoint into the tree. -/
theorem TreeSequenceAdjoinEdge.vertexSet_eq_insert.{u_1, u_2} :
  open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] (G :
      LooplessMultigraph V E) (e0 : E) (A B : TreeSequence G e0) (f : E) (x y : V), G.ends f =
      s(x, y) → y ∉ TreeSequenceVertexSet A → TreeSequenceAdjoinEdge A f B →
      TreeSequenceVertexSet B = insert y (TreeSequenceVertexSet A) := by
  classical
  intro V E _ G e0 A B f x y hxy hyA hAB
  rcases hAB with ⟨hlen, hinit, hlast⟩
  rcases hinit with ⟨hle, hvertices, hedges⟩
  have holdSubset : TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hv ⊢
    obtain ⟨q, hq⟩ := hv
    refine ⟨Fin.castLE (Nat.succ_le_succ hle) q, ?_⟩
    rw [hvertices]
    exact hq
  have hyB : y ∈ TreeSequenceVertexSet B := by
    let q : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
    obtain ⟨a, ha⟩ := B.attaches q
    have hyEnds : y ∈ G.ends (B.edge q) := by
      rw [hlast, hxy]
      simp
    rw [ha] at hyEnds
    rcases (by simpa only [Sym2.mem_iff] using hyEnds) with hynew | hyold
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨q.succ, hynew.symm⟩
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt)),
        hyold.symm⟩
  have hinsert : insert y (TreeSequenceVertexSet A) ⊆
      TreeSequenceVertexSet B := by
    intro v hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact hyB
    · exact holdSubset hv
  have hAcard : (TreeSequenceVertexSet A).card = A.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      A.vertex_injective]
  have hBcard : (TreeSequenceVertexSet B).card = B.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      B.vertex_injective]
  have hcard : (TreeSequenceVertexSet B).card ≤
      (insert y (TreeSequenceVertexSet A)).card := by
    rw [hBcard, Finset.card_insert_of_notMem hyA, hAcard, hlen]
  exact (Finset.eq_of_subset_of_card_le hinsert hcard).symm

end GoldbergSeymour

end
