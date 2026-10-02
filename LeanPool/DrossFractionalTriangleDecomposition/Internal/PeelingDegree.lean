/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.PeelingGeometry

/-!
# Degree control under triangle peeling

Removing a triangle lowers each affected degree by at most two. When its
three vertices have degree at least `minDegree + 2`, minimum degree is
unchanged.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

public theorem peeled_heavy_triangle_degree_add_two (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w x : V} :
    G.degree x ≤ (G.deleteEdges (triEdges {u, v, w})).degree x + 2 := by
  rw [← G.card_neighborFinset_eq_degree, ← (G.deleteEdges _).card_neighborFinset_eq_degree]
  let A := (G.deleteEdges (triEdges {u, v, w})).neighborFinset x
  let B := G.neighborFinset x
  have hAB : A ⊆ B := by
    intro y hy
    simp only [B, G.mem_neighborFinset]
    change y ∈ (G.deleteEdges (triEdges {u, v, w})).neighborFinset x at hy
    exact (deleteEdges_adj.mp ((G.deleteEdges _).mem_neighborFinset x y |>.mp hy)).1
  have hBA : B \ A ⊆ ({u, v, w} : Finset V) := by
    intro y hy
    have hyadj : G.Adj x y := (G.mem_neighborFinset x y).mp (mem_sdiff.mp hy).1
    simp only [mem_insert, mem_singleton]
    by_contra hn
    have hnot : s(x, y) ∉ triEdges {u, v, w} := by
      intro he
      have hall := (mem_sym2_iff.mp (mem_filter.mp he).1) y (by simp)
      exact hn (by simpa using hall)
    apply (mem_sdiff.mp hy).2
    simp [A, (G.deleteEdges _).mem_neighborFinset, deleteEdges_adj, hyadj, hnot]
  have hcard : #(B \ A) ≤ 2 := by
    by_cases hempty : B \ A = ∅
    · simp [hempty]
    · obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.mpr hempty
      have hxmem : x ∈ ({u, v, w} : Finset V) := by
        have hyadj : G.Adj x y := (G.mem_neighborFinset x y).mp (mem_sdiff.mp hy).1
        by_contra hx
        have hnot : s(x, y) ∉ triEdges {u, v, w} := by
          intro he
          have hall := (mem_sym2_iff.mp (mem_filter.mp he).1) x (by simp)
          exact hx (by simpa using hall)
        apply (mem_sdiff.mp hy).2
        simp [A, (G.deleteEdges _).mem_neighborFinset, deleteEdges_adj, hyadj, hnot]
      have hsub : B \ A ⊆ ({u, v, w} : Finset V).erase x := by
        intro z hz
        refine mem_erase.mpr ⟨?_, hBA hz⟩
        exact ((G.mem_neighborFinset x z).mp (mem_sdiff.mp hz).1).ne.symm
      have hc := card_le_card hsub
      have hthree : #({u, v, w} : Finset V) ≤ 3 := by
        calc
          #({u, v, w} : Finset V) ≤ #({v, w} : Finset V) + 1 := card_insert_le _ _
          _ ≤ (#{w} + 1) + 1 := by gcongr; exact card_insert_le _ _
          _ ≤ 3 := by simp
      have herase : #(({u, v, w} : Finset V).erase x) + 1 = #({u, v, w} : Finset V) :=
        card_erase_add_one hxmem
      omega
  rw [← card_sdiff_add_card_inter B A, inter_eq_right.mpr hAB]
  change #(B \ A) + #A ≤ #A + 2
  omega

public theorem peeled_heavy_triangle_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (hu : G.minDegree + 2 ≤ G.degree u)
    (hv : G.minDegree + 2 ≤ G.degree v)
    (hw : G.minDegree + 2 ≤ G.degree w) :
    (G.deleteEdges (triEdges {u, v, w})).minDegree = G.minDegree := by
  apply Nat.le_antisymm
  · exact minDegree_le_minDegree (deleteEdges_le _)
  · refine @le_minDegree_of_forall_le_degree V (G.deleteEdges (triEdges {u, v, w}))
      _ _ ⟨u⟩ G.minDegree ?_
    intro x
    by_cases hx : x = u ∨ x = v ∨ x = w
    · rcases hx with hx | hx | hx
      · have hb := peeled_heavy_triangle_degree_add_two G (u := u) (v := v) (w := w) (x := u)
        subst x
        omega
      · have hb := peeled_heavy_triangle_degree_add_two G (u := u) (v := v) (w := w) (x := v)
        subst x
        omega
      · have hb := peeled_heavy_triangle_degree_add_two G (u := u) (v := v) (w := w) (x := w)
        subst x
        omega
    · have hxu : x ≠ u := fun h => hx (Or.inl h)
      have hxv : x ≠ v := fun h => hx (Or.inr (Or.inl h))
      have hxw : x ≠ w := fun h => hx (Or.inr (Or.inr h))
      have hdeg : (G.deleteEdges (triEdges {u, v, w})).degree x = G.degree x := by
        rw [← G.card_neighborFinset_eq_degree,
          ← (G.deleteEdges _).card_neighborFinset_eq_degree]
        congr 1
        ext y
        simp only [mem_neighborFinset, deleteEdges_adj]
        constructor
        · exact And.left
        · intro hxy
          refine ⟨hxy, ?_⟩
          intro he
          have he' : s(x, y) ∈ triEdges {u, v, w} := he
          rw [triEdges, mem_filter] at he'
          have hxmem := (mem_sym2_iff.mp he'.1) x (by simp)
          simp only [mem_insert, mem_singleton] at hxmem
          exact hxmem.elim hxu (fun h => h.elim hxv hxw)
      rw [hdeg]
      exact G.minDegree_le_degree x

end LeanPool.DrossFractionalTriangleDecomposition
