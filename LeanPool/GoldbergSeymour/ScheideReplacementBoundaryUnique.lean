/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideLastExitPath

/-!
# Scheide Replacement Boundary Unique

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideReplacementBoundaryUnique {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k)
    (L : ScheideLastExitPath G k e0 phi T C D R alpha)
    (d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)})
    (hprefix : ∀ (j : Fin (L.path.length + 1)),
      j.val ≤ L.lastIndex.val →
      ∀ x : V, L.path.getVert j.val = Sum.inl x →
        x ∈ TreeSequenceVertexSet (R d).replacementTree) :
    ∀ f : E, f ∈ BoundaryEdges G (ScheideEnlargedVertexSet R) ∧
      Sum.inr f ∈ TwoColorComponent G phi D.alpha0 alpha
        (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩)) →
      f = L.crossing := by
  classical
  let X := ScheideEnlargedVertexSet R
  have hrep : TreeSequenceVertexSet (R d).replacementTree ⊆ X := by
    intro v hv
    rw [(R d).replacement_vertices] at hv
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · simp [X, ScheideEnlargedVertexSet, hv.1]
    · simp only [X, ScheideEnlargedVertexSet, Finset.mem_union]
      right
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      rcases hv with rfl | rfl
      · exact ⟨⟨d.1, d.2⟩, by simp⟩
      · exact ⟨⟨d.1, d.2⟩, by simp⟩
  intro f hf
  obtain ⟨u, hu, w, hw, hends⟩ : ∃ u ∈ X, ∃ w ∉ X, G.ends f = s(u, w) := by
    simpa [X, BoundaryEdges] using hf.1
  have hneuw : u ≠ w := by
    intro h
    exact G.loopless f u (h ▸ hends)
  have hfsupport : Sum.inr f ∈ L.path.support := by
    have hcomponent := hf.2
    rw [← L.pathSpans] at hcomponent
    exact hcomponent
  obtain ⟨n, hnget, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hfsupport
  have hnpos : 0 < n := by
    by_cases hnzero : n = 0
    · subst n
      rw [L.path.getVert_zero] at hnget
      cases hnget
    · omega
  have hlastlt : L.lastIndex.val < L.path.length + 1 := L.lastIndex.isLt
  have hnlt : n < L.path.length := by
    by_contra hnl
    have heq : n = L.path.length := by omega
    subst n
    rw [L.path.getVert_length] at hnget
    cases hnget
  have hprev := L.path.adj_getVert_succ (i := n - 1) (by omega)
  have hnext := L.path.adj_getVert_succ (i := n) hnlt
  rw [show n - 1 + 1 = n by omega, hnget] at hprev
  have hprevExists : ∃ vprev : V, L.path.getVert (n - 1) = Sum.inl vprev := by
    cases hprevVert : L.path.getVert (n - 1) with
    | inl vprev => exact ⟨vprev, rfl⟩
    | inr q =>
        rw [hprevVert] at hprev
        simp [TwoColorIncidenceGraph] at hprev
  obtain ⟨vprev, hprevVert⟩ := hprevExists
  rw [hprevVert] at hprev
  simp only [TwoColorIncidenceGraph, Incident] at hprev
  rw [hnget] at hnext
  have hnextExists : ∃ vnext : V, L.path.getVert (n + 1) = Sum.inl vnext := by
    cases hnextVert : L.path.getVert (n + 1) with
    | inl vnext => exact ⟨vnext, rfl⟩
    | inr q =>
        rw [hnextVert] at hnext
        simp [TwoColorIncidenceGraph] at hnext
  obtain ⟨vnext, hnextVert⟩ := hnextExists
  rw [hnextVert] at hnext
  simp only [TwoColorIncidenceGraph, Incident] at hnext
  have hprevEnds : vprev = u ∨ vprev = w := by
    rw [hends] at hprev
    simpa [Sym2.mem_iff] using hprev.1
  have hnextEnds : vnext = u ∨ vnext = w := by
    rw [hends] at hnext
    simpa [Sym2.mem_iff] using hnext.1
  have hvne : vprev ≠ vnext := by
    intro heq
    have hidx := L.pathSimple.getVert_injOn
      (show n - 1 ≤ L.path.length by omega)
      (show n + 1 ≤ L.path.length by omega)
      (by rw [hprevVert, hnextVert, heq])
    omega
  have hprevXor : (vprev ∈ X ∧ vnext ∉ X) ∨
      (vprev ∉ X ∧ vnext ∈ X) := by
    rcases hprevEnds with hpu | hpw <;> rcases hnextEnds with hnu | hnw
    · exfalso
      apply hvne
      exact hpu.trans hnu.symm
    · left
      constructor
      · simpa [hpu] using hu
      · simpa [hnw] using hw
    · right
      constructor
      · simpa [hpw] using hw
      · simpa [hnu] using hu
    · exfalso
      apply hvne
      exact hpw.trans hnw.symm
  have hprevIn : n - 1 ≤ L.lastIndex.val := by
    rcases hprevXor with hcase | hcase
    · by_contra hnot
      have hout := L.afterLastOutside ⟨n - 1, by omega⟩ (by
        change L.lastIndex.val < n - 1
        omega) vprev hprevVert
      exact hout hcase.1
    · have hnextIn : n + 1 ≤ L.lastIndex.val := by
        by_contra hbad
        have hout := L.afterLastOutside ⟨n + 1, by omega⟩ (by
          change L.lastIndex.val < n + 1
          omega) vnext hnextVert
        exact hout hcase.2
      have hprevBound : n - 1 ≤ L.lastIndex.val := by omega
      exact False.elim (hcase.1 (hrep
        (hprefix ⟨n - 1, by omega⟩ hprevBound vprev hprevVert)))
  have hnextOut : ¬ n + 1 ≤ L.lastIndex.val := by
    intro hnext
    have hvnextX := hrep
      (hprefix ⟨n + 1, by omega⟩ hnext vnext hnextVert)
    rcases hprevXor with hcase | hcase
    · exact hcase.2 hvnextX
    · exact hcase.1 (hrep
        (hprefix ⟨n - 1, by omega⟩ hprevIn vprev hprevVert))
  have hidx : n = L.lastIndex.val + 1 := by
    have hsub : n - 1 + 1 ≤ L.lastIndex.val + 1 :=
      Nat.succ_le_succ hprevIn
    have hle : n ≤ L.lastIndex.val + 1 := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hsub
    have hneq : n ≠ L.lastIndex.val := by
      intro heq
      have hbad := hnget
      rw [heq, L.lastInsideAt] at hbad
      cases hbad
    have hgt : L.lastIndex.val < n := by
      by_contra hnot
      have hnle : n ≤ L.lastIndex.val := by omega
      have hsucc : n + 1 ≤ L.lastIndex.val := by omega
      exact hnextOut hsucc
    have hge : L.lastIndex.val + 1 ≤ n := by omega
    omega
  have heq : (Sum.inr f : Sum V E) = Sum.inr L.crossing := by
    rw [← hnget, hidx, L.crossingAt]
  injection heq

end GoldbergSeymour

end
