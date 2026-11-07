/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeExitPath

/-!
# P2716_T2_First Entry Clipping

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma P2716_T2_FirstEntryClipping {V E : Type*}
    [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (U : TreeSequence G e0)
    (alpha beta : Fin k) (a b : V)
    (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a) (Sum.inl b))
    (hpath : P.IsPath)
    (hmissing : alpha ∈ MissingColors G phi a ∨ beta ∈ MissingColors G phi a)
    (ha : a ∉ TreeSequenceVertexSet U) (hb : b ∈ TreeSequenceVertexSet U) :
    ∃ (v : V)
      (Q : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a) (Sum.inl v)),
      TreeExitPath U phi alpha beta a v Q ∧
      (∀ x, x ∈ Q.support → x ∈ P.support) ∧ Q.length ≤ P.length ∧
      (∀ f : E, Sum.inr f ∈ P.support →
        (∀ w, Incident G w f → w ∈ TreeSequenceVertexSet U) →
        Q.length < P.length) := by
  classical
  let X := TreeSequenceVertexSet U
  obtain ⟨v, hvX, hvP, exit⟩ :=
    TreeExitPath.firstEntry U P hpath hmissing ha ⟨b, hb, P.end_mem_support⟩
  let Q := P.takeUntil (Sum.inl v) hvP
  have hQonly : ∀ w ∈ X, (Sum.inl w ∈ Q.support ↔ w = v) := exit.2.2.2.2.2
  have hQpath : Q.IsPath := exit.1
  refine ⟨v, Q, exit,
    fun x hx => P.support_takeUntil_subset_support hvP hx,
    P.length_takeUntil_le_length hvP, ?_⟩
  intro f hf hall
  have hfnot : Sum.inr f ∉ Q.support := by
    intro hmem
    obtain ⟨j, hj, hjle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem
    have hjpos : 0 < j := by
      by_contra h
      have hj0 : j = 0 := by omega
      rw [hj0, Q.getVert_zero] at hj
      simp at hj
    have hjlt : j < Q.length := by
      by_contra h
      have heq : j = Q.length := by omega
      rw [heq, Q.getVert_length] at hj
      simp at hj
    have hprev := Q.adj_getVert_succ (i := j - 1) (by omega)
    have hsucc : j - 1 + 1 = j := by omega
    rw [hsucc, hj] at hprev
    cases hw : Q.getVert (j - 1) with
    | inr e => rw [hw] at hprev; exact hprev.elim
    | inl w =>
      rw [hw] at hprev
      have hwX := hall w hprev.1
      have hwQ : Sum.inl w ∈ Q.support :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨j - 1, hw, by omega⟩
      have hwv := (hQonly w hwX).mp hwQ
      have heq : Q.getVert (j - 1) = Q.getVert Q.length := by
        rw [hw, hwv, Q.getVert_length]
      have hi : j - 1 = Q.length := by
        apply hQpath.getVert_injOn
        · change j - 1 ≤ Q.length
          omega
        · change Q.length ≤ Q.length
          exact le_rfl
        · exact heq
      omega
  have hle := P.length_takeUntil_le_length hvP
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨j, hj, hjle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
  have hjQ : j ≤ Q.length := by
    rw [show Q.length = P.length from heq]
    exact hjle
  apply hfnot
  apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
  refine ⟨j, ?_, hjQ⟩
  exact (P.getVert_takeUntil hvP hjQ).trans hj

end GoldbergSeymour

end
