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
    [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
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
  let _ := Fintype.ofFinite V
  let H := TwoColorIncidenceGraph G phi alpha beta
  let X := TreeSequenceVertexSet U
  have chooseFirst : ∀ {u v : Sum V E} (p : H.Walk u v)
      (S : Finset (Sum V E)),
      {x ∈ S | x ∈ p.support}.Nonempty →
      ∃ x ∈ S, ∃ (hx : x ∈ p.support),
        ∀ t ∈ S, t ∈ (p.takeUntil x hx).support → t = x := by
    intro u v p S hnonempty
    have firstErase : ∃ x ∈ S, ∃ (hx : x ∈ p.support),
        {t ∈ S.erase x | t ∈ (p.takeUntil x hx).support} = ∅ := by
      simp only [← Finset.subset_empty]
      induction hn : p.length + S.card using Nat.strong_induction_on
          generalizing S v with
      | _ n ih =>
          simp only [Finset.Nonempty, Finset.mem_filter] at hnonempty
          obtain ⟨x, hxS, hxP⟩ := hnonempty
          obtain hempty | hmore := Finset.eq_empty_or_nonempty
            {t ∈ S.erase x | t ∈ (p.takeUntil x hxP).support}
          · exact ⟨x, hxS, hxP, hempty.le⟩
          · have hlt : (p.takeUntil x hxP).length + (S.erase x).card < n := by
              rw [← Finset.card_erase_add_one hxS] at hn
              have hle := p.length_takeUntil_le_length hxP
              omega
            obtain ⟨y, hyS, hyP, hyempty⟩ :=
              ih _ hlt (p.takeUntil x hxP) (S.erase x) hmore rfl
            refine ⟨y, Finset.mem_of_mem_erase hyS,
              p.support_takeUntil_subset_support hxP hyP, ?_⟩
            rwa [p.takeUntil_takeUntil, Finset.erase_right_comm,
              Finset.filter_erase, Finset.erase_eq_of_notMem] at hyempty
            simp only [Finset.mem_filter, Finset.mem_erase, ne_eq, not_and, and_imp]
            rintro hxy -
            exact p.notMem_support_takeUntil_support_takeUntil_subset
              (Ne.symm hxy) hxP hyP
    obtain ⟨x, hxS, hxP, hempty⟩ := firstErase
    refine ⟨x, hxS, hxP, ?_⟩
    suffices {t ∈ S | t ∈ (p.takeUntil x hxP).support} ⊆ {x} by
      simpa [Finset.subset_iff] using this
    rwa [Finset.filter_erase, ← Finset.subset_empty,
      ← Finset.subset_insert_iff, LawfulSingleton.insert_empty_eq] at hempty
  let S : Finset (Sum V E) := X.image Sum.inl
  obtain ⟨z, hzS, hzP, hzfirst⟩ := chooseFirst P S
    ⟨Sum.inl b, by simp [S, X, hb, P.end_mem_support]⟩
  obtain ⟨v, hvX, hvz⟩ : ∃ v, v ∈ X ∧ Sum.inl v = z := by
    simpa [S] using hzS
  subst z
  let Q := P.takeUntil (Sum.inl v) hzP
  have hQonly : ∀ w ∈ X, (Sum.inl w ∈ Q.support ↔ w = v) := by
    intro w hw
    constructor
    · intro hmem
      exact Sum.inl.inj (hzfirst (Sum.inl w) (by simp [S, hw]) hmem)
    · rintro rfl
      exact Q.end_mem_support
  have hav : a ≠ v := by rintro rfl; exact ha hvX
  have hQlen : 2 ≤ Q.length := by
    have hpos : 0 < Q.length := by
      apply Nat.pos_of_ne_zero
      intro hn
      exact hav (Sum.inl.inj (SimpleGraph.Walk.length_eq_zero_iff.mp hn).eq)
    by_contra hnot
    have hlen : Q.length = 1 := by omega
    have hadj := Q.adj_getVert_succ (i := 0) (by omega)
    have hend : Q.getVert 1 = Sum.inl v := by
      have heq := Q.getVert_length
      rwa [hlen] at heq
    rw [Q.getVert_zero, hend] at hadj
    exact hadj.elim
  have hQpath : Q.IsPath := hpath.takeUntil _
  refine ⟨v, Q, ⟨hQpath, hQlen, ha, hvX, hmissing, hQonly⟩,
    fun x hx => P.support_takeUntil_subset_support hzP hx,
    P.length_takeUntil_le_length hzP, ?_⟩
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
  have hle := P.length_takeUntil_le_length hzP
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨j, hj, hjle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
  have hjQ : j ≤ Q.length := by
    rw [show Q.length = P.length from heq]
    exact hjle
  apply hfnot
  apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
  refine ⟨j, ?_, hjQ⟩
  exact (P.getVert_takeUntil hzP hjQ).trans hj

end GoldbergSeymour

end
