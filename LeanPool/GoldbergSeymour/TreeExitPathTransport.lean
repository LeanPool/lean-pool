/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeExitPath
public import LeanPool.GoldbergSeymour.TwoColorComponent

/-!
# Exit paths under component swaps

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Every edge of a tree exit path has an incident path vertex outside the tree. -/
theorem TreeExitPath.edge_has_outside_vertex {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (tree : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    {u v : V} (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v))
    (hExit : TreeExitPath tree phi alpha beta u v P)
    (f : E) (hfSupport : Sum.inr f ∈ P.support) :
    ∃ w : V, Sum.inl w ∈ P.support ∧ w ∉ TreeSequenceVertexSet tree ∧ Incident G w f := by
  classical
  let X := TreeSequenceVertexSet tree
  rcases hExit with ⟨hPath, hLength, huX, hvX, hMissing, honly⟩
  obtain ⟨m, hm, hmle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hfSupport
  have hmpos : 0 < m := by
    by_contra h
    have hmzero : m = 0 := by omega
    rw [hmzero] at hm
    simp at hm
  have hmlt : m < P.length := by
    by_contra h
    have hmlast : m = P.length := by omega
    rw [hmlast] at hm
    simp at hm
  have hprev := P.adj_getVert_succ (i := m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega, hm] at hprev
  obtain ⟨w, hwPrev⟩ : ∃ w : V, P.getVert (m - 1) = Sum.inl w := by
    cases hnode : P.getVert (m - 1) with
    | inl w => exact ⟨w, rfl⟩
    | inr e =>
        rw [hnode] at hprev
        simp [TwoColorIncidenceGraph] at hprev
  have hnext := P.adj_getVert_succ (i := m) hmlt
  rw [hm] at hnext
  obtain ⟨z, hzNext⟩ : ∃ z : V, P.getVert (m + 1) = Sum.inl z := by
    cases hnode : P.getVert (m + 1) with
    | inl z => exact ⟨z, rfl⟩
    | inr e =>
        rw [hnode] at hnext
        simp [TwoColorIncidenceGraph] at hnext
  have hwIncident : Incident G w f := by
    rw [hwPrev] at hprev
    simpa [TwoColorIncidenceGraph] using hprev.1
  have hzIncident : Incident G z f := by
    rw [hzNext] at hnext
    simpa [TwoColorIncidenceGraph] using hnext.1
  have hwSupport : Sum.inl w ∈ P.support := by
    rw [← hwPrev]
    exact P.getVert_mem_support (m - 1)
  have hzSupport : Sum.inl z ∈ P.support := by
    rw [← hzNext]
    exact P.getVert_mem_support (m + 1)
  by_cases hwX : w ∈ X
  · by_cases hzX : z ∈ X
    · have hwv : w = v :=
        (honly w (by simpa [X] using hwX)).mp hwSupport
      have hzv : z = v :=
        (honly z (by simpa [X] using hzX)).mp hzSupport
      have hverts : P.getVert (m - 1) = P.getVert (m + 1) := by
        rw [hwPrev, hzNext, hwv, hzv]
      have hindices := hPath.getVert_injOn
        (show m - 1 ≤ P.length by omega)
        (show m + 1 ≤ P.length by omega) hverts
      omega
    · exact ⟨z, hzSupport, hzX, hzIncident⟩
  · exact ⟨w, hwSupport, hwX, hwIncident⟩

/-- Swapping components rooted outside a tree transports its two-color exit paths. -/
theorem TreeExitPath.componentSwapTransport {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (tree : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha beta c : Fin k)
    (hac : alpha ≠ c) :
    open scoped Classical in
    let X := TreeSequenceVertexSet tree;
    let roots : Finset (V ⊕ E) :=
      {z : V ⊕ E | match z with | Sum.inl u => u ∉ X | Sum.inr _ => False};
    let rho : PartialEdgeColoring E k := fun f =>
      if ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha c z then
        if phi f = some alpha then some c else if phi f = some c then some alpha else phi f
      else phi f;
    let selected : E → Prop := fun f =>
      ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha c z;
    (∀ f, rho f = some beta ↔ phi f = some beta) →
    (∀ u ∉ X, ∀ f, Incident G u f → phi f = some alpha ∨ phi f = some c → selected f) →
    ∀ (u v : V) (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
      TreeExitPath tree phi alpha beta u v P →
      ∃ Q : (TwoColorIncidenceGraph G rho c beta).Walk (Sum.inl u) (Sum.inl v),
        TreeExitPath tree rho c beta u v Q ∧ Q.support = P.support := by
  classical
  intro X roots rho selected hbetaFixed selectedOfOutside u v P hExit
  have selectedAlphaEdge : ∀ f : E, Sum.inr f ∈ P.support →
      phi f = some alpha → selected f := by
    intro f hfP hfa
    obtain ⟨w, hwP, hwX, hwf⟩ :=
      TreeExitPath.edge_has_outside_vertex tree phi alpha beta P hExit f hfP
    exact selectedOfOutside w hwX f hwf (Or.inl hfa)
  have adjacencyTransport :
    ∀ (z w : Sum V E), z ∈ P.support → w ∈ P.support → (TwoColorIncidenceGraph G phi alpha
        beta).Adj z w → (TwoColorIncidenceGraph G rho c beta).Adj z w := by
    intro z w hzP hwP hadj
    cases z with
    | inl z =>
        cases w with
        | inl w => exact False.elim hadj
        | inr f =>
            rcases hadj with ⟨hzf, hcolor⟩
            refine ⟨hzf, ?_⟩
            rcases hcolor with hfa | hfb
            · left
              have hsel := selectedAlphaEdge f hwP hfa
              change ∃ z ∈ roots,
                Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
              simp only [rho]
              rw [ite_eq_left hsel, ite_eq_left hfa]
            · right
              exact (hbetaFixed f).2 hfb
    | inr f =>
        cases w with
        | inl w =>
            rcases hadj with ⟨hwf, hcolor⟩
            refine ⟨hwf, ?_⟩
            rcases hcolor with hfa | hfb
            · left
              have hsel := selectedAlphaEdge f hzP hfa
              change ∃ z ∈ roots,
                Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
              simp only [rho]
              rw [ite_eq_left hsel, ite_eq_left hfa]
            · right
              exact (hbetaFixed f).2 hfb
        | inr e => exact False.elim hadj
  have rebuild : ∀ {s t : Sum V E}
      (R : (TwoColorIncidenceGraph G phi alpha beta).Walk s t),
      (∀ z, z ∈ R.support → z ∈ P.support) →
      ∃ Q : (TwoColorIncidenceGraph G rho c beta).Walk s t,
        Q.support = R.support ∧ Q.length = R.length := by
    intro s t R
    induction R with
    | nil =>
        intro hsub
        exact ⟨.nil, rfl, rfl⟩
    | @cons s w t hsw R ih =>
        intro hsub
        have hsP : s ∈ P.support := hsub s (by simp)
        have hwP : w ∈ P.support := hsub w (by simp)
        obtain ⟨Q, hQsupport, hQlength⟩ := ih (by
          intro z hz
          exact hsub z (by simp [hz]))
        have hsw' := adjacencyTransport s w hsP hwP hsw
        refine ⟨.cons hsw' Q, ?_, ?_⟩
        · simp [hQsupport]
        · simp [hQlength]
  obtain ⟨Q, hQsupport, hQlength⟩ := rebuild P (by
    intro z hz
    exact hz)
  have hQpath : Q.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [hQsupport]
    exact hExit.1.support_nodup
  have hmissing : c ∈ MissingColors G rho u ∨
      beta ∈ MissingColors G rho u := by
    rcases hExit.2.2.2.2.1 with halphaMissing | hbetaMissing
    · left
      have huX : u ∉ X := by simpa [X] using hExit.2.2.1
      have hnotAlpha : alpha ∉ PresentColors G phi u := by
        simpa [MissingColors] using halphaMissing
      have hnotC : c ∉ PresentColors G rho u := by
        intro hcPresent
        obtain ⟨f, huf, hrhof⟩ := by
          simpa [PresentColors] using hcPresent
        by_cases hsel : selected f
        · change ∃ z ∈ roots,
            Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
          by_cases hfa : phi f = some alpha
          · apply hnotAlpha
            simpa [PresentColors] using
              (show ∃ q, Incident G u q ∧ phi q = some alpha from
                ⟨f, huf, hfa⟩)
          · by_cases hfc : phi f = some c
            · have hrhoAlpha : rho f = some alpha := by
                simp only [rho]
                rw [ite_eq_left hsel, ite_eq_right hfa, ite_eq_left hfc]
              have : some alpha = some c := hrhoAlpha.symm.trans hrhof
              exact hac (Option.some.inj this)
            · have hrhoOld : rho f = phi f := by
                simp only [rho]
                rw [ite_eq_left hsel, ite_eq_right hfa, ite_eq_right hfc]
              exact hfc (hrhoOld.symm.trans hrhof)
        · change ¬ ∃ z ∈ roots,
            Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
          have hfc : phi f = some c := by
            have hrhoOld : rho f = phi f := by
              simp only [rho]
              rw [ite_eq_right hsel]
            exact hrhoOld.symm.trans hrhof
          have hchosen := selectedOfOutside u huX f huf (Or.inr hfc)
          exact hsel hchosen
      simpa [MissingColors] using hnotC
    · right
      have hnotBeta : beta ∉ PresentColors G phi u := by
        simpa [MissingColors] using hbetaMissing
      have hnotBetaRho : beta ∉ PresentColors G rho u := by
        intro hbPresent
        obtain ⟨f, huf, hrf⟩ := by
          simpa [PresentColors] using hbPresent
        apply hnotBeta
        simpa [PresentColors] using
          (show ∃ q, Incident G u q ∧ phi q = some beta from
            ⟨f, huf, (hbetaFixed f).1 hrf⟩)
      simpa [MissingColors] using hnotBetaRho
  refine ⟨Q, ?_, hQsupport⟩
  refine ⟨hQpath, ?_, hExit.2.2.1, hExit.2.2.2.1, hmissing, ?_⟩
  · rw [hQlength]
    exact hExit.2.1
  · intro w hw
    rw [hQsupport]
    exact hExit.2.2.2.2.2 w hw

end GoldbergSeymour

end
