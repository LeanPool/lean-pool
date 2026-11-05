/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HkuIncidentColorPreserved

public import LeanPool.GoldbergSeymour.InternalEdges

/-!
# Same Color Series Preserved

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem SameColorSeriesPreserved_segment_52.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
    LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
    : TashkinovSeries G k rounds e0 input) (j : Fin (rounds + 1)) (i : Fin rounds), j = i.succ
    → TreeSequenceInitialSegment (series.data.tree i.succ.castSucc) (series.data.tree
    i.succ.succ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series j i hji
  cases series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero i) hji.symm |>.elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hvals := congrArg Fin.val hji
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hvals := congrArg Fin.val hji
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hvals := congrArg Fin.val hji
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension

private theorem SameColorSeriesPreserved_intervalClaim_110.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
    LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
    : TashkinovSeries G k rounds e0 input) (p q : Fin rounds) (f : E) (c : Fin k),
    TreeIncidentEdge (series.data.tree p.succ.castSucc) f → series.data.coloring p.castSucc f
    = some c → c ∈ TreeMissingColors (series.data.coloring p.castSucc) (series.data.tree
    p.succ.castSucc) ∪ TashkinovStoredColors series.data p.castSucc → (∀ (j : Fin (rounds +
    1)) (i : Fin rounds), j = i.succ → TreeSequenceInitialSegment (series.data.tree
    i.succ.castSucc) (series.data.tree i.succ.succ)) → (∀ {A B : TreeSequence G e0},
    TreeSequenceInitialSegment A B → ∀ {e : E}, TreeIncidentEdge A e → TreeIncidentEdge B e) →
    ∀ (n : ℕ), (↑p : ℕ) ≤ n → n ≤ (↑q : ℕ) → ∀ (r : Fin rounds), (↑r : ℕ) = n →
    TreeIncidentEdge (series.data.tree r.succ.castSucc) f ∧ (series.data.coloring r.succ f =
    series.data.coloring p.castSucc f ∨ ∃ (j : Fin rounds), (↑p : ℕ) ≤ (↑j : ℕ) ∧ (↑j : ℕ) ≤
    (↑r : ℕ) ∧ series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
    series.data.connectingEdges j.succ = {f}) ∧ ∃ (d : Fin k), series.data.coloring r.succ f =
    some d ∧ d ∈ TreeMissingColors (series.data.coloring r.succ) (series.data.tree
    r.succ.castSucc) ∪ TashkinovStoredColors series.data r.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input series p q f c hf hfc hc segment incidentTransfer n hpn
  induction n, hpn using Nat.le_induction with
  | base =>
      intro hnq r hr
      have hpr : r = p := by apply Fin.ext; omega
      subst r
      have first := HkuIncidentColorPreserved G k rounds e0 input series p f c
        hf hfc hc
      refine ⟨hf, ?_, first.2⟩
      rcases first.1 with hp | he
      · exact Or.inl hp
      · exact Or.inr ⟨p, le_rfl, le_rfl, he.1, he.2.1⟩
  | succ n hn ih =>
      intro hnq s hs
      let r : Fin rounds := ⟨n, by omega⟩
      have current := ih (by omega) r rfl
      have hseg := segment r.succ r rfl
      have hinc := incidentTransfer hseg current.1
      rcases current.2.2 with ⟨d, hd, hdm⟩
      have hmem := (HkuMissingStoredMonotone G k rounds e0 input series r).2 hdm
      let nextIndex : Fin rounds := ⟨n + 1, by omega⟩
      have htree : r.succ.succ = nextIndex.succ.castSucc := by
        apply Fin.ext
        simp [r, nextIndex]
      have hcolor : r.succ = nextIndex.castSucc := by
        apply Fin.ext
        simp [r, nextIndex]
      rw [htree] at hinc
      rw [hcolor] at hd
      have next := HkuIncidentColorPreserved G k rounds e0 input series nextIndex f
        d (by simpa [nextIndex] using hinc)
        (by simpa [nextIndex] using hd) hmem
      have hsr : s = nextIndex := by apply Fin.ext; simp [nextIndex, hs]
      rw [hsr]
      refine ⟨hinc, ?_, next.2⟩
      rcases current.2.1 with old | witness
      · rcases next.1 with keep | exception
        · exact Or.inl (keep.trans old)
        · exact Or.inr ⟨nextIndex, by omega, le_rfl, exception.1, exception.2.1⟩
      · rcases next.1 with keep | exception
        · rcases witness with ⟨w, hwp, hwr, hwk, hwe⟩
          have hw : w.val ≤ n := by simpa [r] using hwr
          exact Or.inr ⟨w, hwp, by simpa [nextIndex] using Nat.le_trans hw (Nat.le_succ n), hwk,
              hwe⟩
        · exact Or.inr ⟨nextIndex, by omega, le_rfl, exception.1, exception.2.1⟩

private theorem SameColorSeriesPreserved_branch_168.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (p q : Fin rounds) (f : E),
    let _ := Classical.decEq V; (
    ∀ (j : Fin (rounds + 1)) (i : Fin rounds), j = i.succ → TreeSequenceInitialSegment
        (series.data.tree i.succ.castSucc) (series.data.tree i.succ.succ)) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B →
    ∀ {v : V}, v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B) → (
    ∀ (n : ℕ), (↑p : ℕ) ≤ n → n ≤ (↑q : ℕ) →
    ∀ (r : Fin rounds), (↑r : ℕ) = n → TreeIncidentEdge (series.data.tree r.succ.castSucc) f ∧
        (series.data.coloring r.succ f = series.data.coloring p.castSucc f ∨
    ∃ (j : Fin rounds), (↑p : ℕ) ≤ (↑j : ℕ) ∧ (↑j : ℕ) ≤ (↑r : ℕ) ∧ series.data.kind j.succ = some
        TashkinovExtensionKind.PE ∧ series.data.connectingEdges j.succ = {f}) ∧
    ∃ (d : Fin k), series.data.coloring r.succ f = some d ∧ d ∈ TreeMissingColors
        (series.data.coloring r.succ) (series.data.tree r.succ.castSucc) ∪ TashkinovStoredColors
        series.data r.succ) → (TreeIncidentEdge (series.data.tree q.succ.castSucc) f ∧
        (series.data.coloring q.succ f = series.data.coloring p.castSucc f ∨
    ∃ (j : Fin rounds), (↑p : ℕ) ≤ (↑j : ℕ) ∧ (↑j : ℕ) ≤ (↑q : ℕ) ∧ series.data.kind j.succ = some
        TashkinovExtensionKind.PE ∧ series.data.connectingEdges j.succ = {f}) ∧
    ∃ (d : Fin k), series.data.coloring q.succ f = some d ∧ d ∈ TreeMissingColors
        (series.data.coloring q.succ) (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors
        series.data q.succ) → f ∈ InternalEdges G (TreeSequenceVertexSet (series.data.tree
        p.succ.castSucc)) → series.data.coloring q.succ f = series.data.coloring p.castSucc f := by
  classical
  intro V E _ _ _ G k rounds e0 input series p q f this segment vertexTransfer intervalClaim
      finalClaim hinternal
  rcases finalClaim.2.1 with preserved | witness
  · exact preserved
  · exfalso
    rcases witness with ⟨j, hjp, hjq, hjkind, hjedges⟩
    have hsegAll : ∀ t : Fin rounds, p.val ≤ t.val → t.val ≤ q.val →
        TreeIncidentEdge (series.data.tree t.succ.castSucc) f := by
      intro t htp htq
      have h := intervalClaim t.val htp htq t rfl
      exact h.1
    have hjinc := hsegAll j hjp hjq
    have hbase : ∀ v, Incident G v f →
        v ∈ TreeSequenceVertexSet (series.data.tree p.succ.castSucc) := by
      intro v hv
      simpa [InternalEdges] using (Finset.mem_filter.mp hinternal).2 v hv
    have jlt := j.isLt
    have carry : ∀ n : ℕ, p.val ≤ n → n ≤ j.val → n < rounds →
          ∀ z : Fin rounds, z.val = n → ∀ x : V, x ∈ TreeSequenceVertexSet
          (series.data.tree p.succ.castSucc) →
          x ∈ TreeSequenceVertexSet
            (series.data.tree z.succ.castSucc) := by
      intro n hpn
      induction n, hpn using Nat.le_induction with
      | base =>
          intro hn hnr z hz x hx
          have heq : z = p := by apply Fin.ext; omega
          rw [heq]
          exact hx
      | succ n hn ih =>
          intro hnq hnr z hz x hx
          let prev : Fin rounds := ⟨n, by omega⟩
          have hold := ih (by omega) (by omega) prev rfl x hx
          have hstep := segment prev.succ prev rfl
          have hnew := vertexTransfer hstep hold
          let nextStep : Fin rounds := ⟨n + 1, by omega⟩
          have htree : prev.succ.succ = nextStep.succ.castSucc := by
            apply Fin.ext
            simp [prev, nextStep]
          rw [htree] at hnew
          have hzeq : z = nextStep := by apply Fin.ext; omega
          rw [hzeq]
          exact hnew
    have hverts : ∀ v, Incident G v f →
        v ∈ TreeSequenceVertexSet (series.data.tree j.succ.castSucc) := by
      intro v hv
      have hvbase := hbase v hv
      exact carry j.val hjp le_rfl jlt j rfl v hvbase
    have hnotboundary : f ∉ BoundaryEdges G
        (TreeSequenceVertexSet (series.data.tree j.succ.castSucc)) := by
      intro hb
      simp only [BoundaryEdges, Fin.castSucc_succ, Finset.mem_filter, Finset.mem_univ, true_and]
          at hb
      rcases hb with ⟨u, hu, v, hv, hend⟩
      have hvin : Incident G v f := by
        simp [Incident, hend]
      exact hv (hverts v hvin)
    have hstep := series.certified j.succ
    revert hnotboundary hjkind hjedges
    generalize hz : j.succ = z at hstep
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        intro hjkind hjedges hnotboundary
        have hv := congrArg Fin.val hz
        simp at hv
    | PE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
        intro hjkind hjedges hnotboundary
        have hci : ci = j := by
          apply Fin.ext
          have hv := congrArg Fin.val hz
          simp at hv ⊢
          omega
        subst ci
        have hedge : choice.edge = f := by
          rw [currentEdges] at hjedges
          exact Finset.singleton_inj.mp hjedges
        have hdef := choice.edgeDefective
        rcases hdef with ⟨alpha, hcolor, hboundary⟩
        have hboundary' : choice.edge ∈ BoundaryEdges G
            (TreeSequenceVertexSet (series.data.tree j.succ.castSucc)) := by
          change choice.edge ∈ BoundaryColorEdges G choice.selected
            (TreeSequenceVertexSet (series.data.tree j.succ.castSucc)) alpha
              at hboundary
          simpa [BoundaryColorEdges] using (Finset.mem_filter.mp hboundary).1
        exact hnotboundary (hedge ▸ hboundary')
    | SE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        intro hjkind hjedges hnotboundary
        have hci : ci = j := by
          apply Fin.ext
          have hv := congrArg Fin.val hz
          simp at hv ⊢
          omega
        subst ci
        have ck := currentKind
        rw [ck] at hjkind
        simp at hjkind
    | RE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        intro hjkind hjedges hnotboundary
        have hci : ci = j := by
          apply Fin.ext
          have hv := congrArg Fin.val hz
          simp at hv ⊢
          omega
        subst ci
        have ck := currentKind
        rw [ck] at hjkind
        simp at hjkind

theorem SameColorSeriesPreserved {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (p q : Fin rounds)
    (hpq : p.val ≤ q.val) (f : E) (c : Fin k)
    (hf : TreeIncidentEdge (series.data.tree p.succ.castSucc) f)
    (hfc : series.data.coloring p.castSucc f = some c)
    (hc : c ∈ TreeMissingColors (series.data.coloring p.castSucc)
          (series.data.tree p.succ.castSucc) ∪
        TashkinovStoredColors series.data p.castSucc) :
    (series.data.coloring q.succ f = series.data.coloring p.castSucc f ∨
      ∃ j : Fin rounds, p.val ≤ j.val ∧ j.val ≤ q.val ∧
        series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
        series.data.connectingEdges j.succ = {f}) ∧
    (f ∈ InternalEdges G
          (TreeSequenceVertexSet (series.data.tree p.succ.castSucc)) →
      series.data.coloring q.succ f = series.data.coloring p.castSucc f) := by
  classical
  let : DecidableEq V := Classical.decEq V
  have segment : ∀ (j : Fin (rounds + 1)) (i : Fin rounds), j = i.succ →
      TreeSequenceInitialSegment (series.data.tree i.succ.castSucc)
        (series.data.tree i.succ.succ) := by
    exact @SameColorSeriesPreserved_segment_52 V E inferInstance inferInstance inferInstance G k
        rounds e0 input series
  have vertexTransfer {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨x, hx⟩
    rcases hab with ⟨hlen, hvertices, hedges⟩
    unfold TreeSequenceVertexSet
    apply Finset.mem_image.mpr
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) x, ?_, ?_⟩
    · exact Finset.mem_univ _
    · exact (hvertices x).trans hx
  have incidentTransfer {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {e : E}
      (he : TreeIncidentEdge A e) : TreeIncidentEdge B e := by
    rcases he with ⟨v, hv, hve⟩
    exact ⟨v, vertexTransfer hab hv, hve⟩
  have intervalClaim :
    ∀ (n : ℕ), p.val ≤ n → n ≤ q.val →
    ∀ r : Fin rounds, r.val = n → (TreeIncidentEdge (series.data.tree r.succ.castSucc) f ∧
        (series.data.coloring r.succ f = series.data.coloring p.castSucc f ∨
    ∃ j : Fin rounds, p.val ≤ j.val ∧ j.val ≤ r.val ∧ series.data.kind j.succ = some
        TashkinovExtensionKind.PE ∧ series.data.connectingEdges j.succ = {f}) ∧
    ∃ d : Fin k, series.data.coloring r.succ f = some d ∧ d ∈ TreeMissingColors
        (series.data.coloring r.succ) (series.data.tree r.succ.castSucc) ∪ TashkinovStoredColors
        series.data r.succ) := by
    exact @SameColorSeriesPreserved_intervalClaim_110 V E inferInstance inferInstance
        inferInstance G k rounds e0 input series p q f c hf hfc hc segment incidentTransfer
  have finalClaim := intervalClaim q.val (by omega) le_rfl q rfl
  refine ⟨?_, ?_⟩
  · exact finalClaim.2.1
  · exact @SameColorSeriesPreserved_branch_168 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series p q f segment vertexTransfer intervalClaim finalClaim
end GoldbergSeymour

end
