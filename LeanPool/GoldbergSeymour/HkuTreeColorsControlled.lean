/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesColoringProperties

public import LeanPool.GoldbergSeymour.HkuIncidentColorPreserved
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TreeUsedColors

/-!
# Hku Tree Colors Controlled

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_augmentationUsed_86.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G :
    LooplessMultigraph V E) (k : ℕ) (e0 : E), (∀ {A B : TreeSequence G e0},
    TreeSequenceInitialSegment A B → ∀ {phi : PartialEdgeColoring E k}, TreeMissingColors phi
    A ⊆ TreeMissingColors phi B) → ∀ {A B : TreeSequence G e0} {phi : PartialEdgeColoring E
    k}, TashkinovAugmentation phi A B → TreeUsedColors phi B ⊆ TreeMissingColors phi B ∪
    TreeUsedColors phi A := by
  classical
  intro V E _ _ G k e0 missingTransfer A B phi hab
  let _ := Fintype.ofFinite V
  rcases hab with ⟨hlen, hseg, c, hcolor, hmissing⟩
  intro d hd
  simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hd ⊢
  rcases hd with ⟨j, hj, hdj⟩
  by_cases hlast : j.val = A.length
  · have hjlast : j = Fin.cast hlen.symm (Fin.last A.length) := by
      apply Fin.ext
      simp [hlast]
    left
    have : d = c := by
      rw [hjlast] at hdj
      exact (Option.some.inj (hcolor.symm.trans hdj)).symm
    rw [this]
    exact missingTransfer hseg hmissing
  · have hjlt : j.val < A.length := by
      have := j.isLt
      omega
    let jold : Fin A.length := ⟨j.val, hjlt⟩
    have hle : A.length ≤ B.length := hseg.1
    have hjcast : j = Fin.castLE hle jold := by
      apply Fin.ext
      rw [Fin.val_castLE]
    have hedge : B.edge j = A.edge jold := by
      rw [hjcast]
      exact hseg.2.2 jold
    right
    refine ⟨jold, ?_, ?_⟩
    · simpa [jold] using hj
    · rw [hedge] at hdj
      exact hdj

private theorem helper_firstClaim_290.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input), (∀ {A B :
    TreeSequence G e0} {phi : PartialEdgeColoring E k}, TashkinovAugmentationSequence phi A B
    → TreeUsedColors phi B ⊆ TreeMissingColors phi B ∪ TreeUsedColors phi A) → (∀ {A B :
    TreeSequence G e0} {f : E}, TreeSequenceAdjoinEdge A f B → ∀ {phi : PartialEdgeColoring E
    k} {c : Fin k}, phi f = some c → TreeUsedColors phi B ⊆ TreeUsedColors phi A ∪ {c}) → (∀
    {i : Fin (rounds + (1 : ℕ))} {c : Fin k}, (↑i : ℕ) ≠ (0 : ℕ) → c ∈ series.data.stored i →
    c ∈ TreeMissingColors (series.data.coloring i) (series.data.tree i.castSucc) ∪
    TashkinovStoredColors series.data i) → (∀ {i : Fin rounds}, IsOneEdgeUncolored
    (series.data.coloring i.castSucc) e0 → TreeUsedColors (series.data.coloring i.castSucc)
    (series.data.tree i.succ.castSucc) ⊆ TreeMissingColors (series.data.coloring i.castSucc)
    (series.data.tree i.succ.castSucc) ∪ TashkinovStoredColors series.data i.castSucc → ∀ {d :
    Fin k}, d ∈ TreeUsedColors (series.data.coloring i.succ) (series.data.tree
    i.succ.castSucc) → d ∈ TreeMissingColors (series.data.coloring i.succ) (series.data.tree
    i.succ.castSucc) ∪ TashkinovStoredColors series.data i.succ) → ∀ (i : Fin (rounds + (1 :
    ℕ))), TreeUsedColors (series.data.coloring i) (series.data.tree i.succ) ⊆
    TreeMissingColors (series.data.coloring i) (series.data.tree i.succ) ∪
    TashkinovStoredColors series.data i := by
  classical
  intro V E _ _ _ G k rounds e0 input series closureUsed adjoinUsed storedOrMissing colorTransport i
  induction i using Fin.induction with
  | zero =>
    have cert := series.certified (0 : Fin (rounds + 1))
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      have hzero : TreeUsedColors (series.data.coloring 0)
          (series.data.tree 0) = ∅ := by
        ext c
        simp [TreeUsedColors]
        omega
      have hbase := closureUsed initialClosure.1
      rw [hzero] at hbase
      change TreeUsedColors (series.data.coloring 0)
          (series.data.tree 1) ⊆ _
      intro c hc
      exact Finset.mem_union.mpr (Or.inl (by
        exact (Finset.mem_union.mp
            (by simpa only [Fin.succ_zero_eq_one] using hbase hc)).resolve_right
          (by simp)))
  | succ i ih =>
    have cert := series.certified i.succ
    generalize hz : i.succ = z at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      have hbad : i.succ.val + 1 = 0 := by simpa using congrArg Fin.val hz
      omega
    | SE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hi : ci = i := by
        apply Fin.ext
        have hv := congrArg Fin.val hz
        simp at hv ⊢
        omega
      subst ci
      unfold IsOneEdgeUncolored at previousOneUncolored
      intro d hd
      have hclose := closureUsed closedExtension.1 hd
      rcases Finset.mem_union.mp hclose with hm | ha
      · exact Finset.mem_union.mpr (Or.inl hm)
      · have hadj := adjoinUsed adjoinedExactly
          (show series.data.coloring i.succ choice.edge = some choice.color by
            rw [← choice.edgeColor, ← currentColoring])
        have hparts := hadj ha
        rcases Finset.mem_union.mp hparts with hold | hnew
        · exact (HkuMissingStoredMonotone G k rounds e0 input series i).2
            (colorTransport previousOneUncolored ih hold)
        · have hstored : choice.color ∈ series.data.stored i.succ := by
            rw [currentStored]
            simp
          have hdcolor : d = choice.color := by simpa using hnew
          exact (HkuMissingStoredMonotone G k rounds e0 input series i).2
            (by simpa [hdcolor] using
              storedOrMissing (c := choice.color) (by simp) hstored)
    | PE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      have hi : ci = i := by
        apply Fin.ext
        have hv := congrArg Fin.val hz
        simp at hv ⊢
        omega
      subst ci
      unfold IsOneEdgeUncolored at previousOneUncolored
      intro d hd
      have hclose := closureUsed closedExtension.1 hd
      rcases Finset.mem_union.mp hclose with hm | ho
      · exact Finset.mem_union.mpr (Or.inl hm)
      · exact (HkuMissingStoredMonotone G k rounds e0 input series i).2
          (colorTransport previousOneUncolored ih ho)
    | RE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hi : ci = i := by
        apply Fin.ext
        have hv := congrArg Fin.val hz
        simp at hv ⊢
        omega
      subst ci
      unfold IsOneEdgeUncolored at previousOneUncolored
      intro d hd
      have hclose := closureUsed closedExtension.1 hd
      rcases Finset.mem_union.mp hclose with hm | ho
      · exact Finset.mem_union.mpr (Or.inl hm)
      · have hcol : series.data.coloring i.succ available.edge =
            some available.delta ∨ series.data.coloring i.succ available.edge =
              some available.gamma := by
          rw [currentColoring]
          cases available.returnPath with
          | cons adjacent _ =>
            exact (TwoColorIncidenceEdgeColors adjacent).elim Or.inr Or.inl
        rcases hcol with hdelta | hgamma
        · have hparts := adjoinUsed adjoinedExactly hdelta ho
          rcases Finset.mem_union.mp hparts with hold | hnew
          · exact (HkuMissingStoredMonotone G k rounds e0 input series i).2
              (colorTransport previousOneUncolored ih hold)
          · have hstored : available.delta ∈ series.data.stored i.succ := by
              rw [currentStored]
              simp
            have hdcolor : d = available.delta := by simpa using hnew
            exact (HkuMissingStoredMonotone G k rounds e0 input series i).2
              (by simpa [hdcolor] using storedOrMissing (c := available.delta) (by simp) hstored)
        · have hparts := adjoinUsed adjoinedExactly hgamma ho
          rcases Finset.mem_union.mp hparts with hold | hnew
          · exact (HkuMissingStoredMonotone G k rounds e0 input series i).2
              (colorTransport previousOneUncolored ih hold)
          · have hstored : available.gamma ∈ series.data.stored i.succ := by
              rw [currentStored]
              simp
            have hdcolor : d = available.gamma := by simpa using hnew
            exact (HkuMissingStoredMonotone G k rounds e0 input series i).2
              (by simpa [hdcolor] using storedOrMissing (c := available.gamma) (by simp) hstored)

private theorem helper_firstColored_439.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input), (∀ {T :
    TreeSequence G e0} {j : Fin T.length}, (1 : ℕ) ≤ (↑j : ℕ) → TreeIncidentEdge T (T.edge j))
    → (∀ {A B : TreeSequence G e0} {phi : PartialEdgeColoring E k},
    TashkinovAugmentationSequence phi A B → (∀ (j : Fin A.length), (1 : ℕ) ≤ (↑j : ℕ) → ∃ (c :
    Fin k), phi (A.edge j) = some c) → ∀ (j : Fin B.length), (1 : ℕ) ≤ (↑j : ℕ) → ∃ (c : Fin
    k), phi (B.edge j) = some c) → (∀ {A B : TreeSequence G e0} {f : E} {c : Fin k},
    TreeSequenceAdjoinEdge A f B → ∀ {phi : PartialEdgeColoring E k}, phi f = some c → (∀ (j :
    Fin A.length), (1 : ℕ) ≤ (↑j : ℕ) → ∃ (d : Fin k), phi (A.edge j) = some d) → ∀ (j : Fin
    B.length), (1 : ℕ) ≤ (↑j : ℕ) → ∃ (d : Fin k), phi (B.edge j) = some d) → (∀ (i : Fin
    (rounds + (1 : ℕ))), TreeUsedColors (series.data.coloring i) (series.data.tree i.succ) ⊆
    TreeMissingColors (series.data.coloring i) (series.data.tree i.succ) ∪
    TashkinovStoredColors series.data i) → (∀ {A : TreeSequence G e0} {phi pi :
    PartialEdgeColoring E k} {C : Finset (Fin k)}, StableColoring A C phi pi →
    TreeMissingColors phi A ⊆ TreeMissingColors pi A) → ∀ (i : Fin (rounds + (1 : ℕ))) (j :
    Fin (series.data.tree i.succ).length), (1 : ℕ) ≤ (↑j : ℕ) → ∃ (c : Fin k),
    series.data.coloring i ((series.data.tree i.succ).edge j) = some c := by
  classical
  intro V E _ _ _ G k rounds e0 input series edgeIncident sequenceColored adjoinColored
      firstClaim stableMissingTransfer i
  induction i using Fin.induction with
  | zero =>
    have cert := series.certified (0 : Fin (rounds + 1))
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      exact sequenceColored initialClosure.1 (by
        intro j hj
        have hz : j.val = 0 := by simpa [seedLength] using j.isLt
        omega)
  | succ i ih =>
    have cert := series.certified i.succ
    generalize hz : i.succ = z at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      have : i.succ.val + 1 = 0 := by simpa using congrArg Fin.val hz
      omega
    | SE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hi : ci = i := by apply Fin.ext; have hv := congrArg Fin.val hz; simp at hv ⊢; omega
      subst ci
      intro j hj
      rw [currentColoring] at closedExtension
      have hold : ∀ j : Fin (series.data.tree i.succ.castSucc).length,
          1 ≤ j.val → ∃ c, choice.selected
            ((series.data.tree i.succ.castSucc).edge j) = some c := by
        intro j hj
        obtain ⟨c, hc⟩ := ih j hj
        have hs := choice.selectedStable.1 _
          (edgeIncident (T := series.data.tree i.succ.castSucc) hj)
        have hmem := firstClaim i.castSucc
          (by simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j,
              hj, hc⟩)
        exact ⟨c, (hs ⟨c, hmem, hc⟩).trans hc⟩
      simpa [currentColoring] using (sequenceColored closedExtension.1
        (adjoinColored adjoinedExactly choice.edgeColor hold) j hj)
    | PE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      have hi : ci = i := by apply Fin.ext; have hv := congrArg Fin.val hz; simp at hv ⊢; omega
      subst ci
      intro j hj
      have hold : ∀ j : Fin (series.data.tree i.succ.castSucc).length,
          1 ≤ j.val → ∃ c, series.data.coloring i.succ
            ((series.data.tree i.succ.castSucc).edge j) = some c := by
        intro j hj
        obtain ⟨c, hc⟩ := ih j hj
        have hmem := firstClaim i.castSucc
          (by simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j,
              hj, hc⟩)
        have hmem' : c ∈ TreeMissingColors (series.data.coloring i.castSucc)
            (series.data.tree i.succ.castSucc) ∪
            TashkinovStoredColors series.data i.castSucc := by simpa using hmem
        have hselmem : c ∈ TreeMissingColors choice.selected
            (series.data.tree i.succ.castSucc) ∪
            TashkinovStoredColors series.data i.castSucc := by
          rcases Finset.mem_union.mp hmem' with hm | hs
          · exact Finset.mem_union.mpr (Or.inl
              (stableMissingTransfer choice.selectedStable hm))
          · exact Finset.mem_union.mpr (Or.inr hs)
        have hs := choice.selectedStable.1 _
          (edgeIncident (T := series.data.tree i.succ.castSucc) hj)
          ⟨c, hmem, hc⟩
        have hss := secondStableRelation.1 _
          (edgeIncident (T := series.data.tree i.succ.castSucc) hj)
          ⟨c, by
            rcases Finset.mem_union.mp hselmem with hm | hs
            · exact Finset.mem_union.mpr (Or.inl hm)
            · exact Finset.mem_union.mpr (Or.inr (by simp [hs])), hs.trans hc⟩
        rw [currentColoring]
        exact TwoColorComponentSwapColored (hss.trans (hs.trans hc))
      exact sequenceColored closedExtension.1 hold j hj
    | RE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hi : ci = i := by apply Fin.ext; have hv := congrArg Fin.val hz; simp at hv ⊢; omega
      subst ci
      intro j hj
      rw [currentColoring] at closedExtension
      have hcol : series.data.coloring i.succ available.edge =
            some available.delta ∨
            series.data.coloring i.succ available.edge =
              some available.gamma := by
        rw [currentColoring]
        cases available.returnPath with
        | cons adjacent _ =>
          exact (TwoColorIncidenceEdgeColors adjacent).elim Or.inr Or.inl
      rcases hcol with hcol | hcol
      · have hcol' : series.data.coloring i.castSucc available.edge =
            some available.delta := by simpa [currentColoring] using hcol
        simpa [currentColoring] using (sequenceColored closedExtension.1
          (adjoinColored adjoinedExactly hcol' ih) j hj)
      · have hcol' : series.data.coloring i.castSucc available.edge =
            some available.gamma := by simpa [currentColoring] using hcol
        simpa [currentColoring] using (sequenceColored closedExtension.1
          (adjoinColored adjoinedExactly hcol' ih) j hj)

private theorem helper_branch_776.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds)
    (sigma : PartialEdgeColoring E k), IsOneEdgeUncolored sigma e0 → ∀ (j : Fin
    (series.data.tree q.succ.castSucc).length), (↑j : ℕ) = (0 : ℕ) → sigma ((series.data.tree
    q.succ.castSucc).edge j) = series.data.coloring q.succ ((series.data.tree
    q.succ.castSucc).edge j) := by
  classical
  intro V E _ _ _ G k rounds e0 input series q sigma hone j hj
  have he : (series.data.tree q.succ.castSucc).edge j = e0 := by
    rw [show j = ⟨0, (series.data.tree q.succ.castSucc).positive⟩ by
      apply Fin.ext; exact hj]
    exact (series.data.tree q.succ.castSucc).first_edge
  have hroot : series.data.coloring q.succ e0 = none := by
    have cert := series.certified q.succ
    generalize hq : q.succ = z at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero q) hq |>.elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hv := congrArg Fin.val hq
      simp at hv
      have hi : i = q := by apply Fin.ext; omega
      subst i
      rw [currentColoring]
      exact choice.selectedOneUncolored.1
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper currentOneUncolored
        currentStored currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      have hv := congrArg Fin.val hq
      simp at hv
      have hi : i = q := by apply Fin.ext; omega
      subst i
      exact currentOneUncolored.1
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
      have hv := congrArg Fin.val hq
      simp at hv
      have hi : i = q := by apply Fin.ext; omega
      subst i
      rw [currentColoring]
      exact previousOneUncolored.1
  rw [he, hroot, hone.1]

private theorem helper_branch_820.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds),
    (∀ {T : TreeSequence G e0} {j : Fin T.length}, (1 : ℕ) ≤ (↑j : ℕ) → TreeIncidentEdge T
    (T.edge j)) → (∀ {i : Fin rounds}, IsOneEdgeUncolored (series.data.coloring i.castSucc) e0
    → TreeUsedColors (series.data.coloring i.castSucc) (series.data.tree i.succ.castSucc) ⊆
    TreeMissingColors (series.data.coloring i.castSucc) (series.data.tree i.succ.castSucc) ∪
    TashkinovStoredColors series.data i.castSucc → ∀ {d : Fin k}, d ∈ TreeUsedColors
    (series.data.coloring i.succ) (series.data.tree i.succ.castSucc) → d ∈ TreeMissingColors
    (series.data.coloring i.succ) (series.data.tree i.succ.castSucc) ∪ TashkinovStoredColors
    series.data i.succ) → (∀ (i : Fin (rounds + (1 : ℕ))), TreeUsedColors
    (series.data.coloring i) (series.data.tree i.succ) ⊆ TreeMissingColors
    (series.data.coloring i) (series.data.tree i.succ) ∪ TashkinovStoredColors series.data i)
    → (∀ (i : Fin (rounds + (1 : ℕ))) (j : Fin (series.data.tree i.succ).length), (1 : ℕ) ≤
    (↑j : ℕ) → ∃ (c : Fin k), series.data.coloring i ((series.data.tree i.succ).edge j) = some
    c) → ∀ (sigma : PartialEdgeColoring E k), StableColoring (series.data.tree
    q.succ.castSucc) (TashkinovStoredColors series.data q.succ) (series.data.coloring q.succ)
    sigma → ∀ (j : Fin (series.data.tree q.succ.castSucc).length), ¬(↑j : ℕ) = (0 : ℕ) → sigma
    ((series.data.tree q.succ.castSucc).edge j) = series.data.coloring q.succ
    ((series.data.tree q.succ.castSucc).edge j) := by
  classical
  intro V E _ _ _ G k rounds e0 input series q edgeIncident colorTransport firstClaim
      firstColored sigma hstable j hj
  have hjinc : TreeIncidentEdge (series.data.tree q.succ.castSucc)
      ((series.data.tree q.succ.castSucc).edge j) := by
    exact edgeIncident (T := series.data.tree q.succ.castSucc) (by omega)
    /-
    obtain ⟨v, hv⟩ := (series.data.tree q.succ.castSucc).attaches j
    exact ⟨_, by simp [TreeSequenceVertexSet], by
      unfold Incident
      rw [hv]
      exact Sym2.mem_mk_left _ _⟩ -/
  have hprev : IsOneEdgeUncolored (series.data.coloring q.castSucc) e0 := by
    have cert := series.certified q.succ
    generalize hq : q.succ = z at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero q) hq |>.elim
    | SE i a b c d e f g h j l m n o p r s t u =>
      have hv := congrArg Fin.val hq
      simp at hv
      have hi : i = q := by apply Fin.ext; omega
      subst i
      simpa using b
    | PE i a b c d e f g h j l m n o p r s t u v w x y z aa ab ac ad =>
      have hv := congrArg Fin.val hq
      simp at hv
      have hi : i = q := by apply Fin.ext; omega
      subst i
      simpa using b
    | RE i a b c d e f g h j l m n o p q' r s t =>
      have hv := congrArg Fin.val hq
      simp at hv
      have hi : i = q := by apply Fin.ext; omega
      subst i
      simpa using b
  have hmem :
    ∀ {d : Fin k}, d ∈ TreeUsedColors (series.data.coloring q.succ) (series.data.tree
        q.succ.castSucc) → d ∈ TreeMissingColors (series.data.coloring q.succ) (series.data.tree
        q.succ.castSucc) ∪ TashkinovStoredColors series.data q.succ :=
    colorTransport (i := q) hprev (firstClaim q.castSucc)
  have hstableEdge := hstable.1 _ hjinc
  obtain ⟨d, hd⟩ := firstColored q.castSucc j (by omega)
  have hmove := HkuIncidentColorPreserved G k rounds e0 input series q
    _ d hjinc hd (firstClaim q.castSucc (by
      simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨j, Nat.one_le_iff_ne_zero.mpr hj, hd⟩))
  obtain ⟨d', hd', hctrl⟩ := hmove.2
  apply hstableEdge
  refine ⟨d', hmem ?_, hd'⟩
  simp only [TreeUsedColors, Fin.castSucc_succ, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨j, Nat.one_le_iff_ne_zero.mpr hj, hd'⟩

private theorem helper_adjoinUsed_863.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k :
    ℕ) (e0 : E) {A B : TreeSequence G e0} {f : E}, TreeSequenceAdjoinEdge A f B → ∀ {phi :
    PartialEdgeColoring E k} {c : Fin k}, phi f = some c → TreeUsedColors phi B ⊆
    TreeUsedColors phi A ∪ {c} := by
  classical
  intro V E G k e0 A B f hadj phi c hcolor
  rcases hadj with ⟨hlen, hseg, hlast⟩
  intro d hd
  simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and, Finset.union_singleton,
    Finset.mem_insert] at hd ⊢
  rcases hd with ⟨j, hj, hdj⟩
  by_cases hold : j.val < A.length
  · let jold : Fin A.length := ⟨j.val, hold⟩
    have hle : A.length ≤ B.length := hseg.1
    have hjcast : j = Fin.castLE hle jold := by
      apply Fin.ext
      rw [Fin.val_castLE]
    exact Or.inr (by
    refine ⟨jold, ?_, ?_⟩
    · simpa [jold] using hj
    · rw [hjcast, hseg.2.2 jold] at hdj
      exact hdj)
  · exact Or.inl (by
    have hjlast : j = Fin.cast hlen.symm (Fin.last A.length) := by
      apply Fin.ext
      have := j.isLt
      simp at *
      omega
    have : d = c := by
      rw [hjlast, hlast] at hdj
      exact (Option.some.inj (hcolor.symm.trans hdj)).symm
    exact this)

private theorem helper_colorTransport_913.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input), (∀ {T :
    TreeSequence G e0} {j : Fin T.length}, (1 : ℕ) ≤ (↑j : ℕ) → TreeIncidentEdge T (T.edge j))
    → ∀ {i : Fin rounds}, IsOneEdgeUncolored (series.data.coloring i.castSucc) e0 →
    TreeUsedColors (series.data.coloring i.castSucc) (series.data.tree i.succ.castSucc) ⊆
    TreeMissingColors (series.data.coloring i.castSucc) (series.data.tree i.succ.castSucc) ∪
    TashkinovStoredColors series.data i.castSucc → ∀ {d : Fin k}, d ∈ TreeUsedColors
    (series.data.coloring i.succ) (series.data.tree i.succ.castSucc) → d ∈ TreeMissingColors
    (series.data.coloring i.succ) (series.data.tree i.succ.castSucc) ∪ TashkinovStoredColors
    series.data i.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input series edgeIncident i hone hclaim d hd
  unfold IsOneEdgeUncolored at hone
  simp only [TreeUsedColors, Fin.castSucc_succ, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  rcases hd with ⟨j, hj, hdj⟩
  let jj : Fin (series.data.tree i.succ.castSucc).length :=
    ⟨j.val, by simp⟩
  have hjj : 1 ≤ jj.val := by simpa [jj] using hj
  have hne : (series.data.tree i.succ.castSucc).edge jj ≠ e0 := by
    intro he
    have hj0 := (series.data.tree i.succ.castSucc).edge_injective
      (he.trans (series.data.tree i.succ.castSucc).first_edge.symm)
    have hv0 := congrArg Fin.val hj0
    have hz0 : jj.val = 0 := by simpa using hv0
    omega
  obtain ⟨c, hfc⟩ := hone.2 _ hne
  have hp : c ∈ TreeUsedColors (series.data.coloring i.castSucc)
      (series.data.tree i.succ.castSucc) := by
    simp only [TreeUsedColors, Fin.castSucc_succ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨jj, hjj, hfc⟩
  have hc := hclaim hp
  have hr := HkuIncidentColorPreserved G k rounds e0 input series i
    _ c (edgeIncident hjj) hfc hc
  rcases hr.2 with ⟨d', hd', hc'⟩
  have hdj' : series.data.coloring i.succ
      ((series.data.tree i.succ.castSucc).edge jj) = some d := by
    simpa [jj] using hdj
  have heq : d' = d := Option.some.inj (hd'.symm.trans hdj')
  simpa [heq] using hc'

theorem HkuTreeColorsControlled {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) :
    TreeUsedColors (series.data.coloring q.castSucc)
          (series.data.tree q.succ.castSucc) ⊆
        TreeMissingColors (series.data.coloring q.castSucc)
            (series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors series.data q.castSucc ∧
    TreeUsedColors (series.data.coloring q.succ)
          (series.data.tree q.succ.castSucc) ⊆
        TreeMissingColors (series.data.coloring q.succ)
            (series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors series.data q.succ ∧
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.succ)
        (series.data.coloring q.succ) sigma →
      ∀ j : Fin (series.data.tree q.succ.castSucc).length,
        sigma ((series.data.tree q.succ.castSucc).edge j) =
          series.data.coloring q.succ
            ((series.data.tree q.succ.castSucc).edge j) := by
  classical
  have vertexTransfer {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    rcases hv with ⟨i, hi⟩
    rcases hab with ⟨hlen, hvertices, hedges⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, ?_⟩
    exact (hvertices i).trans hi
  have missingTransfer {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {phi : PartialEdgeColoring E k} :
      TreeMissingColors phi A ⊆ TreeMissingColors phi B := by
    intro c hc
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    rcases hc with ⟨v, hv, hvc⟩
    exact ⟨v, vertexTransfer hab hv, hvc⟩
  have usedSegment {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {phi : PartialEdgeColoring E k} :
      TreeUsedColors phi A ⊆ TreeUsedColors phi B := by
    intro c hc
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rcases hab with ⟨hlen, hvertices, hedges⟩
    rcases hc with ⟨j, hj, hcolor⟩
    refine ⟨Fin.castLE hlen j, ?_, ?_⟩
    · exact hj
    · rw [hedges j]
      exact hcolor
  have augmentationUsed := @helper_augmentationUsed_86 V E inferInstance inferInstance G k e0
      missingTransfer
  have closureMissing {A B : TreeSequence G e0}
      {phi : PartialEdgeColoring E k}
      (hseq : TashkinovAugmentationSequence phi A B) :
      TreeMissingColors phi A ⊆ TreeMissingColors phi B := by
    unfold TashkinovAugmentationSequence at hseq
    induction hseq using Relation.ReflTransGen.head_induction_on with
    | refl => intro c hc; exact hc
    | head hstep htail ih =>
      intro c hc
      exact ih (missingTransfer hstep.2.1 hc)
  have closureUsed {A B : TreeSequence G e0}
      {phi : PartialEdgeColoring E k}
      (hseq : TashkinovAugmentationSequence phi A B) :
      TreeUsedColors phi B ⊆ TreeMissingColors phi B ∪ TreeUsedColors phi A := by
    unfold TashkinovAugmentationSequence at hseq
    induction hseq using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro c hc
      exact Finset.mem_union.mpr (Or.inr hc)
    | head hstep htail ih =>
      intro c hc
      have middle := ih hc
      rcases Finset.mem_union.mp middle with hm | ho
      · exact Finset.mem_union.mpr (Or.inl hm)
      · have earlier := augmentationUsed (phi := phi) hstep ho
        rcases Finset.mem_union.mp earlier with hm | ho
        · exact Finset.mem_union.mpr (Or.inl (closureMissing htail hm))
        · exact Finset.mem_union.mpr (Or.inr ho)
  have adjoinUsed := @helper_adjoinUsed_863 V E G k e0
  have edgeIncident {T : TreeSequence G e0} {j : Fin T.length}
      (hj : 1 ≤ j.val) : TreeIncidentEdge T (T.edge j) := by
    obtain ⟨v, hv⟩ := T.attaches j
    refine ⟨T.vertex j.succ, ?_, ?_⟩
    · simp [TreeSequenceVertexSet]
    · unfold Incident
      rw [hv]
      exact Sym2.mem_mk_left _ _
  have storedOrMissing {i : Fin (rounds + 1)} {c : Fin k}
      (hi : i.val ≠ 0) (hs : c ∈ series.data.stored i) :
      c ∈ TreeMissingColors (series.data.coloring i)
          (series.data.tree i.castSucc) ∪ TashkinovStoredColors series.data i := by
    by_cases hm : c ∈ TreeMissingColors (series.data.coloring i)
          (series.data.tree i.castSucc)
    · exact Finset.mem_union.mpr (Or.inl hm)
    · exact Finset.mem_union.mpr (Or.inr (by
      unfold TashkinovStoredColors
      simp only [hi, ↓reduceIte, Fin.val_fin_le, Finset.mem_sdiff, Finset.mem_biUnion,
          Finset.mem_univ, true_and,
    hm, not_false_eq_true, and_true]
      exact ⟨⟨i, by omega⟩, by simpa using hs⟩))
  have colorTransport := @helper_colorTransport_913 V E inferInstance inferInstance inferInstance G
      k rounds e0 input series edgeIncident
  have augmentationColored {A B : TreeSequence G e0}
      {phi : PartialEdgeColoring E k}
      (hab : TashkinovAugmentation phi A B)
      (hold : ∀ j : Fin A.length, 1 ≤ j.val → ∃ c, phi (A.edge j) = some c) :
      ∀ j : Fin B.length, 1 ≤ j.val → ∃ c, phi (B.edge j) = some c := by
    rcases hab with ⟨hlen, hseg, c, hcolor, hmissing⟩
    intro j hj
    by_cases hlt : j.val < A.length
    · let jold : Fin A.length := ⟨j.val, hlt⟩
      obtain ⟨d, hd⟩ := hold jold (by simpa [jold] using hj)
      refine ⟨d, ?_⟩
      rw [show j = Fin.castLE hseg.1 jold by
        apply Fin.ext; simp [jold]]
      rw [hseg.2.2 jold]
      exact hd
    · have heq : j = Fin.cast hlen.symm (Fin.last A.length) := by
        apply Fin.ext
        have hjlt := j.isLt
        simp at *
        omega
      exact ⟨c, by simpa [heq] using hcolor⟩
  have sequenceColored {A B : TreeSequence G e0}
      {phi : PartialEdgeColoring E k}
      (hseq : TashkinovAugmentationSequence phi A B)
      (hold : ∀ j : Fin A.length, 1 ≤ j.val → ∃ c, phi (A.edge j) = some c) :
      ∀ j : Fin B.length, 1 ≤ j.val → ∃ c, phi (B.edge j) = some c := by
    unfold TashkinovAugmentationSequence at hseq
    induction hseq using Relation.ReflTransGen.head_induction_on with
    | refl => exact hold
    | head hstep htail ih => exact ih (augmentationColored hstep hold)
  have adjoinColored {A B : TreeSequence G e0} {f : E} {c : Fin k}
      (hadj : TreeSequenceAdjoinEdge A f B) {phi : PartialEdgeColoring E k}
      (hcolor : phi f = some c)
      (hold : ∀ j : Fin A.length, 1 ≤ j.val → ∃ d, phi (A.edge j) = some d) :
      ∀ j : Fin B.length, 1 ≤ j.val → ∃ d, phi (B.edge j) = some d := by
    rcases hadj with ⟨hlen, hseg, hlast⟩
    intro j hj
    by_cases hlt : j.val < A.length
    · let jold : Fin A.length := ⟨j.val, hlt⟩
      obtain ⟨d, hd⟩ := hold jold (by simpa [jold] using hj)
      refine ⟨d, ?_⟩
      rw [show j = Fin.castLE hseg.1 jold by
        apply Fin.ext; simp [jold], hseg.2.2 jold]
      exact hd
    · have heq : j = Fin.cast hlen.symm (Fin.last A.length) := by
        apply Fin.ext
        have hjlt := j.isLt
        simp at *
        omega
      rw [← hlast] at hcolor
      exact ⟨c, by simpa [heq] using hcolor⟩
  have firstClaim := @helper_firstClaim_290 V E inferInstance inferInstance inferInstance G k rounds
      e0 input series closureUsed adjoinUsed storedOrMissing colorTransport
  have stableMissingTransfer {A : TreeSequence G e0}
      {phi pi : PartialEdgeColoring E k} {C : Finset (Fin k)}
      (hst : StableColoring A C phi pi) :
      TreeMissingColors phi A ⊆ TreeMissingColors pi A := by
    intro c hc
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    rcases hc with ⟨v, hv, hvc⟩
    refine ⟨v, hv, ?_⟩
    exact (hst.2 v hv) ▸ hvc
  have firstColored := @helper_firstColored_439 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series edgeIncident sequenceColored adjoinColored firstClaim
      stableMissingTransfer
  exact ⟨firstClaim q.castSucc, by
    have hp := (series.coloringProperties q.castSucc).2
    exact fun d hd => colorTransport hp (firstClaim q.castSucc) hd, by
    intro sigma hproper hone hstable j
    by_cases hj : j.val = 0
    · exact @helper_branch_776 V E inferInstance inferInstance inferInstance G k rounds e0 input
        series q sigma hone j hj
    · exact @helper_branch_820 V E inferInstance inferInstance inferInstance G k rounds e0 input
        series q edgeIncident colorTransport firstClaim firstColored sigma hstable j hj
  ⟩

end GoldbergSeymour

end
