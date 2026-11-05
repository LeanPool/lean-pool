/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ParallelExtensionColor
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificate
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TreeExit
public import LeanPool.GoldbergSeymour.TreeExitPath
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Tashkinov Stored Colors Cardinality

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_priorVertices_70.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (series : TashkinovSeries G k rounds e0 input),
    (∀ {A B : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          ∀ {v : V}, v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B) →
    (∀ {A B : TreeSequence G e0} {phi : PartialEdgeColoring E k},
        TashkinovAugmentationSequence phi A B →
          ∀ {v : V}, v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B) →
    ∀ (q : Fin rounds),
    ∀ v ∈ TreeSequenceVertexSet (series.data.tree q.castSucc.castSucc),
    v ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc) := by
  classical
  intro V E _ _ _ G k rounds e0 input series vertexTransfer closureTransfer q v hv
  have cert := series.certified q.castSucc
  generalize hj : q.castSucc = j at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    have hval := congrArg Fin.val hj
    have hq : q.val = 0 := by simpa using hval
    have hidx : q.castSucc.castSucc = (0 : Fin (rounds + 2)) := by
      apply Fin.ext
      simp [hq]
    have hnext : q.succ.castSucc = (1 : Fin (rounds + 2)) := by
      apply Fin.ext
      simp [hq]
    have hv' : v ∈ TreeSequenceVertexSet (series.data.tree 0) := by
      rw [hidx] at hv
      exact hv
    have h := closureTransfer initialClosure.1 hv'
    simpa [hnext] using h
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hvals := congrArg Fin.val hj
    have hi : ci.succ = q.castSucc := by apply Fin.ext; simp at hvals ⊢; omega
    have hs := vertexTransfer (by simpa [hi] using orderedExtension) hv
    have heq : q.castSucc.succ = q.succ.castSucc := by apply Fin.ext; rfl
    rw [heq] at hs
    exact hs
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have hvals := congrArg Fin.val hj
    have hi : ci.succ = q.castSucc := by apply Fin.ext; simp at hvals ⊢; omega
    have hs := vertexTransfer (by simpa [hi] using orderedExtension) hv
    have heq : q.castSucc.succ = q.succ.castSucc := by apply Fin.ext; rfl
    rw [heq] at hs
    exact hs
  | RE ci previousProper previousUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hvals := congrArg Fin.val hj
    have hi : ci.succ = q.castSucc := by apply Fin.ext; simp at hvals ⊢; omega
    have hs := vertexTransfer (by simpa [hi] using orderedExtension) hv
    have heq : q.castSucc.succ = q.succ.castSucc := by apply Fin.ext; rfl
    rw [heq] at hs
    exact hs

private theorem helper_branch_139.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input), (
    ∀ (q : Fin rounds),
    ∀ v ∈ TreeSequenceVertexSet (series.data.tree q.castSucc.castSucc), v ∈ TreeSequenceVertexSet
        (series.data.tree q.succ.castSucc)) → (
    ∀ {r : Fin (rounds + (1 : ℕ))} {c : Fin k}, (↑r : ℕ) ≠ (0 : ℕ) → (c ∈ TashkinovStoredColors
        series.data r ↔ (
    ∃ (h : Fin (rounds + (1 : ℕ))), (↑h : ℕ) ≤ (↑r : ℕ) ∧ c ∈ series.data.stored h) ∧ c ∉
        TreeMissingColors (series.data.coloring r) (series.data.tree r.castSucc))) →
        series.data.stored (0 : Fin (rounds + (1 : ℕ))) = ∅ →
    ∀ (q : Fin rounds), (TashkinovStoredColors series.data q.castSucc).card ≤ (↑q.castSucc : ℕ) →
    ∀ (ci : Fin rounds), IsProperEdgeColoring G (series.data.coloring ci.castSucc) →
        IsOneEdgeUncolored (series.data.coloring ci.castSucc) e0 → ColoredVertexSetClosed G
        (series.data.coloring ci.castSucc) (TreeSequenceVertexSet (series.data.tree
        ci.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G (series.data.coloring ci.castSucc)
        (TreeSequenceVertexSet (series.data.tree ci.succ.castSucc)) → ¬Nonempty
        (RevisitingExtensionCertificate series.data ci.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree ci.succ.castSucc)
        (TashkinovStoredColors series.data ci.castSucc) (series.data.coloring ci.castSucc)), (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors series.data ci.castSucc)) choice.selected pi → Disjoint
        (MissingColors G pi choice.otherEndpoint) (TreeMissingColors pi (series.data.tree
        ci.succ.castSucc))) → series.data.coloring ci.succ = choice.selected → series.data.stored
        ci.succ = { choice.color } → series.data.connectingEdges ci.succ = { choice.edge } →
        series.data.kind ci.succ = some TashkinovExtensionKind.SE → series.data.chosenVertex
        ci.succ = some choice.vertex → series.data.outsideVertex ci.succ = some
        choice.otherEndpoint → series.data.delta ci.succ = some choice.color → series.data.gamma
        ci.succ = none →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (series.data.tree ci.succ.castSucc)
        choice.edge adjoined → TashkinovClosure (series.data.coloring ci.succ) adjoined
        (series.data.tree ci.succ.succ) → TreeSequenceInitialSegment (series.data.tree
        ci.succ.castSucc) (series.data.tree ci.succ.succ) → (series.data.tree
        ci.succ.castSucc).length < (series.data.tree ci.succ.succ).length → q.succ = ci.succ →
        (TashkinovStoredColors series.data ci.succ).card ≤ (↑ci.succ : ℕ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series oldVertices storedMem storedZero q ih ci
      previousProper previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting
      choice seriesAlternative currentColoring currentStored currentEdges currentKind
      currentVertex currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension hj
  have hvals := congrArg Fin.val hj
  have hci : ci = q := by
    apply Fin.ext
    have hqci : q.val + 1 = ci.val + 1 := by simpa using hvals
    omega
  subst ci
  have hsub : TashkinovStoredColors series.data q.succ ⊆
      TashkinovStoredColors series.data q.castSucc ∪ {choice.color} := by
    intro c hc
    have hmem := (storedMem (r := q.succ) (by simp)).mp hc
    rcases hmem with ⟨⟨h, hh, hm⟩, hnot⟩
    by_cases he : h.val = q.succ.val
    · have heq : h = q.succ := by apply Fin.ext; exact he
      rw [heq, currentStored] at hm
      exact Finset.mem_union.mpr (Or.inr (by simpa using hm))
    · by_cases hz : q.val = 0
      · have hqone : q.succ.val = 1 := by simp [hz]
        have hh0 : h = 0 := by
          apply Fin.ext
          have hle0 : h.val ≤ 1 := by simpa [hz] using hh
          have hne1 : h.val ≠ 1 := by simpa [hz] using he
          have hzero : h.val = 0 := by omega
          exact hzero
        subst h
        rw [storedZero] at hm
        simp at hm
      · have hle : h.val ≤ q.val := by
          change h.val ≤ q.val + 1 at hh; change h.val ≠ q.val + 1 at he
          omega
        have oldNot : c ∉ TreeMissingColors (series.data.coloring q.castSucc)
            (series.data.tree q.castSucc.castSucc) := by
          intro hold
          apply hnot
          simp only [TreeMissingColors, Finset.mem_biUnion] at hold ⊢
          rcases hold with ⟨v, hv, hcv⟩
          exact ⟨v, oldVertices q v hv, by simpa [currentColoring] using
            ((choice.selectedStable.2 v (oldVertices q v hv)).symm ▸ hcv)⟩
        exact Finset.mem_union.mpr (Or.inl ((storedMem (r := q.castSucc) hz).mpr
          ⟨⟨h, hle, hm⟩, oldNot⟩))
  calc
    _ ≤ (TashkinovStoredColors series.data q.castSucc ∪ {choice.color}).card :=
        Finset.card_le_card hsub
    _ ≤ (TashkinovStoredColors series.data q.castSucc).card + 1 := by
      simpa using Finset.card_union_le (TashkinovStoredColors series.data q.castSucc) {choice.color}
    _ ≤ q.val + 1 := by
      have hiq := ih
      simp at hiq
      omega

private theorem helper_branch_191.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input), (
    ∀ (q : Fin rounds), TreeMissingColors (series.data.coloring q.castSucc) (series.data.tree
        q.castSucc.castSucc) ⊆ TreeMissingColors (series.data.coloring q.castSucc)
        (series.data.tree q.succ.castSucc)) → (
    ∀ {r : Fin (rounds + (1 : ℕ))} {c : Fin k}, (↑r : ℕ) ≠ (0 : ℕ) → (c ∈ TashkinovStoredColors
        series.data r ↔ (
    ∃ (h : Fin (rounds + (1 : ℕ))), (↑h : ℕ) ≤ (↑r : ℕ) ∧ c ∈ series.data.stored h) ∧ c ∉
        TreeMissingColors (series.data.coloring r) (series.data.tree r.castSucc))) →
        series.data.stored (0 : Fin (rounds + (1 : ℕ))) = ∅ →
    ∀ (q : Fin rounds), (TashkinovStoredColors series.data q.castSucc).card ≤ (↑q.castSucc : ℕ) →
    ∀ (ci : Fin rounds), IsProperEdgeColoring G (series.data.coloring ci.castSucc) →
        IsOneEdgeUncolored (series.data.coloring ci.castSucc) e0 → ColoredVertexSetClosed G
        (series.data.coloring ci.castSucc) (TreeSequenceVertexSet (series.data.tree
        ci.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G (series.data.coloring ci.castSucc)
        (TreeSequenceVertexSet (series.data.tree ci.succ.castSucc)) →
    ∀ (available : RevisitingExtensionCertificate series.data ci.castSucc), series.data.coloring
        ci.succ = series.data.coloring ci.castSucc → series.data.stored ci.succ =
        { available.delta, available.gamma } → series.data.connectingEdges ci.succ =
        { available.edge } → series.data.kind ci.succ = some TashkinovExtensionKind.RE →
        series.data.chosenVertex ci.succ = some available.insideEndpoint →
        series.data.outsideVertex ci.succ = some available.outsideEndpoint → series.data.delta
        ci.succ = some available.delta → series.data.gamma ci.succ = some available.gamma →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (series.data.tree ci.succ.castSucc)
        available.edge adjoined → TashkinovClosure (series.data.coloring ci.succ) adjoined
        (series.data.tree ci.succ.succ) → TreeSequenceInitialSegment (series.data.tree
        ci.succ.castSucc) (series.data.tree ci.succ.succ) → (series.data.tree
        ci.succ.castSucc).length < (series.data.tree ci.succ.succ).length → q.succ = ci.succ →
        (TashkinovStoredColors series.data ci.succ).card ≤ (↑ci.succ : ℕ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series missingTransfer storedMem storedZero q ih ci
      previousProper previousUncolored previousClosed previousNotStronglyClosed available
      currentColoring currentStored currentEdges currentKind currentVertex currentOutside
      currentDelta currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension hj
  have hvals := congrArg Fin.val hj
  have hci : ci = q := by
    apply Fin.ext
    have hqci : q.val + 1 = ci.val + 1 := by simpa using hvals
    omega
  subst ci
  have qpos : q.val ≠ 0 := by
    have hp := available.earlierPositive
    have hle : available.earlier.val ≤ q.val := by simpa using available.earlierAtMost
    omega
  have hsub : TashkinovStoredColors series.data q.succ ⊆
      TashkinovStoredColors series.data q.castSucc := by
    intro c hc
    have hmem := (storedMem (r := q.succ) (by simp)).mp hc
    rcases hmem with ⟨⟨h, hh, hm⟩, hnot⟩
    by_cases he : h.val = q.succ.val
    · have heq : h = q.succ := by apply Fin.ext; exact he
      have oldNot : c ∉ TreeMissingColors (series.data.coloring q.castSucc)
          (series.data.tree q.castSucc.castSucc) := by
        intro hold
        apply hnot
        rw [currentColoring]
        exact missingTransfer q hold
      have earlierBound : available.earlier.val ≤ q.val := by
        simpa using available.earlierAtMost
      have earlierMem : c ∈ series.data.stored available.earlier := by
        have hmPair : c = available.delta ∨ c = available.gamma := by
          rw [heq, currentStored] at hm
          simpa using hm
        have ec := series.certified available.earlier
        generalize hj : available.earlier = j at ec
        cases ec with
        | initial triple seedLength initialColoring initialStored initialEdges
            initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
          have hz : available.earlier.val = 0 := by simp [hj]
          exact (Nat.ne_of_gt available.earlierPositive hz).elim
        | SE ci previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting oldChoice seriesAlternative
            oldColoring oldStored oldEdges oldKind oldVertex oldOutside oldDelta oldGamma
            adjoined adjoinedExactly closedExtension orderedExtension strictExtension =>
          have hk : series.data.kind available.earlier =
              some TashkinovExtensionKind.PE := available.earlierPE
          rw [hj, oldKind] at hk
          simp at hk
        | PE ci previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting oldChoice seriesAlternativeFails
            oldGammaPrev gammaRule oldStable oldStableProper oldStableOneUncolored
            oldStableRelation exitWitness oldColoring oldProper oldOneUncolored oldStored
            oldEdges oldKind oldVertex oldOutside oldDelta oldGamma closedExtension
            orderedExtension strictExtension =>
          have hd : oldChoice.color = available.delta := by
            apply Option.some.inj
            calc
              some oldChoice.color = series.data.delta ci.succ := oldDelta.symm
              _ = series.data.delta available.earlier := by rw [hj]
              _ = some available.delta := available.earlierDelta
          have hg : oldGammaPrev = available.gamma := by
            apply Option.some.inj
            calc
              some oldGammaPrev = series.data.gamma ci.succ := oldGamma.symm
              _ = series.data.gamma available.earlier := by rw [hj]
              _ = some available.gamma := available.earlierGamma
          simpa [hj, oldStored, hd, hg] using hmPair
        | RE ci previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed oldAvailable oldColoring oldStored oldEdges oldKind
            oldVertex oldOutside oldDelta oldGamma adjoined adjoinedExactly closedExtension
            orderedExtension strictExtension =>
          have hk : series.data.kind available.earlier =
              some TashkinovExtensionKind.PE := available.earlierPE
          rw [hj, oldKind] at hk
          simp at hk
      exact (storedMem (r := q.castSucc) qpos).mpr
        ⟨⟨available.earlier, earlierBound, earlierMem⟩, oldNot⟩
    · by_cases hz : q.val = 0
      · have hqone : q.succ.val = 1 := by simp [hz]
        have hh0 : h = 0 := by
          apply Fin.ext
          have hle0 : h.val ≤ 1 := by simpa [hz] using hh
          have hne1 : h.val ≠ 1 := by simpa [hz] using he
          exact Nat.lt_one_iff.mp (Nat.lt_of_le_of_ne hle0 hne1)
        subst h
        rw [storedZero] at hm
        simp at hm
      · have hle : h.val ≤ q.val := by
          change h.val ≤ q.val + 1 at hh; change h.val ≠ q.val + 1 at he
          omega
        have oldNot : c ∉ TreeMissingColors (series.data.coloring q.castSucc)
            (series.data.tree q.castSucc.castSucc) := by
          intro hold
          apply hnot
          rw [currentColoring]
          exact missingTransfer q hold
        exact (storedMem (r := q.castSucc) hz).mpr
          ⟨⟨h, hle, hm⟩, oldNot⟩
  have ih' : (TashkinovStoredColors series.data q.castSucc).card ≤ q.val := by
    simpa using ih
  have hcard := Finset.card_le_card hsub
  change (TashkinovStoredColors series.data q.succ).card ≤ q.val + 1
  exact hcard.trans (by omega)

private theorem helper_branch_295.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input), (
    ∀ (q : Fin rounds),
    ∀ v ∈ TreeSequenceVertexSet (series.data.tree q.castSucc.castSucc), v ∈ TreeSequenceVertexSet
        (series.data.tree q.succ.castSucc)) → (
    ∀ {phi : PartialEdgeColoring E k} {a b : Fin k} {z : V ⊕ E} {v : V} {c : Fin k}, c ∈
        MissingColors G phi v → c ≠ a → c ≠ b → c ∈ MissingColors G (TwoColorComponentSwap G phi a
        b z) v) → (
    ∀ {r : Fin (rounds + (1 : ℕ))} {c : Fin k}, (↑r : ℕ) ≠ (0 : ℕ) → (c ∈ TashkinovStoredColors
        series.data r ↔ (
    ∃ (h : Fin (rounds + (1 : ℕ))), (↑h : ℕ) ≤ (↑r : ℕ) ∧ c ∈ series.data.stored h) ∧ c ∉
        TreeMissingColors (series.data.coloring r) (series.data.tree r.castSucc))) →
        series.data.stored (0 : Fin (rounds + (1 : ℕ))) = ∅ →
    ∀ (q : Fin rounds), (TashkinovStoredColors series.data q.castSucc).card ≤ (↑q.castSucc : ℕ) →
    ∀ (ci : Fin rounds), IsProperEdgeColoring G (series.data.coloring ci.castSucc) →
        IsOneEdgeUncolored (series.data.coloring ci.castSucc) e0 → ColoredVertexSetClosed G
        (series.data.coloring ci.castSucc) (TreeSequenceVertexSet (series.data.tree
        ci.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G (series.data.coloring ci.castSucc)
        (TreeSequenceVertexSet (series.data.tree ci.succ.castSucc)) → ¬Nonempty
        (RevisitingExtensionCertificate series.data ci.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree ci.succ.castSucc)
        (TashkinovStoredColors series.data ci.castSucc) (series.data.coloring ci.castSucc)), (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors series.data ci.castSucc)) choice.selected rho ∧ ¬Disjoint
        (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho (series.data.tree
        ci.succ.castSucc))) →
    ∀ (gamma : Fin k), ParallelExtensionColor series.data ci.castSucc choice.selected
        choice.vertex gamma →
    ∀ (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G secondStable →
        StableColoring (series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors series.data ci.castSucc)) choice.selected secondStable → TreeExit
        (series.data.tree ci.succ.castSucc) secondStable gamma choice.color choice.vertex →
        series.data.coloring ci.succ = TwoColorComponentSwap G secondStable gamma choice.color
        (Sum.inl choice.vertex) → IsProperEdgeColoring G (series.data.coloring ci.succ) →
        IsOneEdgeUncolored (series.data.coloring ci.succ) e0 → series.data.stored ci.succ =
        {choice.color, gamma} → series.data.connectingEdges ci.succ = { choice.edge } →
        series.data.kind ci.succ = some TashkinovExtensionKind.PE → series.data.chosenVertex
        ci.succ = some choice.vertex → series.data.outsideVertex ci.succ = some
        choice.otherEndpoint → series.data.delta ci.succ = some choice.color → series.data.gamma
        ci.succ = some gamma → TashkinovClosure (series.data.coloring ci.succ) (series.data.tree
        ci.succ.castSucc) (series.data.tree ci.succ.succ) → TreeSequenceInitialSegment
        (series.data.tree ci.succ.castSucc) (series.data.tree ci.succ.succ) → (series.data.tree
        ci.succ.castSucc).length < (series.data.tree ci.succ.succ).length → q.succ = ci.succ →
        (TashkinovStoredColors series.data ci.succ).card ≤ (↑ci.succ : ℕ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series oldVertices swapMissing storedMem storedZero q ih ci
      previousProper previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting
      choice seriesAlternativeFails gamma gammaRule secondStable secondStableProper
      secondStableRelation exitWitness currentColoring currentProper currentOneUncolored
      currentStored currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension hj
  have hvals := congrArg Fin.val hj
  have hci : ci = q := by
    apply Fin.ext
    have hqci : q.val + 1 = ci.val + 1 := by simpa using hvals
    omega
  subst ci
  have hsub : TashkinovStoredColors series.data q.succ ⊆
      TashkinovStoredColors series.data q.castSucc ∪ {choice.color, gamma} := by
    intro c hc
    have hmem := (storedMem (r := q.succ) (by simp)).mp hc
    rcases hmem with ⟨⟨h, hh, hm⟩, hnot⟩
    by_cases he : h.val = q.succ.val
    · have heq : h = q.succ := by apply Fin.ext; exact he
      rw [heq, currentStored] at hm
      exact Finset.mem_union.mpr (Or.inr (by simpa using hm))
    · by_cases hz : q.val = 0
      · have hqone : q.succ.val = 1 := by simp [hz]
        have hh0 : h = 0 := by
          apply Fin.ext
          have hle0 : h.val ≤ 1 := by simpa [hz] using hh
          have hne1 : h.val ≠ 1 := by simpa [hz] using he
          exact Nat.lt_one_iff.mp (Nat.lt_of_le_of_ne hle0 hne1)
        subst h
        rw [storedZero] at hm
        simp at hm
      · have hle : h.val ≤ q.val := by
          change h.val ≤ q.val + 1 at hh; change h.val ≠ q.val + 1 at he
          omega
        by_cases hc : c = choice.color
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hc)))
        by_cases hg : c = gamma
        · exact Finset.mem_union.mpr (Or.inr (by simp [hg]))
        have oldNot : c ∉ TreeMissingColors (series.data.coloring q.castSucc)
            (series.data.tree q.castSucc.castSucc) :=
          (by
            intro hold
            apply hnot
            rw [currentColoring]
            simp only [TreeMissingColors, Finset.mem_biUnion] at hold ⊢
            rcases hold with ⟨v, hv, hcv⟩
            have hv' := oldVertices q v hv
            have hcv' : c ∈ MissingColors G secondStable v := by
              rw [secondStableRelation.2 v hv', choice.selectedStable.2 v hv']
              exact hcv
            exact ⟨v, oldVertices q v hv,
              swapMissing (phi := secondStable)
                (a := gamma) (b := choice.color)
                (z := Sum.inl choice.vertex) (v := v) (c := c)
                hcv' hg hc⟩)
        exact Finset.mem_union.mpr (Or.inl ((storedMem (r := q.castSucc) hz).mpr
          ⟨⟨h, hle, hm⟩, oldNot⟩))
  have hdelta : choice.color ∈ TreeMissingColors
      (TwoColorComponentSwap G secondStable gamma choice.color
        (Sum.inl choice.vertex)) (series.data.tree q.succ.castSucc) := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    refine ⟨choice.vertex, choice.vertexDefective.1, ?_⟩
    have hgamma : gamma ∈ MissingColors G secondStable choice.vertex := by
      exact (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸ gammaRule.1
    have hedge : secondStable choice.edge = some choice.color := by
      exact (secondStableRelation.1 choice.edge
        ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
        ⟨choice.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _),
            choice.edgeColor⟩).trans choice.edgeColor
    have hneq : gamma ≠ choice.color := by
      intro heq
      apply (Finset.mem_sdiff.mp hgamma).2
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨choice.edge, choice.edgeIncident, by simpa [heq] using hedge⟩
    have hm : choice.color ∈ MissingColors G
        (TwoColorComponentSwap G secondStable gamma choice.color
          (Sum.inl choice.vertex)) choice.vertex := by
      unfold MissingColors
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hp
      rw [PresentColors] at hp
      rcases Finset.mem_filter.mp hp with ⟨_, e, heinc, hecol⟩
      unfold TwoColorComponentSwap at hecol
      by_cases hk : Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl
          choice.vertex)
      · simp only [ite_eq_left hk] at hecol
        by_cases hg : secondStable e = some gamma
        · simp only [ite_eq_left hg] at hecol
          apply (Finset.mem_sdiff.mp hgamma).2
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨e, heinc, hg⟩
        · simp only [ite_eq_right hg] at hecol
          by_cases hc : secondStable e = some choice.color
          · simp only [ite_eq_left hc] at hecol
            exact hneq (Option.some.inj hecol)
          · simp only [ite_eq_right hc] at hecol
            exact hc hecol
      · simp only [ite_eq_right hk] at hecol
        have hbad : e = choice.edge :=
          (by
            by_contra hne
            exact (secondStableProper hne ⟨choice.vertex, heinc, choice.edgeIncident⟩ hecol
                hedge).elim)
        have edgeMember : Sum.inr choice.edge ∈
            TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex) := by
          change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
            (Sum.inr choice.edge) =
            (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
              (Sum.inl choice.vertex)
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (by
            simp [TwoColorIncidenceGraph, choice.edgeIncident, hedge])).symm
        exact hk (by simpa [hbad] using edgeMember)
    exact hm
  have hsub' : TashkinovStoredColors series.data q.succ ⊆
      TashkinovStoredColors series.data q.castSucc ∪ {gamma} := by
    intro c hc
    have h := hsub hc
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union.mpr (Or.inl h)
    · rcases Finset.mem_insert.mp h with rfl | h
      · have hmc := (storedMem (r := q.succ) (by simp)).mp hc
        rw [currentColoring] at hmc
        exact (hmc.2 hdelta).elim
      · exact Finset.mem_union.mpr (Or.inr h)
  calc
    _ ≤ (TashkinovStoredColors series.data q.castSucc ∪ {gamma}).card := Finset.card_le_card hsub'
    _ ≤ (TashkinovStoredColors series.data q.castSucc).card + 1 := by
      simpa using Finset.card_union_le (TashkinovStoredColors series.data q.castSucc) {gamma}
    _ ≤ q.val + 1 := by
      simpa using Nat.add_le_add_right ih 1

private theorem helper_branch_189.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input), (
    ∀ (q : Fin rounds),
    ∀ v ∈ TreeSequenceVertexSet (series.data.tree q.castSucc.castSucc), v ∈ TreeSequenceVertexSet
        (series.data.tree q.succ.castSucc)) → (
    ∀ (q : Fin rounds), TreeMissingColors (series.data.coloring q.castSucc) (series.data.tree
        q.castSucc.castSucc) ⊆ TreeMissingColors (series.data.coloring q.castSucc)
        (series.data.tree q.succ.castSucc)) → (
    ∀ {phi : PartialEdgeColoring E k} {a b : Fin k} {z : V ⊕ E} {v : V} {c : Fin k}, c ∈
        MissingColors G phi v → c ≠ a → c ≠ b → c ∈ MissingColors G (TwoColorComponentSwap G phi a
        b z) v) → (
    ∀ {r : Fin (rounds + (1 : ℕ))} {c : Fin k}, (↑r : ℕ) ≠ (0 : ℕ) → (c ∈ TashkinovStoredColors
        series.data r ↔ (
    ∃ (h : Fin (rounds + (1 : ℕ))), (↑h : ℕ) ≤ (↑r : ℕ) ∧ c ∈ series.data.stored h) ∧ c ∉
        TreeMissingColors (series.data.coloring r) (series.data.tree r.castSucc))) →
        series.data.stored (0 : Fin (rounds + (1 : ℕ))) = ∅ →
    ∀ (q : Fin rounds), (TashkinovStoredColors series.data q.castSucc).card ≤ (↑q.castSucc : ℕ) →
        (TashkinovStoredColors series.data q.succ).card ≤ (↑q.succ : ℕ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series oldVertices missingTransfer swapMissing storedMem
      storedZero q ih
  have cert := series.certified q.succ
  generalize hj : q.succ = j at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    exact (Fin.succ_ne_zero q) hj |>.elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
          exact @helper_branch_139 V E inferInstance inferInstance inferInstance G k rounds e0
              input series oldVertices storedMem storedZero q ih ci previousProper
              previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
              seriesAlternative currentColoring currentStored currentEdges currentKind
              currentVertex currentOutside currentDelta currentGamma adjoined adjoinedExactly
              closedExtension orderedExtension strictExtension hj
  | RE ci previousProper previousUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_191 V E inferInstance inferInstance inferInstance G k rounds e0
              input series missingTransfer storedMem storedZero q ih ci previousProper
              previousUncolored previousClosed previousNotStronglyClosed available
              currentColoring currentStored currentEdges currentKind currentVertex currentOutside
              currentDelta currentGamma adjoined adjoinedExactly closedExtension orderedExtension
              strictExtension hj
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_295 V E inferInstance inferInstance inferInstance G k rounds e0
              input series oldVertices swapMissing storedMem storedZero q ih ci previousProper
              previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
              seriesAlternativeFails gamma gammaRule secondStable secondStableProper
              secondStableRelation exitWitness currentColoring currentProper currentOneUncolored
              currentStored currentEdges currentKind currentVertex currentOutside currentDelta
              currentGamma closedExtension orderedExtension strictExtension hj
theorem TashkinovStoredColorsCardinality {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (i : Fin (rounds + 1)) :
    (TashkinovStoredColors series.data i).card ≤ i.val := by
  classical
  have vertexTransfer {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    rcases hv with ⟨j, hj⟩
    rcases hab with ⟨hlen, hvertices, hedges⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) j, (hvertices j).trans hj⟩
  have augmentationTransfer {A B : TreeSequence G e0}
      {phi : PartialEdgeColoring E k}
      (hab : TashkinovAugmentation phi A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    exact vertexTransfer hab.2.1 hv
  have closureTransfer {A B : TreeSequence G e0}
      {phi : PartialEdgeColoring E k}
      (hab : TashkinovAugmentationSequence phi A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    unfold TashkinovAugmentationSequence at hab
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => exact hv
    | head hstep htail ih => exact ih (augmentationTransfer hstep hv)
  have priorVertices := @helper_priorVertices_70 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series vertexTransfer closureTransfer
  have oldVertices : ∀ q : Fin rounds, ∀ v : V,
      v ∈ TreeSequenceVertexSet (series.data.tree q.castSucc.castSucc) →
      v ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc) := by
    intro q v hv
    exact priorVertices q v hv
  have missingTransfer :
    ∀ q : Fin rounds, TreeMissingColors (series.data.coloring q.castSucc) (series.data.tree
        q.castSucc.castSucc) ⊆ TreeMissingColors (series.data.coloring q.castSucc)
        (series.data.tree q.succ.castSucc) := by
    intro q c hc
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    rcases hc with ⟨v, hv, hvc⟩
    exact ⟨v, oldVertices q v hv, hvc⟩
  have swapMissing {phi : PartialEdgeColoring E k} {a b : Fin k} {z : Sum V E}
      {v : V} {c : Fin k} (hc : c ∈ MissingColors G phi v)
      (hca : c ≠ a) (hcb : c ≠ b) :
      c ∈ MissingColors G (TwoColorComponentSwap G phi a b z) v := by
    unfold MissingColors at hc ⊢
    rw [Finset.mem_sdiff] at hc ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hp
    rw [PresentColors] at hp
    rcases Finset.mem_filter.mp hp with ⟨_, e, he, hec⟩
    apply hc.2
    rw [PresentColors]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, ?_⟩
    unfold TwoColorComponentSwap at hec
    by_cases hh : Sum.inr e ∈ TwoColorComponent G phi a b z
    · simp only [ite_eq_left hh] at hec
      by_cases ha : phi e = some a
      · simp only [ite_eq_left ha] at hec
        exact (hcb (Option.some.inj hec).symm).elim
      · by_cases hb : phi e = some b
        · simp only [ite_eq_right ha, ite_eq_left hb] at hec
          exact (hca (Option.some.inj hec).symm).elim
        · simp only [ite_eq_right ha, ite_eq_right hb] at hec
          exact hec
    · simpa [hh] using hec
  have storedMem {r : Fin (rounds + 1)} {c : Fin k} (hr : r.val ≠ 0) :
      c ∈ TashkinovStoredColors series.data r ↔
        (∃ h : Fin (rounds + 1), h.val ≤ r.val ∧ c ∈ series.data.stored h) ∧
          c ∉ TreeMissingColors (series.data.coloring r) (series.data.tree r.castSucc) := by
    unfold TashkinovStoredColors
    simp only [ite_eq_right hr, Finset.mem_sdiff, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hu, hn⟩
      rcases hu with ⟨h, hh⟩
      by_cases hle : h.val ≤ r.val
      · exact ⟨⟨h, hle, by simpa [hle] using hh⟩, hn⟩
      · simp [hle] at hh
    · rintro ⟨⟨h, hle, hm⟩, hn⟩
      exact ⟨⟨h, by simpa [hle] using hm⟩, hn⟩
  have storedZero : series.data.stored 0 = ∅ := by
    have z := series.certified (0 : Fin (rounds + 1))
    cases z with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      exact initialStored
  induction i using Fin.induction with
  | zero => simp [TashkinovStoredColors]
  | succ q ih =>
      exact @helper_branch_189 V E inferInstance inferInstance inferInstance G k rounds e0 input
          series oldVertices missingTransfer swapMissing storedMem storedZero q ih
end GoldbergSeymour

end
