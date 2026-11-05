/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingTerminalClosureEq
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.MaximumStableClosureExists
public import LeanPool.GoldbergSeymour.TechnicalTheoremLarge
public import LeanPool.GoldbergSeymour.TerminalClosureMaximum
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdgeUnique
public import LeanPool.GoldbergSeymour.StableColoringEquivalence

/-!
# Normalize Positive Terminal Maximum

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem NormalizePositiveTerminalMaximum_terminalSeedAndClosure_63.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating),
    ∃ (seed : TreeSequence G e0), IsProperEdgeColoring G (ett.series.data.coloring (Fin.last
        ett.rounds)) ∧ IsOneEdgeUncolored (ett.series.data.coloring (Fin.last ett.rounds)) e0 ∧
        (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧ seed =
        ett.series.data.tree (Fin.last ett.rounds).castSucc ∨ (ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.SE ∨ ett.series.data.kind (Fin.last ett.rounds)
        = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges (Fin.last ett.rounds) = { f } ∧
        TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed) ∧
        TashkinovClosure (ett.series.data.coloring (Fin.last ett.rounds)) seed
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett
  let q : Fin ett.rounds :=
    ⟨ett.rounds - 1,
      Nat.sub_lt (Nat.zero_lt_of_lt ett.roundsPositive) (by omega)⟩
  have hq : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    exact Nat.sub_add_cancel ett.roundsPositive
  have hq2 : q.succ.succ = Fin.last (ett.rounds + 1) := by
    rw [hq]
    rfl
  have step := ett.series.certified (Fin.last ett.rounds)
  generalize hidx : Fin.last ett.rounds = target at step
  cases step with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hv : ett.rounds = 0 := by
      simpa using congrArg Fin.val hidx
    have hp := ett.roundsPositive
    omega
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hi : i = q := by
      apply Fin.ext
      have hv := congrArg Fin.val hidx
      simp [q] at hv ⊢
      omega
    subst i
    refine ⟨adjoined, ?_, ?_, Or.inr ?_, ?_⟩
    · rw [currentColoring]
      exact choice.selectedProper
    · rw [currentColoring]
      exact choice.selectedOneUncolored
    · refine ⟨Or.inl ?_, choice.edge, ?_, ?_⟩
      · exact currentKind
      · exact currentEdges
      · exact adjoinedExactly
    · rw [← hq2]
      exact closedExtension
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have hi : i = q := by
      apply Fin.ext
      have hv := congrArg Fin.val hidx
      simp [q] at hv ⊢
      omega
    subst i
    refine ⟨ett.series.data.tree (Fin.last ett.rounds).castSucc,
      ?_, ?_, Or.inl ?_, ?_⟩
    · exact currentProper
    · exact currentOneUncolored
    · refine ⟨currentKind, ?_⟩
      rw [← hq]
    · rw [← hq, ← hq2]
      exact closedExtension
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hi : i = q := by
      apply Fin.ext
      have hv := congrArg Fin.val hidx
      simp [q] at hv ⊢
      omega
    subst i
    refine ⟨adjoined, ?_, ?_, Or.inr ?_, ?_⟩
    · rw [currentColoring]
      exact previousProper
    · rw [currentColoring]
      exact previousOneUncolored
    · refine ⟨Or.inr ?_, available.edge, ?_, ?_⟩
      · exact currentKind
      · exact currentEdges
      · exact adjoinedExactly
    · rw [← hq2]
      exact closedExtension

private theorem NormalizePositiveTerminalMaximum_terminalMaximum_253.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating),
    let terminal := Fin.last ett.rounds;
    let Tn := ett.series.data.tree terminal.castSucc;
    let phiN := ett.series.data.coloring terminal;
    let C := TashkinovStoredColors ett.series.data terminal;
    ∀ (seed : TreeSequence G e0), IsProperEdgeColoring G (ett.series.data.coloring (Fin.last
        ett.rounds)) → IsOneEdgeUncolored (ett.series.data.coloring (Fin.last ett.rounds)) e0 →
        (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧ seed =
        ett.series.data.tree (Fin.last ett.rounds).castSucc ∨ (ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.SE ∨ ett.series.data.kind (Fin.last ett.rounds)
        = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges (Fin.last ett.rounds) = { f } ∧
        TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed) →
    ∀ (sigmaN : PartialEdgeColoring E k) (Tstar : TreeSequence G e0), (
    ∀ (rho : PartialEdgeColoring E k) (other : TreeSequence G e0), IsProperEdgeColoring G rho →
        IsOneEdgeUncolored rho e0 → StableColoring Tn C phiN rho → TashkinovClosure rho seed other
        → (TreeSequenceVertexSet other).card ≤ (TreeSequenceVertexSet Tstar).card) →
    ∀ (hcorr : Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigmaN Tstar)),
    let corr := Classical.choice hcorr; corr.replacementSeries.data.tree (Fin.last (ett.rounds +
        1)) = Tstar → MaximumProperty corr.replacementETT → TerminalClosureMaximum
        corr.replacementETT := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminal Tn phiN C seed hproper hone hroute
      sigmaN _ hmax hcorr corr terminalEq replacementMP
  rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
    rungAgreement, seriesPresentation, finalGeneratingColoring,
    ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
    extensionKindsAgree, replacementProper, replacementOneUncolored,
    replacementStable⟩
  cases replacementETT with
  | mk rounds roundsPositive replacementData above strict below generatingEq =>
    cases rungAgreement
    have seriesSame : replacementData = replacementSeries :=
      eq_of_heq seriesPresentation
    cases seriesSame
    let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let q : Fin ett.rounds :=
      ⟨ett.rounds - 1,
        Nat.sub_lt (Nat.zero_lt_of_lt ett.roundsPositive) (by omega)⟩
    have hq : q.succ = terminal := by
      apply Fin.ext
      exact Nat.sub_add_cancel ett.roundsPositive
    have treeEq : replacementSeries.data.tree terminal.castSucc =
        ett.series.data.tree terminal.castSucc := by
      rw [← hq]
      exact ladderTreesAgree q
    have kindEq : replacementSeries.data.kind terminal =
        ett.series.data.kind terminal := extensionKindsAgree terminal
    have edgesEq : replacementSeries.data.connectingEdges terminal =
        ett.series.data.connectingEdges terminal :=
      connectingEdgesAgree terminal
    have stableBridge : StableColoring
        (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data terminal)
        (ett.series.data.coloring terminal)
        (replacementSeries.data.coloring terminal) := by
      rw [← hq]
      exact replacementStable q
    have missingEq :
    forall v, v ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc) -> MissingColors
        G (replacementSeries.data.coloring terminal) v = MissingColors G (ett.series.data.coloring
        terminal) v := by
      intro v hv
      exact stableBridge.2 v hv
    have treeMissingEq :
        TreeMissingColors (replacementSeries.data.coloring terminal)
            (replacementSeries.data.tree terminal.castSucc) =
          TreeMissingColors (ett.series.data.coloring terminal)
            (ett.series.data.tree terminal.castSucc) := by
      rw [treeEq]
      ext c
      simp only [TreeMissingColors, Finset.mem_biUnion]
      constructor
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [← missingEq v hv]; exact hc⟩
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [missingEq v hv]; exact hc⟩
    have storedEq : TashkinovStoredColors replacementSeries.data terminal =
        TashkinovStoredColors ett.series.data terminal := by
      have nonzero : ¬ terminal.val = 0 := by
        simpa [terminal] using
          (Nat.ne_of_gt (Nat.zero_lt_of_lt ett.roundsPositive))
      unfold TashkinovStoredColors
      simp only [ite_eq_right nonzero]
      ext c
      simp only [Finset.mem_sdiff, Finset.mem_biUnion]
      constructor
      · rintro ⟨⟨h, hh, hc⟩, hn⟩
        refine ⟨⟨h, hh, ?_⟩, ?_⟩
        · by_cases hle : h.val ≤ terminal.val
          · simp only [ite_eq_left hle] at hc ⊢
            simpa [storedColorsAgree h] using hc
          · simp only [ite_eq_right hle] at hc ⊢
            exact hc
        · rw [treeMissingEq] at hn
          exact hn
      · rintro ⟨⟨h, hh, hc⟩, hn⟩
        refine ⟨⟨h, hh, ?_⟩, ?_⟩
        · by_cases hle : h.val ≤ terminal.val
          · simp only [ite_eq_left hle] at hc ⊢
            simpa [storedColorsAgree h] using hc
          · simp only [ite_eq_right hle] at hc ⊢
            exact hc
        · rw [← treeMissingEq] at hn
          exact hn
    unfold TerminalClosureMaximum
    dsimp
    intro rho candidateSeed candidate rhoProper rhoOne rhoStable
      replacementRoute candidateClosure
    have replacementColorProper := replacementProper terminal
    have replacementColorOne := replacementOneUncolored terminal
    have rhoStableBaseTree : StableColoring
        (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data terminal)
        (replacementSeries.data.coloring terminal) rho := by
      rw [← treeEq, ← storedEq]
      exact rhoStable
    have rhoStableBase : StableColoring
        (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data terminal)
        (ett.series.data.coloring terminal) rho := by
      exact (sc2 G e0 (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data terminal)).trans
          (x := ⟨ett.series.data.coloring terminal, ⟨hproper, hone⟩⟩)
          (y := ⟨replacementSeries.data.coloring terminal,
            ⟨replacementColorProper, replacementColorOne⟩⟩)
          (z := ⟨rho, ⟨rhoProper, rhoOne⟩⟩)
          stableBridge rhoStableBaseTree
    have candidateSeedEq : candidateSeed = seed := by
      rcases replacementRoute with replacementPE | replacementSER
      · rcases hroute with basePE | baseSER
        · exact replacementPE.2.trans (treeEq.trans basePE.2.symm)
        · rcases baseSER.1 with baseSE | baseRE
          · have impossible : some TashkinovExtensionKind.PE =
                some TashkinovExtensionKind.SE := by
              calc
                some TashkinovExtensionKind.PE =
                    replacementSeries.data.kind terminal :=
                  replacementPE.1.symm
                _ = ett.series.data.kind terminal := kindEq
                _ = some TashkinovExtensionKind.SE := baseSE
            cases impossible
          · have impossible : some TashkinovExtensionKind.PE =
                some TashkinovExtensionKind.RE := by
              calc
                some TashkinovExtensionKind.PE =
                    replacementSeries.data.kind terminal :=
                  replacementPE.1.symm
                _ = ett.series.data.kind terminal := kindEq
                _ = some TashkinovExtensionKind.RE := baseRE
            cases impossible
      · rcases replacementSER with ⟨replacementKind, f,
            replacementEdges, replacementAdjoin⟩
        rcases hroute with basePE | baseSER
        · rcases replacementKind with replacementSE | replacementRE
          · have impossible : some TashkinovExtensionKind.SE =
                some TashkinovExtensionKind.PE := by
              calc
                some TashkinovExtensionKind.SE =
                    replacementSeries.data.kind terminal := replacementSE.symm
                _ = ett.series.data.kind terminal := kindEq
                _ = some TashkinovExtensionKind.PE := basePE.1
            cases impossible
          · have impossible : some TashkinovExtensionKind.RE =
                some TashkinovExtensionKind.PE := by
              calc
                some TashkinovExtensionKind.RE =
                    replacementSeries.data.kind terminal := replacementRE.symm
                _ = ett.series.data.kind terminal := kindEq
                _ = some TashkinovExtensionKind.PE := basePE.1
            cases impossible
        · rcases baseSER with ⟨_, g, baseEdges, baseAdjoin⟩
          have singletonEq : ({f} : Finset E) = {g} := by
            calc
              {f} = replacementSeries.data.connectingEdges terminal :=
                replacementEdges.symm
              _ = ett.series.data.connectingEdges terminal := edgesEq
              _ = {g} := baseEdges
          have edgeEq : f = g := by simpa using singletonEq
          have replacementAdjoinBase : TreeSequenceAdjoinEdge
              (ett.series.data.tree terminal.castSucc) g candidateSeed := by
            rw [← treeEq, ← edgeEq]
            exact replacementAdjoin
          exact TreeSequenceAdjoinEdgeUnique _ _ _ _
            replacementAdjoinBase baseAdjoin
    rw [candidateSeedEq] at candidateClosure
    have bound := hmax rho candidate rhoProper rhoOne
      rhoStableBase candidateClosure
    rw [terminalEq]
    exact bound

theorem NormalizePositiveTerminalMaximum
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hfinal : T = ett.series.data.tree (Fin.last (ett.rounds + 1)))
    (hMP : MaximumProperty ett)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 11 <= TashkinovOrder G) :
    exists (sigmaN : PartialEdgeColoring E k)
        (Tstar seed : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigmaN Tstar),
      IsProperEdgeColoring G sigmaN /\ IsOneEdgeUncolored sigmaN e0 /\
      StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
        (ett.series.data.coloring (Fin.last ett.rounds)) sigmaN /\
      ((ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE /\
          seed = ett.series.data.tree (Fin.last ett.rounds).castSucc) \/
        ((ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.SE \/
            ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.RE) /\
          exists f : E,
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} /\
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed)) /\
      TashkinovClosure sigmaN seed Tstar /\
      corr.replacementSeries.data.tree (Fin.last (ett.rounds + 1)) = Tstar /\
      MaximumProperty corr.replacementETT /\
      TerminalClosureMaximum corr.replacementETT := by
  classical
  have terminalSeedAndClosure :
      exists seed : TreeSequence G e0,
        IsProperEdgeColoring G
            (ett.series.data.coloring (Fin.last ett.rounds)) /\
        IsOneEdgeUncolored
            (ett.series.data.coloring (Fin.last ett.rounds)) e0 /\
        ((ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.PE /\
            seed = ett.series.data.tree (Fin.last ett.rounds).castSucc) \/
          ((ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.SE \/
              ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.RE) /\
            exists f : E,
              ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} /\
              TreeSequenceAdjoinEdge
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed)) /\
        TashkinovClosure
          (ett.series.data.coloring (Fin.last ett.rounds)) seed
          (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
    exact @NormalizePositiveTerminalMaximum_terminalSeedAndClosure_63 V E inferInstance
        inferInstance inferInstance G k e0 input T generating ett
  let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree terminal.castSucc
  let Tfinal : TreeSequence G e0 :=
    ett.series.data.tree (Fin.last (ett.rounds + 1))
  let phiN : PartialEdgeColoring E k := ett.series.data.coloring terminal
  let C : Finset (Fin k) := TashkinovStoredColors ett.series.data terminal
  obtain ⟨seed, hproper, hone, hroute, holdClosure⟩ := terminalSeedAndClosure
  have hself : StableColoring Tn C phiN phiN := by
    exact (sc2 G e0 Tn C).refl ⟨phiN, hproper, hone⟩
  obtain ⟨sigmaN, Tstar, hsproper, hsone, hstable, hclosure, hmax⟩ :=
    MaximumStableClosureExists Tn seed C phiN
      ⟨phiN, Tfinal, hproper, hone, hself, holdClosure⟩
  have holdBound : (TreeSequenceVertexSet Tfinal).card <=
      (TreeSequenceVertexSet Tstar).card :=
    hmax phiN Tfinal hproper hone hself holdClosure
  have hlengthBound : Tfinal.length <= Tstar.length := by
    simpa [TreeSequenceVertexSet, Finset.card_image_of_injective,
      Tfinal.vertex_injective, Tstar.vertex_injective] using holdBound
  have hstrictOld : Tn.length < Tfinal.length := by
    have hprefix : Tn.length < T.length := by
      have hslot :
          (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
            terminal.castSucc := by
        apply Fin.ext
        rfl
      change (ett.series.data.tree terminal.castSucc).length < T.length
      rw [← hslot]
      exact ett.strictAbovePenultimate
    have hfinalLength : T.length = Tfinal.length :=
      congrArg TreeSequence.length hfinal
    exact hprefix.trans_le hfinalLength.le
  have hstrict : Tn.length < Tstar.length := by omega
  have segmentTrans : forall (A B D : TreeSequence G e0),
      TreeSequenceInitialSegment A B -> TreeSequenceInitialSegment B D ->
        TreeSequenceInitialSegment A D := by
    intro A B D hab hbd
    rcases hab with ⟨hab, hvab, heab⟩
    rcases hbd with ⟨hbd, hvbd, hebd⟩
    refine ⟨Nat.le_trans hab hbd, ?_, ?_⟩
    · intro j
      calc
        D.vertex (Fin.castLE (Nat.succ_le_succ (Nat.le_trans hab hbd)) j) =
            D.vertex (Fin.castLE (Nat.succ_le_succ hbd)
              (Fin.castLE (Nat.succ_le_succ hab) j)) := by congr 1
        _ = B.vertex (Fin.castLE (Nat.succ_le_succ hab) j) := hvbd _
        _ = A.vertex j := hvab _
    · intro j
      calc
        D.edge (Fin.castLE (Nat.le_trans hab hbd) j) =
            D.edge (Fin.castLE hbd (Fin.castLE hab j)) := by congr 1
        _ = B.edge (Fin.castLE hab j) := hebd _
        _ = A.edge j := heab _
  have hseg : TreeSequenceInitialSegment Tn Tstar := by
    have seedToStar :=
      TashkinovAugmentationSequenceInitialSegment sigmaN seed Tstar hclosure.1
    rcases hroute with hPE | hSER
    · simpa [Tn, terminal] using hPE.2 ▸ seedToStar
    · rcases hSER with ⟨_, f, _, hadjoin⟩
      exact segmentTrans Tn seed Tstar hadjoin.choose_spec.1 seedToStar
  have heligible :
      (ett.series.data.kind terminal = some TashkinovExtensionKind.PE /\
          TashkinovAugmentationSequence sigmaN Tn Tstar) \/
      ((ett.series.data.kind terminal = some TashkinovExtensionKind.SE \/
          ett.series.data.kind terminal = some TashkinovExtensionKind.RE) /\
        exists (f : E) (S : TreeSequence G e0),
          ett.series.data.connectingEdges terminal = {f} /\
          TreeSequenceAdjoinEdge Tn f S /\
          TashkinovAugmentationSequence sigmaN S Tstar) := by
    rcases hroute with hPE | hSER
    · exact Or.inl ⟨hPE.1, by simpa [hPE.2] using hclosure.1⟩
    · rcases hSER with ⟨hk, f, hf, hadjoin⟩
      exact Or.inr ⟨hk, f, seed, hf, hadjoin, hclosure.1⟩
  have hmod : ModColoring ett sigmaN := by
    exact (TechnicalTheoremLarge G k e0 input T generating ett hMP hdegree hlarge).2.2.2.2.2
      sigmaN hsproper hsone hstable
  have hcorr : Nonempty
      (CorrespondingExtendedTashkinovTree G k e0 ett sigmaN Tstar) :=
    hmod.2.2 Tstar hseg hstrict heligible
  let corr : CorrespondingExtendedTashkinovTree G k e0 ett sigmaN Tstar :=
    Classical.choice hcorr
  have terminalEq :
      corr.replacementSeries.data.tree (Fin.last (ett.rounds + 1)) = Tstar :=
    CorrespondingTerminalClosureEq G k e0 input T generating ett sigmaN
      Tstar seed corr hroute hclosure
  have replacementMP : MaximumProperty corr.replacementETT :=
    MaximumPropertyTransport G k e0 ett sigmaN hmod Tstar corr hMP
  have terminalMaximum : TerminalClosureMaximum corr.replacementETT := by
    exact @NormalizePositiveTerminalMaximum_terminalMaximum_253 V E inferInstance inferInstance
        inferInstance G k e0 input T generating ett seed hproper hone hroute sigmaN Tstar hmax
        hcorr terminalEq replacementMP
  exact ⟨sigmaN, Tstar, seed, corr, hsproper, hsone, hstable, hroute,
    hclosure, terminalEq, replacementMP, terminalMaximum⟩

end GoldbergSeymour

end
