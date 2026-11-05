/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment

/-!
# Restricted Augmentation Corresponding Endpoint

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBranch102Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (generating sigma : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T generating),
  MaximumProperty ett →
   ∀ (J U : TreeSequence G e0),
    TashkinovAugmentationSequence sigma J U →
     IsProperEdgeColoring G sigma →
      IsOneEdgeUncolored sigma e0 →
       (∀ (Tstar : TreeSequence G e0),
         TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
          (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length →
           (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
              TashkinovAugmentationSequence sigma
               (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar ∨
             (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
               ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
              ∃ (f : E) (seed : TreeSequence G e0),
               ett.series.data.connectingEdges (Fin.last ett.rounds) = { f } ∧
                TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f
                  seed ∧
                 TashkinovAugmentationSequence sigma seed Tstar) →
            Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)) →
        (∀ {A B C : TreeSequence G e0},
          TreeSequenceInitialSegment A B →
           TreeSequenceInitialSegment B C → TreeSequenceInitialSegment A C) →
         (∀ {A B C : TreeSequence G e0},
           TreeSequenceInitialSegment A C →
            TreeSequenceInitialSegment B C → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
          ∀ (replacementInput : PartialEdgeColoring E k)
           (replacementSeries : TashkinovSeries G k ett.rounds e0 replacementInput),
           sigma = replacementSeries.data.coloring (Fin.last ett.rounds) →
            (∀ (i : Fin ett.rounds),
              replacementSeries.data.tree i.succ.castSucc = ett.series.data.tree i.succ.castSucc) →
             (∀ (i : Fin (ett.rounds + (1 : ℕ))),
               replacementSeries.data.connectingEdges i = ett.series.data.connectingEdges i) →
              (∀ (i : Fin (ett.rounds + (1 : ℕ))),
                replacementSeries.data.kind i = ett.series.data.kind i) →
               ∀ (rounds : ℕ) (roundsPositive : (1 : ℕ) ≤ rounds)
                (replacementData : TashkinovSeries G k rounds e0 replacementInput)
                (above :
                 TreeSequenceInitialSegment
                  (replacementData.data.tree (⟨rounds, (by omega)⟩ : Fin (rounds + (2 : ℕ)))) J)
                (strict :
                 (replacementData.data.tree
                    (⟨rounds, (by omega)⟩ : Fin (rounds + (2 : ℕ)))).length <
                  J.length)
                (below :
                 TreeSequenceInitialSegment J
                  (replacementData.data.tree (Fin.last (rounds + (1 : ℕ)))))
                (generatingEq : sigma = replacementData.data.coloring (Fin.last rounds)),
                { rounds := rounds, roundsPositive := roundsPositive, series := replacementData,
                    abovePenultimate := above, strictAbovePenultimate := strict,
                    belowFinal := below, generatingColoring := generatingEq :
                    ExtendedTashkinovTree G k e0 replacementInput J sigma }.rounds =
                  ett.rounds →
                 { rounds := rounds, roundsPositive := roundsPositive, series := replacementData,
                     abovePenultimate := above, strictAbovePenultimate := strict,
                     belowFinal := below, generatingColoring := generatingEq :
                     ExtendedTashkinovTree G k e0 replacementInput J sigma }.series ≍
                   replacementSeries →
                  ∃ (corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U),
                   MaximumProperty corrU.replacementETT

private theorem helper_branch_102.{u_1, u_2} :
    helperBranch102Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett hMP J U hJU sigmaProper sigmaOneUncolored
      hmodExtension initialSegmentTrans initialSegmentOfCommonExtension replacementInput
      replacementSeries finalGeneratingColoring ladderTreesAgree connectingEdgesAgree
      extensionKindsAgree rounds roundsPositive replacementData above strict below generatingEq
      rungAgreement seriesPresentation
  cases rungAgreement
  have seriesSame : replacementData = replacementSeries :=
    eq_of_heq seriesPresentation
  cases seriesSame
  let q : Fin ett.rounds :=
    ⟨ett.rounds - 1,
      Nat.sub_lt (Nat.zero_lt_of_lt ett.roundsPositive) (by omega)⟩
  have hq : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    exact Nat.sub_add_cancel ett.roundsPositive
  have hq2 : q.succ.succ = Fin.last (ett.rounds + 1) := by
    rw [hq]
    rfl
  have ladderEq : replacementSeries.data.tree
        (Fin.last ett.rounds).castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    rw [← hq]
    exact ladderTreesAgree q
  have lastIndexEq : (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
      (Fin.last ett.rounds).castSucc := Fin.ext (by rfl)
  have replacementLastToJ : TreeSequenceInitialSegment
      (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) J := by
    rw [← lastIndexEq]
    exact above
  have replacementLastStrict :
      (replacementSeries.data.tree
        (Fin.last ett.rounds).castSucc).length < J.length := by
    rw [← lastIndexEq]
    exact strict
  have originalLastToJ : TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) J := by
    rw [← ladderEq]
    exact replacementLastToJ
  have originalLastStrict :
      (ett.series.data.tree
        (Fin.last ett.rounds).castSucc).length < J.length := by
    rw [← ladderEq]
    exact replacementLastStrict
  have hJUInitial : TreeSequenceInitialSegment J U :=
    TashkinovAugmentationSequenceInitialSegment sigma J U hJU
  have originalLastToU : TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) U :=
    initialSegmentTrans originalLastToJ hJUInitial
  have originalLastStrictU :
      (ett.series.data.tree
        (Fin.last ett.rounds).castSucc).length < U.length :=
    lt_of_lt_of_le originalLastStrict hJUInitial.1
  have hroute :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) U) ∨
      ((ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
            TashkinovAugmentationSequence sigma seed U) := by
    have finalStep := replacementSeries.certified (Fin.last ett.rounds)
    generalize finalIndex : Fin.last ett.rounds = target at finalStep
    cases finalStep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      have hzero : ett.rounds = 0 := by
        simpa using congrArg Fin.val finalIndex
      have hpositive := ett.roundsPositive
      rw [hzero] at hpositive
      omega
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val finalIndex
        simp [q] at hv ⊢
        omega
      subst i
      rw [hq]
      right
      refine ⟨Or.inl ?_, choice.edge, adjoined, ?_, ?_, ?_⟩
      · rw [← extensionKindsAgree (Fin.last ett.rounds), ← hq]
        exact currentKind
      · rw [← connectingEdgesAgree (Fin.last ett.rounds), ← hq]
        exact currentEdges
      · rw [← ladderEq, ← hq]
        exact adjoinedExactly
      · have routeToFinal : TashkinovAugmentationSequence sigma adjoined
            (replacementSeries.data.tree (Fin.last (ett.rounds + 1))) := by
          rw [finalGeneratingColoring, ← hq, ← hq2]
          exact closedExtension.1
        have adjoinedToFinal : TreeSequenceInitialSegment adjoined
            (replacementSeries.data.tree (Fin.last (ett.rounds + 1))) :=
          TashkinovAugmentationSequenceInitialSegment sigma adjoined _ routeToFinal
        have adjoinedLength : adjoined.length ≤ J.length := by
          have hlen := adjoinedExactly.1
          rw [hq] at hlen
          have hcommon := congrArg TreeSequence.length ladderEq
          omega
        have adjoinedToJ : TreeSequenceInitialSegment adjoined J :=
          initialSegmentOfCommonExtension adjoinedToFinal below adjoinedLength
        have routeToJ := TashkinovAugmentationSequenceRestrict sigma
          adjoined J _ routeToFinal adjoinedToJ below
        exact routeToJ.trans hJU
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension
        orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val finalIndex
        simp [q] at hv ⊢
        omega
      subst i
      rw [hq]
      left
      refine ⟨?_, ?_⟩
      · rw [← extensionKindsAgree (Fin.last ett.rounds), ← hq]
        exact currentKind
      · have routeToFinal : TashkinovAugmentationSequence sigma
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)
            (replacementSeries.data.tree (Fin.last (ett.rounds + 1))) := by
          rw [finalGeneratingColoring, ← ladderEq, ← hq, ← hq2]
          exact closedExtension.1
        have routeToJ := TashkinovAugmentationSequenceRestrict sigma
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) J _
          routeToFinal originalLastToJ below
        exact routeToJ.trans hJU
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val finalIndex
        simp [q] at hv ⊢
        omega
      subst i
      rw [hq]
      right
      refine ⟨Or.inr ?_, available.edge, adjoined, ?_, ?_, ?_⟩
      · rw [← extensionKindsAgree (Fin.last ett.rounds), ← hq]
        exact currentKind
      · rw [← connectingEdgesAgree (Fin.last ett.rounds), ← hq]
        exact currentEdges
      · rw [← ladderEq, ← hq]
        exact adjoinedExactly
      · have routeToFinal : TashkinovAugmentationSequence sigma adjoined
            (replacementSeries.data.tree (Fin.last (ett.rounds + 1))) := by
          rw [finalGeneratingColoring, ← hq, ← hq2]
          exact closedExtension.1
        have adjoinedToFinal : TreeSequenceInitialSegment adjoined
            (replacementSeries.data.tree (Fin.last (ett.rounds + 1))) :=
          TashkinovAugmentationSequenceInitialSegment sigma adjoined _ routeToFinal
        have adjoinedLength : adjoined.length ≤ J.length := by
          have hlen := adjoinedExactly.1
          rw [hq] at hlen
          have hcommon := congrArg TreeSequence.length ladderEq
          omega
        have adjoinedToJ : TreeSequenceInitialSegment adjoined J :=
          initialSegmentOfCommonExtension adjoinedToFinal below adjoinedLength
        have routeToJ := TashkinovAugmentationSequenceRestrict sigma
          adjoined J _ routeToFinal adjoinedToJ below
        exact routeToJ.trans hJU
  have corrUNonempty : Nonempty
      (CorrespondingExtendedTashkinovTree G k e0 ett sigma U) :=
    hmodExtension U originalLastToU originalLastStrictU hroute
  let corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U :=
    Classical.choice corrUNonempty
  refine ⟨corrU, ?_⟩
  exact MaximumPropertyTransport G k e0 ett sigma
    ⟨sigmaProper, sigmaOneUncolored, hmodExtension⟩ U corrU hMP

theorem RestrictedAugmentationCorrespondingEndpoint {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hmod : ModColoring ett sigma) (hMP : MaximumProperty ett)
    (J U : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (hJU : TashkinovAugmentationSequence sigma J U) :
    ∃ corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U,
      MaximumProperty corrU.replacementETT := by
  classical
  rcases hmod with ⟨sigmaProper, sigmaOneUncolored, hmodExtension⟩
  have initialSegmentTrans : ∀ {A B C : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
      TreeSequenceInitialSegment B C →
      TreeSequenceInitialSegment A C := by
    intro A B C hAB hBC
    rcases hAB with ⟨hlenAB, hvertexAB, hedgeAB⟩
    rcases hBC with ⟨hlenBC, hvertexBC, hedgeBC⟩
    refine ⟨Nat.le_trans hlenAB hlenBC, ?_, ?_⟩
    · intro i
      calc
        C.vertex (Fin.castLE
            (Nat.succ_le_succ (Nat.le_trans hlenAB hlenBC)) i) =
            C.vertex (Fin.castLE (Nat.succ_le_succ hlenBC)
              (Fin.castLE (Nat.succ_le_succ hlenAB) i)) := by congr 1
        _ = B.vertex (Fin.castLE (Nat.succ_le_succ hlenAB) i) :=
          hvertexBC _
        _ = A.vertex i := hvertexAB i
    · intro i
      calc
        C.edge (Fin.castLE (Nat.le_trans hlenAB hlenBC) i) =
            C.edge (Fin.castLE hlenBC (Fin.castLE hlenAB i)) := by congr 1
        _ = B.edge (Fin.castLE hlenAB i) := hedgeBC _
        _ = A.edge i := hedgeAB i
  have initialSegmentOfCommonExtension : ∀ {A B C : TreeSequence G e0},
      TreeSequenceInitialSegment A C →
      TreeSequenceInitialSegment B C →
      A.length ≤ B.length →
      TreeSequenceInitialSegment A B := by
    intro A B C hAC hBC hlenAB
    rcases hAC with ⟨hlenAC, hvertexAC, hedgeAC⟩
    rcases hBC with ⟨hlenBC, hvertexBC, hedgeBC⟩
    refine ⟨hlenAB, ?_, ?_⟩
    · intro i
      calc
        B.vertex (Fin.castLE (Nat.succ_le_succ hlenAB) i) =
            C.vertex (Fin.castLE (Nat.succ_le_succ hlenBC)
              (Fin.castLE (Nat.succ_le_succ hlenAB) i)) :=
          (hvertexBC _).symm
        _ = C.vertex (Fin.castLE (Nat.succ_le_succ hlenAC) i) := by
          congr 1
        _ = A.vertex i := hvertexAC i
    · intro i
      calc
        B.edge (Fin.castLE hlenAB i) =
            C.edge (Fin.castLE hlenBC (Fin.castLE hlenAB i)) :=
          (hedgeBC _).symm
        _ = C.edge (Fin.castLE hlenAC i) := by congr 1
        _ = A.edge i := hedgeAC i
  rcases corrJ with ⟨replacementInput, replacementSeries, replacementETT,
    rungAgreement, seriesPresentation, finalGeneratingColoring,
    ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
    extensionKindsAgree, replacementProper, replacementOneUncolored,
    replacementStable⟩
  cases replacementETT with
  | mk rounds roundsPositive replacementData above strict below generatingEq =>
      exact @helper_branch_102 V E inferInstance inferInstance inferInstance G k e0 input T
          generating sigma ett hMP J U hJU sigmaProper sigmaOneUncolored hmodExtension
          initialSegmentTrans initialSegmentOfCommonExtension replacementInput replacementSeries
          finalGeneratingColoring ladderTreesAgree connectingEdgesAgree extensionKindsAgree
          rounds roundsPositive replacementData above strict below generatingEq rungAgreement
          seriesPresentation
end GoldbergSeymour

end
