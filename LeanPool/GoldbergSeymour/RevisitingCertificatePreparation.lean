/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint
public import LeanPool.GoldbergSeymour.ParallelExtensionColor
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificate
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TdEarlierPEWitnessIdentification
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.TwoColorCycle
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.TwoColorInterchangeableDistinctComponentCycle
public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent
public import LeanPool.GoldbergSeymour.TwoColorPathComponent
public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion

/-!
# Revisiting extension kinds in certified prefixes

Supporting lemmas for the Goldberg–Seymour revisiting-certificate construction.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Transfer revisiting extension kinds from a certified replacement prefix to the original
    series. -/
theorem revisitingExtensionKindsInPrefix.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hroundLarge : (1 : ℕ) < ett.rounds),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬ett.rounds - (1
        : ℕ) < ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    ∀ (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬ett.rounds - (1
        : ℕ) < ett.rounds) ↦
    by
                    omega
    ⟩ : Fin ett.rounds).castSucc)) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦
    by
                    omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦
    by
                      omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦
    by
                        omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦
    by
                          omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦
    by
                          omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
        Fin.castLE (
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦
    by
                  omega
    ) replacementLast = (⟨ett.rounds - (1 : ℕ),
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬ett.rounds - (1
        : ℕ) < ett.rounds) ↦
    by
                      omega
    ⟩ : Fin ett.rounds).castSucc →
    ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
    let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
    ∀ (horiginalRoundsLess : originalPrefix.rounds < ett.rounds),
    let oldEarlier : Fin (ett.rounds + (1 : ℕ)) := Fin.castLE (
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦
    by
                      omega
    ) earlierPrefix;
    ∀ (fulli : Fin ett.rounds) (_ : MaximumDefectiveChoice G e0 (ett.series.data.tree
        fulli.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc)) (_ : Fin k) (j : Fin (ett.rounds + (1 : ℕ))),
        (0 : ℕ) < (↑j : ℕ) → (↑oldEarlier : ℕ) < (↑j : ℕ) → (↑j : ℕ) ≤ (↑q.castSucc : ℕ) →
        ett.series.data.kind j = some TashkinovExtensionKind.RE := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q sigmaPrev originalPrefix hr
      hprefixData corr replacementLast hlastMap available earlierPrefix horiginalRoundsLess
      oldEarlier fulli fullChoice fullGamma j hjPositive hjLower hjUpper
  let jPrefix : Fin (originalPrefix.rounds + 1) :=
    ⟨j.val, by
      have hjBound := j.isLt
      simp [q, hr] at hjUpper ⊢
      omega⟩
  have hjMap : Fin.castLE (by omega) jPrefix = j := by
    apply Fin.ext
    rfl
  calc
    ett.series.data.kind j =
        ett.series.data.kind
          (Fin.castLE (by omega) jPrefix) := by
      rw [hjMap]
    _ = originalPrefix.series.data.kind jPrefix :=
      (hprefixData jPrefix).2.2.2.1.symm
    _ = corr.replacementSeries.data.kind jPrefix :=
      (corr.extensionKindsAgree jPrefix).symm
    _ = some TashkinovExtensionKind.RE := by
      apply available.interveningRevisiting jPrefix
      · exact hjPositive
      · simpa [jPrefix, oldEarlier,
          earlierPrefix] using hjLower
      · have hlastVals :=
            congrArg Fin.val hlastMap
        simpa [jPrefix, replacementLast] using
          hjUpper.trans_eq hlastVals.symm

end GoldbergSeymour

end
