/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree

public import LeanPool.GoldbergSeymour.StableColoringEquivalence

/-!
# Corresponding Extended Tashkinov Tree Trans Trees

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

section

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ}
  {e0 : E}

private theorem projectLast :
    ∀ {r s : Nat} {inputColoring : PartialEdgeColoring E k} (h : r = s) (x : TashkinovSeries G k r
        e0 inputColoring), HEq ((h ▸ x).data.coloring (Fin.last s)) (x.data.coloring (Fin.last r))
  := by
  intro r s inputColoring h x
  cases h
  rfl

private theorem projectTree :
    ∀ {r s : Nat} (h : r = s) {inputColoring : PartialEdgeColoring E k} (x : TashkinovSeries G k r
        e0 inputColoring) (i : Fin r), HEq ((h ▸ x).data.tree ((h ▸ i).succ.castSucc))
        (x.data.tree i.succ.castSucc) := by
  intro r s h inputColoring x i
  cases h
  rfl

private theorem castBack : ∀ {r s : Nat} (h : r = s) (i : Fin s),
    h ▸ (h.symm ▸ i) = i := by
  intro r s h i
  cases h
  rfl

private theorem castBackPlus : ∀ {r s : Nat} (h : r = s) (i : Fin (s + 1)),
    h ▸ (h.symm ▸ i) = i := by
  intro r s h i
  cases h
  rfl

private theorem castValue : ∀ {r s : Nat} (h : r = s) (i : Fin r),
    ((h ▸ i : Fin s) : Nat) = (i : Nat) := by
  intro r s h i
  cases h
  rfl

private theorem castValuePlus : ∀ {r s : Nat} (h : r = s) (i : Fin (r + 1)),
    ((h ▸ i : Fin (s + 1)) : Nat) = (i : Nat) := by
  intro r s h i
  cases h
  rfl

private theorem succCast : ∀ {r s : Nat} (h : r = s) (i : Fin r),
    (h ▸ i).succ = h ▸ i.succ := by
  intro r s h i
  cases h
  rfl

private theorem projectColoring : ∀ {r s : Nat} (h : r = s)
    {inputColoring : PartialEdgeColoring E k}
    (x : TashkinovSeries G k r e0 inputColoring) (i : Fin (r + 1)),
    HEq ((h ▸ x).data.coloring (h ▸ i)) (x.data.coloring i) := by
  intro r s h inputColoring x i
  cases h
  rfl

private theorem projectStored :
    ∀ {r s : Nat} (h : r = s) {inputColoring : PartialEdgeColoring E k} (x : TashkinovSeries G k r
        e0 inputColoring) (i : Fin (r + 1)), HEq ((h ▸ x).data.stored (h ▸ i)) (x.data.stored i)
  := by
  intro r s h inputColoring x i
  cases h
  rfl

private theorem projectEdges : ∀ {r s : Nat} (h : r = s)
    {inputColoring : PartialEdgeColoring E k}
    (x : TashkinovSeries G k r e0 inputColoring) (i : Fin (r + 1)),
    HEq ((h ▸ x).data.connectingEdges (h ▸ i)) (x.data.connectingEdges i) := by
  intro r s h inputColoring x i
  cases h
  rfl

private theorem projectKind :
    ∀ {r s : Nat} (h : r = s) {inputColoring : PartialEdgeColoring E k} (x : TashkinovSeries G k r
        e0 inputColoring) (i : Fin (r + 1)), HEq ((h ▸ x).data.kind (h ▸ i)) (x.data.kind i) := by
  intro r s h inputColoring x i
  cases h
  rfl

private theorem replacementSeriesPresentation
    {input : PartialEdgeColoring E k} {T0 T1 : TreeSequence G e0}
    {phi sigma : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T0 phi}
    (first : CorrespondingExtendedTashkinovTree G k e0 ett sigma T1) :
    first.replacementETT.series = first.rungAgreement.symm ▸ first.replacementSeries := by
  have castProof : HEq first.replacementSeries
      (first.rungAgreement.symm ▸ first.replacementSeries) := by simp
  exact eq_of_heq (HEq.trans first.seriesPresentation castProof)

private theorem correspondingStoredColors
    {input : PartialEdgeColoring E k} {T0 T1 : TreeSequence G e0}
    {phi sigma : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T0 phi}
    (first : CorrespondingExtendedTashkinovTree G k e0 ett sigma T1)
    (i : Fin ett.rounds) :
    TashkinovStoredColors first.replacementETT.series.data
        (first.rungAgreement.symm ▸ i).succ =
      TashkinovStoredColors ett.series.data i.succ := by
  classical
  let middleIndex := first.rungAgreement.symm ▸ i
  have firstSeriesEq := replacementSeriesPresentation first
  have treeBridge :
      first.replacementETT.series.data.tree middleIndex.succ.castSucc =
        ett.series.data.tree i.succ.castSucc := by
    rw [firstSeriesEq]
    exact (eq_of_heq (projectTree first.rungAgreement.symm
      first.replacementSeries i)).trans (first.ladderTreesAgree i)
  have storedBridge :
      first.replacementETT.series.data.stored middleIndex.succ =
        ett.series.data.stored i.succ := by
    have middleSucc : middleIndex.succ = first.rungAgreement.symm ▸ i.succ := by
      exact succCast first.rungAgreement.symm i
    rw [middleSucc]
    rw [firstSeriesEq]
    exact (eq_of_heq (projectStored first.rungAgreement.symm
      first.replacementSeries i.succ)).trans
      (first.storedColorsAgree i.succ)
  have middleColorBridge :
      first.replacementETT.series.data.coloring middleIndex.succ =
        first.replacementSeries.data.coloring i.succ := by
    have middleSucc : middleIndex.succ = first.rungAgreement.symm ▸ i.succ := by
      exact succCast first.rungAgreement.symm i
    rw [middleSucc]
    rw [firstSeriesEq]
    exact eq_of_heq (projectColoring first.rungAgreement.symm
      first.replacementSeries i.succ)
  have raw : ∀ j : Fin (first.replacementETT.rounds + 1),
      first.replacementETT.series.data.stored j =
        ett.series.data.stored (first.rungAgreement ▸ j) := by
    intro j
    rw [firstSeriesEq]
    have p := projectStored first.rungAgreement.symm
      first.replacementSeries (first.rungAgreement ▸ j)
    have pj := eq_of_heq p
    rw [castBackPlus first.rungAgreement.symm j] at pj
    exact pj.trans (first.storedColorsAgree (first.rungAgreement ▸ j))
  have missing :
      TreeMissingColors
          (first.replacementETT.series.data.coloring middleIndex.succ)
          (first.replacementETT.series.data.tree middleIndex.succ.castSucc) =
        TreeMissingColors (ett.series.data.coloring i.succ)
          (ett.series.data.tree i.succ.castSucc) := by
    rw [middleColorBridge, treeBridge]
    ext c
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor
    · rintro ⟨v, hv, hc⟩
      exact ⟨v, hv, by
        rw [← (first.replacementStable i).2 v hv]
        exact hc⟩
    · rintro ⟨v, hv, hc⟩
      exact ⟨v, hv, by
        rw [(first.replacementStable i).2 v hv]
        exact hc⟩
  unfold TashkinovStoredColors
  simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Fin.castSucc_succ]
  ext c
  simp only [Finset.mem_sdiff, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨j, hj, hc⟩, hn⟩
    refine ⟨⟨first.rungAgreement ▸ j, by simp, ?_⟩, ?_⟩
    · rw [← raw j]
      have castJ := castValuePlus first.rungAgreement j
      have castI := castValue first.rungAgreement.symm i
      simpa [middleIndex, castJ, castI] using hc
    · have hn' : c ∉ TreeMissingColors
          (ett.series.data.coloring i.succ)
          (ett.series.data.tree i.succ.castSucc) := by
        rw [← missing]
        exact hn
      simpa [Fin.succ] using hn'
  · rintro ⟨⟨j, hj, hc⟩, hn⟩
    refine ⟨⟨first.rungAgreement.symm ▸ j, by simp, ?_⟩, ?_⟩
    · have rr := raw (first.rungAgreement.symm ▸ j)
      rw [rr]
      have castJ := castValuePlus first.rungAgreement.symm j
      have castI := castValue first.rungAgreement.symm i
      rw [castBackPlus first.rungAgreement j]
      simpa [middleIndex, castJ, castI] using hc
    · have hn' : c ∉ TreeMissingColors
          (first.replacementETT.series.data.coloring middleIndex.succ)
          (first.replacementETT.series.data.tree middleIndex.succ.castSucc) := by
        rw [missing]
        exact hn
      simpa [Fin.succ] using hn'

private theorem correspondingStableComposition
    {input : PartialEdgeColoring E k} {T0 T1 T2 : TreeSequence G e0}
    {phi sigma tau : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T0 phi}
    (first : CorrespondingExtendedTashkinovTree G k e0 ett sigma T1)
    (second : CorrespondingExtendedTashkinovTree G k e0 first.replacementETT tau T2)
    (i : Fin ett.rounds) :
    StableColoring (ett.series.data.tree i.succ.castSucc)
      (TashkinovStoredColors ett.series.data i.succ)
      (ett.series.data.coloring i.succ)
      ((first.rungAgreement ▸ second.replacementSeries).data.coloring i.succ) := by
  classical
  let transported : TashkinovSeries G k ett.rounds e0 second.replacementInput :=
    first.rungAgreement ▸ second.replacementSeries
  have firstSeriesEq := replacementSeriesPresentation first
  let middleIndex := first.rungAgreement.symm ▸ i
  have treeBridge :
      first.replacementETT.series.data.tree middleIndex.succ.castSucc =
        ett.series.data.tree i.succ.castSucc := by
    rw [firstSeriesEq]
    exact (eq_of_heq (projectTree first.rungAgreement.symm
      first.replacementSeries i)).trans (first.ladderTreesAgree i)
  have storedBridge :
      first.replacementETT.series.data.stored middleIndex.succ =
        ett.series.data.stored i.succ := by
    have middleSucc : middleIndex.succ = first.rungAgreement.symm ▸ i.succ := by
      exact succCast first.rungAgreement.symm i
    rw [middleSucc]
    rw [firstSeriesEq]
    exact (eq_of_heq (projectStored first.rungAgreement.symm
      first.replacementSeries i.succ)).trans
      (first.storedColorsAgree i.succ)
  have middleColorBridge :
      first.replacementETT.series.data.coloring middleIndex.succ =
        first.replacementSeries.data.coloring i.succ := by
    have middleSucc : middleIndex.succ = first.rungAgreement.symm ▸ i.succ := by
      exact succCast first.rungAgreement.symm i
    rw [middleSucc]
    rw [firstSeriesEq]
    exact eq_of_heq (projectColoring first.rungAgreement.symm
      first.replacementSeries i.succ)
  have storedColorBridge := correspondingStoredColors first i
  have secondStable : StableColoring
      (ett.series.data.tree i.succ.castSucc)
      (TashkinovStoredColors ett.series.data i.succ)
      (first.replacementSeries.data.coloring i.succ)
      (second.replacementSeries.data.coloring middleIndex.succ) := by
    have h := second.replacementStable middleIndex
    rw [treeBridge, storedColorBridge, middleColorBridge] at h
    exact h
  have originalGood : IsProperEdgeColoring G (ett.series.data.coloring i.succ) ∧
      IsOneEdgeUncolored (ett.series.data.coloring i.succ) e0 := by
    exact ett.series.coloringProperties i.succ
  have middleGood : IsProperEdgeColoring G
      (first.replacementSeries.data.coloring i.succ) ∧
      IsOneEdgeUncolored (first.replacementSeries.data.coloring i.succ) e0 :=
    ⟨first.replacementProper i.succ, first.replacementOneUncolored i.succ⟩
  have finalGood : IsProperEdgeColoring G
      (second.replacementSeries.data.coloring middleIndex.succ) ∧
      IsOneEdgeUncolored (second.replacementSeries.data.coloring middleIndex.succ) e0 :=
    ⟨second.replacementProper middleIndex.succ,
      second.replacementOneUncolored middleIndex.succ⟩
  have finalColor : transported.data.coloring i.succ =
      second.replacementSeries.data.coloring middleIndex.succ := by
    have hc := projectColoring first.rungAgreement
      second.replacementSeries middleIndex.succ
    have hi : i.succ = first.rungAgreement ▸ middleIndex.succ := by
      calc
        i.succ = first.rungAgreement ▸
            (first.rungAgreement.symm ▸ i.succ) :=
          (castBackPlus first.rungAgreement i.succ).symm
        _ = first.rungAgreement ▸ middleIndex.succ := by
          rw [succCast]
    convert (eq_of_heq hc) using 1
    simpa [transported, middleIndex] using congrArg
      (fun q => transported.data.coloring q) hi
  rw [finalColor]
  exact (sc2 G e0 (ett.series.data.tree i.succ.castSucc)
    (TashkinovStoredColors ett.series.data i.succ)).trans
    (x := ⟨ett.series.data.coloring i.succ, originalGood⟩)
    (y := ⟨first.replacementSeries.data.coloring i.succ, middleGood⟩)
    (z := ⟨second.replacementSeries.data.coloring middleIndex.succ, finalGood⟩)
    (first.replacementStable i) secondStable

end

lemma CorrespondingExtendedTashkinovTreeTransTrees
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k)
    (T0 T1 T2 : TreeSequence G e0)
    (phi sigma tau : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T0 phi)
    (first : CorrespondingExtendedTashkinovTree G k e0 ett sigma T1)
    (second : CorrespondingExtendedTashkinovTree
      G k e0 first.replacementETT tau T2) :
    exists composite : CorrespondingExtendedTashkinovTree G k e0 ett tau T2,
      composite.replacementInput = second.replacementInput /\
        HEq composite.replacementSeries second.replacementSeries /\
        HEq composite.replacementETT second.replacementETT := by
  classical
  have roundLink : second.replacementETT.rounds = ett.rounds :=
    second.rungAgreement.trans first.rungAgreement
  let transported : TashkinovSeries G k ett.rounds e0 second.replacementInput :=
    first.rungAgreement ▸ second.replacementSeries
  have seriesTransport : HEq transported second.replacementSeries := by
    simp [transported]
  have firstSeriesEq := replacementSeriesPresentation first
  let composite : CorrespondingExtendedTashkinovTree G k e0 ett tau T2 := {
    replacementInput := second.replacementInput
    replacementSeries := transported
    replacementETT := second.replacementETT
    rungAgreement := roundLink
    seriesPresentation := by
      exact HEq.trans second.seriesPresentation seriesTransport.symm
    finalGeneratingColoring := by
      have finalTransport := projectLast first.rungAgreement second.replacementSeries
      exact second.finalGeneratingColoring.trans (eq_of_heq finalTransport).symm
    ladderTreesAgree := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have secondStep := second.ladderTreesAgree middleIndex
      have firstStep := first.ladderTreesAgree i
      rw [firstSeriesEq] at secondStep
      have transportedCast := projectTree first.rungAgreement
        second.replacementSeries middleIndex
      have firstCast := projectTree first.rungAgreement.symm
        first.replacementSeries i
      have firstStepCast :
          (first.rungAgreement.symm ▸ first.replacementSeries).data.tree
              middleIndex.succ.castSucc =
            ett.series.data.tree i.succ.castSucc := by
        exact (eq_of_heq firstCast).trans firstStep
      have secondStepCast :
          second.replacementSeries.data.tree middleIndex.succ.castSucc =
            (first.rungAgreement.symm ▸ first.replacementSeries).data.tree
              middleIndex.succ.castSucc := by
        exact secondStep
      have transportedCastEq :
          transported.data.tree i.succ.castSucc =
            second.replacementSeries.data.tree middleIndex.succ.castSucc := by
        have indexBack : first.rungAgreement ▸ middleIndex = i := by
          exact castBack first.rungAgreement i
        convert (eq_of_heq transportedCast) using 1
        · simp [transported, indexBack]
      exact transportedCastEq.trans (secondStepCast.trans firstStepCast)
    storedColorsAgree := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have a := second.storedColorsAgree middleIndex
      rw [firstSeriesEq] at a
      have b := first.storedColorsAgree i
      have c := projectStored first.rungAgreement.symm first.replacementSeries i
      have d := projectStored first.rungAgreement second.replacementSeries middleIndex
      have hi : i = first.rungAgreement ▸ middleIndex := by
        exact (castBackPlus first.rungAgreement i).symm
      have dEq : transported.data.stored i =
          second.replacementSeries.data.stored middleIndex := by
        convert (eq_of_heq d) using 1
        simpa [transported, middleIndex, Fin.cast_eq_self] using congrArg
          (fun q => transported.data.stored q)
          hi
      exact dEq.trans (a.trans ((eq_of_heq c).trans b))
    connectingEdgesAgree := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have a := second.connectingEdgesAgree middleIndex
      rw [firstSeriesEq] at a
      have b := first.connectingEdgesAgree i
      have c := projectEdges first.rungAgreement.symm first.replacementSeries i
      have d := projectEdges first.rungAgreement second.replacementSeries middleIndex
      have hi : i = first.rungAgreement ▸ middleIndex := by
        exact (castBackPlus first.rungAgreement i).symm
      have dEq : transported.data.connectingEdges i =
          second.replacementSeries.data.connectingEdges middleIndex := by
        convert (eq_of_heq d) using 1
        simpa [transported, middleIndex, Fin.cast_eq_self] using congrArg
          (fun q => transported.data.connectingEdges q)
          hi
      exact dEq.trans (a.trans ((eq_of_heq c).trans b))
    extensionKindsAgree := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have a := second.extensionKindsAgree middleIndex
      rw [firstSeriesEq] at a
      have b := first.extensionKindsAgree i
      have c := projectKind first.rungAgreement.symm first.replacementSeries i
      have d := projectKind first.rungAgreement second.replacementSeries middleIndex
      have hi : i = first.rungAgreement ▸ middleIndex := by
        exact (castBackPlus first.rungAgreement i).symm
      have dEq : transported.data.kind i =
          second.replacementSeries.data.kind middleIndex := by
        convert (eq_of_heq d) using 1
        simpa [transported, middleIndex, Fin.cast_eq_self] using congrArg
          (fun q => transported.data.kind q)
          hi
      exact dEq.trans (a.trans ((eq_of_heq c).trans b))
    replacementProper := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have hc := projectColoring first.rungAgreement second.replacementSeries middleIndex
      have hi : i = first.rungAgreement ▸ middleIndex := by
        exact (castBackPlus first.rungAgreement i).symm
      have hcEq : transported.data.coloring i =
          second.replacementSeries.data.coloring middleIndex := by
        convert (eq_of_heq hc) using 1
        simpa [transported, middleIndex, Fin.cast_eq_self] using congrArg
          (fun q => transported.data.coloring q)
          hi
      rw [hcEq]
      exact second.replacementProper middleIndex
    replacementOneUncolored := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have hc := projectColoring first.rungAgreement second.replacementSeries middleIndex
      have hi : i = first.rungAgreement ▸ middleIndex := by
        exact (castBackPlus first.rungAgreement i).symm
      have hcEq : transported.data.coloring i =
          second.replacementSeries.data.coloring middleIndex := by
        convert (eq_of_heq hc) using 1
        simpa [transported, middleIndex, Fin.cast_eq_self] using congrArg
          (fun q => transported.data.coloring q)
          hi
      rw [hcEq]
      exact second.replacementOneUncolored middleIndex
    replacementStable := correspondingStableComposition first second }
  exact ⟨composite, rfl, seriesTransport, by rfl⟩

end GoldbergSeymour

end
