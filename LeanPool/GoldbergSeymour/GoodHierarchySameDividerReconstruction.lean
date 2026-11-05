/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.HierarchyStageMissingColors
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Good Hierarchy Same Divider Reconstruction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation610Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (generating sigma : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T generating) (J U : TreeSequence G e0)
  (replacementInputJ : PartialEdgeColoring E k)
  (replacementSeriesJ : TashkinovSeries G k ett.rounds e0 replacementInputJ)
  (finalGeneratingColoringJ : sigma = replacementSeriesJ.data.coloring (Fin.last ett.rounds))
  (ladderTreesAgreeJ :
   ∀ (i : Fin ett.rounds),
    replacementSeriesJ.data.tree i.succ.castSucc = ett.series.data.tree i.succ.castSucc)
  (storedColorsAgreeJ :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), replacementSeriesJ.data.stored i = ett.series.data.stored i)
  (connectingEdgesAgreeJ :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))),
    replacementSeriesJ.data.connectingEdges i = ett.series.data.connectingEdges i)
  (extensionKindsAgreeJ :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), replacementSeriesJ.data.kind i = ett.series.data.kind i)
  (replacementProperJ :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsProperEdgeColoring G (replacementSeriesJ.data.coloring i))
  (replacementOneUncoloredJ :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsOneEdgeUncolored (replacementSeriesJ.data.coloring i) e0)
  (replacementStableJ :
   ∀ (i : Fin ett.rounds),
    StableColoring (ett.series.data.tree i.succ.castSucc)
     (TashkinovStoredColors ett.series.data i.succ) (ett.series.data.coloring i.succ)
     (replacementSeriesJ.data.coloring i.succ))
  (roundsPositiveJ : (1 : ℕ) ≤ ett.rounds)
  (aboveJ :
   TreeSequenceInitialSegment
    (replacementSeriesJ.data.tree (⟨ett.rounds, (by omega)⟩ : Fin (ett.rounds + (2 : ℕ)))) J)
  (strictJ :
   (replacementSeriesJ.data.tree (⟨ett.rounds, (by omega)⟩ : Fin (ett.rounds + (2 : ℕ)))).length <
    J.length)
  (belowJ :
   TreeSequenceInitialSegment J (replacementSeriesJ.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
  (generatingJ : sigma = replacementSeriesJ.data.coloring (Fin.last ett.rounds))
  (seriesPresentationJ :
   { rounds := ett.rounds, roundsPositive := roundsPositiveJ, series := replacementSeriesJ,
      abovePenultimate := aboveJ, strictAbovePenultimate := strictJ, belowFinal := belowJ,
      generatingColoring := generatingJ :
      ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.series ≍
    replacementSeriesJ)
  (baseJ :
   HierarchyBase
    { replacementInput := replacementInputJ, replacementSeries := replacementSeriesJ,
      replacementETT :=
       {
        rounds := ett.rounds, roundsPositive := roundsPositiveJ, series := replacementSeriesJ,
        abovePenultimate := aboveJ, strictAbovePenultimate := strictJ, belowFinal := belowJ,
        generatingColoring := generatingJ :
        ExtendedTashkinovTree G k e0 replacementInputJ J sigma },
      rungAgreement :=
       Eq.refl
        { rounds := ett.rounds, roundsPositive := roundsPositiveJ, series := replacementSeriesJ,
          abovePenultimate := aboveJ, strictAbovePenultimate := strictJ, belowFinal := belowJ,
          generatingColoring := generatingJ :
          ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.rounds,
      seriesPresentation := seriesPresentationJ,
      finalGeneratingColoring := finalGeneratingColoringJ, ladderTreesAgree := ladderTreesAgreeJ,
      storedColorsAgree := storedColorsAgreeJ, connectingEdgesAgree := connectingEdgesAgreeJ,
      extensionKindsAgree := extensionKindsAgreeJ, replacementProper := replacementProperJ,
      replacementOneUncolored := replacementOneUncoloredJ, replacementStable := replacementStableJ :
      CorrespondingExtendedTashkinovTree G k e0 ett sigma J }.replacementETT
    sigma)
  (KJ :
   TashkinovHierarchy
    { replacementInput := replacementInputJ, replacementSeries := replacementSeriesJ,
      replacementETT :=
       {
        rounds := ett.rounds, roundsPositive := roundsPositiveJ, series := replacementSeriesJ,
        abovePenultimate := aboveJ, strictAbovePenultimate := strictJ, belowFinal := belowJ,
        generatingColoring := generatingJ :
        ExtendedTashkinovTree G k e0 replacementInputJ J sigma },
      rungAgreement :=
       Eq.refl
        { rounds := ett.rounds, roundsPositive := roundsPositiveJ, series := replacementSeriesJ,
          abovePenultimate := aboveJ, strictAbovePenultimate := strictJ, belowFinal := belowJ,
          generatingColoring := generatingJ :
          ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.rounds,
      seriesPresentation := seriesPresentationJ,
      finalGeneratingColoring := finalGeneratingColoringJ, ladderTreesAgree := ladderTreesAgreeJ,
      storedColorsAgree := storedColorsAgreeJ, connectingEdgesAgree := connectingEdgesAgreeJ,
      extensionKindsAgree := extensionKindsAgreeJ, replacementProper := replacementProperJ,
      replacementOneUncolored := replacementOneUncoloredJ, replacementStable := replacementStableJ :
      CorrespondingExtendedTashkinovTree G k e0 ett sigma J }.replacementETT
    baseJ)
  (replacementInputU : PartialEdgeColoring E k)
  (replacementSeriesU : TashkinovSeries G k ett.rounds e0 replacementInputU)
  (finalGeneratingColoringU : sigma = replacementSeriesU.data.coloring (Fin.last ett.rounds))
  (ladderTreesAgreeU :
   ∀ (i : Fin ett.rounds),
    replacementSeriesU.data.tree i.succ.castSucc = ett.series.data.tree i.succ.castSucc)
  (storedColorsAgreeU :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), replacementSeriesU.data.stored i = ett.series.data.stored i)
  (connectingEdgesAgreeU :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))),
    replacementSeriesU.data.connectingEdges i = ett.series.data.connectingEdges i)
  (extensionKindsAgreeU :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), replacementSeriesU.data.kind i = ett.series.data.kind i)
  (replacementProperU :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsProperEdgeColoring G (replacementSeriesU.data.coloring i))
  (replacementOneUncoloredU :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsOneEdgeUncolored (replacementSeriesU.data.coloring i) e0)
  (replacementStableU :
   ∀ (i : Fin ett.rounds),
    StableColoring (ett.series.data.tree i.succ.castSucc)
     (TashkinovStoredColors ett.series.data i.succ) (ett.series.data.coloring i.succ)
     (replacementSeriesU.data.coloring i.succ))
  (roundsPositiveU : (1 : ℕ) ≤ ett.1)
  (aboveU :
   TreeSequenceInitialSegment
    (replacementSeriesU.data.tree (⟨ett.1, (by omega)⟩ : Fin (ett.1 + (2 : ℕ)))) U)
  (strictU :
   (replacementSeriesU.data.tree (⟨ett.1, (by omega)⟩ : Fin (ett.1 + (2 : ℕ)))).length < U.length)
  (belowU :
   TreeSequenceInitialSegment U (replacementSeriesU.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
  (generatingU : sigma = replacementSeriesU.data.coloring (Fin.last ett.1))
  (seriesPresentationU :
   { rounds := ett.1, roundsPositive := roundsPositiveU, series := replacementSeriesU,
      abovePenultimate := aboveU, strictAbovePenultimate := strictU, belowFinal := belowU,
      generatingColoring := generatingU :
      ExtendedTashkinovTree G k e0 replacementInputU U sigma }.series ≍
    replacementSeriesU)
  (baseU :
   HierarchyBase
    { replacementInput := replacementInputU, replacementSeries := replacementSeriesU,
      replacementETT :=
       {
        rounds := ett.1, roundsPositive := roundsPositiveU, series := replacementSeriesU,
        abovePenultimate := aboveU, strictAbovePenultimate := strictU, belowFinal := belowU,
        generatingColoring := generatingU :
        ExtendedTashkinovTree G k e0 replacementInputU U sigma },
      rungAgreement :=
       Eq.refl
        { rounds := ett.1, roundsPositive := roundsPositiveU, series := replacementSeriesU,
          abovePenultimate := aboveU, strictAbovePenultimate := strictU, belowFinal := belowU,
          generatingColoring := generatingU :
          ExtendedTashkinovTree G k e0 replacementInputU U sigma }.rounds,
      seriesPresentation := seriesPresentationU,
      finalGeneratingColoring := finalGeneratingColoringU, ladderTreesAgree := ladderTreesAgreeU,
      storedColorsAgree := storedColorsAgreeU, connectingEdgesAgree := connectingEdgesAgreeU,
      extensionKindsAgree := extensionKindsAgreeU, replacementProper := replacementProperU,
      replacementOneUncolored := replacementOneUncoloredU, replacementStable := replacementStableU :
      CorrespondingExtendedTashkinovTree G k e0 ett sigma U }.replacementETT
    sigma)
  (hcore : baseU.core = baseJ.core) (segmentJU : TreeSequenceInitialSegment J U)
  (segmentTrans :
   ∀ {A B C : TreeSequence G e0},
    TreeSequenceInitialSegment A B →
     TreeSequenceInitialSegment B C → TreeSequenceInitialSegment A C)
  (finalTreeEq :
   replacementSeriesU.data.tree (Fin.last ett.rounds).castSucc =
    replacementSeriesJ.data.tree (Fin.last ett.rounds).castSucc),
  TashkinovStoredColors replacementSeriesU.data (Fin.last ett.rounds) =
    TashkinovStoredColors replacementSeriesJ.data (Fin.last ett.rounds) →
   let kuStage : Fin (KJ.dividerCount + (2 : ℕ)) → TreeSequence G e0 :=
    fun (j : Fin (KJ.dividerCount + (2 : ℕ))) =>
    if (↑j : ℕ) = KJ.dividerCount + (1 : ℕ) then U
    else KJ.stage (⟨(↑j : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ)));
   ∀
    (kuStageOld : ∀ (j : Fin (KJ.dividerCount + (1 : ℕ))), kuStage j.castSucc = KJ.stage j.castSucc)
    (kuStageLast : kuStage (Fin.last (KJ.dividerCount + (1 : ℕ))) = U)
    (kuStageAt :
     ∀ (j : Fin (KJ.dividerCount + (2 : ℕ))) (hj : (↑j : ℕ) ≤ KJ.dividerCount),
      kuStage j = KJ.stage (⟨(↑j : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ))))
    (kuNested :
     ∀ (j : Fin (KJ.dividerCount + (1 : ℕ))),
      TreeSequenceInitialSegment (kuStage j.castSucc) (kuStage j.succ))
    (kuStrict :
     ∀ (j : Fin (KJ.dividerCount + (1 : ℕ))),
      (kuStage j.castSucc).length < (kuStage j.succ).length),
    let kuDividerPosition : Fin KJ.dividerCount → Fin (U.length + (1 : ℕ)) :=
     fun (i : Fin KJ.dividerCount) =>
     (⟨(↑(KJ.dividerPosition i) : ℕ),
       lt_of_lt_of_le (KJ.dividerPosition i).isLt (Nat.succ_le_succ segmentJU.1)⟩ :
      Fin (U.length + (1 : ℕ)));
    let _ :
     TashkinovHierarchy
      {
       rounds := ett.rounds, roundsPositive := roundsPositiveU, series := replacementSeriesU,
       abovePenultimate := aboveU, strictAbovePenultimate := strictU, belowFinal := belowU,
       generatingColoring := generatingU : ExtendedTashkinovTree G k e0 replacementInputU U sigma }
      baseU :=
     {
      dividerCount := KJ.dividerCount, stage := kuStage,
      baseStage :=
       Trans.trans
        (Trans.trans (id (kuStageOld (0 : Fin (KJ.dividerCount + (1 : ℕ))))) KJ.baseStage)
        (Eq.symm finalTreeEq),
      terminalStage := kuStageLast, nested := kuNested, strict := kuStrict,
      dividerPosition := kuDividerPosition,
      dividerPositive := fun (i : Fin KJ.dividerCount) => KJ.dividerPositive i,
      dividerIncreasing := fun (i j : Fin KJ.dividerCount) (hij : (↑i : ℕ) < (↑j : ℕ)) =>
       KJ.dividerIncreasing i j hij,
      dividerStage := fun (i : Fin KJ.dividerCount) =>
       have hstageIndex : (↑i : ℕ) + (1 : ℕ) ≤ KJ.dividerCount := Nat.succ_le_of_lt i.isLt;
       have hstage :
        kuStage (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ))) =
         KJ.stage (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ))) :=
        kuStageAt (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ))) hstageIndex;
       have hposJ : (↑(KJ.dividerPosition i) : ℕ) ≤ J.length :=
        Nat.le_of_lt_succ (KJ.dividerPosition i).isLt;
       have hposU : (↑(KJ.dividerPosition i) : ℕ) ≤ U.length := le_trans hposJ segmentJU.1;
       have prefixEq :
        TreeSequencePrefix U (↑(KJ.dividerPosition i) : ℕ) (KJ.dividerPositive i) hposU =
         TreeSequencePrefix J (↑(KJ.dividerPosition i) : ℕ) (KJ.dividerPositive i) hposJ :=
        Eq.mpr
         (id
          (congrArg
           (fun (_a : TreeSequence G e0) =>
            _a = TreeSequencePrefix J (↑(KJ.dividerPosition i) : ℕ) (KJ.dividerPositive i) hposJ)
           (TreeSequencePrefix.eq_1 U (↑(KJ.dividerPosition i) : ℕ) (KJ.dividerPositive i) hposU)))
         (Eq.mpr
          (id
           (congrArg
            (fun (_a : TreeSequence G e0) =>
             { length := (↑(KJ.dividerPosition i) : ℕ), positive := KJ.dividerPositive i,
               vertex := fun (i_1 : Fin ((↑(KJ.dividerPosition i) : ℕ) + (1 : ℕ))) =>
                U.vertex (Fin.castLE ((by omega)) i_1),
               edge := fun (i_1 : Fin (↑(KJ.dividerPosition i) : ℕ)) =>
                U.edge (Fin.castLE hposU i_1),
               vertex_injective :=
                (by
                 intro _ _ h
                 apply Fin.ext
                 simpa only [Fin.castLE] using congrArg (fun x => x.val) ((U).vertex_injective h)),
               edge_injective :=
                (by
                 intro _ _ h
                 apply Fin.ext
                 simpa only [Fin.castLE] using congrArg (fun x => x.val) ((U).edge_injective h)),
               first_edge := (by simpa only [Fin.castLE] using (U).first_edge),
               attaches :=
                (by
                 intro j;
                 simpa only [Fin.castLE, Fin.castLT, Fin.succ] using
                  (U).attaches (Fin.castLE (hposU) j)) :
               TreeSequence G e0 } =
              _a)
            (TreeSequencePrefix.eq_1 J (↑(KJ.dividerPosition i) : ℕ) (KJ.dividerPositive i) hposJ)))
          ((fun {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {e0 : E} (length : ℕ)
             (positive : (1 : ℕ) ≤ length) (vertex vertex_1 : Fin (length + (1 : ℕ)) → V)
             (e_vertex : vertex = vertex_1) =>
            Eq.rec (motive :=
             fun (vertex_2 : Fin (length + (1 : ℕ)) → V) (e_vertex : vertex = vertex_2) =>
             ∀ (edge edge_1 : Fin length → E) (e_edge : edge = edge_1)
              (vertex_injective : Function.Injective vertex)
              (edge_injective : Function.Injective edge)
              (first_edge : edge (⟨(0 : ℕ), positive⟩ : Fin length) = e0)
              (attaches :
               ∀ (j : Fin length),
                ∃ (i : Fin ((↑j : ℕ) + (1 : ℕ))),
                 G.ends (edge j) =
                  s(vertex j.succ,
                   vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))))),
              { length := length, positive := positive, vertex := vertex, edge := edge,
                vertex_injective := vertex_injective, edge_injective := edge_injective,
                first_edge := first_edge, attaches := attaches : TreeSequence G e0 } =
               {
                length := length, positive := positive, vertex := vertex_2, edge := edge_1,
                vertex_injective := e_vertex ▸ vertex_injective,
                edge_injective := e_edge ▸ edge_injective, first_edge := e_edge ▸ first_edge,
                attaches :=
                 Eq.ndrec (motive := fun (vertex : Fin (length + (1 : ℕ)) → V) =>
                  ∀ (j : Fin length),
                   ∃ (i : Fin ((↑j : ℕ) + (1 : ℕ))),
                    G.ends (edge_1 j) =
                     s(vertex j.succ,
                      vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)))))
                  (Eq.ndrec (motive := fun (edge : Fin length → E) =>
                   ∀ (j : Fin length),
                    ∃ (i : Fin ((↑j : ℕ) + (1 : ℕ))),
                     G.ends (edge j) =
                      s(vertex j.succ,
                       vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)))))
                   attaches e_edge)
                  e_vertex :
                TreeSequence G e0 })
             (fun (edge edge_1 : Fin length → E) (e_edge : edge = edge_1) =>
              Eq.rec (motive := fun (edge_2 : Fin length → E) (e_edge : edge = edge_2) =>
               ∀ (vertex_injective : Function.Injective vertex)
                (edge_injective : Function.Injective edge)
                (first_edge : edge (⟨(0 : ℕ), positive⟩ : Fin length) = e0)
                (attaches :
                 ∀ (j : Fin length),
                  ∃ (i : Fin ((↑j : ℕ) + (1 : ℕ))),
                   G.ends (edge j) =
                    s(vertex j.succ,
                     vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))))),
                { length := length, positive := positive, vertex := vertex, edge := edge,
                  vertex_injective := vertex_injective, edge_injective := edge_injective,
                  first_edge := first_edge, attaches := attaches : TreeSequence G e0 } =
                 {
                  length := length, positive := positive, vertex := vertex, edge := edge_2,
                  vertex_injective := Eq.refl vertex ▸ vertex_injective,
                  edge_injective := e_edge ▸ edge_injective, first_edge := e_edge ▸ first_edge,
                  attaches :=
                   Eq.ndrec (motive := fun (vertex : Fin (length + (1 : ℕ)) → V) =>
                    ∀ (j : Fin length),
                     ∃ (i : Fin ((↑j : ℕ) + (1 : ℕ))),
                      G.ends (edge_2 j) =
                       s(vertex j.succ,
                        vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)))))
                    (Eq.ndrec (motive := fun (edge : Fin length → E) =>
                     ∀ (j : Fin length),
                      ∃ (i : Fin ((↑j : ℕ) + (1 : ℕ))),
                       G.ends (edge j) =
                        s(vertex j.succ,
                         vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)))))
                     attaches e_edge)
                    (Eq.refl vertex) :
                  TreeSequence G e0 })
               (fun (vertex_injective : Function.Injective vertex)
                 (edge_injective : Function.Injective edge)
                 (first_edge : edge (⟨(0 : ℕ), positive⟩ : Fin length) = e0)
                 (attaches :
                  ∀ (j : Fin length),
                   ∃ (i : Fin ((↑j : ℕ) + (1 : ℕ))),
                    G.ends (edge j) =
                     s(vertex j.succ,
                      vertex (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))))) =>
                Eq.refl
                 {
                  length := length, positive := positive, vertex := vertex, edge := edge,
                  vertex_injective := vertex_injective, edge_injective := edge_injective,
                  first_edge := first_edge, attaches := attaches : TreeSequence G e0 })
               e_edge)
             e_vertex)
           (↑(KJ.dividerPosition i) : ℕ) (KJ.dividerPositive i)
           (fun (i_1 : Fin ((↑(KJ.dividerPosition i) : ℕ) + (1 : ℕ))) =>
            U.vertex (Fin.castLE ((by omega)) i_1))
           (fun (i_1 : Fin ((↑(KJ.dividerPosition i) : ℕ) + (1 : ℕ))) =>
            J.vertex (Fin.castLE ((by omega)) i_1))
           (funext fun (x : Fin ((↑(KJ.dividerPosition i) : ℕ) + (1 : ℕ))) =>
            have hv :
             U.vertex
               (Fin.castLE (Nat.succ_le_succ segmentJU.1) (Fin.castLE (Nat.succ_le_succ hposJ) x)) =
              J.vertex (Fin.castLE (Nat.succ_le_succ hposJ) x) :=
             segmentJU.2.left (Fin.castLE (Nat.succ_le_succ hposJ) x);
            id
             (Eq.mp
              (congrFun'
               (congrArg Eq
                (congrArg U.vertex
                 (Fin.castLE_castLE (Nat.succ_le_succ hposJ) (Nat.succ_le_succ segmentJU.1) x)))
               (J.vertex (Fin.castLE (Nat.succ_le_succ hposJ) x)))
              hv))
           (fun (i_1 : Fin (↑(KJ.dividerPosition i) : ℕ)) => U.edge (Fin.castLE hposU i_1))
           (fun (i_1 : Fin (↑(KJ.dividerPosition i) : ℕ)) => J.edge (Fin.castLE hposJ i_1))
           (funext fun (x : Fin (↑(KJ.dividerPosition i) : ℕ)) =>
            have he :
             U.edge (Fin.castLE segmentJU.1 (Fin.castLE hposJ x)) = J.edge (Fin.castLE hposJ x) :=
             segmentJU.2.right (Fin.castLE hposJ x);
            id
             (Eq.mp
              (congrFun' (congrArg Eq (congrArg U.edge (Fin.castLE_castLE hposJ segmentJU.1 x)))
               (J.edge (Fin.castLE hposJ x)))
              he))
           ((by
            intro _ _ h
            apply Fin.ext
            simpa only [Fin.castLE] using congrArg (fun x => x.val) ((U).vertex_injective h)))
           ((by
            intro _ _ h
            apply Fin.ext
            simpa only [Fin.castLE] using congrArg (fun x => x.val) ((U).edge_injective h)))
           ((by simpa only [Fin.castLE] using (U).first_edge))
           ((by
            intro j;
            simpa only [Fin.castLE, Fin.castLT, Fin.succ] using
             (U).attaches (Fin.castLE (hposU) j)))));
       Eq.mpr
        (id
         (congrArg
          (fun (_a : TreeSequence G e0) =>
           kuStage (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ))) = _a)
          prefixEq))
        (Eq.mpr
         (id
          (congrArg
           (fun (_a : TreeSequence G e0) =>
            _a = TreeSequencePrefix J (↑(KJ.dividerPosition i) : ℕ) (KJ.dividerPositive i) hposJ)
           hstage))
         (id (KJ.dividerStage i))),
      coreInsideFirst :=
       if hd : KJ.dividerCount = (0 : ℕ) then
        have hstage : kuStage (⟨(1 : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ))) = U :=
         of_eq_true
          (Eq.trans
           (congrFun'
            (congrArg Eq
             (Eq.trans
              (congrFun'
               (funext fun (j : Fin (KJ.dividerCount + (2 : ℕ))) =>
                ite_congr
                 (congrArg (Eq (↑j : ℕ))
                  (Eq.trans (congrFun' (congrArg HAdd.hAdd hd) (1 : ℕ)) (zero_add (1 : ℕ))))
                 (fun (_ : (↑j : ℕ) = (1 : ℕ)) => Eq.refl U) fun (_ : ¬(↑j : ℕ) = (1 : ℕ)) =>
                 Eq.refl (KJ.stage j))
               (1 : Fin (KJ.dividerCount + (2 : ℕ))))
              (ite_eq_left_of_eq_true U (KJ.stage (1 : Fin (KJ.dividerCount + (2 : ℕ))))
               (Eq.trans
                (congrFun'
                 (congrArg Eq
                  (Eq.trans
                   (congrArg (HMod.hMod (1 : ℕ))
                    (Eq.trans (congrFun' (congrArg HAdd.hAdd hd) (2 : ℕ)) (zero_add (2 : ℕ))))
                   (Nat.mod_succ (1 : ℕ))))
                 (1 : ℕ))
                (eq_self (1 : ℕ))))))
            U)
           (eq_self U));
        Eq.mpr
         (id
          (congrArg (fun (_a : TreeSequence G e0) => TreeSequenceInitialSegment baseU.core _a)
           hstage))
         (have hold :
          TreeSequenceInitialSegment baseJ.core
           (KJ.stage (⟨(1 : ℕ), (by omega)⟩ : Fin (KJ.dividerCount + (2 : ℕ)))) :=
          KJ.coreInsideFirst;
         have holdStage : KJ.stage (⟨(1 : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ))) = J :=
          Eq.mpr
           (eq_of_heq
            ((fun (α : Type (max u_1 u_2)) (a a' : α) (e'_2 : a = a') (a_1 : α) =>
              Eq.casesOn (motive := fun (a_2 : α) (x : a = a_2) =>
               a' = a_2 → e'_2 ≍ x → (a = a_1) ≍ (a' = a_1)) e'_2
               (fun (h : a' = a) =>
                Eq.ndrec (motive := fun (a' : α) =>
                 ∀ (e_2 : a = a'), e_2 ≍ Eq.refl a → (a = a_1) ≍ (a' = a_1))
                 (fun (e_2 : a = a) (_ : e_2 ≍ Eq.refl a) => HEq.refl (a = a_1)) (Eq.symm h) e'_2)
               (Eq.refl a') (HEq.refl e'_2))
             (TreeSequence G e0) (KJ.stage (⟨(1 : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ))))
             (KJ.stage (Fin.last (KJ.dividerCount + (1 : ℕ))))
             (congrArg KJ.stage
              (Fin.ext
               (of_eq_true
                (Eq.trans
                 (congrArg (Eq (1 : ℕ))
                  (Eq.trans (congrFun' (congrArg HAdd.hAdd hd) (1 : ℕ)) (zero_add (1 : ℕ))))
                 (eq_self (1 : ℕ))))))
             J))
           KJ.terminalStage;
         Eq.mpr
          (id (congrArg (fun (_a : TreeSequence G e0) => TreeSequenceInitialSegment _a U) hcore))
          (segmentTrans
           (Eq.mp
            (congrArg (fun (_a : TreeSequence G e0) => TreeSequenceInitialSegment baseJ.core _a)
             holdStage)
            hold)
           segmentJU))
       else
        have hstage :
         kuStage (⟨(1 : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ))) =
          KJ.stage (⟨(1 : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ))) :=
         kuStageAt (⟨(1 : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ)))
          (Nat.one_le_iff_ne_zero.mpr hd);
        Eq.mpr
         (id
          (congrArg (fun (_a : TreeSequence G e0) => TreeSequenceInitialSegment baseU.core _a)
           hstage))
         (Eq.mpr
          (id
           (congrArg
            (fun (_a : TreeSequence G e0) =>
             TreeSequenceInitialSegment _a
              (KJ.stage (⟨(1 : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ)))))
            hcore))
          KJ.coreInsideFirst) :
      TashkinovHierarchy
       {
        rounds := ett.rounds, roundsPositive := roundsPositiveU, series := replacementSeriesU,
        abovePenultimate := aboveU, strictAbovePenultimate := strictU, belowFinal := belowU,
        generatingColoring := generatingU : ExtendedTashkinovTree G k e0 replacementInputU U sigma }
       baseU };
    ∃ (KU :
     TashkinovHierarchy
      { replacementInput := replacementInputU, replacementSeries := replacementSeriesU,
        replacementETT :=
         {
          rounds := ett.1, roundsPositive := roundsPositiveU, series := replacementSeriesU,
          abovePenultimate := aboveU, strictAbovePenultimate := strictU, belowFinal := belowU,
          generatingColoring := generatingU :
          ExtendedTashkinovTree G k e0 replacementInputU U sigma },
        rungAgreement :=
         Eq.refl
          { rounds := ett.1, roundsPositive := roundsPositiveU, series := replacementSeriesU,
            abovePenultimate := aboveU, strictAbovePenultimate := strictU, belowFinal := belowU,
            generatingColoring := generatingU :
            ExtendedTashkinovTree G k e0 replacementInputU U sigma }.rounds,
        seriesPresentation := seriesPresentationU,
        finalGeneratingColoring := finalGeneratingColoringU, ladderTreesAgree := ladderTreesAgreeU,
        storedColorsAgree := storedColorsAgreeU, connectingEdgesAgree := connectingEdgesAgreeU,
        extensionKindsAgree := extensionKindsAgreeU, replacementProper := replacementProperU,
        replacementOneUncolored := replacementOneUncoloredU,
        replacementStable := replacementStableU :
        CorrespondingExtendedTashkinovTree G k e0 ett sigma U }.replacementETT
      baseU)
     (hcount : KU.dividerCount = KJ.dividerCount),
     (∀ (j : Fin (KU.dividerCount + (1 : ℕ))),
       let jo : Fin (KJ.dividerCount + (1 : ℕ)) :=
        Fin.cast (congrArg (fun (n : ℕ) => n + (1 : ℕ)) hcount) j;
       KU.stage j.castSucc = KJ.stage jo.castSucc ∧
        HierarchyStarredStage KU j = HierarchyStarredStage KJ jo ∧
         HierarchyStoredColorsAt KU j = HierarchyStoredColorsAt KJ jo ∧
          HierarchyStageMissingColors KU j = HierarchyStageMissingColors KJ jo) ∧
      ∀ (i : Fin KU.dividerCount),
       (↑(KU.dividerPosition i) : ℕ) = (↑(KJ.dividerPosition (Fin.cast hcount i)) : ℕ)

private abbrev helperBranch126Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (generating sigma : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T generating) (J U : TreeSequence G e0)
  (_ : TashkinovAugmentationSequence sigma J U) (replacementInputJ : PartialEdgeColoring E k)
  (replacementSeriesJ : TashkinovSeries G k ett.rounds e0 replacementInputJ)
  (finalGeneratingColoringJ : sigma = replacementSeriesJ.data.coloring (Fin.last ett.rounds))
  (ladderTreesAgreeJ :
   ∀ (i : Fin ett.rounds),
    replacementSeriesJ.data.tree i.succ.castSucc = ett.series.data.tree i.succ.castSucc)
  (storedColorsAgreeJ :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), replacementSeriesJ.data.stored i = ett.series.data.stored i)
  (connectingEdgesAgreeJ :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))),
    replacementSeriesJ.data.connectingEdges i = ett.series.data.connectingEdges i)
  (extensionKindsAgreeJ :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), replacementSeriesJ.data.kind i = ett.series.data.kind i)
  (replacementProperJ :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsProperEdgeColoring G (replacementSeriesJ.data.coloring i))
  (replacementOneUncoloredJ :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsOneEdgeUncolored (replacementSeriesJ.data.coloring i) e0)
  (replacementStableJ :
   ∀ (i : Fin ett.rounds),
    StableColoring (ett.series.data.tree i.succ.castSucc)
     (TashkinovStoredColors ett.series.data i.succ) (ett.series.data.coloring i.succ)
     (replacementSeriesJ.data.coloring i.succ))
  (roundsPositiveJ : (1 : ℕ) ≤ ett.1)
  (aboveJ :
   TreeSequenceInitialSegment
    (replacementSeriesJ.data.tree (⟨ett.1, (by omega)⟩ : Fin (ett.1 + (2 : ℕ)))) J)
  (strictJ :
   (replacementSeriesJ.data.tree (⟨ett.1, (by omega)⟩ : Fin (ett.1 + (2 : ℕ)))).length < J.length)
  (belowJ :
   TreeSequenceInitialSegment J (replacementSeriesJ.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
  (generatingJ : sigma = replacementSeriesJ.data.coloring (Fin.last ett.1))
  (seriesPresentationJ :
   { rounds := ett.1, roundsPositive := roundsPositiveJ, series := replacementSeriesJ,
      abovePenultimate := aboveJ, strictAbovePenultimate := strictJ, belowFinal := belowJ,
      generatingColoring := generatingJ :
      ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.series ≍
    replacementSeriesJ)
  (baseJ :
   HierarchyBase
    { replacementInput := replacementInputJ, replacementSeries := replacementSeriesJ,
      replacementETT :=
       {
        rounds := ett.1, roundsPositive := roundsPositiveJ, series := replacementSeriesJ,
        abovePenultimate := aboveJ, strictAbovePenultimate := strictJ, belowFinal := belowJ,
        generatingColoring := generatingJ :
        ExtendedTashkinovTree G k e0 replacementInputJ J sigma },
      rungAgreement :=
       Eq.refl
        { rounds := ett.1, roundsPositive := roundsPositiveJ, series := replacementSeriesJ,
          abovePenultimate := aboveJ, strictAbovePenultimate := strictJ, belowFinal := belowJ,
          generatingColoring := generatingJ :
          ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.rounds,
      seriesPresentation := seriesPresentationJ,
      finalGeneratingColoring := finalGeneratingColoringJ, ladderTreesAgree := ladderTreesAgreeJ,
      storedColorsAgree := storedColorsAgreeJ, connectingEdgesAgree := connectingEdgesAgreeJ,
      extensionKindsAgree := extensionKindsAgreeJ, replacementProper := replacementProperJ,
      replacementOneUncolored := replacementOneUncoloredJ, replacementStable := replacementStableJ :
      CorrespondingExtendedTashkinovTree G k e0 ett sigma J }.replacementETT
    sigma)
  (KJ :
   TashkinovHierarchy
    { replacementInput := replacementInputJ, replacementSeries := replacementSeriesJ,
      replacementETT :=
       {
        rounds := ett.1, roundsPositive := roundsPositiveJ, series := replacementSeriesJ,
        abovePenultimate := aboveJ, strictAbovePenultimate := strictJ, belowFinal := belowJ,
        generatingColoring := generatingJ :
        ExtendedTashkinovTree G k e0 replacementInputJ J sigma },
      rungAgreement :=
       Eq.refl
        { rounds := ett.1, roundsPositive := roundsPositiveJ, series := replacementSeriesJ,
          abovePenultimate := aboveJ, strictAbovePenultimate := strictJ, belowFinal := belowJ,
          generatingColoring := generatingJ :
          ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.rounds,
      seriesPresentation := seriesPresentationJ,
      finalGeneratingColoring := finalGeneratingColoringJ, ladderTreesAgree := ladderTreesAgreeJ,
      storedColorsAgree := storedColorsAgreeJ, connectingEdgesAgree := connectingEdgesAgreeJ,
      extensionKindsAgree := extensionKindsAgreeJ, replacementProper := replacementProperJ,
      replacementOneUncolored := replacementOneUncoloredJ, replacementStable := replacementStableJ :
      CorrespondingExtendedTashkinovTree G k e0 ett sigma J }.replacementETT
    baseJ)
  (replacementInputU : PartialEdgeColoring E k)
  (replacementSeriesU : TashkinovSeries G k ett.rounds e0 replacementInputU)
  (finalGeneratingColoringU : sigma = replacementSeriesU.data.coloring (Fin.last ett.rounds))
  (ladderTreesAgreeU :
   ∀ (i : Fin ett.rounds),
    replacementSeriesU.data.tree i.succ.castSucc = ett.series.data.tree i.succ.castSucc)
  (storedColorsAgreeU :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), replacementSeriesU.data.stored i = ett.series.data.stored i)
  (connectingEdgesAgreeU :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))),
    replacementSeriesU.data.connectingEdges i = ett.series.data.connectingEdges i)
  (extensionKindsAgreeU :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), replacementSeriesU.data.kind i = ett.series.data.kind i)
  (replacementProperU :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsProperEdgeColoring G (replacementSeriesU.data.coloring i))
  (replacementOneUncoloredU :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsOneEdgeUncolored (replacementSeriesU.data.coloring i) e0)
  (replacementStableU :
   ∀ (i : Fin ett.rounds),
    StableColoring (ett.series.data.tree i.succ.castSucc)
     (TashkinovStoredColors ett.series.data i.succ) (ett.series.data.coloring i.succ)
     (replacementSeriesU.data.coloring i.succ))
  (roundsU : ℕ) (roundsPositiveU : (1 : ℕ) ≤ roundsU)
  (replacementDataU : TashkinovSeries G k roundsU e0 replacementInputU)
  (aboveU :
   TreeSequenceInitialSegment
    (replacementDataU.data.tree (⟨roundsU, (by omega)⟩ : Fin (roundsU + (2 : ℕ)))) U)
  (strictU :
   (replacementDataU.data.tree (⟨roundsU, (by omega)⟩ : Fin (roundsU + (2 : ℕ)))).length < U.length)
  (belowU :
   TreeSequenceInitialSegment U (replacementDataU.data.tree (Fin.last (roundsU + (1 : ℕ)))))
  (generatingU : sigma = replacementDataU.data.coloring (Fin.last roundsU))
  (rungAgreementU :
   { rounds := roundsU, roundsPositive := roundsPositiveU, series := replacementDataU,
      abovePenultimate := aboveU, strictAbovePenultimate := strictU, belowFinal := belowU,
      generatingColoring := generatingU :
      ExtendedTashkinovTree G k e0 replacementInputU U sigma }.rounds =
    ett.rounds)
  (seriesPresentationU :
   { rounds := roundsU, roundsPositive := roundsPositiveU, series := replacementDataU,
      abovePenultimate := aboveU, strictAbovePenultimate := strictU, belowFinal := belowU,
      generatingColoring := generatingU :
      ExtendedTashkinovTree G k e0 replacementInputU U sigma }.series ≍
    replacementSeriesU)
  (baseU :
   HierarchyBase
    { replacementInput := replacementInputU, replacementSeries := replacementSeriesU,
      replacementETT :=
       {
        rounds := roundsU, roundsPositive := roundsPositiveU, series := replacementDataU,
        abovePenultimate := aboveU, strictAbovePenultimate := strictU, belowFinal := belowU,
        generatingColoring := generatingU :
        ExtendedTashkinovTree G k e0 replacementInputU U sigma },
      rungAgreement := rungAgreementU, seriesPresentation := seriesPresentationU,
      finalGeneratingColoring := finalGeneratingColoringU, ladderTreesAgree := ladderTreesAgreeU,
      storedColorsAgree := storedColorsAgreeU, connectingEdgesAgree := connectingEdgesAgreeU,
      extensionKindsAgree := extensionKindsAgreeU, replacementProper := replacementProperU,
      replacementOneUncolored := replacementOneUncoloredU, replacementStable := replacementStableU :
      CorrespondingExtendedTashkinovTree G k e0 ett sigma U }.replacementETT
    sigma)
  (_ : baseU.core = baseJ.core),
  ∃ (KU :
   TashkinovHierarchy
    { replacementInput := replacementInputU, replacementSeries := replacementSeriesU,
      replacementETT :=
       {
        rounds := roundsU, roundsPositive := roundsPositiveU, series := replacementDataU,
        abovePenultimate := aboveU, strictAbovePenultimate := strictU, belowFinal := belowU,
        generatingColoring := generatingU :
        ExtendedTashkinovTree G k e0 replacementInputU U sigma },
      rungAgreement := rungAgreementU, seriesPresentation := seriesPresentationU,
      finalGeneratingColoring := finalGeneratingColoringU, ladderTreesAgree := ladderTreesAgreeU,
      storedColorsAgree := storedColorsAgreeU, connectingEdgesAgree := connectingEdgesAgreeU,
      extensionKindsAgree := extensionKindsAgreeU, replacementProper := replacementProperU,
      replacementOneUncolored := replacementOneUncoloredU, replacementStable := replacementStableU :
      CorrespondingExtendedTashkinovTree G k e0 ett sigma U }.replacementETT
    baseU)
   (hcount : KU.dividerCount = KJ.dividerCount),
   (∀ (j : Fin (KU.dividerCount + (1 : ℕ))),
     let jo : Fin (KJ.dividerCount + (1 : ℕ)) :=
      Fin.cast (congrArg (fun (n : ℕ) => n + (1 : ℕ)) hcount) j;
     KU.stage j.castSucc = KJ.stage jo.castSucc ∧
      HierarchyStarredStage KU j = HierarchyStarredStage KJ jo ∧
       HierarchyStoredColorsAt KU j = HierarchyStoredColorsAt KJ jo ∧
        HierarchyStageMissingColors KU j = HierarchyStageMissingColors KJ jo) ∧
    ∀ (i : Fin KU.dividerCount),
     (↑(KU.dividerPosition i) : ℕ) = (↑(KJ.dividerPosition (Fin.cast hcount i)) : ℕ)

private theorem helper_terminalStoredEq_231.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (replacementInputJ : PartialEdgeColoring E k)
      (replacementSeriesJ : TashkinovSeries G k ett.rounds e0 replacementInputJ)
      (replacementInputU : PartialEdgeColoring E k)
      (replacementSeriesU : TashkinovSeries G k ett.rounds e0 replacementInputU),
    (∀ (i : Fin (ett.rounds + (1 : ℕ))),
        replacementSeriesU.data.stored i = replacementSeriesJ.data.stored i) →
    TreeMissingColors (replacementSeriesU.data.coloring (Fin.last ett.rounds))
          (replacementSeriesU.data.tree (Fin.last ett.rounds).castSucc) =
        TreeMissingColors (replacementSeriesJ.data.coloring (Fin.last ett.rounds))
          (replacementSeriesJ.data.tree (Fin.last ett.rounds).castSucc) →
    TashkinovStoredColors replacementSeriesU.data (Fin.last ett.rounds) =
      TashkinovStoredColors replacementSeriesJ.data (Fin.last ett.rounds) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett replacementInputJ replacementSeriesJ
      replacementInputU replacementSeriesU storedEntryEq finalMissingEq
  unfold TashkinovStoredColors
  have hnonzero : (Fin.last ett.rounds).val ≠ 0 := by
    simpa using Nat.ne_of_gt (Nat.zero_lt_of_lt ett.roundsPositive)
  simp only [ite_eq_right hnonzero]
  ext c
  simp only [Finset.mem_sdiff, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨i, hi, hc⟩, hn⟩
    refine ⟨⟨i, hi, ?_⟩, ?_⟩
    · by_cases hle : i.val ≤ (Fin.last ett.rounds).val
      · simp only [ite_eq_left hle] at hc ⊢
        simpa [storedEntryEq i] using hc
      · simp only [ite_eq_right hle] at hc ⊢
        exact hc
    · rwa [finalMissingEq] at hn
  · rintro ⟨⟨i, hi, hc⟩, hn⟩
    refine ⟨⟨i, hi, ?_⟩, ?_⟩
    · by_cases hle : i.val ≤ (Fin.last ett.rounds).val
      · simp only [ite_eq_left hle] at hc ⊢
        simpa [storedEntryEq i] using hc
      · simp only [ite_eq_right hle] at hc ⊢
        exact hc
    · rwa [finalMissingEq]

private theorem helper_kuNested_276.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating sigma : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (J U : TreeSequence G e0)
      (replacementInputJ : PartialEdgeColoring E k)
      (replacementSeriesJ : TashkinovSeries G k ett.rounds e0 replacementInputJ)
      (finalGeneratingColoringJ :
        sigma = replacementSeriesJ.data.coloring (Fin.last ett.rounds))
      (ladderTreesAgreeJ :
        ∀ (i : Fin ett.rounds),
          replacementSeriesJ.data.tree i.succ.castSucc =
            ett.series.data.tree i.succ.castSucc)
      (storedColorsAgreeJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          replacementSeriesJ.data.stored i = ett.series.data.stored i)
      (connectingEdgesAgreeJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          replacementSeriesJ.data.connectingEdges i = ett.series.data.connectingEdges i)
      (extensionKindsAgreeJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          replacementSeriesJ.data.kind i = ett.series.data.kind i)
      (replacementProperJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          IsProperEdgeColoring G (replacementSeriesJ.data.coloring i))
      (replacementOneUncoloredJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          IsOneEdgeUncolored (replacementSeriesJ.data.coloring i) e0)
      (replacementStableJ :
        ∀ (i : Fin ett.rounds),
          StableColoring (ett.series.data.tree i.succ.castSucc)
            (TashkinovStoredColors ett.series.data i.succ) (ett.series.data.coloring i.succ)
            (replacementSeriesJ.data.coloring i.succ))
      (roundsPositiveJ : (1 : ℕ) ≤ ett.rounds)
      (aboveJ :
        TreeSequenceInitialSegment
          (replacementSeriesJ.data.tree
            (⟨ett.rounds, (by omega)⟩ : Fin (ett.rounds + (2 : ℕ))))
          J)
      (strictJ :
        (replacementSeriesJ.data.tree
              (⟨ett.rounds, (by omega)⟩ : Fin (ett.rounds + (2 : ℕ)))).length <
          J.length)
      (belowJ :
        TreeSequenceInitialSegment J
          (replacementSeriesJ.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
      (generatingJ : sigma = replacementSeriesJ.data.coloring (Fin.last ett.rounds))
      (seriesPresentationJ :
        { rounds := ett.rounds, roundsPositive := roundsPositiveJ,
              series := replacementSeriesJ, abovePenultimate := aboveJ,
              strictAbovePenultimate := strictJ, belowFinal := belowJ,
              generatingColoring := generatingJ :
              ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.series ≍
          replacementSeriesJ)
      (baseJ :
        HierarchyBase
          { replacementInput := replacementInputJ, replacementSeries := replacementSeriesJ,
              replacementETT :=
                { rounds := ett.rounds, roundsPositive := roundsPositiveJ,
                  series := replacementSeriesJ, abovePenultimate := aboveJ,
                  strictAbovePenultimate := strictJ, belowFinal := belowJ,
                  generatingColoring := generatingJ :
                  ExtendedTashkinovTree G k e0 replacementInputJ J sigma },
              rungAgreement :=
                Eq.refl
                  { rounds := ett.rounds, roundsPositive := roundsPositiveJ,
                      series := replacementSeriesJ, abovePenultimate := aboveJ,
                      strictAbovePenultimate := strictJ, belowFinal := belowJ,
                      generatingColoring := generatingJ :
                      ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.rounds,
              seriesPresentation := seriesPresentationJ,
              finalGeneratingColoring := finalGeneratingColoringJ,
              ladderTreesAgree := ladderTreesAgreeJ,
              storedColorsAgree := storedColorsAgreeJ,
              connectingEdgesAgree := connectingEdgesAgreeJ,
              extensionKindsAgree := extensionKindsAgreeJ,
              replacementProper := replacementProperJ,
              replacementOneUncolored := replacementOneUncoloredJ,
              replacementStable := replacementStableJ :
              CorrespondingExtendedTashkinovTree G k e0 ett sigma J }.replacementETT
          sigma)
      (KJ :
        TashkinovHierarchy
          { replacementInput := replacementInputJ, replacementSeries := replacementSeriesJ,
              replacementETT :=
                { rounds := ett.rounds, roundsPositive := roundsPositiveJ,
                  series := replacementSeriesJ, abovePenultimate := aboveJ,
                  strictAbovePenultimate := strictJ, belowFinal := belowJ,
                  generatingColoring := generatingJ :
                  ExtendedTashkinovTree G k e0 replacementInputJ J sigma },
              rungAgreement :=
                Eq.refl
                  { rounds := ett.rounds, roundsPositive := roundsPositiveJ,
                      series := replacementSeriesJ, abovePenultimate := aboveJ,
                      strictAbovePenultimate := strictJ, belowFinal := belowJ,
                      generatingColoring := generatingJ :
                      ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.rounds,
              seriesPresentation := seriesPresentationJ,
              finalGeneratingColoring := finalGeneratingColoringJ,
              ladderTreesAgree := ladderTreesAgreeJ,
              storedColorsAgree := storedColorsAgreeJ,
              connectingEdgesAgree := connectingEdgesAgreeJ,
              extensionKindsAgree := extensionKindsAgreeJ,
              replacementProper := replacementProperJ,
              replacementOneUncolored := replacementOneUncoloredJ,
              replacementStable := replacementStableJ :
              CorrespondingExtendedTashkinovTree G k e0 ett sigma J }.replacementETT
          baseJ)
      (replacementInputU : PartialEdgeColoring E k)
      (_ : TashkinovSeries G k ett.rounds e0 replacementInputU)
      (_ : TreeSequenceInitialSegment J U)
      (_ :
        (∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B)
          (_ : TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)),
    let kuStage : Fin (KJ.dividerCount + (2 : ℕ)) → TreeSequence G e0 :=
      fun (j : Fin (KJ.dividerCount + (2 : ℕ))) =>
      if (↑j : ℕ) = KJ.dividerCount + (1 : ℕ) then U
      else KJ.stage (⟨(↑j : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ)));
    ∀
      (_ :
        (∀ (j : Fin (KJ.dividerCount + (1 : ℕ))), kuStage j.castSucc = KJ.stage j.castSucc))
      (_ : kuStage (Fin.last (KJ.dividerCount + (1 : ℕ))) = U)
      (_ :
        (∀ (j : Fin (KJ.dividerCount + (2 : ℕ))) (hj : (↑j : ℕ) ≤ KJ.dividerCount),
          kuStage j = KJ.stage (⟨(↑j : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ)))))
      (j : Fin (KJ.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (kuStage j.castSucc) (kuStage j.succ) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett J U replacementInputJ replacementSeriesJ
      finalGeneratingColoringJ ladderTreesAgreeJ storedColorsAgreeJ connectingEdgesAgreeJ
      extensionKindsAgreeJ replacementProperJ replacementOneUncoloredJ replacementStableJ
      roundsPositiveJ aboveJ strictJ belowJ generatingJ seriesPresentationJ baseJ KJ
      replacementInputU replacementSeriesU segmentJU segmentTrans kuStage kuStageOld kuStageLast
      kuStageAt j
  by_cases hj : j.val = KJ.dividerCount
  · have hlast : j = Fin.last KJ.dividerCount := Fin.ext (by simpa using hj)
    rw [hlast, kuStageOld]
    have hsucc : (Fin.last KJ.dividerCount).succ =
        Fin.last (KJ.dividerCount + 1) := rfl
    rw [hsucc, kuStageLast]
    have oldLast := KJ.nested (Fin.last KJ.dividerCount)
    rw [hsucc, KJ.terminalStage] at oldLast
    exact segmentTrans oldLast segmentJU
  · have hjlt : j.val < KJ.dividerCount := by omega
    have hcast : j.castSucc.val ≤ KJ.dividerCount := by
      simpa using Nat.le_of_lt_succ j.isLt
    have hsuccle : j.succ.val ≤ KJ.dividerCount := by
      change j.val + 1 ≤ KJ.dividerCount
      omega
    rw [kuStageAt j.castSucc hcast, kuStageAt j.succ hsuccle]
    have hold := KJ.nested ⟨j.val, by omega⟩
    convert hold using 1

private theorem helper_kuStrict_298.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating sigma : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (J U : TreeSequence G e0)
      (replacementInputJ : PartialEdgeColoring E k)
      (replacementSeriesJ : TashkinovSeries G k ett.rounds e0 replacementInputJ)
      (finalGeneratingColoringJ :
        sigma = replacementSeriesJ.data.coloring (Fin.last ett.rounds))
      (ladderTreesAgreeJ :
        ∀ (i : Fin ett.rounds),
          replacementSeriesJ.data.tree i.succ.castSucc =
            ett.series.data.tree i.succ.castSucc)
      (storedColorsAgreeJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          replacementSeriesJ.data.stored i = ett.series.data.stored i)
      (connectingEdgesAgreeJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          replacementSeriesJ.data.connectingEdges i = ett.series.data.connectingEdges i)
      (extensionKindsAgreeJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          replacementSeriesJ.data.kind i = ett.series.data.kind i)
      (replacementProperJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          IsProperEdgeColoring G (replacementSeriesJ.data.coloring i))
      (replacementOneUncoloredJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          IsOneEdgeUncolored (replacementSeriesJ.data.coloring i) e0)
      (replacementStableJ :
        ∀ (i : Fin ett.rounds),
          StableColoring (ett.series.data.tree i.succ.castSucc)
            (TashkinovStoredColors ett.series.data i.succ) (ett.series.data.coloring i.succ)
            (replacementSeriesJ.data.coloring i.succ))
      (roundsPositiveJ : (1 : ℕ) ≤ ett.rounds)
      (aboveJ :
        TreeSequenceInitialSegment
          (replacementSeriesJ.data.tree
            (⟨ett.rounds, (by omega)⟩ : Fin (ett.rounds + (2 : ℕ))))
          J)
      (strictJ :
        (replacementSeriesJ.data.tree
              (⟨ett.rounds, (by omega)⟩ : Fin (ett.rounds + (2 : ℕ)))).length <
          J.length)
      (belowJ :
        TreeSequenceInitialSegment J
          (replacementSeriesJ.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
      (generatingJ : sigma = replacementSeriesJ.data.coloring (Fin.last ett.rounds))
      (seriesPresentationJ :
        { rounds := ett.rounds, roundsPositive := roundsPositiveJ,
              series := replacementSeriesJ, abovePenultimate := aboveJ,
              strictAbovePenultimate := strictJ, belowFinal := belowJ,
              generatingColoring := generatingJ :
              ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.series ≍
          replacementSeriesJ)
      (baseJ :
        HierarchyBase
          { replacementInput := replacementInputJ, replacementSeries := replacementSeriesJ,
              replacementETT :=
                { rounds := ett.rounds, roundsPositive := roundsPositiveJ,
                  series := replacementSeriesJ, abovePenultimate := aboveJ,
                  strictAbovePenultimate := strictJ, belowFinal := belowJ,
                  generatingColoring := generatingJ :
                  ExtendedTashkinovTree G k e0 replacementInputJ J sigma },
              rungAgreement :=
                Eq.refl
                  { rounds := ett.rounds, roundsPositive := roundsPositiveJ,
                      series := replacementSeriesJ, abovePenultimate := aboveJ,
                      strictAbovePenultimate := strictJ, belowFinal := belowJ,
                      generatingColoring := generatingJ :
                      ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.rounds,
              seriesPresentation := seriesPresentationJ,
              finalGeneratingColoring := finalGeneratingColoringJ,
              ladderTreesAgree := ladderTreesAgreeJ,
              storedColorsAgree := storedColorsAgreeJ,
              connectingEdgesAgree := connectingEdgesAgreeJ,
              extensionKindsAgree := extensionKindsAgreeJ,
              replacementProper := replacementProperJ,
              replacementOneUncolored := replacementOneUncoloredJ,
              replacementStable := replacementStableJ :
              CorrespondingExtendedTashkinovTree G k e0 ett sigma J }.replacementETT
          sigma)
      (KJ :
        TashkinovHierarchy
          { replacementInput := replacementInputJ, replacementSeries := replacementSeriesJ,
              replacementETT :=
                { rounds := ett.rounds, roundsPositive := roundsPositiveJ,
                  series := replacementSeriesJ, abovePenultimate := aboveJ,
                  strictAbovePenultimate := strictJ, belowFinal := belowJ,
                  generatingColoring := generatingJ :
                  ExtendedTashkinovTree G k e0 replacementInputJ J sigma },
              rungAgreement :=
                Eq.refl
                  { rounds := ett.rounds, roundsPositive := roundsPositiveJ,
                      series := replacementSeriesJ, abovePenultimate := aboveJ,
                      strictAbovePenultimate := strictJ, belowFinal := belowJ,
                      generatingColoring := generatingJ :
                      ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.rounds,
              seriesPresentation := seriesPresentationJ,
              finalGeneratingColoring := finalGeneratingColoringJ,
              ladderTreesAgree := ladderTreesAgreeJ,
              storedColorsAgree := storedColorsAgreeJ,
              connectingEdgesAgree := connectingEdgesAgreeJ,
              extensionKindsAgree := extensionKindsAgreeJ,
              replacementProper := replacementProperJ,
              replacementOneUncolored := replacementOneUncoloredJ,
              replacementStable := replacementStableJ :
              CorrespondingExtendedTashkinovTree G k e0 ett sigma J }.replacementETT
          baseJ)
      (replacementInputU : PartialEdgeColoring E k)
      (_ : TashkinovSeries G k ett.rounds e0 replacementInputU)
      (_ : TreeSequenceInitialSegment J U),
    let kuStage : Fin (KJ.dividerCount + (2 : ℕ)) → TreeSequence G e0 :=
      fun (j : Fin (KJ.dividerCount + (2 : ℕ))) =>
      if (↑j : ℕ) = KJ.dividerCount + (1 : ℕ) then U
      else KJ.stage (⟨(↑j : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ)));
    ∀
      (_ :
        (∀ (j : Fin (KJ.dividerCount + (1 : ℕ))), kuStage j.castSucc = KJ.stage j.castSucc))
      (_ : kuStage (Fin.last (KJ.dividerCount + (1 : ℕ))) = U)
      (_ :
        (∀ (j : Fin (KJ.dividerCount + (2 : ℕ))) (hj : (↑j : ℕ) ≤ KJ.dividerCount),
          kuStage j = KJ.stage (⟨(↑j : ℕ), by omega⟩ : Fin (KJ.dividerCount + (2 : ℕ)))))
      (j : Fin (KJ.dividerCount + (1 : ℕ))),
    (kuStage j.castSucc).length < (kuStage j.succ).length := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett J U replacementInputJ replacementSeriesJ
      finalGeneratingColoringJ ladderTreesAgreeJ storedColorsAgreeJ connectingEdgesAgreeJ
      extensionKindsAgreeJ replacementProperJ replacementOneUncoloredJ replacementStableJ
      roundsPositiveJ aboveJ strictJ belowJ generatingJ seriesPresentationJ baseJ KJ
      replacementInputU replacementSeriesU segmentJU kuStage kuStageOld kuStageLast kuStageAt j
  by_cases hj : j.val = KJ.dividerCount
  · have hlast : j = Fin.last KJ.dividerCount := Fin.ext (by simpa using hj)
    rw [hlast, kuStageOld]
    have hsucc : (Fin.last KJ.dividerCount).succ =
        Fin.last (KJ.dividerCount + 1) := rfl
    rw [hsucc, kuStageLast]
    have hold := KJ.strict (Fin.last KJ.dividerCount)
    rw [hsucc, KJ.terminalStage] at hold
    exact lt_of_lt_of_le hold segmentJU.1
  · have hjlt : j.val < KJ.dividerCount := by omega
    have hcast : j.castSucc.val ≤ KJ.dividerCount := by
      simpa using Nat.le_of_lt_succ j.isLt
    have hsuccle : j.succ.val ≤ KJ.dividerCount := by
      change j.val + 1 ≤ KJ.dividerCount
      omega
    rw [kuStageAt j.castSucc hcast, kuStageAt j.succ hsuccle]
    have hold := KJ.strict ⟨j.val, by omega⟩
    convert hold using 1

private theorem helper_continuation_610.{u_1, u_2} :
    helperContinuation610Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett J U replacementInputJ replacementSeriesJ
      finalGeneratingColoringJ ladderTreesAgreeJ storedColorsAgreeJ connectingEdgesAgreeJ
      extensionKindsAgreeJ replacementProperJ replacementOneUncoloredJ replacementStableJ
      roundsPositiveJ aboveJ strictJ belowJ generatingJ seriesPresentationJ baseJ KJ
      replacementInputU replacementSeriesU finalGeneratingColoringU ladderTreesAgreeU
      storedColorsAgreeU connectingEdgesAgreeU extensionKindsAgreeU replacementProperU
      replacementOneUncoloredU replacementStableU roundsPositiveU aboveU strictU belowU
      generatingU seriesPresentationU baseU hcore segmentJU segmentTrans finalTreeEq
      terminalStoredEq kuStage kuStageOld kuStageLast kuStageAt kuNested kuStrict
      kuDividerPosition KU
  have stageEq (j : Fin (KJ.dividerCount + 1)) :
      KU.stage j.castSucc = KJ.stage j.castSucc := kuStageOld j
  have starredEq (j : Fin (KJ.dividerCount + 1)) :
      HierarchyStarredStage KU j = HierarchyStarredStage KJ j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [HierarchyStarredStage, KU] using hcore
    · change KU.stage i.succ.castSucc = KJ.stage i.succ.castSucc
      exact stageEq i.succ
  have storedEq (j : Fin (KJ.dividerCount + 1)) :
      HierarchyStoredColorsAt KU j = HierarchyStoredColorsAt KJ j := by
    unfold HierarchyStoredColorsAt
    change TashkinovStoredColors replacementSeriesU.data
          (Fin.last ett.rounds) \
        TreeMissingColors sigma (HierarchyStarredStage KU j) =
      TashkinovStoredColors replacementSeriesJ.data
          (Fin.last ett.rounds) \
        TreeMissingColors sigma (HierarchyStarredStage KJ j)
    rw [terminalStoredEq, starredEq]
  have missingEq (j : Fin (KJ.dividerCount + 1)) :
      HierarchyStageMissingColors KU j =
        HierarchyStageMissingColors KJ j := by
    unfold HierarchyStageMissingColors
    refine Fin.cases ?_ (fun i => ?_) j
    · change TreeMissingColors sigma
          (replacementSeriesU.data.tree (Fin.last ett.rounds).castSucc) =
        TreeMissingColors sigma
          (replacementSeriesJ.data.tree (Fin.last ett.rounds).castSucc)
      rw [finalTreeEq]
    · change TreeMissingColors sigma (KU.stage i.succ.castSucc) =
        TreeMissingColors sigma (KJ.stage i.succ.castSucc)
      exact congrArg (TreeMissingColors sigma) (stageEq i.succ)
  refine ⟨KU, rfl, ?_, ?_⟩
  · intro j
    exact ⟨stageEq j, starredEq j, storedEq j, missingEq j⟩
  · intro i
    rfl

private theorem helper_branch_126.{u_1, u_2} :
    helperBranch126Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett J U hJU replacementInputJ
      replacementSeriesJ finalGeneratingColoringJ ladderTreesAgreeJ storedColorsAgreeJ
      connectingEdgesAgreeJ extensionKindsAgreeJ replacementProperJ replacementOneUncoloredJ
      replacementStableJ roundsPositiveJ aboveJ strictJ belowJ generatingJ seriesPresentationJ
      baseJ KJ replacementInputU replacementSeriesU finalGeneratingColoringU ladderTreesAgreeU
      storedColorsAgreeU connectingEdgesAgreeU extensionKindsAgreeU replacementProperU
      replacementOneUncoloredU replacementStableU roundsU roundsPositiveU replacementDataU aboveU
      strictU belowU generatingU rungAgreementU seriesPresentationU baseU hcore
  cases rungAgreementU
  have seriesSameU : replacementDataU = replacementSeriesU :=
    eq_of_heq seriesPresentationU
  cases seriesSameU
  have segmentJU : TreeSequenceInitialSegment J U :=
    TashkinovAugmentationSequenceInitialSegment sigma J U hJU
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    apply TreeSequenceInitialSegment.trans <;> assumption
  let terminalIndex : Fin ett.rounds :=
    ⟨ett.rounds - 1,
      Nat.sub_lt (Nat.zero_lt_of_lt ett.roundsPositive) (by omega)⟩
  have terminalIndexEq : terminalIndex.succ.castSucc =
      (Fin.last ett.rounds).castSucc := by
    apply Fin.ext
    simp [terminalIndex, Nat.sub_add_cancel ett.roundsPositive]
  have finalTreeEq : replacementSeriesU.data.tree
        (Fin.last ett.rounds).castSucc =
      replacementSeriesJ.data.tree (Fin.last ett.rounds).castSucc := by
    rw [← terminalIndexEq]
    exact (ladderTreesAgreeU terminalIndex).trans
      (ladderTreesAgreeJ terminalIndex).symm
  have storedEntryEq (i : Fin (ett.rounds + 1)) :
      replacementSeriesU.data.stored i = replacementSeriesJ.data.stored i :=
    (storedColorsAgreeU i).trans (storedColorsAgreeJ i).symm
  have finalMissingEq : TreeMissingColors
        (replacementSeriesU.data.coloring (Fin.last ett.rounds))
        (replacementSeriesU.data.tree (Fin.last ett.rounds).castSucc) =
      TreeMissingColors
        (replacementSeriesJ.data.coloring (Fin.last ett.rounds))
        (replacementSeriesJ.data.tree (Fin.last ett.rounds).castSucc) := by
    rw [← finalGeneratingColoringU, ← finalGeneratingColoringJ, finalTreeEq]
  have terminalStoredEq :=
    @helper_terminalStoredEq_231 V E inferInstance inferInstance inferInstance G k e0 input
        T generating ett replacementInputJ replacementSeriesJ replacementInputU
        replacementSeriesU storedEntryEq finalMissingEq
  let kuStage : Fin (KJ.dividerCount + 2) → TreeSequence G e0 :=
    fun j => if j.val = KJ.dividerCount + 1 then U
      else KJ.stage ⟨j.val, by omega⟩
  have kuStageOld (j : Fin (KJ.dividerCount + 1)) :
      kuStage j.castSucc = KJ.stage j.castSucc := by
    have hj : j.castSucc.val ≠ KJ.dividerCount + 1 :=
      Nat.ne_of_lt j.isLt
    simp only [kuStage, ite_eq_right hj]
  have kuStageLast :
      kuStage (Fin.last (KJ.dividerCount + 1)) = U := by
    simp [kuStage]
  have kuStageAt (j : Fin (KJ.dividerCount + 2))
      (hj : j.val ≤ KJ.dividerCount) :
      kuStage j = KJ.stage ⟨j.val, by omega⟩ := by
    simp only [kuStage]
    split <;> rename_i hs
    · omega
    · rfl
  have kuNested :=
    @helper_kuNested_276 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T generating sigma ett J U replacementInputJ replacementSeriesJ
        finalGeneratingColoringJ ladderTreesAgreeJ storedColorsAgreeJ connectingEdgesAgreeJ
        extensionKindsAgreeJ replacementProperJ replacementOneUncoloredJ replacementStableJ
        roundsPositiveJ aboveJ strictJ belowJ generatingJ seriesPresentationJ baseJ KJ
        replacementInputU replacementSeriesU segmentJU segmentTrans kuStageOld kuStageLast kuStageAt
  have kuStrict :=
    @helper_kuStrict_298 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T generating sigma ett J U replacementInputJ replacementSeriesJ
        finalGeneratingColoringJ ladderTreesAgreeJ storedColorsAgreeJ connectingEdgesAgreeJ
        extensionKindsAgreeJ replacementProperJ replacementOneUncoloredJ replacementStableJ
        roundsPositiveJ aboveJ strictJ belowJ generatingJ seriesPresentationJ baseJ KJ
        replacementInputU replacementSeriesU segmentJU kuStageOld kuStageLast kuStageAt
  let kuDividerPosition (i : Fin KJ.dividerCount) : Fin (U.length + 1) :=
    ⟨(KJ.dividerPosition i).val,
      lt_of_lt_of_le (KJ.dividerPosition i).isLt
        (Nat.succ_le_succ segmentJU.1)⟩
  let KU : TashkinovHierarchy
      { rounds := ett.rounds
        roundsPositive := roundsPositiveU
        series := replacementSeriesU
        abovePenultimate := aboveU
        strictAbovePenultimate := strictU
        belowFinal := belowU
        generatingColoring := generatingU }
      baseU :=
    { dividerCount := KJ.dividerCount
      stage := kuStage
      baseStage := by
        calc
          kuStage 0 = KJ.stage 0 := by
            simpa using kuStageOld (0 : Fin (KJ.dividerCount + 1))
          _ = replacementSeriesJ.data.tree
                (Fin.last ett.rounds).castSucc := KJ.baseStage
          _ = replacementSeriesU.data.tree
                (Fin.last ett.rounds).castSucc := finalTreeEq.symm
      terminalStage := kuStageLast
      nested := kuNested
      strict := kuStrict
      dividerPosition := kuDividerPosition
      dividerPositive := by intro i; exact KJ.dividerPositive i
      dividerIncreasing := by
        intro i j hij
        exact KJ.dividerIncreasing i j hij
      dividerStage := by
        intro i
        have hstageIndex : (i.val + 1) ≤ KJ.dividerCount :=
          Nat.succ_le_of_lt i.isLt
        have hstage : kuStage ⟨i.val + 1, by omega⟩ =
            KJ.stage ⟨i.val + 1, by omega⟩ :=
          kuStageAt ⟨i.val + 1, by omega⟩ hstageIndex
        have hposJ : (KJ.dividerPosition i).val ≤ J.length :=
          Nat.le_of_lt_succ (KJ.dividerPosition i).isLt
        have hposU : (KJ.dividerPosition i).val ≤ U.length :=
          le_trans hposJ segmentJU.1
        have prefixEq : TreeSequencePrefix U (KJ.dividerPosition i).val
              (KJ.dividerPositive i) hposU =
            TreeSequencePrefix J (KJ.dividerPosition i).val
              (KJ.dividerPositive i) hposJ := by
          rw [TreeSequencePrefix, TreeSequencePrefix]
          congr
          · funext x
            have hv := segmentJU.2.1
              (Fin.castLE (Nat.succ_le_succ hposJ) x)
            simpa using hv
          · funext x
            have he := segmentJU.2.2 (Fin.castLE hposJ x)
            simpa using he
        rw [prefixEq]
        rw [hstage]
        simpa [kuDividerPosition] using KJ.dividerStage i
      coreInsideFirst := by
        by_cases hd : KJ.dividerCount = 0
        · have hstage : kuStage ⟨1, by omega⟩ = U := by
            simp [kuStage, hd]
          rw [hstage]
          have hold := KJ.coreInsideFirst
          have holdStage : KJ.stage ⟨1, by omega⟩ = J := by
            convert KJ.terminalStage using 1; apply congrArg KJ.stage;
              apply Fin.ext; simp [hd]
          rw [holdStage] at hold
          rw [hcore]
          exact segmentTrans hold segmentJU
        · have hstage : kuStage ⟨1, by omega⟩ = KJ.stage ⟨1, by omega⟩ :=
            kuStageAt ⟨1, by omega⟩ (Nat.one_le_iff_ne_zero.mpr hd)
          rw [hstage, hcore]
          exact KJ.coreInsideFirst }
  exact @helper_continuation_610 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating sigma ett J U replacementInputJ replacementSeriesJ
      finalGeneratingColoringJ ladderTreesAgreeJ storedColorsAgreeJ connectingEdgesAgreeJ
      extensionKindsAgreeJ replacementProperJ replacementOneUncoloredJ replacementStableJ
      roundsPositiveJ aboveJ strictJ belowJ generatingJ seriesPresentationJ baseJ KJ
      replacementInputU replacementSeriesU finalGeneratingColoringU ladderTreesAgreeU
      storedColorsAgreeU connectingEdgesAgreeU extensionKindsAgreeU replacementProperU
      replacementOneUncoloredU replacementStableU roundsPositiveU aboveU strictU belowU
      generatingU seriesPresentationU baseU hcore segmentJU segmentTrans finalTreeEq
      terminalStoredEq kuStageOld kuStageLast kuStageAt kuNested kuStrict
private theorem helper_branch_64.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating sigma : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (J U : TreeSequence G e0)
      (corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U)
      (baseU : HierarchyBase corrU.replacementETT sigma)
      (_ : TashkinovAugmentationSequence sigma J U)
      (replacementInputJ : PartialEdgeColoring E k)
      (replacementSeriesJ : TashkinovSeries G k ett.rounds e0 replacementInputJ)
      (finalGeneratingColoringJ :
        sigma = replacementSeriesJ.data.coloring (Fin.last ett.rounds))
      (ladderTreesAgreeJ :
        ∀ (i : Fin ett.rounds),
          replacementSeriesJ.data.tree i.succ.castSucc =
            ett.series.data.tree i.succ.castSucc)
      (storedColorsAgreeJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          replacementSeriesJ.data.stored i = ett.series.data.stored i)
      (connectingEdgesAgreeJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          replacementSeriesJ.data.connectingEdges i = ett.series.data.connectingEdges i)
      (extensionKindsAgreeJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          replacementSeriesJ.data.kind i = ett.series.data.kind i)
      (replacementProperJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          IsProperEdgeColoring G (replacementSeriesJ.data.coloring i))
      (replacementOneUncoloredJ :
        ∀ (i : Fin (ett.rounds + (1 : ℕ))),
          IsOneEdgeUncolored (replacementSeriesJ.data.coloring i) e0)
      (replacementStableJ :
        ∀ (i : Fin ett.rounds),
          StableColoring (ett.series.data.tree i.succ.castSucc)
            (TashkinovStoredColors ett.series.data i.succ) (ett.series.data.coloring i.succ)
            (replacementSeriesJ.data.coloring i.succ))
      (roundsJ : ℕ) (roundsPositiveJ : (1 : ℕ) ≤ roundsJ)
      (replacementDataJ : TashkinovSeries G k roundsJ e0 replacementInputJ)
      (aboveJ :
        TreeSequenceInitialSegment
          (replacementDataJ.data.tree (⟨roundsJ, (by omega)⟩ : Fin (roundsJ + (2 : ℕ)))) J)
      (strictJ :
        (replacementDataJ.data.tree
              (⟨roundsJ, (by omega)⟩ : Fin (roundsJ + (2 : ℕ)))).length <
          J.length)
      (belowJ :
        TreeSequenceInitialSegment J
          (replacementDataJ.data.tree (Fin.last (roundsJ + (1 : ℕ)))))
      (generatingJ : sigma = replacementDataJ.data.coloring (Fin.last roundsJ))
      (rungAgreementJ :
        { rounds := roundsJ, roundsPositive := roundsPositiveJ, series := replacementDataJ,
              abovePenultimate := aboveJ, strictAbovePenultimate := strictJ,
              belowFinal := belowJ, generatingColoring := generatingJ :
              ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.rounds =
          ett.rounds)
      (seriesPresentationJ :
        { rounds := roundsJ, roundsPositive := roundsPositiveJ, series := replacementDataJ,
              abovePenultimate := aboveJ, strictAbovePenultimate := strictJ,
              belowFinal := belowJ, generatingColoring := generatingJ :
              ExtendedTashkinovTree G k e0 replacementInputJ J sigma }.series ≍
          replacementSeriesJ)
      (baseJ :
        HierarchyBase
          { replacementInput := replacementInputJ, replacementSeries := replacementSeriesJ,
              replacementETT :=
                { rounds := roundsJ, roundsPositive := roundsPositiveJ,
                  series := replacementDataJ, abovePenultimate := aboveJ,
                  strictAbovePenultimate := strictJ, belowFinal := belowJ,
                  generatingColoring := generatingJ :
                  ExtendedTashkinovTree G k e0 replacementInputJ J sigma },
              rungAgreement := rungAgreementJ, seriesPresentation := seriesPresentationJ,
              finalGeneratingColoring := finalGeneratingColoringJ,
              ladderTreesAgree := ladderTreesAgreeJ,
              storedColorsAgree := storedColorsAgreeJ,
              connectingEdgesAgree := connectingEdgesAgreeJ,
              extensionKindsAgree := extensionKindsAgreeJ,
              replacementProper := replacementProperJ,
              replacementOneUncolored := replacementOneUncoloredJ,
              replacementStable := replacementStableJ :
              CorrespondingExtendedTashkinovTree G k e0 ett sigma J }.replacementETT
          sigma)
      (KJ :
        TashkinovHierarchy
          { replacementInput := replacementInputJ, replacementSeries := replacementSeriesJ,
              replacementETT :=
                { rounds := roundsJ, roundsPositive := roundsPositiveJ,
                  series := replacementDataJ, abovePenultimate := aboveJ,
                  strictAbovePenultimate := strictJ, belowFinal := belowJ,
                  generatingColoring := generatingJ :
                  ExtendedTashkinovTree G k e0 replacementInputJ J sigma },
              rungAgreement := rungAgreementJ, seriesPresentation := seriesPresentationJ,
              finalGeneratingColoring := finalGeneratingColoringJ,
              ladderTreesAgree := ladderTreesAgreeJ,
              storedColorsAgree := storedColorsAgreeJ,
              connectingEdgesAgree := connectingEdgesAgreeJ,
              extensionKindsAgree := extensionKindsAgreeJ,
              replacementProper := replacementProperJ,
              replacementOneUncolored := replacementOneUncoloredJ,
              replacementStable := replacementStableJ :
              CorrespondingExtendedTashkinovTree G k e0 ett sigma J }.replacementETT
          baseJ)
      (_ : baseU.core = baseJ.core),
    ∃ (KU : TashkinovHierarchy corrU.replacementETT baseU) (hcount :
      KU.dividerCount = KJ.dividerCount),
    (∀ (j : Fin (KU.dividerCount + (1 : ℕ))),
        let jo : Fin (KJ.dividerCount + (1 : ℕ)) :=
          Fin.cast (congrArg (fun (n : ℕ) => n + (1 : ℕ)) hcount) j;
        KU.stage j.castSucc = KJ.stage jo.castSucc ∧
          HierarchyStarredStage KU j = HierarchyStarredStage KJ jo ∧
            HierarchyStoredColorsAt KU j = HierarchyStoredColorsAt KJ jo ∧
              HierarchyStageMissingColors KU j = HierarchyStageMissingColors KJ jo) ∧
      ∀ (i : Fin KU.dividerCount),
        (↑(KU.dividerPosition i) : ℕ) = (↑(KJ.dividerPosition (Fin.cast hcount i)) : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett J U corrU baseU hJU replacementInputJ
      replacementSeriesJ finalGeneratingColoringJ ladderTreesAgreeJ storedColorsAgreeJ
      connectingEdgesAgreeJ extensionKindsAgreeJ replacementProperJ replacementOneUncoloredJ
      replacementStableJ roundsJ roundsPositiveJ replacementDataJ aboveJ strictJ belowJ
      generatingJ rungAgreementJ seriesPresentationJ baseJ KJ hcore
  cases rungAgreementJ
  have seriesSameJ : replacementDataJ = replacementSeriesJ :=
    eq_of_heq seriesPresentationJ
  cases seriesSameJ
  rcases corrU with ⟨replacementInputU, replacementSeriesU, replacementETTU,
    rungAgreementU, seriesPresentationU, finalGeneratingColoringU,
    ladderTreesAgreeU, storedColorsAgreeU, connectingEdgesAgreeU,
    extensionKindsAgreeU, replacementProperU, replacementOneUncoloredU,
    replacementStableU⟩
  cases replacementETTU with
  | mk roundsU roundsPositiveU replacementDataU aboveU strictU belowU generatingU =>
      exact @helper_branch_126 V E inferInstance inferInstance inferInstance inferInstance G k e0
          input T generating sigma ett J U hJU replacementInputJ replacementSeriesJ
          finalGeneratingColoringJ ladderTreesAgreeJ storedColorsAgreeJ connectingEdgesAgreeJ
          extensionKindsAgreeJ replacementProperJ replacementOneUncoloredJ replacementStableJ
          roundsPositiveJ aboveJ strictJ belowJ generatingJ seriesPresentationJ baseJ KJ
          replacementInputU replacementSeriesU finalGeneratingColoringU ladderTreesAgreeU
          storedColorsAgreeU connectingEdgesAgreeU extensionKindsAgreeU replacementProperU
          replacementOneUncoloredU replacementStableU roundsU roundsPositiveU replacementDataU
          aboveU strictU belowU generatingU rungAgreementU seriesPresentationU baseU hcore
theorem GoodHierarchySameDividerReconstruction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J U : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (baseJ : HierarchyBase corrJ.replacementETT sigma)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U)
    (baseU : HierarchyBase corrU.replacementETT sigma)
    (hcore : baseU.core = baseJ.core)
    (hJU : TashkinovAugmentationSequence sigma J U) :
    ∃ KU : TashkinovHierarchy corrU.replacementETT baseU,
    ∃ hcount : KU.dividerCount = KJ.dividerCount,
    (∀ j : Fin (KU.dividerCount + 1),
        let jo : Fin (KJ.dividerCount + 1) :=
          Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
        KU.stage j.castSucc = KJ.stage jo.castSucc ∧
          HierarchyStarredStage KU j = HierarchyStarredStage KJ jo ∧
            HierarchyStoredColorsAt KU j = HierarchyStoredColorsAt KJ jo ∧
              HierarchyStageMissingColors KU j = HierarchyStageMissingColors KJ jo) ∧
      ∀ i : Fin KU.dividerCount,
        (KU.dividerPosition i).val = (KJ.dividerPosition (Fin.cast hcount i)).val := by
  classical
  rcases corrJ with ⟨replacementInputJ, replacementSeriesJ, replacementETTJ,
    rungAgreementJ, seriesPresentationJ, finalGeneratingColoringJ,
    ladderTreesAgreeJ, storedColorsAgreeJ, connectingEdgesAgreeJ,
    extensionKindsAgreeJ, replacementProperJ, replacementOneUncoloredJ,
    replacementStableJ⟩
  cases replacementETTJ with
  | mk roundsJ roundsPositiveJ replacementDataJ aboveJ strictJ belowJ generatingJ =>
      exact @helper_branch_64 V E inferInstance inferInstance inferInstance inferInstance G k e0
          input T generating sigma ett J U corrU baseU hJU replacementInputJ replacementSeriesJ
          finalGeneratingColoringJ ladderTreesAgreeJ storedColorsAgreeJ connectingEdgesAgreeJ
          extensionKindsAgreeJ replacementProperJ replacementOneUncoloredJ replacementStableJ
          roundsJ roundsPositiveJ replacementDataJ aboveJ strictJ belowJ generatingJ
          rungAgreementJ seriesPresentationJ baseJ KJ hcore
end GoldbergSeymour

end
