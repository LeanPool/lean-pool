/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAntitone
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TerminalRoute
public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor
public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.BaseControl
public import LeanPool.GoldbergSeymour.DisplayedEdges
public import LeanPool.GoldbergSeymour.RecoloredPrefixReconstruction
public import LeanPool.GoldbergSeymour.RetainedHierarchy
public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CombinedStableClosurePreserved
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchyNewMissingClosed
public import LeanPool.GoldbergSeymour.GoodHierarchyPrefixRepackage
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.HkuTreeColorsControlled
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloring
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable
public import LeanPool.GoldbergSeymour.ParallelCommonMissingClosed
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificate
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.ParallelInterchangeability
public import LeanPool.GoldbergSeymour.HierarchyOrderedExitReduction
public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.HierarchyStageInterchangeability

public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Stable Change Cases One Two

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperCaseContinuation868Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (hproper : IsProperEdgeColoring G phi)
   (hone : IsOneEdgeUncolored phi e0)
   (hprefixElementary :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 :=
     TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
      (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive)
      (Nat.min_le_right (A.length + (ell - (1 : ℕ))) T.length);
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
   (alpha beta : Fin k) (hne : alpha ≠ beta) (z : V ⊕ E) (sigma : PartialEdgeColoring E k)
   (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   ∀ (hsproper : IsProperEdgeColoring G sigma) (hsone : IsOneEdgeUncolored sigma e0)
    (houtside :
     ∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))) (c : Fin k),
      c = alpha ∨ c = beta →
       c ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy r) →
        TreeColorSetClosed G phi (HierarchyStarredStage C.hierarchy r) ({ c } : Finset (Fin k)) →
         OutsideKempeRecoloring (HierarchyStarredStage C.hierarchy r) phi sigma alpha beta)
    (preStepElementary :
     let i : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
        have this : (0 : ℕ) < ett.rounds := C.positive;
        Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by omega⟩ :
       Fin ett.rounds);
     ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc) (TreeSequenceVertexSet Tn))
    (hfixed : ∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t))
    (hmissing : ∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v)
    (hq : (0 : ℕ) < H.dividerCount),
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    ∀
     (trans :
      ∀ {U W Z : TreeSequence G e0} (hUW : TreeSequenceInitialSegment U W)
       (hWZ : TreeSequenceInitialSegment W Z), TreeSequenceInitialSegment U Z)
     (hA : A = H.stage q.castSucc)
     (coreToStar :
      ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
       TreeSequenceInitialSegment base.core (HierarchyStarredStage H j))
     (coreA : TreeSequenceInitialSegment base.core A)
     (ett0 : ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi)
     (base0 : HierarchyBase ett0 phi) (H0 : TashkinovHierarchy ett0 base0),
     let ettP : ExtendedTashkinovTree G k e0 input A phi :=
      {
       rounds := ett0.rounds, roundsPositive := ett0.roundsPositive, series := ett0.series,
       abovePenultimate :=
        ((Eq.symm
          (id
           (congrArg
            (fun (_a : TreeSequence G e0) ↦
             TreeSequenceInitialSegment
              (ett0.series.data.tree (⟨ett0.rounds, by omega⟩ : Fin (ett0.rounds + (2 : ℕ)))) _a)
            hA))) ▸
         ett0.abovePenultimate),
       strictAbovePenultimate := by rw [hA]; exact ett0.strictAbovePenultimate,
       belowFinal :=
        ((Eq.symm
          (id
           (congrArg
            (fun (_a : TreeSequence G e0) ↦
             TreeSequenceInitialSegment _a
              (ett0.series.data.tree (Fin.last (ett0.rounds + (1 : ℕ)))))
            hA))) ▸
         ett0.belowFinal),
       generatingColoring := ett0.generatingColoring : ExtendedTashkinovTree G k e0 input A phi };
     let baseP : HierarchyBase ettP phi :=
      {
       core := base0.core, closure := base0.closure, supportPosition := base0.supportPosition,
       supportPositive := base0.supportPositive,
       terminalMissingColors := base0.terminalMissingColors, parallel := base0.parallel,
       nonparallel := base0.nonparallel : HierarchyBase ettP phi };
     ∀ (hcoreP : baseP.core = base.core),
      let dividerP : (i : Fin H0.dividerCount) → Fin (A.length + (1 : ℕ)) :=
       fun (i : Fin H0.dividerCount) ↦
       (⟨(↑(H0.dividerPosition i) : ℕ), by
         first
         | omega
         | (
           have := GoldbergSeymour.TreeSequence.positive T
           have := GoldbergSeymour.TreeSequence.positive A
           have := GoldbergSeymour.HierarchyCounterexample.positive C
           have := Fin.isLt q
           have := Fin.isLt i
           have := coreA.1
           have := congrArg GoldbergSeymour.TreeSequence.length hA
           have := congrArg GoldbergSeymour.TreeSequence.length hcoreP
           have := GoldbergSeymour.TreeSequence.positive (H.stage q.castSucc)
           have := GoldbergSeymour.TreeSequence.positive A
           try dsimp only [H] at *
           try dsimp only [q] at *
           try dsimp only [A] at *
           try dsimp only [GoldbergSeymour.TreeSequencePrefix] at *
           all_goals omega)⟩ :
        Fin (A.length + (1 : ℕ)));
      let HP : TashkinovHierarchy ettP baseP :=
       {
        dividerCount := H0.dividerCount, stage := H0.stage, baseStage := H0.baseStage,
        terminalStage := Eq.trans H0.terminalStage (Eq.symm hA), nested := H0.nested,
        strict := H0.strict, dividerPosition := dividerP, dividerPositive := H0.dividerPositive,
        dividerIncreasing := H0.dividerIncreasing,
        dividerStage := fun (i : Fin H0.dividerCount) ↦
         ((Eq.symm
           (id
            (congrArg
             (Eq (H0.stage (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (H0.dividerCount + (2 : ℕ)))))
             (TreeSequencePrefix.congr_simp A (H.stage q.castSucc) hA (↑(dividerP i) : ℕ)
              (↑(H0.dividerPosition i) : ℕ)
              (by
               first
               | omega
               | (
                 have := GoldbergSeymour.TreeSequence.positive T
                 have := GoldbergSeymour.HierarchyCounterexample.positive C
                 have := Fin.isLt q
                 have := Fin.isLt i
                 have := coreA.1
                 have := congrArg GoldbergSeymour.TreeSequence.length hA
                 have := congrArg GoldbergSeymour.TreeSequence.length hcoreP
                 have := GoldbergSeymour.TreeSequence.positive (H.stage q.castSucc)
                 try dsimp only [H] at *))
              (H0.dividerPositive i) (Nat.le_of_lt_succ (dividerP i).isLt))))) ▸
          H0.dividerStage i),
        coreInsideFirst := H0.coreInsideFirst : TashkinovHierarchy ettP baseP };
      ∀ (hc : HP.dividerCount + (1 : ℕ) = H.dividerCount)
       (pStage :
        ∀ (j : Fin (HP.dividerCount + (2 : ℕ))),
         HP.stage j =
          H.stage
           (⟨(↑j : ℕ),
             have this : (↑j : ℕ) < HP.dividerCount + (2 : ℕ) := j.isLt;
             Decidable.byContradiction fun (a : ¬(↑j : ℕ) < H.dividerCount + (2 : ℕ)) ↦ by omega⟩ :
            Fin (H.dividerCount + (2 : ℕ))))
       (pTree : ettP.series.data.tree (Fin.last ettP.rounds).castSucc = Tn)
       (fullBase :
        ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA A sigma),
         MaximumProperty ettA ∧
          ettA.series.data.tree (Fin.last ettA.rounds).castSucc = Tn ∧
           ettA.series.data.kind (Fin.last ettA.rounds) = ett.series.data.kind n ∧
            TashkinovStoredColors ettA.series.data (Fin.last ettA.rounds) = Dn ∧
             ∃ (baseA : HierarchyBase ettA sigma),
              baseA.core = base.core ∧ baseA.closure = base.closure),
       ∃ (inputA : PartialEdgeColoring E k) (ettA :
        ExtendedTashkinovTree G k e0 inputA
         (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) sigma)
        (baseA : HierarchyBase ettA sigma) (K : TashkinovHierarchy ettA baseA) (goodA :
        GoodHierarchy K),
        MaximumProperty ettA ∧
         ettA.series.data.kind (Fin.last ettA.rounds) = ett.series.data.kind (Fin.last ett.rounds) ∧
          ∃ (hcount : K.dividerCount + (1 : ℕ) = C.hierarchy.dividerCount),
           baseA.core = base.core ∧
            baseA.closure = base.closure ∧
             (∀ (j : Fin (K.dividerCount + (2 : ℕ))),
               K.stage j =
                C.hierarchy.stage
                 (⟨(↑j : ℕ), by omega⟩ : Fin (C.hierarchy.dividerCount + (2 : ℕ)))) ∧
              (∀ (j : Fin (K.dividerCount + (1 : ℕ))),
                HierarchyStoredColorsAt K j =
                  HierarchyStoredColorsAt C.hierarchy
                   (⟨(↑j : ℕ), by omega⟩ : Fin (C.hierarchy.dividerCount + (1 : ℕ))) ∧
                 ∀ eta ∈ HierarchyStoredColorsAt K j,
                  goodA.gamma j eta =
                   C.good.gamma (⟨(↑j : ℕ), by omega⟩ : Fin (C.hierarchy.dividerCount + (1 : ℕ)))
                    eta) ∧
               TreeColorSetMinusClosed G sigma
                (C.hierarchy.stage
                 (⟨C.hierarchy.dividerCount, by omega⟩ : Fin (C.hierarchy.dividerCount + (2 : ℕ))))
                ((HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount)).biUnion
                 (C.good.gamma
                  (⟨C.hierarchy.dividerCount - (1 : ℕ), by omega⟩ :
                   Fin (C.hierarchy.dividerCount + (1 : ℕ)))))

private abbrev helperCaseContinuation1156Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (hproper : IsProperEdgeColoring G phi)
   (hone : IsOneEdgeUncolored phi e0)
   (hprefixElementary :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 :=
     TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
      (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive)
      (Nat.min_le_right (A.length + (ell - (1 : ℕ))) T.length);
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
   (alpha beta : Fin k) (hne : alpha ≠ beta)
   (hmissingPrefix :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 :=
     TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
      (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive)
      (Nat.min_le_right (A.length + (ell - (1 : ℕ))) T.length);
    alpha ∈ TreeMissingColors phi Ty ∧ beta ∈ TreeMissingColors phi Ty)
   (z : V ⊕ E) (hpath : TwoColorPathComponent G phi alpha beta z) (sigma : PartialEdgeColoring E k)
   (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
   (hcase :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Tnq : TreeSequence G e0 :=
     H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    (0 : ℕ) < H.dividerCount ∧ alpha ∈ TreeMissingColors phi Tnq ∨
     H.dividerCount = (0 : ℕ) ∧
      (alpha ∈ TreeMissingColors phi Tn ∨ alpha ∈ TreeMissingColors phi A ∧ alpha ∉ Dn ∧ beta ∉ Dn))
   (hdisjoint :
    let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    Disjoint (TwoColorComponent G phi alpha beta z)
     (TwoColorComponent G phi alpha beta (Sum.inl va)))
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   ∀ (hsproper : IsProperEdgeColoring G sigma) (hsone : IsOneEdgeUncolored sigma e0)
    (houtside :
     ∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))) (c : Fin k),
      c = alpha ∨ c = beta →
       c ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy r) →
        TreeColorSetClosed G phi (HierarchyStarredStage C.hierarchy r) ({ c } : Finset (Fin k)) →
         OutsideKempeRecoloring (HierarchyStarredStage C.hierarchy r) phi sigma alpha beta)
    (preStepElementary :
     let i : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
        have this : (0 : ℕ) < ett.rounds := C.positive;
        Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by omega⟩ :
       Fin ett.rounds);
     ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc) (TreeSequenceVertexSet Tn))
    (hfixed : ∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t))
    (hmissing : ∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v)
    (hq : (0 : ℕ) < H.dividerCount),
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    ∀
     (hstable :
      if ett.series.data.kind n = some TashkinovExtensionKind.PE then
       CombinedStableColoring Tn base.closure Dn phi sigma
      else StableColoring Tn Dn phi sigma)
     (trans :
      ∀ {U W Z : TreeSequence G e0} (hUW : TreeSequenceInitialSegment U W)
       (hWZ : TreeSequenceInitialSegment W Z), TreeSequenceInitialSegment U Z)
     (hA : A = H.stage q.castSucc) (hAT : TreeSequenceInitialSegment A T)
     (ordinaryToA :
      ∀ (j : Fin (H.dividerCount + (2 : ℕ))) (hj : (↑j : ℕ) ≤ H.dividerCount),
       TreeSequenceInitialSegment (H.stage j) A)
     (coreToStar :
      ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
       TreeSequenceInitialSegment base.core (HierarchyStarredStage H j))
     (coreA : TreeSequenceInitialSegment base.core A) (TnA : TreeSequenceInitialSegment Tn A)
     (treeMissingEq :
      ∀ (U : TreeSequence G e0) (hUA : TreeSequenceInitialSegment U A),
       TreeMissingColors sigma U = TreeMissingColors phi U)
     (ett0 : ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi)
     (base0 : HierarchyBase ett0 phi) (H0 : TashkinovHierarchy ett0 base0),
     let ettP : ExtendedTashkinovTree G k e0 input A phi :=
      {
       rounds := ett0.rounds, roundsPositive := ett0.roundsPositive, series := ett0.series,
       abovePenultimate :=
        ((Eq.symm
          (id
           (congrArg
            (fun (_a : TreeSequence G e0) ↦
             TreeSequenceInitialSegment
              (ett0.series.data.tree (⟨ett0.rounds, by omega⟩ : Fin (ett0.rounds + (2 : ℕ)))) _a)
            hA))) ▸
         ett0.abovePenultimate),
       strictAbovePenultimate := by rw [hA]; exact ett0.strictAbovePenultimate,
       belowFinal :=
        ((Eq.symm
          (id
           (congrArg
            (fun (_a : TreeSequence G e0) ↦
             TreeSequenceInitialSegment _a
              (ett0.series.data.tree (Fin.last (ett0.rounds + (1 : ℕ)))))
            hA))) ▸
         ett0.belowFinal),
       generatingColoring := ett0.generatingColoring : ExtendedTashkinovTree G k e0 input A phi };
     ∀ (hMPp : MaximumProperty ettP) (hrp : ettP.rounds = ett.rounds),
      let baseP : HierarchyBase ettP phi :=
       {
        core := base0.core, closure := base0.closure, supportPosition := base0.supportPosition,
        supportPositive := base0.supportPositive,
        terminalMissingColors := base0.terminalMissingColors, parallel := base0.parallel,
        nonparallel := base0.nonparallel : HierarchyBase ettP phi };
      ∀ (hcoreP : baseP.core = base.core) (hclosureP : baseP.closure = base.closure),
       let dividerP : (i : Fin H0.dividerCount) → Fin (A.length + (1 : ℕ)) :=
        fun (i : Fin H0.dividerCount) ↦
        (⟨(↑(H0.dividerPosition i) : ℕ), by
          first
          | omega
          | (
            have := GoldbergSeymour.TreeSequence.positive T
            have := GoldbergSeymour.TreeSequence.positive A
            have := GoldbergSeymour.HierarchyCounterexample.positive C
            have := Fin.isLt q
            have := Fin.isLt i
            have := hAT.1
            have := coreA.1
            have := TnA.1
            have := congrArg GoldbergSeymour.TreeSequence.length hA
            have := congrArg GoldbergSeymour.TreeSequence.length hcoreP
            have := congrArg GoldbergSeymour.TreeSequence.length hclosureP
            have := GoldbergSeymour.TreeSequence.positive (H.stage q.castSucc)
            have := GoldbergSeymour.TreeSequence.positive A
            try dsimp only [H] at *
            try dsimp only [q] at *
            try dsimp only [A] at *
            try dsimp only [GoldbergSeymour.TreeSequencePrefix] at *
            all_goals omega)⟩ :
         Fin (A.length + (1 : ℕ)));
       let HP : TashkinovHierarchy ettP baseP :=
        {
         dividerCount := H0.dividerCount, stage := H0.stage, baseStage := H0.baseStage,
         terminalStage := Eq.trans H0.terminalStage (Eq.symm hA), nested := H0.nested,
         strict := H0.strict, dividerPosition := dividerP, dividerPositive := H0.dividerPositive,
         dividerIncreasing := H0.dividerIncreasing,
         dividerStage := fun (i : Fin H0.dividerCount) ↦
          ((Eq.symm
            (id
             (congrArg
              (Eq (H0.stage (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (H0.dividerCount + (2 : ℕ)))))
              (TreeSequencePrefix.congr_simp A (H.stage q.castSucc) hA (↑(dividerP i) : ℕ)
               (↑(H0.dividerPosition i) : ℕ)
               (by
                first
                | omega
                | (
                  have := GoldbergSeymour.TreeSequence.positive T
                  have := GoldbergSeymour.HierarchyCounterexample.positive C
                  have := Fin.isLt q
                  have := Fin.isLt i
                  have := hAT.1
                  have := coreA.1
                  have := TnA.1
                  have := congrArg GoldbergSeymour.TreeSequence.length hA
                  have := congrArg GoldbergSeymour.TreeSequence.length hcoreP
                  have := congrArg GoldbergSeymour.TreeSequence.length hclosureP
                  have := GoldbergSeymour.TreeSequence.positive (H.stage q.castSucc)
                  try dsimp only [H] at *))
               (H0.dividerPositive i) (Nat.le_of_lt_succ (dividerP i).isLt))))) ▸
           H0.dividerStage i),
         coreInsideFirst := H0.coreInsideFirst : TashkinovHierarchy ettP baseP };
       ∀ (hc : HP.dividerCount + (1 : ℕ) = H.dividerCount)
        (pStage :
         ∀ (j : Fin (HP.dividerCount + (2 : ℕ))),
          HP.stage j =
           H.stage
            (⟨(↑j : ℕ),
              have this : (↑j : ℕ) < HP.dividerCount + (2 : ℕ) := j.isLt;
              Decidable.byContradiction fun (a : ¬(↑j : ℕ) < H.dividerCount + (2 : ℕ)) ↦ by omega⟩ :
             Fin (H.dividerCount + (2 : ℕ))))
        (pTree : ettP.series.data.tree (Fin.last ettP.rounds).castSucc = Tn)
        (pKind : ettP.series.data.kind (Fin.last ettP.rounds) = ett.series.data.kind n)
        (pStored : TashkinovStoredColors ettP.series.data (Fin.last ettP.rounds) = Dn),
        ∃ (inputA : PartialEdgeColoring E k) (ettA :
         ExtendedTashkinovTree G k e0 inputA
          (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) sigma)
         (baseA : HierarchyBase ettA sigma) (K : TashkinovHierarchy ettA baseA) (goodA :
         GoodHierarchy K),
         MaximumProperty ettA ∧
          ettA.series.data.kind (Fin.last ettA.rounds) =
            ett.series.data.kind (Fin.last ett.rounds) ∧
           ∃ (hcount : K.dividerCount + (1 : ℕ) = C.hierarchy.dividerCount),
            baseA.core = base.core ∧
             baseA.closure = base.closure ∧
              (∀ (j : Fin (K.dividerCount + (2 : ℕ))),
                K.stage j =
                 C.hierarchy.stage
                  (⟨(↑j : ℕ), by omega⟩ : Fin (C.hierarchy.dividerCount + (2 : ℕ)))) ∧
               (∀ (j : Fin (K.dividerCount + (1 : ℕ))),
                 HierarchyStoredColorsAt K j =
                   HierarchyStoredColorsAt C.hierarchy
                    (⟨(↑j : ℕ), by omega⟩ : Fin (C.hierarchy.dividerCount + (1 : ℕ))) ∧
                  ∀ eta ∈ HierarchyStoredColorsAt K j,
                   goodA.gamma j eta =
                    C.good.gamma (⟨(↑j : ℕ), by omega⟩ : Fin (C.hierarchy.dividerCount + (1 : ℕ)))
                     eta) ∧
                TreeColorSetMinusClosed G sigma
                 (C.hierarchy.stage
                  (⟨C.hierarchy.dividerCount, by omega⟩ : Fin (C.hierarchy.dividerCount + (2 : ℕ))))
                 ((HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount)).biUnion
                  (C.good.gamma
                   (⟨C.hierarchy.dividerCount - (1 : ℕ), by omega⟩ :
                    Fin (C.hierarchy.dividerCount + (1 : ℕ)))))

private abbrev helperCaseContinuation1561Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (hproper : IsProperEdgeColoring G phi)
   (hone : IsOneEdgeUncolored phi e0)
   (hprefixElementary :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 :=
     TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
      (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive)
      (Nat.min_le_right (A.length + (ell - (1 : ℕ))) T.length);
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
   (alpha beta : Fin k) (hne : alpha ≠ beta)
   (hmissingPrefix :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 :=
     TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
      (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive)
      (Nat.min_le_right (A.length + (ell - (1 : ℕ))) T.length);
    alpha ∈ TreeMissingColors phi Ty ∧ beta ∈ TreeMissingColors phi Ty)
   (z : V ⊕ E) (hpath : TwoColorPathComponent G phi alpha beta z) (sigma : PartialEdgeColoring E k)
   (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
   (hcase :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Tnq : TreeSequence G e0 :=
     H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    (0 : ℕ) < H.dividerCount ∧ alpha ∈ TreeMissingColors phi Tnq ∨
     H.dividerCount = (0 : ℕ) ∧
      (alpha ∈ TreeMissingColors phi Tn ∨ alpha ∈ TreeMissingColors phi A ∧ alpha ∉ Dn ∧ beta ∉ Dn))
   (hdisjoint :
    let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    Disjoint (TwoColorComponent G phi alpha beta z)
     (TwoColorComponent G phi alpha beta (Sum.inl va)))
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   ∀ (hsproper : IsProperEdgeColoring G sigma) (hsone : IsOneEdgeUncolored sigma e0)
    (houtside :
     ∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))) (c : Fin k),
      c = alpha ∨ c = beta →
       c ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy r) →
        TreeColorSetClosed G phi (HierarchyStarredStage C.hierarchy r) ({ c } : Finset (Fin k)) →
         OutsideKempeRecoloring (HierarchyStarredStage C.hierarchy r) phi sigma alpha beta)
    (preStepElementary :
     let i : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
        have this : (0 : ℕ) < ett.rounds := C.positive;
        Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by omega⟩ :
       Fin ett.rounds);
     ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc) (TreeSequenceVertexSet Tn))
    (hfixed : ∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t))
    (hmissing : ∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v)
    (hq : (0 : ℕ) < H.dividerCount),
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    ∀
     (hstable :
      if ett.series.data.kind n = some TashkinovExtensionKind.PE then
       CombinedStableColoring Tn base.closure Dn phi sigma
      else StableColoring Tn Dn phi sigma)
     (trans :
      ∀ {U W Z : TreeSequence G e0} (hUW : TreeSequenceInitialSegment U W)
       (hWZ : TreeSequenceInitialSegment W Z), TreeSequenceInitialSegment U Z)
     (hA : A = H.stage q.castSucc) (hAT : TreeSequenceInitialSegment A T)
     (ordinaryToA :
      ∀ (j : Fin (H.dividerCount + (2 : ℕ))) (hj : (↑j : ℕ) ≤ H.dividerCount),
       TreeSequenceInitialSegment (H.stage j) A)
     (coreToStar :
      ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
       TreeSequenceInitialSegment base.core (HierarchyStarredStage H j))
     (coreA : TreeSequenceInitialSegment base.core A)
     (TnCore : TreeSequenceInitialSegment Tn base.core),
     ∃ (inputA : PartialEdgeColoring E k) (ettA :
      ExtendedTashkinovTree G k e0 inputA
       (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) sigma)
      (baseA : HierarchyBase ettA sigma) (K : TashkinovHierarchy ettA baseA) (goodA :
      GoodHierarchy K),
      MaximumProperty ettA ∧
       ettA.series.data.kind (Fin.last ettA.rounds) = ett.series.data.kind (Fin.last ett.rounds) ∧
        ∃ (hcount : K.dividerCount + (1 : ℕ) = C.hierarchy.dividerCount),
         baseA.core = base.core ∧
          baseA.closure = base.closure ∧
           (∀ (j : Fin (K.dividerCount + (2 : ℕ))),
             K.stage j =
              C.hierarchy.stage (⟨(↑j : ℕ), by omega⟩ : Fin (C.hierarchy.dividerCount + (2 : ℕ)))) ∧
            (∀ (j : Fin (K.dividerCount + (1 : ℕ))),
              HierarchyStoredColorsAt K j =
                HierarchyStoredColorsAt C.hierarchy
                 (⟨(↑j : ℕ), by omega⟩ : Fin (C.hierarchy.dividerCount + (1 : ℕ))) ∧
               ∀ eta ∈ HierarchyStoredColorsAt K j,
                goodA.gamma j eta =
                 C.good.gamma (⟨(↑j : ℕ), by omega⟩ : Fin (C.hierarchy.dividerCount + (1 : ℕ)))
                  eta) ∧
             TreeColorSetMinusClosed G sigma
              (C.hierarchy.stage
               (⟨C.hierarchy.dividerCount, by omega⟩ : Fin (C.hierarchy.dividerCount + (2 : ℕ))))
              ((HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount)).biUnion
               (C.good.gamma
                (⟨C.hierarchy.dividerCount - (1 : ℕ), by omega⟩ :
                 Fin (C.hierarchy.dividerCount + (1 : ℕ)))))

private theorem helper_corrData_414.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    (∀ {U W Z : TreeSequence G e0},
        TreeSequenceInitialSegment U W →
          TreeSequenceInitialSegment W Z → TreeSequenceInitialSegment U Z) →
    TreeSequenceInitialSegment Tn A →
    (∀ (U : TreeSequence G e0),
        TreeSequenceInitialSegment U A →
          TreeMissingColors sigma U = TreeMissingColors phi U) →
    ∀ {input0 : PartialEdgeColoring E k} {T0 : TreeSequence G e0}
      (old : ExtendedTashkinovTree G k e0 input0 T0 phi),
    old.series.data.tree (Fin.last old.rounds).castSucc = Tn →
    old.series.data.kind (Fin.last old.rounds) = ett.series.data.kind n →
    TashkinovStoredColors old.series.data (Fin.last old.rounds) = Dn →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 old sigma A),
    corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
        Tn ∧
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          ett.series.data.kind n ∧
        TashkinovStoredColors corr.replacementETT.series.data
            (Fin.last corr.replacementETT.rounds) =
          Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A n Tn Dn trans TnA treeMissingEq
      input0 T0 old holdTree holdKind holdStored corr
  clear * - old holdTree holdKind holdStored treeMissingEq TnA
  rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
    rungAgreement, seriesPresentation, finalGeneratingColoring,
    ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
    extensionKindsAgree, replacementProper, replacementOneUncolored,
    replacementStable⟩
  cases replacementETT with
  | mk rounds roundsPositive replacementData above strict below generating =>
    cases rungAgreement
    have hs : replacementData = replacementSeries := eq_of_heq seriesPresentation
    cases hs
    let a : Fin old.rounds := ⟨old.rounds - 1, by have := old.roundsPositive; omega⟩
    have ha : a.succ = Fin.last old.rounds := by
      apply Fin.ext
      change old.rounds - 1 + 1 = old.rounds
      have := old.roundsPositive
      omega
    have ht : replacementSeries.data.tree (Fin.last old.rounds).castSucc = Tn := by
      rw [← ha]
      have hold := holdTree
      rw [← ha] at hold
      exact (ladderTreesAgree a).trans hold
    have hm : TreeMissingColors (replacementSeries.data.coloring (Fin.last old.rounds))
        (replacementSeries.data.tree (Fin.last old.rounds).castSucc) =
        TreeMissingColors phi Tn := by
      rw [← finalGeneratingColoring, ht]
      exact treeMissingEq Tn TnA
    have hmOld : TreeMissingColors (old.series.data.coloring (Fin.last old.rounds))
        (old.series.data.tree (Fin.last old.rounds).castSucc) =
        TreeMissingColors phi Tn := by
      rw [← old.generatingColoring, holdTree]
    refine ⟨ht, (extensionKindsAgree (Fin.last old.rounds)).trans holdKind, ?_⟩
    rw [← holdStored]
    change TashkinovStoredColors replacementSeries.data (Fin.last old.rounds) =
      TashkinovStoredColors old.series.data (Fin.last old.rounds)
    simp only [TashkinovStoredColors, storedColorsAgree, hm, hmOld]

private theorem helper_branch_267.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ {u : V},
    ett.rounds = (1 : ℕ) →
    u ∈ TreeSequenceVertexSet Tn →
    ∀ {v : V},
    v ∈ TreeSequenceVertexSet Tn →
    u ≠ v →
    Disjoint
      (MissingColors G
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ),
                have this : (0 : ℕ) < ett.rounds := C.positive;
                Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
                  omega⟩ :
              Fin ett.rounds).castSucc)
        u)
      (MissingColors G
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ),
                have this : (0 : ℕ) < ett.rounds := C.positive;
                Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
                  omega⟩ :
              Fin ett.rounds).castSucc)
        v) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C n Tn _ hn
  have hcolor : (⟨ett.rounds - 1, by have := C.positive; omega⟩ : Fin ett.rounds).castSucc = 0 :=
    Fin.ext (by simp [hn])
  have htree : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
    Fin.ext (by simp [n, hn])
  dsimp only [Tn]
  rw [hcolor, htree]
  exact (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1

private theorem helper_branch_274.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (hproper : IsProperEdgeColoring G phi) (hone : IsOneEdgeUncolored phi e0)
      (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
      (hfewer :
        ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
          {generating' : PartialEdgeColoring E k}
          (other : ExtendedTashkinovTree G k e0 input' T' generating'),
          other.rounds = ett.rounds →
            MaximumProperty other →
              ∀ (base' : HierarchyBase other generating')
                (K : TashkinovHierarchy other base') (_ : GoodHierarchy K),
                K.dividerCount < C.hierarchy.dividerCount →
                  ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T'))
      (hminimal :
        ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
          {generating' : PartialEdgeColoring E k}
          {other : ExtendedTashkinovTree G k e0 input' T' generating'}
          {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
          other.rounds = ett.rounds →
            C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
              ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
                  (HierarchyCounterexampleMeasure C))
      (hlarge :
        let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
        let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
        (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card),
    let _ : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C :=
      { proper := hproper, oneEdgeUncolored := hone,
        lowerRung :=
          fun {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
            {generating' : PartialEdgeColoring E k} ↦
          hlower,
        fewerDividers :=
          fun {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
            {generating' : PartialEdgeColoring E k} ↦
          hfewer,
        lexicographicMinimality :=
          fun {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
            {generating' : PartialEdgeColoring E k}
            {other : ExtendedTashkinovTree G k e0 input' T' generating'}
            {base' : HierarchyBase other generating'} ↦
          hminimal,
        largeMissingSet := hlarge :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C };
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ {u : V},
    ¬ett.rounds = (1 : ℕ) →
    u ∈ TreeSequenceVertexSet Tn →
    ∀ {v : V},
    v ∈ TreeSequenceVertexSet Tn →
    u ≠ v →
    Disjoint
      (MissingColors G
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ),
                have this : (0 : ℕ) < ett.rounds := C.positive;
                Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
                  omega⟩ :
              Fin ett.rounds).castSucc)
        u)
      (MissingColors G
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ),
                have this : (0 : ℕ) < ett.rounds := C.positive;
                Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
                  omega⟩ :
              Fin ett.rounds).castSucc)
        v) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge ctx
      n Tn _ hn
  have hmore : 1 < ett.rounds := by have := C.positive; omega
  obtain ⟨predecessor, hr, hmaximum, _, _⟩ :=
    CertifiedETTPredecessor G k e0 input T phi ett C.maximum hmore
  have htree : n.castSucc = (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) :=
    Fin.ext rfl
  dsimp only [Tn]
  rw [htree]
  exact (ctx.lowerRung predecessor (by omega) (by omega) hmaximum).1

private theorem helper_hweak_291.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (if ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE then
        CombinedStableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          base.closure (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi
          sigma
      else
        StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma) →
    (∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) →
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    HierarchyWeaklyStable H q sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A hbase hfixed hmissing
  cases hq : q using Fin.cases with
  | zero =>
    exact hbase
  | succ i =>
    have hA : A = H.stage i.succ.castSucc := by
      dsimp only [A]
      rw [hq]
      rfl
    refine ⟨hbase, ?_⟩
    have he : ∀ t : Fin (H.stage i.succ.castSucc).length,
        sigma ((H.stage i.succ.castSucc).edge t) =
          phi ((H.stage i.succ.castSucc).edge t) := by
      exact hA ▸ hfixed
    have hm : ∀ v ∈ TreeSequenceVertexSet (H.stage i.succ.castSucc),
        MissingColors G sigma v = MissingColors G phi v := by
      simpa only [hA] using hmissing
    exact ⟨fun t _ => he t, hm⟩

private theorem helper_trans_321.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      {U W Z : TreeSequence G e0},
    TreeSequenceInitialSegment U W →
    TreeSequenceInitialSegment W Z →
    TreeSequenceInitialSegment U Z := by
  classical
  intro V E G e0 U W Z hUW hWZ
  refine ⟨hUW.1.trans hWZ.1, ?_, ?_⟩
  · intro j
    exact (hWZ.2.1 (Fin.castLE (Nat.succ_le_succ hUW.1) j)).trans
      (hUW.2.1 j)
  · intro j
    exact (hWZ.2.2 (Fin.castLE hUW.1 j)).trans (hUW.2.2 j)

private theorem helper_stageChain_332.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    (∀ {U W Z : TreeSequence G e0},
        TreeSequenceInitialSegment U W →
          TreeSequenceInitialSegment W Z → TreeSequenceInitialSegment U Z) →
    ∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))),
    (↑i : ℕ) ≤ j →
    TreeSequenceInitialSegment (H.stage i)
      (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H trans j
  induction j with
  | zero =>
      intro hj i hi
      have hi0 : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero hi)
      subst i
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  | succ j ih =>
      intro hj i hi
      by_cases heq : i.val = j + 1
      · have heq' : i = ⟨j + 1, hj⟩ := Fin.ext heq
        subst i
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      · exact trans (ih (by omega) i (by omega))
          (H.nested ⟨j, by omega⟩)

private theorem helper_starPositive_351.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (0 : ℕ) < (↑j : ℕ) →
    HierarchyStarredStage H j = H.stage j.castSucc := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H j hj
  have hn : j ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero] at this
    omega
  rw [← Fin.succ_pred j hn]
  rfl

private theorem helper_coreToStar_371.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    alpha ≠ beta →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    (∀ {U W Z : TreeSequence G e0},
        TreeSequenceInitialSegment U W →
          TreeSequenceInitialSegment W Z → TreeSequenceInitialSegment U Z) →
    (∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))),
        (↑i : ℕ) ≤ j →
          TreeSequenceInitialSegment (H.stage i)
            (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        (0 : ℕ) < (↑j : ℕ) → HierarchyStarredStage H j = H.stage j.castSucc) →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment base.core (HierarchyStarredStage H j) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne H trans stageChain starPositive j
  clear * - H trans stageChain starPositive
  by_cases hj : j = 0
  · subst j
    exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  · have hjp : 0 < j.val := by
      have hne : j.val ≠ 0 := fun hh => hj (Fin.ext hh)
      omega
    rw [starPositive j hjp]
    exact trans H.coreInsideFirst
      (stageChain j.val (by omega) ⟨1, by omega⟩ (by simp; omega))

private theorem helper_starToA_383.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    alpha ≠ beta →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        (0 : ℕ) < (↑j : ℕ) → HierarchyStarredStage H j = H.stage j.castSucc) →
    (∀ (j : Fin (H.dividerCount + (2 : ℕ))),
        (↑j : ℕ) ≤ H.dividerCount → TreeSequenceInitialSegment (H.stage j) A) →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment base.core (HierarchyStarredStage H j)) →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne H q A starPositive ordinaryToA
      coreToStar j
  by_cases hj : j = 0
  · subst j
    exact coreToStar q
  · rw [starPositive j (by
      have hne : j.val ≠ 0 := fun hh => hj (Fin.ext hh)
      omega)]
    exact ordinaryToA j.castSucc (by have := j.isLt; simp only [Fin.val_castSucc]; omega)

private theorem helper_preStepElementary_574.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (_ : IsProperEdgeColoring G phi) (_ : IsOneEdgeUncolored phi e0)
      (_ : LowerRoundInductionHypothesis G k e0 ett.rounds)
      (_ :
        ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
          {generating' : PartialEdgeColoring E k}
          (other : ExtendedTashkinovTree G k e0 input' T' generating'),
          other.rounds = ett.rounds →
            MaximumProperty other →
              ∀ (base' : HierarchyBase other generating')
                (K : TashkinovHierarchy other base') (_ : GoodHierarchy K),
                K.dividerCount < C.hierarchy.dividerCount →
                  ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T'))
      (_ :
        ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
          {generating' : PartialEdgeColoring E k}
          {other : ExtendedTashkinovTree G k e0 input' T' generating'}
          {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
          other.rounds = ett.rounds →
            C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
              ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
                  (HierarchyCounterexampleMeasure C))
      (_ :
        let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
        let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
        (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let i : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          have this : (0 : ℕ) < ett.rounds := C.positive;
          Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
            omega⟩ :
        Fin ett.rounds);
    ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
      (TreeSequenceVertexSet Tn) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge n Tn
  dsimp only
  by_cases hn : ett.rounds = 1
  · apply helper_branch_267 <;> assumption
  · apply helper_branch_274 <;> assumption
private theorem helper_caseContinuation_868.{u_1, u_2} :
    helperCaseContinuation868Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hprefixElementary alpha beta hne z
      sigma hsigma ctx H q A n Tn hsproper hsone houtside preStepElementary hfixed hmissing hq Dn
      trans hA coreToStar coreA ett0 base0 H0 ettP baseP hcoreP dividerP HP hc pStage pTree fullBase
  obtain ⟨inputA, ettA, hMPa, htreeA, hkindA, hstoredA, baseA, hcoreA, hclosureA⟩ := fullBase
  let K : TashkinovHierarchy ettA baseA :=
    { dividerCount := HP.dividerCount
      stage := HP.stage
      baseStage := HP.baseStage.trans (pTree.trans htreeA.symm)
      terminalStage := HP.terminalStage
      nested := HP.nested
      strict := HP.strict
      dividerPosition := HP.dividerPosition
      dividerPositive := HP.dividerPositive
      dividerIncreasing := HP.dividerIncreasing
      dividerStage := HP.dividerStage
      coreInsideFirst := by
        rw [hcoreA, ← hcoreP]
        exact HP.coreInsideFirst }
  have hcount : K.dividerCount + 1 = H.dividerCount := hc
  have stageEq (j : Fin (K.dividerCount + 2)) :
      K.stage j = H.stage ⟨j.val, by have := j.isLt; omega⟩ := pStage j
  let R0 := (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0)
  have hPEWitness (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      ∃ c : Fin k, c ∈ TreeMissingColors phi base.core \ R0 ∧
        ∃ f : E, f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet base.core) c ∧
          sigma f = phi f := by
    have hold := (C.good.parallelBase hp).1
    have witness : ∃ c : Fin k, c ∈ TreeMissingColors phi base.core \ R0 ∧
        ∃ f : E, f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet base.core) c := by
      by_contra hn
      apply hold
      intro c hc
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro f hf
      exact hn ⟨c, hc, f, hf⟩
    obtain ⟨c, hc, f, hf⟩ := witness
    have hcm := (Finset.mem_sdiff.mp hc).1
    have hcn := (Finset.mem_sdiff.mp hc).2
    have hb : f ∈ BoundaryEdges G (TreeSequenceVertexSet base.core) ∧ phi f = some c :=
      Finset.mem_filter.mp hf
    have hincident : TreeIncidentEdge base.core f := by
      have hends : ∃ u ∈ TreeSequenceVertexSet base.core,
          ∃ v ∉ TreeSequenceVertexSet base.core, G.ends f = Sym2.mk u v := by
        simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hb.1
      obtain ⟨u, hu, v, hv, he⟩ := hends
      refine ⟨u, hu, ?_⟩
      rw [Incident, he]
      exact Sym2.mem_mk_left _ _
    have hvalue : sigma f = phi f := by
      by_cases haffected : c = alpha ∨ c = beta
      · by_cases hex : ∃ j : Fin (H.dividerCount + 1),
            TreeColorSetClosed G phi (HierarchyStarredStage H j) {c}
        · obtain ⟨j, hj⟩ := hex
          have hmj : c ∈ TreeMissingColors phi (HierarchyStarredStage H j) := by
            obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hcm
            exact Finset.mem_biUnion.mpr
              ⟨v, TreeSequenceInitialSegmentVertexSetSubset (coreToStar j) hv, hcv⟩
          have hout := houtside j c haffected hmj hj
          apply (OutsideKempeRecoloringStable G e0 (HierarchyStarredStage H j) ∅
            phi sigma alpha beta ctx.proper ctx.oneEdgeUncolored hout).2.2.2.2
          obtain ⟨u, hu, huf⟩ := hincident
          exact ⟨u, TreeSequenceInitialSegmentVertexSetSubset (coreToStar j) hu, huf⟩
        · have hmA : c ∈ TreeMissingColors phi A := by
            obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hcm
            exact Finset.mem_biUnion.mpr
              ⟨v, TreeSequenceInitialSegmentVertexSetSubset coreA hv, hcv⟩
          have hh := (rutcor G k e0 input T phi ett base H C.good hq
            hprefixElementary preStepElementary c hmA).2
            (fun j hj => hex ⟨j, hj⟩)
          have hreserved := (hh.1 (⟨0, hq⟩ : Fin H.dividerCount)).2
          exact False.elim (hcn hreserved)
      · have hca : c ≠ alpha := fun h => haffected (Or.inl h)
        have hcb : c ≠ beta := fun h => haffected (Or.inr h)
        rw [hsigma]
        simp only [TwoColorComponentSwap, hb.2, Option.some.injEq, hca, hcb,
          ite_false, ite_self]
    exact ⟨c, hc, f, hf, hvalue⟩
  obtain ⟨goodA, hgamma, hclosed⟩ := P2813_T1_RetainedHierarchy
    G k e0 input T phi ett base H C.good hq alpha beta hne z sigma hsigma
    hproper hone hsproper hsone inputA ettA baseA K htreeA hkindA hstoredA
    hcount hcoreA hclosureA stageEq hfixed hmissing houtside hPEWitness
  refine ⟨inputA, ettA, baseA, K, goodA, hMPa, hkindA, hcount,
    hcoreA, hclosureA, stageEq, ?_, hclosed⟩
  intro j
  exact ⟨(hgamma j).1, fun eta _ => (hgamma j).2 eta⟩

private theorem helper_caseContinuation_1156.{u_1, u_2} :
    helperCaseContinuation1156Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hprefixElementary alpha beta hne
      hmissingPrefix z hpath sigma hsigma hcase hdisjoint ctx H q A n Tn hsproper hsone houtside
      preStepElementary hfixed hmissing hq Dn hstable trans hA hAT ordinaryToA coreToStar coreA
      TnA treeMissingEq ett0 base0 H0 ettP hMPp hrp baseP hcoreP hclosureP dividerP HP hc pStage
      pTree pKind pStored
  have corrData {input0 : PartialEdgeColoring E k} {T0 : TreeSequence G e0}
      (old : ExtendedTashkinovTree G k e0 input0 T0 phi)
      (holdTree : old.series.data.tree (Fin.last old.rounds).castSucc = Tn)
      (holdKind : old.series.data.kind (Fin.last old.rounds) = ett.series.data.kind n)
      (holdStored : TashkinovStoredColors old.series.data (Fin.last old.rounds) = Dn)
      (corr : CorrespondingExtendedTashkinovTree G k e0 old sigma A) :
      corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc = Tn ∧
        corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          ett.series.data.kind n ∧
        TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) = Dn := by
    apply helper_corrData_414 <;> assumption
  have fullBase :
      ∃ inputA : PartialEdgeColoring E k,
        ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
          MaximumProperty ettA ∧
          ettA.series.data.tree (Fin.last ettA.rounds).castSucc = Tn ∧
          ettA.series.data.kind (Fin.last ettA.rounds) = ett.series.data.kind n ∧
          TashkinovStoredColors ettA.series.data (Fin.last ettA.rounds) = Dn ∧
          ∃ baseA : HierarchyBase ettA sigma,
            baseA.core = base.core ∧ baseA.closure = base.closure := by
    clear * - hstable hmissing hsproper hsone hfixed treeMissingEq TnA hAT trans
      hMPp hrp pTree pKind pStored baseP HP hcoreP hclosureP corrData ordinaryToA hq ctx
      hprefixElementary hcase hmissingPrefix hpath hdisjoint hsigma
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · have hcombined : CombinedStableColoring Tn base.closure Dn phi sigma := by
        simpa only [hp, ite_true] using hstable
      have hroute : TashkinovAugmentationSequence sigma Tn A := by
        rcases P2813_T1_TerminalRoute G k e0 input T phi ett with
          ⟨_, hseq⟩ | ⟨hk, rest⟩
        · have hpre := TashkinovAugmentationSequenceRestrict phi Tn A T hseq TnA hAT
          unfold TashkinovAugmentationSequence at hpre ⊢
          have transport : ∀ U, Relation.ReflTransGen (TashkinovAugmentation phi) Tn U →
              TreeSequenceInitialSegment U A →
              Relation.ReflTransGen (TashkinovAugmentation sigma) Tn U := by
            intro U hseq
            induction hseq with
            | refl => intro _; exact Relation.ReflTransGen.refl
            | @tail U W hTU hUW ih =>
              intro hWA
              obtain ⟨hlen, hseg, c, hcolor, hcm⟩ := hUW
              have hUA := trans hseg hWA
              have hcmSigma : c ∈ TreeMissingColors sigma U := by
                rw [treeMissingEq U hUA]
                exact hcm
              let t : Fin W.length := Fin.cast hlen.symm (Fin.last U.length)
              have he : sigma (W.edge t) = phi (W.edge t) := by
                rw [← hWA.2.2 t]
                exact hfixed _
              exact Relation.ReflTransGen.tail (ih hUA)
                ⟨hlen, hseg, c, he.trans hcolor, hcmSigma⟩
          exact transport A hpre ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        · rcases hk with hk | hk <;> rw [hp] at hk <;> cases hk
      have hcombinedP : CombinedStableColoring
          (ettP.series.data.tree (Fin.last ettP.rounds).castSucc) baseP.closure
          (TashkinovStoredColors ettP.series.data (Fin.last ettP.rounds)) phi sigma := by
        rw [pTree, pStored, hclosureP]
        exact hcombined
      obtain ⟨corr, hMP, baseA, K0, hsame⟩ := HierarchySplitter G k e0 input A phi sigma
        ettP hMPp (by rw [hrp]; exact C.positive)
        (by
          intro input' T' generating' lower hpos hless hmax
          rw [hrp] at hless
          exact ctx.lowerRung lower hpos hless hmax)
        baseP HP (pKind.trans hp) ctx.proper ctx.oneEdgeUncolored hsproper hsone hcombinedP
        (by rw [pTree]; exact hroute)
      have hd := corrData ettP pTree pKind pStored corr
      exact ⟨corr.replacementInput, corr.replacementETT, hMP, hd.1, hd.2.1, hd.2.2,
        baseA, hsame.1.symm.trans hcoreP,
        (hsame.2.2.2.2.2 (pKind.trans hp)).symm.trans hclosureP⟩
    · have hh := P2813_T1_PrefixReconstruction G k e0 input T phi ett base C ctx sigma
        hsproper hsone hstable hfixed hmissing
      rcases hh.2 with he | ⟨corr, hMP⟩
      · have hstrict : (H.stage (0 : Fin (H.dividerCount + 2))).length <
            (H.stage ⟨1, by omega⟩).length := H.strict 0
        have hle := ordinaryToA ⟨1, by omega⟩ (by simp; omega)
        rw [H.baseStage] at hstrict
        have hlen := congrArg TreeSequence.length he
        change A.length = Tn.length at hlen
        have : Tn.length < (H.stage ⟨1, by omega⟩).length := hstrict
        exact False.elim ((Nat.ne_of_lt (lt_of_lt_of_le this hle.1)) hlen.symm)
      · have hd := corrData ett rfl rfl rfl corr
        let pos : Fin ((corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc).length + 1) :=
          Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1) hd.1.symm)
            base.supportPosition
        let baseA : HierarchyBase corr.replacementETT sigma :=
          { core := base.core
            closure := base.closure
            supportPosition := pos
            supportPositive := by simpa only [pos, Fin.val_cast] using base.supportPositive
            terminalMissingColors := rfl
            parallel := by
              dsimp only
              intro hPE
              exact False.elim (hp (hd.2.1.symm.trans hPE))
            nonparallel := by
              dsimp only
              intro _
              exact (base.nonparallel hp).trans hd.1.symm }
        exact ⟨corr.replacementInput, corr.replacementETT, hMP, hd.1, hd.2.1, hd.2.2,
          baseA, rfl, rfl⟩
  exact @helper_caseContinuation_868 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hprefixElementary) (@alpha) (@beta) (@hne) (@z) (@sigma) (@hsigma) (@ctx) (@hsproper)
      (@hsone) (@houtside) (@preStepElementary) (@hfixed) (@hmissing) (@hq) (@trans) (@hA)
      (@coreToStar) (@coreA) (@ett0) (@base0) (@H0) (@hcoreP) (@hc) (@pStage) (@pTree) (@fullBase)

private theorem helper_caseContinuation_1561.{u_1, u_2} :
    helperCaseContinuation1561Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hprefixElementary alpha beta hne
      hmissingPrefix z hpath sigma hsigma hcase hdisjoint ctx H q A n Tn hsproper hsone houtside
      preStepElementary hfixed hmissing hq Dn hstable trans hA hAT ordinaryToA coreToStar coreA
      TnCore
  have TnA := trans TnCore coreA
  have treeMissingEq (U : TreeSequence G e0)
      (hUA : TreeSequenceInitialSegment U A) :
      TreeMissingColors sigma U = TreeMissingColors phi U := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl
      (fun v hv => hmissing v (TreeSequenceInitialSegmentVertexSetSubset hUA hv))
  have prefixPackage := GoodHierarchyPrefixRepackage G k e0 input T phi phi ett
    C.maximum base H C.good q (by change 1 ≤ H.dividerCount; omega)
  obtain ⟨ett0, hMP0, hr0, hs0, base0, hcore0, hclosure0, hsupport0,
    H0, hcount0, hstage0, hdivider0, good0, hgamma0, hclosed0⟩ := prefixPackage
  let ettP : ExtendedTashkinovTree G k e0 input A phi :=
    { rounds := ett0.rounds
      roundsPositive := ett0.roundsPositive
      series := ett0.series
      abovePenultimate := by rw [hA]; exact ett0.abovePenultimate
      strictAbovePenultimate := by rw [hA]; exact ett0.strictAbovePenultimate
      belowFinal := by rw [hA]; exact ett0.belowFinal
      generatingColoring := ett0.generatingColoring }
  have hMPp : MaximumProperty ettP := hMP0
  have hrp : ettP.rounds = ett.rounds := hr0
  have hsp : HEq ettP.series ett.series := hs0
  let baseP : HierarchyBase ettP phi :=
    { core := base0.core
      closure := base0.closure
      supportPosition := base0.supportPosition
      supportPositive := base0.supportPositive
      terminalMissingColors := base0.terminalMissingColors
      parallel := base0.parallel
      nonparallel := base0.nonparallel }
  have hcoreP : baseP.core = base.core := hcore0
  have hclosureP : baseP.closure = base.closure := hclosure0
  let dividerP (i : Fin H0.dividerCount) : Fin (A.length + 1) :=
    ⟨(H0.dividerPosition i).val, by rw [hA]; exact (H0.dividerPosition i).isLt⟩
  let HP : TashkinovHierarchy ettP baseP :=
    { dividerCount := H0.dividerCount
      stage := H0.stage
      baseStage := H0.baseStage
      terminalStage := H0.terminalStage.trans hA.symm
      nested := H0.nested
      strict := H0.strict
      dividerPosition := dividerP
      dividerPositive := H0.dividerPositive
      dividerIncreasing := H0.dividerIncreasing
      dividerStage := by
        intro i
        simpa only [dividerP, hA] using H0.dividerStage i
      coreInsideFirst := H0.coreInsideFirst }
  have hc : HP.dividerCount + 1 = H.dividerCount := by
    clear * - hcount0 hq
    have hh : HP.dividerCount = H.dividerCount - 1 := hcount0
    omega
  have pStage (j : Fin (HP.dividerCount + 2)) :
      HP.stage j = H.stage ⟨j.val, by have := j.isLt; omega⟩ := by
    clear * - hc hstage0
    have hh := hstage0 (⟨j.val, by have := j.isLt; change j.val < H.dividerCount + 1; omega⟩)
    simpa only [Fin.cast, Fin.val_mk, Fin.eta] using hh
  have pTree : ettP.series.data.tree (Fin.last ettP.rounds).castSucc = Tn := by
    change ett0.series.data.tree (Fin.last ett0.rounds).castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc
    clear * - hr0 hs0
    cases ett0
    cases ett
    dsimp only at hr0 hs0 ⊢
    cases hr0
    rw [eq_of_heq hs0]
  have pKind : ettP.series.data.kind (Fin.last ettP.rounds) = ett.series.data.kind n := by
    change ett0.series.data.kind (Fin.last ett0.rounds) = ett.series.data.kind (Fin.last
        ett.rounds)
    clear * - hr0 hs0
    cases ett0
    cases ett
    dsimp only at hr0 hs0 ⊢
    cases hr0
    rw [eq_of_heq hs0]
  have pStored : TashkinovStoredColors ettP.series.data (Fin.last ettP.rounds) = Dn := by
    change TashkinovStoredColors ett0.series.data (Fin.last ett0.rounds) =
      TashkinovStoredColors ett.series.data (Fin.last ett.rounds)
    clear * - hr0 hs0
    cases ett0
    cases ett
    dsimp only at hr0 hs0 ⊢
    cases hr0
    rw [eq_of_heq hs0]
  exact @helper_caseContinuation_1156 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hprefixElementary) (@alpha) (@beta) (@hne) (@hmissingPrefix) (@z) (@hpath) (@sigma)
      (@hsigma) (@hcase) (@hdisjoint) (@ctx) (@hsproper) (@hsone) (@houtside)
      (@preStepElementary) (@hfixed) (@hmissing) (@hq) (@hstable) (@trans) (@hA) (@hAT)
      (@ordinaryToA) (@coreToStar) (@coreA) (@TnA) (@treeMissingEq) (@ett0) (@base0) (@H0)
      (@hMPp) (@hrp) (@hcoreP) (@hclosureP) (@hc) (@pStage) (@pTree) (@pKind) (@pStored)

theorem StableChangeCasesOneTwo {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < C.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hminimal : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      {other : ExtendedTashkinovTree G k e0 input' T' generating'}
      {base' : HierarchyBase other generating'}
      (C' : HierarchyCounterexample base'),
      other.rounds = ett.rounds →
      C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬ HierarchyCounterexampleLess
        (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C))
    (hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hmissingPrefix :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      alpha ∈ TreeMissingColors phi Ty ∧
        beta ∈ TreeMissingColors phi Ty)
    (z : Sum V E) (hpath : TwoColorPathComponent G phi alpha beta z)
    (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hcase :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let A := HierarchyStarredStage H q
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := ett.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ett.series.data n
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors phi Tnq) ∨
        (H.dividerCount = 0 ∧
          (alpha ∈ TreeMissingColors phi Tn ∨
            (alpha ∈ TreeMissingColors phi A ∧
              alpha ∉ Dn ∧ beta ∉ Dn))))
    (hdisjoint :
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      Disjoint (TwoColorComponent G phi alpha beta z)
        (TwoColorComponent G phi alpha beta (Sum.inl va))) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let A := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dnq := HierarchyStoredColorsAt H q
    HierarchyWeaklyStable H q sigma ∧
      ModColoring ett sigma ∧
      (A = Tn ∨
        ∃ inputA : PartialEdgeColoring E k,
          ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
            MaximumProperty ettA) ∧
      (∀ hq : 0 < H.dividerCount,
        ∃ inputA : PartialEdgeColoring E k,
          ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
            ∃ baseA : HierarchyBase ettA sigma,
              ∃ K : TashkinovHierarchy ettA baseA,
                ∃ goodA : GoodHierarchy K,
                  MaximumProperty ettA ∧
                    ettA.series.data.kind (Fin.last ettA.rounds) =
                        ett.series.data.kind (Fin.last ett.rounds) ∧
                    ∃ hcount : K.dividerCount + 1 = H.dividerCount,
                      baseA.core = base.core ∧
                      baseA.closure = base.closure ∧
                      (∀ j : Fin (K.dividerCount + 2),
                        K.stage j = H.stage ⟨j.val, by omega⟩) ∧
                      (∀ j : Fin (K.dividerCount + 1),
                        let jH : Fin (H.dividerCount + 1) :=
                          ⟨j.val, by omega⟩
                        HierarchyStoredColorsAt K j =
                            HierarchyStoredColorsAt H jH ∧
                          ∀ eta ∈ HierarchyStoredColorsAt K j,
                            goodA.gamma j eta = C.good.gamma jH eta) ∧
                      TreeColorSetMinusClosed G sigma Tnq
                        (Dnq.biUnion
                          (C.good.gamma ⟨C.hierarchy.dividerCount - 1,
                            by omega⟩))) := by
  classical
  let ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C := {
    proper := hproper
    oneEdgeUncolored := hone
    lowerRung := hlower
    fewerDividers := hfewer
    lexicographicMinimality := hminimal
    largeMissingSet := hlarge }
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  have controls := P2813_T1_BaseControl G k e0 input T phi ett base C ctx
    hprefixElementary alpha beta hne hmissingPrefix z hpath sigma hsigma hcase hdisjoint
  rcases controls with ⟨hbase, hmissing, hsproper, hsone, houtside⟩
  have preStepElementary :
      let i : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
      ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet Tn) := by
    apply helper_preStepElementary_574 <;> assumption
  have hfixed := P2813_T1_DisplayedEdges G k e0 input T phi ett base H C.good
    hproper hone preStepElementary hprefixElementary alpha beta z sigma hsigma hsone
    hbase houtside
  have rebuilt := P2813_T1_PrefixReconstruction G k e0 input T phi ett base C ctx
    sigma hsproper hsone hbase hfixed hmissing
  change (∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t)) at hfixed
  change (∀ v ∈ TreeSequenceVertexSet A,
    MissingColors G sigma v = MissingColors G phi v) at hmissing
  have hweak := helper_hweak_291 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@sigma)
      (@hbase) (@hfixed) (@hmissing)
  refine ⟨hweak, rebuilt.1, ?_, ?_⟩
  · rcases rebuilt.2 with he | ⟨corr, hMP⟩
    · exact Or.inl he
    · exact Or.inr ⟨corr.replacementInput, corr.replacementETT, hMP⟩
  · dsimp only
    intro hq
    change 0 < H.dividerCount at hq
    let Dn := TashkinovStoredColors ett.series.data n
    have hstable := hbase
    change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure Dn phi sigma
      else StableColoring Tn Dn phi sigma) at hstable
    have trans {U W Z : TreeSequence G e0}
        (hUW : TreeSequenceInitialSegment U W)
        (hWZ : TreeSequenceInitialSegment W Z) :
        TreeSequenceInitialSegment U Z := by
      exact helper_trans_321 (@G) (@e0) (@hUW) (@hWZ)
    have stageChain : ∀ (j : ℕ) (hj : j < H.dividerCount + 2)
        (i : Fin (H.dividerCount + 2)), i.val ≤ j →
        TreeSequenceInitialSegment (H.stage i) (H.stage ⟨j, hj⟩) := by
      apply helper_stageChain_332; assumption
    have starPositive := helper_starPositive_351 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base)
        (@C)
    have hA : A = H.stage q.castSucc := starPositive q hq
    have hAT : TreeSequenceInitialSegment A T := by
      rw [hA]
      have hh := H.nested q
      have hlast : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
      simpa only [hlast, H.terminalStage] using hh
    have ordinaryToA (j : Fin (H.dividerCount + 2)) (hj : j.val ≤ H.dividerCount) :
        TreeSequenceInitialSegment (H.stage j) A := by
      rw [hA]
      exact stageChain H.dividerCount (by omega) j hj
    have coreToStar (j : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment base.core (HierarchyStarredStage H j) := by
      apply helper_coreToStar_371 <;> assumption
    have starToA := helper_starToA_383 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@alpha) (@beta) (@hne) (@starPositive) (@ordinaryToA) (@coreToStar)
    have coreA : TreeSequenceInitialSegment base.core A := coreToStar q
    have TnCore : TreeSequenceInitialSegment Tn base.core := by
      by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
      · exact (base.parallel hp).2.2.some.leftSegment
      · rw [base.nonparallel hp]
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    exact @helper_caseContinuation_1561 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
        (@hprefixElementary) (@alpha) (@beta) (@hne) (@hmissingPrefix) (@z) (@hpath) (@sigma)
        (@hsigma) (@hcase) (@hdisjoint) (@ctx) (@hsproper) (@hsone) (@houtside)
        (@preStepElementary) (@hfixed) (@hmissing) (@hq) (@hstable) (@trans) (@hA) (@hAT)
        (@ordinaryToA) (@coreToStar) (@coreA) (@TnCore)
end GoldbergSeymour

end
