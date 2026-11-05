/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.StableChangeCaseThree.Preparation3
public import LeanPool.GoldbergSeymour.GoodHierarchyPrefixRepackage

/-!
# StableChangeCaseThree: supporting constructions, part 4

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.StableChangeCaseThreePreparation

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperPositivePackage2874Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq V]
   [inst_3 : DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (alpha beta : Fin k) (hne : alpha ≠ beta)
   (sigma : PartialEdgeColoring E k),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
   ∀ (coreToA : TreeSequenceInitialSegment base.core A) (TnToA : TreeSequenceInitialSegment Tn A)
    (ordinaryToA :
     ∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage j.castSucc) A)
    (missingA : ∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v)
    (treeMissingEq :
     ∀ (S : TreeSequence G e0),
      TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
       TreeMissingColors sigma S = TreeMissingColors phi S)
    (closureInsideA :
     ett.series.data.kind n = some TashkinovExtensionKind.PE →
      TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A)
    (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    MaximumProperty corrT.replacementETT →
     ∀ (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core)
      (hclosureT : baseT.closure = base.closure)
      (terminalData :
       corrT.replacementETT.series.data.tree (Fin.last corrT.replacementETT.rounds).castSucc = Tn ∧
        corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
          ett.series.data.kind n ∧
         TashkinovStoredColors corrT.replacementETT.series.data
           (Fin.last corrT.replacementETT.rounds) =
          Dn),
      let K : TashkinovHierarchy corrT.replacementETT baseT :=
       {
        dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst :=
         @Eq.mpr
          (@TreeSequenceInitialSegment V E G e0
           (@HierarchyBase.core V E inst inst_1 inst_2 inst_3 G k e0
            (@CorrespondingExtendedTashkinovTree.replacementInput V E inst inst_1 inst_3 G k e0
             input T phi ett sigma T corrT)
            T sigma
            (@CorrespondingExtendedTashkinovTree.replacementETT V E inst inst_1 inst_3 G k e0 input
             T phi ett sigma T corrT)
            sigma baseT)
           (@TashkinovHierarchy.stage V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi ett base
            H
            (@Fin.mk
             (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@TashkinovHierarchy.dividerCount V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi
               ett base H)
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
             (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by omega))))
          (@TreeSequenceInitialSegment V E G e0
           (@HierarchyBase.core V E inst inst_1 inst_2 inst_3 G k e0 input T phi ett phi base)
           (@TashkinovHierarchy.stage V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi ett base
            H
            (@Fin.mk
             (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@TashkinovHierarchy.dividerCount V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi
               ett base H)
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
             (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by omega))))
          (@id
           (@Eq Prop
            (@TreeSequenceInitialSegment V E G e0
             (@HierarchyBase.core V E inst inst_1 inst_2 inst_3 G k e0
              (@CorrespondingExtendedTashkinovTree.replacementInput V E inst inst_1 inst_3 G k e0
               input T phi ett sigma T corrT)
              T sigma
              (@CorrespondingExtendedTashkinovTree.replacementETT V E inst inst_1 inst_3 G k e0
               input T phi ett sigma T corrT)
              sigma baseT)
             (@TashkinovHierarchy.stage V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi ett
              base H
              (@Fin.mk
               (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@TashkinovHierarchy.dividerCount V E inst inst_1 inst_2 inst_3 G k e0 input T phi
                 phi ett base H)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
               (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by omega))))
            (@TreeSequenceInitialSegment V E G e0
             (@HierarchyBase.core V E inst inst_1 inst_2 inst_3 G k e0 input T phi ett phi base)
             (@TashkinovHierarchy.stage V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi ett
              base H
              (@Fin.mk
               (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@TashkinovHierarchy.dividerCount V E inst inst_1 inst_2 inst_3 G k e0 input T phi
                 phi ett base H)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
               (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by omega)))))
           (@congrArg (@TreeSequence V E G e0) Prop
            (@HierarchyBase.core V E inst inst_1 inst_2 inst_3 G k e0
             (@CorrespondingExtendedTashkinovTree.replacementInput V E inst inst_1 inst_3 G k e0
              input T phi ett sigma T corrT)
             T sigma
             (@CorrespondingExtendedTashkinovTree.replacementETT V E inst inst_1 inst_3 G k e0 input
              T phi ett sigma T corrT)
             sigma baseT)
            (@HierarchyBase.core V E inst inst_1 inst_2 inst_3 G k e0 input T phi ett phi base)
            (fun (_a : @TreeSequence V E G e0) ↦
             @TreeSequenceInitialSegment V E G e0 _a
              (@TashkinovHierarchy.stage V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi ett
               base H
               (@Fin.mk
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                 (@TashkinovHierarchy.dividerCount V E inst inst_1 inst_2 inst_3 G k e0 input T phi
                  phi ett base H)
                 (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by omega))))
            hcoreT))
          (@TashkinovHierarchy.coreInsideFirst V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi
           ett base H) :
        TashkinovHierarchy corrT.replacementETT baseT };
      ∀
       (starredEq :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         HierarchyStarredStage K j = HierarchyStarredStage H j)
       (storedEq :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j)
       (stageMissingEq :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         HierarchyStageMissingColors K j = HierarchyStageMissingColors H j)
       (gammaNot :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         ∀ eta ∈ HierarchyStoredColorsAt H j, ∀ c ∈ C.good.gamma j eta, c ≠ alpha ∧ c ≠ beta)
       (segmentTransfer :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         ∀ eta ∈ HierarchyStoredColorsAt H j,
          ∀ (c : Fin k),
           c ≠ alpha →
            c ≠ beta → c ∈ HierarchySegmentColors K j eta → c ∈ HierarchySegmentColors H j eta)
       (minusEq :
        ∀ (S : TreeSequence G e0),
         TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          ∀ (R : Finset (Fin k)),
           TreeColorSetMinusClosed G sigma S R ↔ TreeColorSetMinusClosed G phi S R),
       let goodT : GoodHierarchy K :=
        helperGoodT2426 G k e0 input T phi ett base C alpha beta hne sigma coreToA TnToA ordinaryToA
         missingA treeMissingEq closureInsideA corrT baseT hcoreT hclosureT terminalData starredEq
         storedEq stageMissingEq gammaNot segmentTransfer minusEq;
       (0 : ℕ) < C.hierarchy.dividerCount →
        (1 : ℕ) ≤ (↑q : ℕ) →
         ∀ (U : TreeSequence G e0),
          U = H.stage q.castSucc →
           ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA U sigma)
            (baseA : HierarchyBase ettA sigma) (KA : TashkinovHierarchy ettA baseA) (goodA :
            GoodHierarchy KA),
            MaximumProperty ettA ∧
             ∃ (hcount : KA.dividerCount + (1 : ℕ) = H.dividerCount),
              baseA.core = base.core ∧
               baseA.closure = base.closure ∧
                (∀ (j : Fin (KA.dividerCount + (2 : ℕ))),
                  KA.stage j = H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∧
                 (∀ (j : Fin (KA.dividerCount + (1 : ℕ))),
                   let jH : Fin (H.dividerCount + (1 : ℕ)) :=
                    (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (1 : ℕ)));
                   HierarchyStoredColorsAt KA j = HierarchyStoredColorsAt H jH ∧
                    ∀ eta ∈ HierarchyStoredColorsAt KA j, goodA.gamma j eta = C.good.gamma jH eta) ∧
                  TreeColorSetMinusClosed G sigma
                   (H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
                   ((HierarchyStoredColorsAt H q).biUnion
                    (C.good.gamma
                     (⟨H.dividerCount - (1 : ℕ),
                       Nat.lt_succ_of_le (Nat.sub_le H.dividerCount (1 : ℕ))⟩ :
                      Fin (C.hierarchy.dividerCount + (1 : ℕ)))))

theorem helper_positivePackage_2874.{u_1, u_2} :
    helperPositivePackage2874Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne sigma H q A n Tn Dn coreToA
      TnToA ordinaryToA missingA treeMissingEq closureInsideA corrT hmaximumT baseT hcoreT
      hclosureT terminalData K starredEq storedEq stageMissingEq gammaNot segmentTransfer minusEq
      goodT hq hqK U hU
  subst U
  obtain ⟨ettA, hMPA, hrA, hsA, baseA, hcoreA, hclosureA, hsupportA,
      KA, hcount, hstages, hdividers, goodA, hgammaA, hminusA⟩ :=
    GoodHierarchyPrefixRepackage G k e0 corrT.replacementInput T sigma sigma
      corrT.replacementETT hmaximumT baseT K goodT q hqK
  refine ⟨corrT.replacementInput, ettA, baseA, KA, goodA, hMPA, ?_⟩
  have hcount' : KA.dividerCount + 1 = H.dividerCount := by
    change KA.dividerCount = H.dividerCount - 1 at hcount
    change 0 < H.dividerCount at hq
    omega
  refine ⟨hcount', hcoreA.trans hcoreT, hclosureA.trans hclosureT, ?_, ?_, ?_⟩
  · intro j
    let jp : Fin (q.val + 1) := ⟨j.val, by dsimp [q]; have := j.isLt; omega⟩
    have he : Fin.cast (by omega) jp = j := Fin.ext rfl
    simpa only [he] using hstages jp
  · intro j
    let jp : Fin q.val := ⟨j.val, by dsimp [q]; have := j.isLt; omega⟩
    have he : Fin.cast (by omega) jp = j := Fin.ext rfl
    have hg := hgammaA jp
    simp only [he] at hg
    refine ⟨hg.1.trans (storedEq _), ?_⟩
    intro eta heta
    exact hg.2 eta
  · have he : (Fin.last H.dividerCount).castSucc =
        (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) := Fin.ext rfl
    simpa [K, goodT, storedEq, q, he] using hminusA

theorem helper_sameComponent_3526.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (_ : alpha ≠ beta)
      (_ :
        let H : TashkinovHierarchy ett base := C.hierarchy;
        let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
        let ell : ℕ := T.length - A.length;
        let Ty : TreeSequence G e0 :=
          TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
            (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive)
            (Nat.min_le_right (A.length + (ell - (1 : ℕ))) T.length);
        alpha ∈ TreeMissingColors phi Ty ∧ beta ∈ TreeMissingColors phi Ty)
      (z : V ⊕ E) (sigma : PartialEdgeColoring E k)
      (_ : sigma = TwoColorComponentSwap G phi alpha beta z)
      (_ :
        let H : TashkinovHierarchy ett base := C.hierarchy;
        let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
        let A : TreeSequence G e0 := HierarchyStarredStage H q;
        let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
        ∀ u ∈ TreeSequenceVertexSet A, TreeVertexOrder T u va)
      (_ :
        let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
        let vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
        TreeVertexOrder T va vb)
      (_ :
        let H : TashkinovHierarchy ett base := C.hierarchy;
        let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
        let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
        alpha ∉ Dnq ∧ beta ∉ Dnq)
      (_ :
        let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
        let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
        alpha ∉
          ({c : Fin k |
              ∃ (t : Fin T.length),
                (↑ia : ℕ) ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑ib : ℕ) ∧ phi (T.edge t) = some c} :
            Finset (Fin k))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let va : V := T.vertex ia;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        have this_1 : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction
          fun (a : ¬(1 : ℕ) ≤ min (A.length + (ell - (1 : ℕ))) T.length) ↦ by omega)
        (Nat.min_le_right (A.length + (ell - (1 : ℕ))) T.length);
    ∀ (_ : alpha ∈ TreeMissingColors phi Y ∧ beta ∈ TreeMissingColors phi Y)
      (_ :
        alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
          (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length)
      (_ : (↑ia : ℕ) < (↑ib : ℕ))
      (_ : va ∉ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A)
      (_ : A.length < (↑ia : ℕ)) (_ : va ∈ TreeSequenceVertexSet Y)
      (_ : alpha ∉ TreeMissingColors phi A) (_ : alpha ∉ Dn ∧ beta ∉ Dn)
      (_ : ∀ (c : Fin k) (_ : c = alpha ∨ c = beta), c ∉ TreeMissingColors phi Tn ∪ Dn)
      (_ :
        ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence phi Tn T ∨
          (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (f : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
                TreeSequenceAdjoinEdge Tn f seed ∧
                  TashkinovAugmentationSequence phi seed T ∧
                    phi f ≠ some alpha ∧ phi f ≠ some beta)
      (_ :
        ∀ (t : Fin Tn.length), phi (Tn.edge t) ≠ some alpha ∧ phi (Tn.edge t) ≠ some beta)
      (_ :
        ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence phi S T)
          (t : Fin T.length) (_ : S.length ≤ (↑t : ℕ)) (_ : (↑t : ℕ) < (↑ib : ℕ)),
          phi (T.edge t) ≠ some alpha ∧ phi (T.edge t) ≠ some beta)
      (_ :
        ∀ (t : Fin T.length) (_ : (↑t : ℕ) < (↑ib : ℕ)),
          phi (T.edge t) ≠ some alpha ∧ phi (T.edge t) ≠ some beta)
      (_ :
        alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A →
          TreeVertexOrder T va vb ∧
            alpha ∉
              ({c : Fin k |
                  ∃ (t : Fin T.length),
                    A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑ib : ℕ) ∧ phi (T.edge t) = some c} :
                Finset (Fin k)))
      (_ :
        let H : TashkinovHierarchy ett base := C.hierarchy;
        have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
        have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
        have _ : TreeSequence G e0 := HierarchyStarredStage H q;
        have Tnq : TreeSequence G e0 :=
          H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
        have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
        have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
        have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
        have va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
        have vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
        have sameComponent : Prop :=
          TwoColorComponent G phi alpha beta (Sum.inl va) =
            TwoColorComponent G phi alpha beta (Sum.inl vb);
        ((0 : ℕ) < H.dividerCount ∧
              (alpha ∈ TreeMissingColors phi Tnq ∨
                Disjoint (insert alpha ({ beta } : Finset (Fin k)) : Finset (Fin k)) Dnq) →
            sameComponent) ∧
          (H.dividerCount = (0 : ℕ) ∧
              (alpha ∈ TreeMissingColors phi Tn ∨
                Disjoint (insert alpha ({ beta } : Finset (Fin k)) : Finset (Fin k)) Dn) →
            sameComponent)),
    TwoColorComponent G phi alpha beta (Sum.inl va) =
      TwoColorComponent G phi alpha beta (Sum.inl vb) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne hmissingPrefix z sigma hsigma
      hAprecedes hordered hnotStored hunused H q A n Tn Dn ia ib va vb ell Y hmissingY ha
      habIndex hout hAia haY halphaA hDn notControlled terminalRoute treeControlled
      augmentationControlled prefixControlled horderedUnused hchange
  by_cases hz : H.dividerCount = 0
  · apply hchange.2
    refine ⟨hz, Or.inr ?_⟩
    apply Finset.disjoint_left.mpr
    intro c hc hd
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hDn.1 hd
    · have he := Finset.mem_singleton.mp hc; subst c; exact hDn.2 hd
  · apply hchange.1
    refine ⟨by change 0 < H.dividerCount; omega, Or.inr ?_⟩
    apply Finset.disjoint_left.mpr
    intro c hc hd
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hnotStored.1 hd
    · have he := Finset.mem_singleton.mp hc; subst c; exact hnotStored.2 hd

end GoldbergSeymour.StableChangeCaseThreePreparation

end
