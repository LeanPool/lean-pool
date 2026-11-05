/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.StableChangeCaseThree.Preparation2

/-!
# StableChangeCaseThree: supporting constructions, part 3

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.StableChangeCaseThreePreparation

/-- Typed data construction shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperGoodT2426.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [inst : Fintype V] →
  [inst_1 : Fintype E] →
  [inst_2 : DecidableEq V] →
  [inst_3 : DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (phi : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T phi) →
  (base : HierarchyBase ett phi) →
  (C : HierarchyCounterexample base) →
  (alpha beta : Fin k) →
  alpha ≠ beta →
  (sigma : PartialEdgeColoring E k) →
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) :=
    Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 :=
    ett.series.data.tree n.castSucc;
  let Dn : Finset (Fin k) :=
    TashkinovStoredColors ett.series.data n;
  TreeSequenceInitialSegment base.core A →
  TreeSequenceInitialSegment Tn A →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
      TreeSequenceInitialSegment (H.stage j.castSucc)
        A) →
  (∀ v ∈ TreeSequenceVertexSet A,
      MissingColors G sigma v =
        MissingColors G phi v) →
  (∀ (S : TreeSequence G e0),
      TreeSequenceVertexSet S ⊆
          TreeSequenceVertexSet A →
        TreeMissingColors sigma S =
          TreeMissingColors phi S) →
  (ett.series.data.kind n =
        some TashkinovExtensionKind.PE →
      TreeSequenceVertexSet base.closure ⊆
        TreeSequenceVertexSet A) →
  (corrT :
      CorrespondingExtendedTashkinovTree G k e0
        ett sigma T) →
  (baseT :
      HierarchyBase corrT.replacementETT
        sigma) →
  (hcoreT : baseT.core = base.core) →
  baseT.closure = base.closure →
  (terminalData :
      corrT.replacementETT.series.data.tree
            (Fin.last
                corrT.replacementETT.rounds).castSucc =
          Tn ∧
        corrT.replacementETT.series.data.kind
              (Fin.last
                corrT.replacementETT.rounds) =
            ett.series.data.kind n ∧
          TashkinovStoredColors
              corrT.replacementETT.series.data
              (Fin.last
                corrT.replacementETT.rounds) =
            Dn) →
  let K :
    TashkinovHierarchy
      corrT.replacementETT baseT :=
    { dividerCount := H.dividerCount,
      stage := H.stage,
      baseStage :=
        Eq.trans H.baseStage
          (Eq.symm terminalData.left),
      terminalStage :=
        H.terminalStage,
      nested := H.nested,
      strict := H.strict,
      dividerPosition :=
        H.dividerPosition,
      dividerPositive :=
        H.dividerPositive,
      dividerIncreasing :=
        H.dividerIncreasing,
      dividerStage := H.dividerStage,
      coreInsideFirst :=
        @Eq.mpr
          (@TreeSequenceInitialSegment
            V E G e0
            (@HierarchyBase.core V E
              inst inst_1 inst_2
              inst_3 G k e0
              (@CorrespondingExtendedTashkinovTree.replacementInput
                V E inst inst_1 inst_3
                G k e0 input T phi ett
                sigma T corrT)
              T sigma
              (@CorrespondingExtendedTashkinovTree.replacementETT
                V E inst inst_1 inst_3
                G k e0 input T phi ett
                sigma T corrT)
              sigma baseT)
            (@TashkinovHierarchy.stage
              V E inst inst_1 inst_2
              inst_3 G k e0 input T
              phi phi ett base H
              (@Fin.mk
                (@HAdd.hAdd Nat Nat
                  Nat
                  (@instHAdd Nat
                    instAddNat)
                  (@TashkinovHierarchy.dividerCount
                    V E inst inst_1
                    inst_2 inst_3 G k
                    e0 input T phi phi
                    ett base H)
                  (@OfNat.ofNat Nat
                    (nat_lit 2)
                    (instOfNatNat
                      (nat_lit 2))))
                (@OfNat.ofNat Nat
                  (nat_lit 1)
                  (instOfNatNat
                    (nat_lit 1)))
                (by
                  have :=
                    GoldbergSeymour.TreeSequence.positive
                      T
                  omega))))
          (@TreeSequenceInitialSegment
            V E G e0
            (@HierarchyBase.core V E
              inst inst_1 inst_2
              inst_3 G k e0 input T
              phi ett phi base)
            (@TashkinovHierarchy.stage
              V E inst inst_1 inst_2
              inst_3 G k e0 input T
              phi phi ett base H
              (@Fin.mk
                (@HAdd.hAdd Nat Nat
                  Nat
                  (@instHAdd Nat
                    instAddNat)
                  (@TashkinovHierarchy.dividerCount
                    V E inst inst_1
                    inst_2 inst_3 G k
                    e0 input T phi phi
                    ett base H)
                  (@OfNat.ofNat Nat
                    (nat_lit 2)
                    (instOfNatNat
                      (nat_lit 2))))
                (@OfNat.ofNat Nat
                  (nat_lit 1)
                  (instOfNatNat
                    (nat_lit 1)))
                (by
                  have :=
                    GoldbergSeymour.TreeSequence.positive
                      T
                  omega))))
          (@id
            (@Eq Prop
              (@TreeSequenceInitialSegment
                V E G e0
                (@HierarchyBase.core V
                  E inst inst_1 inst_2
                  inst_3 G k e0
                  (@CorrespondingExtendedTashkinovTree.replacementInput
                    V E inst inst_1
                    inst_3 G k e0
                    input T phi ett
                    sigma T corrT)
                  T sigma
                  (@CorrespondingExtendedTashkinovTree.replacementETT
                    V E inst inst_1
                    inst_3 G k e0
                    input T phi ett
                    sigma T corrT)
                  sigma baseT)
                (@TashkinovHierarchy.stage
                  V E inst inst_1
                  inst_2 inst_3 G k e0
                  input T phi phi ett
                  base H
                  (@Fin.mk
                    (@HAdd.hAdd Nat
                      Nat Nat
                      (@instHAdd Nat
                        instAddNat)
                      (@TashkinovHierarchy.dividerCount
                        V E inst
                        inst_1 inst_2
                        inst_3 G k e0
                        input T phi
                        phi ett base
                        H)
                      (@OfNat.ofNat
                        Nat
                        (nat_lit 2)
                        (instOfNatNat
                          (nat_lit
                            2))))
                    (@OfNat.ofNat Nat
                      (nat_lit 1)
                      (instOfNatNat
                        (nat_lit 1)))
                    (by
                      have :=
                        GoldbergSeymour.TreeSequence.positive
                          T
                      omega))))
              (@TreeSequenceInitialSegment
                V E G e0
                (@HierarchyBase.core V
                  E inst inst_1 inst_2
                  inst_3 G k e0 input
                  T phi ett phi base)
                (@TashkinovHierarchy.stage
                  V E inst inst_1
                  inst_2 inst_3 G k e0
                  input T phi phi ett
                  base H
                  (@Fin.mk
                    (@HAdd.hAdd Nat
                      Nat Nat
                      (@instHAdd Nat
                        instAddNat)
                      (@TashkinovHierarchy.dividerCount
                        V E inst
                        inst_1 inst_2
                        inst_3 G k e0
                        input T phi
                        phi ett base
                        H)
                      (@OfNat.ofNat
                        Nat
                        (nat_lit 2)
                        (instOfNatNat
                          (nat_lit
                            2))))
                    (@OfNat.ofNat Nat
                      (nat_lit 1)
                      (instOfNatNat
                        (nat_lit 1)))
                    (by
                      have :=
                        GoldbergSeymour.TreeSequence.positive
                          T
                      omega)))))
            (@congrArg
              (@TreeSequence V E G e0)
              Prop
              (@HierarchyBase.core V E
                inst inst_1 inst_2
                inst_3 G k e0
                (@CorrespondingExtendedTashkinovTree.replacementInput
                  V E inst inst_1
                  inst_3 G k e0 input
                  T phi ett sigma T
                  corrT)
                T sigma
                (@CorrespondingExtendedTashkinovTree.replacementETT
                  V E inst inst_1
                  inst_3 G k e0 input
                  T phi ett sigma T
                  corrT)
                sigma baseT)
              (@HierarchyBase.core V E
                inst inst_1 inst_2
                inst_3 G k e0 input T
                phi ett phi base)
              (fun
                  (_a :
                    @TreeSequence V E
                      G e0) ↦
                @TreeSequenceInitialSegment
                  V E G e0 _a
                  (@TashkinovHierarchy.stage
                    V E inst inst_1
                    inst_2 inst_3 G k
                    e0 input T phi phi
                    ett base H
                    (@Fin.mk
                      (@HAdd.hAdd Nat
                        Nat Nat
                        (@instHAdd Nat
                          instAddNat)
                        (@TashkinovHierarchy.dividerCount
                          V E inst
                          inst_1
                          inst_2
                          inst_3 G k
                          e0 input T
                          phi phi ett
                          base H)
                        (@OfNat.ofNat
                          Nat
                          (nat_lit 2)
                          (instOfNatNat
                            (nat_lit
                              2))))
                      (@OfNat.ofNat
                        Nat
                        (nat_lit 1)
                        (instOfNatNat
                          (nat_lit
                            1)))
                      (by
                        have :=
                          GoldbergSeymour.TreeSequence.positive
                            T
                        omega))))
              hcoreT))
          (@TashkinovHierarchy.coreInsideFirst
            V E inst inst_1 inst_2
            inst_3 G k e0 input T phi
            phi ett base H) :
      TashkinovHierarchy
        corrT.replacementETT baseT };
  (∀
      (j :
        Fin
          (H.dividerCount + (1 : ℕ))),
      HierarchyStarredStage K j =
        HierarchyStarredStage H j) →
  (∀
      (j :
        Fin
          (H.dividerCount +
            (1 : ℕ))),
      HierarchyStoredColorsAt K j =
        HierarchyStoredColorsAt H
          j) →
  (∀
      (j :
        Fin
          (H.dividerCount +
            (1 : ℕ))),
      HierarchyStageMissingColors
          K j =
        HierarchyStageMissingColors
          H j) →
  (∀
      (j :
        Fin
          (H.dividerCount +
            (1 : ℕ))),
      ∀
        eta ∈
          HierarchyStoredColorsAt
            H j,
        ∀
          c ∈
            C.good.gamma j eta,
          c ≠ alpha ∧
            c ≠ beta) →
  (∀
      (j :
        Fin
          (H.dividerCount +
            (1 : ℕ))),
      ∀
        eta ∈
          HierarchyStoredColorsAt
            H j,
        ∀ (c : Fin k),
          c ≠ alpha →
            c ≠ beta →
              c ∈
                  HierarchySegmentColors
                    K j eta →
                c ∈
                  HierarchySegmentColors
                    H j eta) →
  (∀
      (S :
        TreeSequence G e0),
      TreeSequenceVertexSet
            S ⊆
          TreeSequenceVertexSet
            A →
        ∀
          (R :
            Finset (Fin k)),
          TreeColorSetMinusClosed
              G sigma S R ↔
            TreeColorSetMinusClosed
              G phi S R) →
  GoodHierarchy K := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne sigma H q A n Tn Dn coreToA
      TnToA ordinaryToA missingA treeMissingEq closureInsideA corrT baseT hcoreT hclosureT
      terminalData K starredEq storedEq stageMissingEq gammaNot segmentTransfer minusEq
  exact {
    gamma := C.good.gamma
    twoColors := by
      intro j eta heta
      exact C.good.twoColors j eta (by rw [storedEq j] at heta; exact heta)
    avoidance := by
      intro j eta heta c hc
      have ho : eta ∈ HierarchyStoredColorsAt H j := by rw [← storedEq j]; exact heta
      have old := C.good.avoidance j eta ho hc
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [stageMissingEq j]; exact (Finset.mem_sdiff.mp old).1
      · intro hseg
        exact (Finset.mem_sdiff.mp old).2
          (segmentTransfer j eta ho c (gammaNot j eta ho c hc).1 (gammaNot j eta ho c hc).2 hseg)
    disjointPairs := by
      intro j eta theta heta htheta hne
      exact C.good.disjointPairs j eta theta
        (by rw [storedEq j] at heta; exact heta)
        (by rw [storedEq j] at htheta; exact htheta) hne
    uniqueRefresh := by
      exact @helper_uniqueRefresh_2220 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@sigma)
          (@ordinaryToA) (@missingA) (@corrT) (@baseT) (@hcoreT) (@terminalData) (@starredEq)
          (@storedEq)
    parallelBase := by
      dsimp only
      intro hp
      have hpOld : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
        terminalData.2.1.symm.trans hp
      obtain ⟨hnot, hcard⟩ := C.good.parallelBase hpOld
      constructor
      · exact @helper_branch_1161 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@sigma)
          (@coreToA) (@corrT) (@baseT) (@hcoreT) (@terminalData) (@storedEq) (@minusEq) (@hnot)
      · exact @helper_branch_1166 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@sigma)
          (@TnToA) (@treeMissingEq) (@closureInsideA) (@corrT) (@baseT) (@hcoreT) (@hclosureT)
          (@terminalData) (@storedEq) (@hpOld) (@hcard)
    minusClosed := by
      intro a
      change TreeColorSetMinusClosed G sigma (H.stage a.succ.castSucc)
        ((HierarchyStoredColorsAt K a.succ).biUnion (C.good.gamma a.castSucc))
      rw [storedEq a.succ, minusEq _ (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA
          a.succ))]
      exact C.good.minusClosed a }

theorem helper_prefixMaximum_1187.{u_1, u_2} :
    helperPrefixMaximum1187Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma H q A n Tn ib commonPrefix
      equalTrees TnToA AToT hAib terminalRoute hmod transportBefore
  by_cases he : A = Tn
  · exact Or.inl he
  · exact @helper_branch_1953 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@sigma)
      (@commonPrefix) (@equalTrees) (@TnToA) (@AToT) (@hAib) (@terminalRoute) (@hmod)
      (@transportBefore) (@he)
/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperSame2713Conditions.{u_1, u_2} : Prop :=
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
   (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
   (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core)
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
        (@CorrespondingExtendedTashkinovTree.replacementInput V E inst inst_1 inst_3 G k e0 input
         T phi ett sigma T corrT)
        T sigma
        (@CorrespondingExtendedTashkinovTree.replacementETT V E inst inst_1 inst_3 G k e0 input T
         phi ett sigma T corrT)
        sigma baseT)
       (@TashkinovHierarchy.stage V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi ett base H
        (@Fin.mk
         (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@TashkinovHierarchy.dividerCount V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi
           ett base H)
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
         (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
         (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega))))
      (@TreeSequenceInitialSegment V E G e0
       (@HierarchyBase.core V E inst inst_1 inst_2 inst_3 G k e0 input T phi ett phi base)
       (@TashkinovHierarchy.stage V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi ett base H
        (@Fin.mk
         (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@TashkinovHierarchy.dividerCount V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi
           ett base H)
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
         (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
         (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega))))
      (@id
       (@Eq Prop
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
           (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
           (by
            have := GoldbergSeymour.TreeSequence.positive T
            omega))))
        (@TreeSequenceInitialSegment V E G e0
         (@HierarchyBase.core V E inst inst_1 inst_2 inst_3 G k e0 input T phi ett phi base)
         (@TashkinovHierarchy.stage V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi ett base
          H
          (@Fin.mk
           (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@TashkinovHierarchy.dividerCount V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi
             ett base H)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
           (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
           (by
            have := GoldbergSeymour.TreeSequence.positive T
            omega)))))
       (@congrArg (@TreeSequence V E G e0) Prop
        (@HierarchyBase.core V E inst inst_1 inst_2 inst_3 G k e0
         (@CorrespondingExtendedTashkinovTree.replacementInput V E inst inst_1 inst_3 G k e0 input
          T phi ett sigma T corrT)
         T sigma
         (@CorrespondingExtendedTashkinovTree.replacementETT V E inst inst_1 inst_3 G k e0 input T
          phi ett sigma T corrT)
         sigma baseT)
        (@HierarchyBase.core V E inst inst_1 inst_2 inst_3 G k e0 input T phi ett phi base)
        (fun (_a : @TreeSequence V E G e0) ↦
         @TreeSequenceInitialSegment V E G e0 _a
          (@TashkinovHierarchy.stage V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi ett base
           H
           (@Fin.mk
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
             (@TashkinovHierarchy.dividerCount V E inst inst_1 inst_2 inst_3 G k e0 input T phi
              phi ett base H)
             (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (by
             have := GoldbergSeymour.TreeSequence.positive T
             omega))))
        hcoreT))
      (@TashkinovHierarchy.coreInsideFirst V E inst inst_1 inst_2 inst_3 G k e0 input T phi phi
       ett base H) :
    TashkinovHierarchy corrT.replacementETT baseT };
  ∀
   (starredEq :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), HierarchyStarredStage K j = HierarchyStarredStage H j)
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
  SameGoodHierarchy C.good goodT

theorem helper_same_2713.{u_1, u_2} :
    helperSame2713Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne sigma H q A n Tn Dn coreToA
      TnToA ordinaryToA missingA treeMissingEq closureInsideA corrT baseT hcoreT hclosureT
      terminalData K starredEq storedEq stageMissingEq gammaNot segmentTransfer minusEq goodT
  refine ⟨?_, rfl, ?_⟩
  · refine ⟨hcoreT.symm, rfl, HEq.rfl, HEq.rfl, ?_, fun _ => hclosureT.symm⟩
    exact ⟨fun hp => terminalData.2.1.trans hp, fun hp => terminalData.2.1.symm.trans hp⟩
  · intro j
    exact ⟨(storedEq j).symm, fun _ _ => rfl⟩

end GoldbergSeymour.StableChangeCaseThreePreparation

end
