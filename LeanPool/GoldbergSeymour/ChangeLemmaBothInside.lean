/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeInterchangeableFacts

public import LeanPool.GoldbergSeymour.TashkinovSeriesNonParallelClosed


public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyStageInterchangeability
public import LeanPool.GoldbergSeymour.GoodHierarchyNewMissingClosed
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Change Lemma Both Inside

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_closedStar_471.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ :
        IsProperEdgeColoring G phi) (_ : IsOneEdgeUncolored phi e0) (_ :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (_ : (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (other : ExtendedTashkinovTree G k e0 input' T'
        generating') (_ : other.rounds = ett.rounds) (_ : MaximumProperty other) (base' :
        HierarchyBase other generating') (K : TashkinovHierarchy other base') (_ : GoodHierarchy
        K) (_ : K.dividerCount < C.hierarchy.dividerCount), ColoredVertexSetElementary G
        generating' (TreeSequenceVertexSet T'))) (_ : (
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; (2 : ℕ) * ett.rounds + (11 : ℕ)
        ≤ (TreeMissingColors phi Tn).card)),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H r)))) (_ : CombinedStableColoring Tn
        base.closure (TashkinovStoredColors ett.series.data n) phi phi) (_ : (
    ∀ (_ : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE),
    ∀ c ∈ TreeMissingColors phi Tn, TreeColorSetClosed G phi Tn ({ c } : Finset (Fin k)))) (r :
        Fin (H.dividerCount + (1 : ℕ))) (c d : Fin k) (_ : c ≠ d) (_ : c ∈ TreeMissingColors phi
        (HierarchyStarredStage H r)) (_ : d ∈ TreeMissingColors phi (HierarchyStarredStage H r))
        (_ : TreeColorSetClosed G phi (HierarchyStarredStage H r) ({ c } : Finset (Fin k))),
        TreeInterchangeable G (HierarchyStarredStage H r) phi c d := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hlarge H n Tn
      helemStar hcombined nonPEMissingClosed r c d hcd hc hd hclosed
  cases r using Fin.cases with
  | zero =>
    change c ∈ TreeMissingColors phi base.core at hc
    change d ∈ TreeMissingColors phi base.core at hd
    change TreeColorSetClosed G phi base.core {c} at hclosed
    change TreeInterchangeable G base.core phi c d
    by_cases hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (interchange G k e0 input T phi phi ett C.maximum C.positive
        hlower hPE base hproper hone hcombined c d).2.2.1 hc hclosed
    · have hcore : base.core = Tn := base.nonparallel hPE
      have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Tn) := by
        rw [← hcore]
        exact helemStar 0
      have hempty : BoundaryColorEdges G phi (TreeSequenceVertexSet Tn) d = ∅ :=
        nonPEMissingClosed hPE d (by simpa only [hcore] using hd)
          d (Finset.mem_singleton_self _)
      rw [hcore]
      exact ElementarySingleBoundaryInterchangeable G phi Tn c d hproper helem
        (by simpa only [hcore] using hclosed c (Finset.mem_singleton_self _))
        (by rw [hempty]; simp)
  | succ i =>
    exact step1 G k e0 input T phi ett C.maximum C.positive hproper hone
      hlower base H C.good hfewer hlarge i c d hc hcd hclosed

private theorem helper_coreSame_500.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ :
        IsProperEdgeColoring G phi) (_ : IsOneEdgeUncolored phi e0) (_ :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let a : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    let b : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
    ∀ (_ : (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H r)))) (_ : alpha ∈ MissingColors G phi a)
        (_ : beta ∈ MissingColors G phi b) (_ : (
    ∀ (B : TreeSequence G e0) (c d : Fin k) (_ : TreeInterchangeable G B phi c d),
        TreeInterchangeable G B phi d c)) (_ : (
    ∀ (B : TreeSequence G e0) (_ : a ∈ TreeSequenceVertexSet B) (_ : b ∈ TreeSequenceVertexSet B)
        (_ : TreeInterchangeable G B phi alpha beta), TwoColorComponent G phi alpha beta (Sum.inl
        a) = TwoColorComponent G phi alpha beta (Sum.inl b))) (_ : (
    ∀ (B : TreeSequence G e0) (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B)) (_
        : TreeColorSetClosed G phi B ({ alpha } : Finset (Fin k))) (_ : TreeColorSetClosed G phi B
        ({ beta } : Finset (Fin k))), TreeInterchangeable G B phi alpha beta)) (_ :
        CombinedStableColoring Tn base.closure (TashkinovStoredColors ett.series.data n) phi phi)
        (_ : (
    ∀ (_ : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE),
    ∀ c ∈ TreeMissingColors phi Tn, TreeColorSetClosed G phi Tn ({ c } : Finset (Fin k)))) (_ : a
        ∈ TreeSequenceVertexSet base.core) (_ : b ∈ TreeSequenceVertexSet base.core),
        TwoColorComponent G phi alpha beta (Sum.inl a) = TwoColorComponent G phi alpha beta
        (Sum.inl b) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower alpha beta H n Tn a b
      helemStar haMissing hbMissing interchangeableSwap equalFromInterchange bothClosed hcombined
      nonPEMissingClosed haCore hbCore
  by_cases hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · obtain ⟨_, _, ⟨hu⟩⟩ := base.parallel hPE
    have haUnion : a ∈ TreeSequenceVertexSet Tn ∨
        a ∈ TreeSequenceVertexSet base.closure := by
      simpa only [hu.vertexSet, Finset.mem_union] using haCore
    have hbUnion : b ∈ TreeSequenceVertexSet Tn ∨
        b ∈ TreeSequenceVertexSet base.closure := by
      simpa only [hu.vertexSet, Finset.mem_union] using hbCore
    have hi := interchange G k e0 input T phi phi ett C.maximum C.positive
      hlower hPE base hproper hone hcombined alpha beta
    have hj := interchange G k e0 input T phi phi ett C.maximum C.positive
      hlower hPE base hproper hone hcombined beta alpha
    rcases haUnion with haN | haR <;> rcases hbUnion with hbN | hbR
    · exact equalFromInterchange Tn haN hbN
        (hi.2.1 (Finset.mem_biUnion.mpr ⟨a, haN, haMissing⟩))
    · exact equalFromInterchange base.core haCore hbCore
        (hi.2.2.2 (Finset.mem_biUnion.mpr ⟨a, haN, haMissing⟩)
          (Finset.mem_biUnion.mpr ⟨b, hbR, hbMissing⟩))
    · exact equalFromInterchange base.core haCore hbCore
        (interchangeableSwap base.core beta alpha
          (hj.2.2.2 (Finset.mem_biUnion.mpr ⟨b, hbN, hbMissing⟩)
            (Finset.mem_biUnion.mpr ⟨a, haR, haMissing⟩)))
    · exact equalFromInterchange base.closure haR hbR
        (hi.1 (Finset.mem_biUnion.mpr ⟨a, haR, haMissing⟩))
  · have hcore : base.core = Tn := base.nonparallel hPE
    have haN : a ∈ TreeSequenceVertexSet Tn := by simpa only [hcore] using haCore
    have hbN : b ∈ TreeSequenceVertexSet Tn := by simpa only [hcore] using hbCore
    have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Tn) := by
      rw [← hcore]
      exact helemStar 0
    exact equalFromInterchange Tn haN hbN
      (bothClosed Tn helem
        (nonPEMissingClosed hPE alpha (Finset.mem_biUnion.mpr ⟨a, haN, haMissing⟩))
        (nonPEMissingClosed hPE beta (Finset.mem_biUnion.mpr ⟨b, hbN, hbMissing⟩)))

private theorem helper_hsame_542.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta
        : Fin k) (_ : alpha ≠ beta),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let a : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    let b : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
    ∀ (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A)) (_ : (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H r)))) (_ : alpha ∈ MissingColors G phi a)
        (_ : beta ∈ MissingColors G phi b) (_ : a ∈ TreeSequenceVertexSet A) (_ : b ∈
        TreeSequenceVertexSet A) (_ : (
    ∀ (B : TreeSequence G e0) (c d : Fin k) (_ : TreeInterchangeable G B phi c d),
        TreeInterchangeable G B phi d c)) (_ : (
    ∀ (B : TreeSequence G e0) (_ : a ∈ TreeSequenceVertexSet B) (_ : b ∈ TreeSequenceVertexSet B)
        (_ : TreeInterchangeable G B phi alpha beta), TwoColorComponent G phi alpha beta (Sum.inl
        a) = TwoColorComponent G phi alpha beta (Sum.inl b))) (_ : (
    ∀ (B : TreeSequence G e0) (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B)) (_
        : TreeColorSetClosed G phi B ({ alpha } : Finset (Fin k))) (_ : TreeColorSetClosed G phi B
        ({ beta } : Finset (Fin k))), TreeInterchangeable G B phi alpha beta)) (_ : (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))) (c d : Fin k) (_ : c ≠ d) (_ : c ∈ TreeMissingColors
        phi (HierarchyStarredStage H r)) (_ : d ∈ TreeMissingColors phi (HierarchyStarredStage H
        r)) (_ : TreeColorSetClosed G phi (HierarchyStarredStage H r) ({ c } : Finset (Fin k))),
        TreeInterchangeable G (HierarchyStarredStage H r) phi c d)) (_ : (
    ∀ (_ : a ∈ TreeSequenceVertexSet base.core) (_ : b ∈ TreeSequenceVertexSet base.core),
        TwoColorComponent G phi alpha beta (Sum.inl a) = TwoColorComponent G phi alpha beta
        (Sum.inl b))) (_ : alpha ∈ TreeMissingColors phi A) (_ : beta ∈ TreeMissingColors phi A),
        TwoColorComponent G phi alpha beta (Sum.inl a) = TwoColorComponent G phi alpha beta
        (Sum.inl b) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne H q A a b helemA helemStar
      haMissing hbMissing haA hbA interchangeableSwap equalFromInterchange bothClosed closedStar
      coreSame haMissingA hbMissingA
  by_cases haClosed : TreeColorSetClosed G phi A {alpha}
  · by_cases hbClosed : TreeColorSetClosed G phi A {beta}
    · exact equalFromInterchange A haA hbA (bothClosed A helemA haClosed hbClosed)
    · exact equalFromInterchange A haA hbA
        (closedStar q alpha beta hne haMissingA hbMissingA haClosed)
  · by_cases hbClosed : TreeColorSetClosed G phi A {beta}
    · exact equalFromInterchange A haA hbA
        (interchangeableSwap A beta alpha
          (closedStar q beta alpha hne.symm hbMissingA haMissingA hbClosed))
    · -- Descend to the least starred stage containing both witnesses.
      let P (r : ℕ) : Prop := ∃ hr : r ≤ H.dividerCount,
        a ∈ TreeSequenceVertexSet (HierarchyStarredStage H ⟨r, by omega⟩) ∧
        b ∈ TreeSequenceVertexSet (HierarchyStarredStage H ⟨r, by omega⟩)
      have hex : ∃ r, P r := ⟨H.dividerCount, le_rfl, haA, hbA⟩
      let r := Nat.find hex
      obtain ⟨hr, har, hbr⟩ : P r := Nat.find_spec hex
      by_cases hr0 : r = 0
      · have hz : (⟨r, by omega⟩ : Fin (H.dividerCount + 1)) = 0 := Fin.ext hr0
        rw [hz] at har hbr
        exact coreSame har hbr
      · let i : Fin H.dividerCount := ⟨r - 1, by omega⟩
        have hri : (⟨r, by omega⟩ : Fin (H.dividerCount + 1)) = i.succ := by
          apply Fin.ext
          simp [i]
          omega
        have haCurrent : a ∈ TreeSequenceVertexSet (H.stage i.succ.castSucc) := by
          simpa only [hri, HierarchyStarredStage, Fin.cases_succ] using har
        have hbCurrent : b ∈ TreeSequenceVertexSet (H.stage i.succ.castSucc) := by
          simpa only [hri, HierarchyStarredStage, Fin.cases_succ] using hbr
        have hnotPrevious : ¬ (a ∈ TreeSequenceVertexSet
              (HierarchyStarredStage H i.castSucc) ∧
            b ∈ TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)) := by
          intro hab
          have hprev : P (r - 1) := ⟨by omega, hab.1, hab.2⟩
          have hmin := Nat.find_min' hex hprev
          change r ≤ r - 1 at hmin
          omega
        have helemCurrent : ColoredVertexSetElementary G phi
            (TreeSequenceVertexSet (H.stage i.succ.castSucc)) := helemStar i.succ
        have ham : alpha ∈ TreeMissingColors phi (H.stage i.succ.castSucc) :=
          Finset.mem_biUnion.mpr ⟨a, haCurrent, haMissing⟩
        have hbm : beta ∈ TreeMissingColors phi (H.stage i.succ.castSucc) :=
          Finset.mem_biUnion.mpr ⟨b, hbCurrent, hbMissing⟩
        by_cases haPrev : a ∈ TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)
        · have hbPrev : b ∉ TreeSequenceVertexSet
              (HierarchyStarredStage H i.castSucc) := fun hb => hnotPrevious ⟨haPrev, hb⟩
          have hnew := GoodHierarchyNewMissingClosed C.good i helemCurrent beta
            (Finset.mem_biUnion.mpr
              ⟨b, Finset.mem_sdiff.mpr ⟨hbCurrent, hbPrev⟩, hbMissing⟩)
          have hclosed : TreeColorSetClosed G phi (H.stage i.succ.castSucc) {beta} := by
            intro d hd
            have hd' := Finset.mem_singleton.mp hd
            simpa only [hd'] using hnew
          exact equalFromInterchange (H.stage i.succ.castSucc) haCurrent hbCurrent
            (interchangeableSwap _ beta alpha
              (closedStar i.succ beta alpha hne.symm hbm ham hclosed))
        · have hnew := GoodHierarchyNewMissingClosed C.good i helemCurrent alpha
            (Finset.mem_biUnion.mpr
              ⟨a, Finset.mem_sdiff.mpr ⟨haCurrent, haPrev⟩, haMissing⟩)
          have hclosed : TreeColorSetClosed G phi (H.stage i.succ.castSucc) {alpha} := by
            intro d hd
            have hd' := Finset.mem_singleton.mp hd
            simpa only [hd'] using hnew
          exact equalFromInterchange (H.stage i.succ.castSucc) haCurrent hbCurrent
            (closedStar i.succ alpha beta hne ham hbm hclosed)

private theorem helper_equalFromInterchange_881 {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {alpha beta : Fin k} {a b : V} (proper : IsProperEdgeColoring G phi)
    (different : alpha ≠ beta) (firstMissing : alpha ∈ MissingColors G phi a)
    (secondMissing : beta ∈ MissingColors G phi b) (B : TreeSequence G e0)
    (firstInside : a ∈ TreeSequenceVertexSet B) (secondInside : b ∈ TreeSequenceVertexSet B)
    (interchange : TreeInterchangeable G B phi alpha beta) :
    TwoColorComponent G phi alpha beta (Sum.inl a) =
      TwoColorComponent G phi alpha beta (Sum.inl b) := by
  apply interchange _ _ (TwoColorPathComponent.of_missing proper different firstMissing)
    (TwoColorPathComponent.swap G phi beta alpha _
      (TwoColorPathComponent.of_missing proper different.symm secondMissing))
  · exact ⟨a, firstInside, rfl⟩
  · exact ⟨b, secondInside, rfl⟩

private theorem helper_nonPEMissingClosed_914.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta
        : Fin k) (_ : (
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀ (_ : alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A), TreeVertexOrder T
        (T.vertex ia) (T.vertex ib) ∧ alpha ∉ ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑ib : ℕ) ∧ phi (T.edge t) = some c} :
        Finset (Fin k)))),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : (
    ∀ (_ : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE), ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet Tn))) (_ : ett.series.data.kind n ≠ some
        TashkinovExtensionKind.PE),
    ∀ c ∈ TreeMissingColors phi Tn, TreeColorSetClosed G phi Tn ({ c } : Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta _ n Tn hnonPEClosed hnonPE c hc d hd
  have hdc : d = c := Finset.mem_singleton.mp hd
  subst d
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨x, hx, hcx⟩ := Finset.mem_biUnion.mp hc
  have hfd : f ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) ∧
      phi f = some c := by simpa [BoundaryColorEdges] using hf
  exact hnonPEClosed hnonPE hfd.1 hx hfd.2 hcx

private theorem helper_helemStar_926.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (_ : (
    ∀ (r s : Fin (H.dividerCount + (1 : ℕ))) (_ : r ≤ s), TreeSequenceInitialSegment
        (HierarchyStarredStage H r) (HierarchyStarredStage H s))) (_ : ColoredVertexSetElementary
        G phi (TreeSequenceVertexSet A)) (r : Fin (H.dividerCount + (1 : ℕ))),
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet (HierarchyStarredStage H r)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A starChain helemA r
  have hsub := TreeSequenceInitialSegmentVertexSetSubset
    (starChain r q (Fin.le_last r))
  intro u hu v hv hne'
  exact helemA (hsub hu) (hsub hv) hne'

private theorem helper_bothClosed_972.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E)
      (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G phi)
      (alpha beta : Fin k) (B : TreeSequence G e0)
      (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B))
      (_ : TreeColorSetClosed G phi B ({ alpha } : Finset (Fin k)))
      (_ : TreeColorSetClosed G phi B ({ beta } : Finset (Fin k))),
    TreeInterchangeable G B phi alpha beta := by
  classical
  intro V E _ _ G k e0 phi hproper alpha beta B helem hc hd
  apply ElementarySingleBoundaryInterchangeable G phi B alpha beta
    hproper helem (hc alpha (Finset.mem_singleton_self _))
  rw [hd beta (Finset.mem_singleton_self _)]
  simp

private theorem helper_continuation_1524.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ :
        IsProperEdgeColoring G phi) (_ : IsOneEdgeUncolored phi e0) (_ :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (_ : (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (other : ExtendedTashkinovTree G k e0 input' T'
        generating') (_ : other.rounds = ett.rounds) (_ : MaximumProperty other) (base' :
        HierarchyBase other generating') (K : TashkinovHierarchy other base') (_ : GoodHierarchy
        K) (_ : K.dividerCount < C.hierarchy.dividerCount), ColoredVertexSetElementary G
        generating' (TreeSequenceVertexSet T'))) (_ : (
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; (2 : ℕ) * ett.rounds + (11 : ℕ)
        ≤ (TreeMissingColors phi Tn).card)) (alpha beta : Fin k) (_ : alpha ≠ beta) (_ : (
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀ (_ : alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A), TreeVertexOrder T
        (T.vertex ia) (T.vertex ib) ∧ alpha ∉ ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑ib : ℕ) ∧ phi (T.edge t) = some c} :
        Finset (Fin k)))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let a : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    let b : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
    ∀ (_ : (
    ∀ {U W Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment U W) (_ :
        TreeSequenceInitialSegment W Z), TreeSequenceInitialSegment U Z)) (_ :
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet A)) (_ : (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H r)))) (_ : alpha ∈ MissingColors G phi a)
        (_ : beta ∈ MissingColors G phi b) (_ : a ∈ TreeSequenceVertexSet A) (_ : b ∈
        TreeSequenceVertexSet A) (_ : (
    ∀ (B : TreeSequence G e0) (c d : Fin k) (_ : TreeInterchangeable G B phi c d),
        TreeInterchangeable G B phi d c)) (_ : (
    ∀ (B : TreeSequence G e0) (_ : a ∈ TreeSequenceVertexSet B) (_ : b ∈ TreeSequenceVertexSet B)
        (_ : TreeInterchangeable G B phi alpha beta), TwoColorComponent G phi alpha beta (Sum.inl
        a) = TwoColorComponent G phi alpha beta (Sum.inl b))) (_ : (
    ∀ (B : TreeSequence G e0) (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B)) (_
        : TreeColorSetClosed G phi B ({ alpha } : Finset (Fin k))) (_ : TreeColorSetClosed G phi B
        ({ beta } : Finset (Fin k))), TreeInterchangeable G B phi alpha beta)) (_ :
        CombinedStableColoring Tn base.closure (TashkinovStoredColors ett.series.data n) phi phi),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    let vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
    let sameComponent : Prop := TwoColorComponent G phi alpha beta (Sum.inl va) =
        TwoColorComponent G phi alpha beta (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (alpha ∈
        TreeMissingColors phi Tnq ∨ Disjoint (insert alpha ({ beta } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ (H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        phi Tn ∨ Disjoint (insert alpha ({ beta } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ (alpha ∈ TreeMissingColors phi A ∧ TreeColorSetClosed G phi A ({ alpha }
        : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A phi alpha beta) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hlarge alpha beta
      hne _ H q A n Tn a b trans helemA helemStar haMissing hbMissing haA hbA interchangeableSwap
      equalFromInterchange bothClosed hcombined
  have hnonPEClosed
      (hnonPE : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE) :
      ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn) := by
    exact ett.series.closedOfNonParallel n
      (by simpa only [n, Fin.val_last] using C.positive) phi hproper hone
      ett.generatingColoring hnonPE
  have nonPEMissingClosed
      (hnonPE : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE)
      (c : Fin k) (hc : c ∈ TreeMissingColors phi Tn) :
      TreeColorSetClosed G phi Tn {c} := by
    exact @helper_nonPEMissingClosed_914 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (by assumption) (@hnonPEClosed) (@hnonPE) (@c) (@hc)
  have closedStar := @helper_closedStar_471 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@hfewer) (@hlarge) (@helemStar) (@hcombined) (@nonPEMissingClosed)
  have coreSame := @helper_coreSame_500 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@alpha) (@beta) (@helemStar) (@haMissing) (@hbMissing) (@interchangeableSwap)
      (@equalFromInterchange) (@bothClosed) (@hcombined) (@nonPEMissingClosed)
  have haMissingA : alpha ∈ TreeMissingColors phi A :=
    Finset.mem_biUnion.mpr ⟨a, haA, haMissing⟩
  have hbMissingA : beta ∈ TreeMissingColors phi A :=
    Finset.mem_biUnion.mpr ⟨b, hbA, hbMissing⟩
  have hsame :=
    @helper_hsame_542 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@hne) (@helemA)
        (@helemStar) (@haMissing) (@hbMissing) (@haA) (@hbA) (@interchangeableSwap)
        (@equalFromInterchange) (@bothClosed) (@closedStar) (@coreSame) (@haMissingA) (@hbMissingA)
  refine ⟨fun _ => hsame, fun _ => hsame, ?_⟩
  intro hc
  exact ⟨hsame, closedStar q alpha beta hne hc.1 hbMissingA hc.2⟩

theorem ChangeLemmaBothInside {V E : Type*}
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
    (_ : ∀ {input' : PartialEdgeColoring E k}
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
    (_ :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let ia := HierarchyFirstMissingPosition phi T alpha
      let ib := HierarchyFirstMissingPosition phi T beta
      (alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A) →
        TreeVertexOrder T (T.vertex ia) (T.vertex ib) ∧
          alpha ∉ (Finset.univ.filter fun c =>
            ∃ t : Fin T.length,
              A.length ≤ t.val ∧ t.val < ib.val ∧
                phi (T.edge t) = some c))
    (hlocation :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
      va ∈ TreeSequenceVertexSet A ∧
        vb ∈ TreeSequenceVertexSet A) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let A := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dn := TashkinovStoredColors ett.series.data n
    let Dnq := HierarchyStoredColorsAt H q
    let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
    let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
    let sameComponent := TwoColorComponent G phi alpha beta (Sum.inl va) =
      TwoColorComponent G phi alpha beta (Sum.inl vb)
    (0 < H.dividerCount ∧
        (alpha ∈ TreeMissingColors phi Tnq ∨
          Disjoint ({alpha, beta} : Finset (Fin k)) Dnq) →
      sameComponent) ∧
    (H.dividerCount = 0 ∧
        (alpha ∈ TreeMissingColors phi Tn ∨
          Disjoint ({alpha, beta} : Finset (Fin k)) Dn) →
      sameComponent) ∧
    (alpha ∈ TreeMissingColors phi A ∧
        TreeColorSetClosed G phi A {alpha} →
      sameComponent ∧ TreeInterchangeable G A phi alpha beta) := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let a := T.vertex (HierarchyFirstMissingPosition phi T alpha)
  let b := T.vertex (HierarchyFirstMissingPosition phi T beta)
  let Ty := TreeSequencePrefix T
    (min (A.length + ((T.length - A.length) - 1)) T.length)
    (by have hA := A.positive; have hT := T.positive; omega)
    (Nat.min_le_right _ _)
  have trans := @TreeSequenceInitialSegment.trans V E G e0
  have starChain := H.starredStageInitialSegmentOfLE
  have hAT : TreeSequenceInitialSegment A T := H.lastStarredInitialSegment
  have hTyT : TreeSequenceInitialSegment Ty T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hATy : TreeSequenceInitialSegment A Ty := hTyT.of_common_extension hAT (by
    change A.length ≤ min (A.length + ((T.length - A.length) - 1)) T.length
    exact Nat.le_min.mpr ⟨Nat.le_add_right _ _, hAT.1⟩)
  have helemA : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
    intro u hu v hv hne'
    exact hprefixElementary
      (TreeSequenceInitialSegmentVertexSetSubset hATy hu)
      (TreeSequenceInitialSegmentVertexSetSubset hATy hv) hne'
  have helemStar := @helper_helemStar_926 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@starChain) (@helemA)
  have missingFirst (color : Fin k) (member : color ∈ TreeMissingColors phi Ty) :
      color ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T color)) :=
    TreeSequenceFirstMissingPositionMemOfMissing (hTyT.treeMissingColors_subset member)
  have haMissing : alpha ∈ MissingColors G phi a :=
    missingFirst alpha hmissingPrefix.1
  have hbMissing : beta ∈ MissingColors G phi b :=
    missingFirst beta hmissingPrefix.2
  have haA : a ∈ TreeSequenceVertexSet A := hlocation.1
  have hbA : b ∈ TreeSequenceVertexSet A := hlocation.2
  have interchangeableSwap (B : TreeSequence G e0) (c d : Fin k)
      (interchange : TreeInterchangeable G B phi c d) : TreeInterchangeable G B phi d c :=
    interchange.symm
  have equalFromInterchange :=
    helper_equalFromInterchange_881 (e0 := e0) hproper hne haMissing hbMissing
  have bothClosed := @helper_bothClosed_972 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@hproper) (@alpha) (@beta)
  have stableRefl (B : TreeSequence G e0) (D : Finset (Fin k)) :
      StableColoring B D phi phi :=
    ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
  have hcombined : CombinedStableColoring Tn base.closure
      (TashkinovStoredColors ett.series.data n) phi phi :=
    ⟨stableRefl _ _, stableRefl _ _⟩
  exact @helper_continuation_1524 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@hfewer) (@hlarge) (@alpha) (@beta) (@hne) (by assumption) (@trans) (@helemA)
      (@helemStar) (@haMissing) (@hbMissing) (@haA) (@hbA) (@interchangeableSwap)
      (@equalFromInterchange) (@bothClosed) (@hcombined)
end GoldbergSeymour

end
