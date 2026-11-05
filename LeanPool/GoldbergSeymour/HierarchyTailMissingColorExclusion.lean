/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTailPrefix

public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HierarchyNonparallelFirstEdge
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificate
public import LeanPool.GoldbergSeymour.RevisitingExtensionSeedStoredColor
public import LeanPool.GoldbergSeymour.SimpleExtensionSeedStoredColor
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePosition
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorCycle
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Hierarchy Tail Missing Color Exclusion

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_segmentTrans_135.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y
        Z → TreeSequenceInitialSegment X Z := by
  classical
  intro V E G e0 X Y Z hXY hYZ
  rcases hXY with ⟨hxy, hvxy, hexy⟩
  rcases hYZ with ⟨hyz, hvyz, heyz⟩
  refine ⟨le_trans hxy hyz, ?_, ?_⟩
  · intro r
    have hmid := hvyz (Fin.castLE (Nat.succ_le_succ hxy) r)
    simpa using hmid.trans (hvxy r)
  · intro r
    have hmid := heyz (Fin.castLE hxy r)
    simpa using hmid.trans (hexy r)

private theorem helper_commonPrefix_148.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y
        Z → X.length ≤ Y.length → TreeSequenceInitialSegment X Y := by
  classical
  intro V E G e0 X Y Z hXZ hYZ hXY
  rcases hXZ with ⟨hxz, hvxz, hexz⟩
  rcases hYZ with ⟨hyz, hvyz, heyz⟩
  refine ⟨hXY, ?_, ?_⟩
  · intro r
    calc
      Y.vertex (Fin.castLE (Nat.succ_le_succ hXY) r) =
          Z.vertex (Fin.castLE (Nat.succ_le_succ hyz)
            (Fin.castLE (Nat.succ_le_succ hXY) r)) :=
        (hvyz _).symm
      _ = Z.vertex (Fin.castLE (Nat.succ_le_succ hxz) r) := by
        congr 1
      _ = X.vertex r := hvxz r
  · intro r
    calc
      Y.edge (Fin.castLE hXY r) =
          Z.edge (Fin.castLE hyz (Fin.castLE hXY r)) :=
        (heyz _).symm
      _ = Z.edge (Fin.castLE hxz r) := by
        congr 1
      _ = X.edge r := hexz r

private theorem helper_prefixToTree_173.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      (X : TreeSequence G e0) (m : ℕ) (hm : (1 : ℕ) ≤ m) (hmX : m ≤ X.length),
    TreeSequenceInitialSegment (TreeSequencePrefix X m hm hmX) X := by
  classical
  intro V E G e0 X m hm hmX
  refine ⟨hmX, ?_, ?_⟩
  · intro r
    simp [TreeSequencePrefix]
  · intro r
    simp [TreeSequencePrefix]

private theorem helper_stageToEnd_206.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (i : ℕ) (_ :
        Fin (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length
        + i) T.length) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    )).length), (
    ∀ (X : TreeSequence G e0), TreeSequenceInitialSegment X X) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage r.castSucc)
        (H.stage (Fin.last (H.dividerCount + (1 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H i t segmentRefl segmentTrans
  have forward : ∀ r : Fin (H.dividerCount + 1), ∀ d : ℕ,
      ∀ hbound : r.val + d ≤ H.dividerCount + 1,
      TreeSequenceInitialSegment (H.stage r.castSucc)
        (H.stage ⟨r.val + d, by omega⟩) := by
    intro r d
    induction d with
    | zero =>
        intro hbound
        exact segmentRefl _
    | succ d ih =>
        intro hbound
        let s : Fin (H.dividerCount + 1) :=
          ⟨r.val + d, by omega⟩
        have hfirst := ih (by omega)
        have hnext := H.nested s
        have hmid : H.stage s.castSucc =
            H.stage ⟨r.val + d, by omega⟩ := by
          congr 1
        have hlast : H.stage s.succ =
            H.stage ⟨r.val + Nat.succ d, by omega⟩ := by
          apply congrArg H.stage
          apply Fin.ext
          rfl
        rw [← hmid] at hfirst
        rw [hlast] at hnext
        exact segmentTrans hfirst hnext
  intro r
  have hforward := forward r (H.dividerCount + 1 - r.val) (by omega)
  simpa [Fin.last] using hforward

private theorem helper_hAT_238.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (i : ℕ) (_ :
        Fin (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length
        + i) T.length) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    )).length),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage r.castSucc)
        (H.stage (Fin.last (H.dividerCount + (1 : ℕ))))) → TreeSequenceInitialSegment A T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H i t q A stageToEnd
  rw [show T = H.stage (Fin.last (H.dividerCount + 1)) from
    H.terminalStage.symm]
  by_cases hq : H.dividerCount = 0
  · have hA : A = base.core := by
      dsimp [A, q, HierarchyStarredStage]
      have hz : Fin.last H.dividerCount =
          (0 : Fin (H.dividerCount + 1)) := by
        apply Fin.ext
        simp [hq]
      rw [hz]
      rfl
    have hs : H.stage (Fin.last (H.dividerCount + 1)) = H.stage 1 := by
      apply congrArg H.stage
      apply Fin.ext
      simp [hq]
    simpa [hA, hs] using H.coreInsideFirst
  · have hs : A = H.stage q.castSucc := by
      have hqsucc : ∃ r : Fin H.dividerCount, q = r.succ := by
        refine ⟨⟨H.dividerCount - 1, by omega⟩, ?_⟩
        apply Fin.ext
        simp [q]
        omega
      rcases hqsucc with ⟨r, hr⟩
      change HierarchyStarredStage H q = H.stage q.castSucc
      rw [hr]
      dsimp [HierarchyStarredStage]
    rw [hs]
    exact stageToEnd q

private theorem helper_stageFromFirst_267.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (i : ℕ) (_ :
        Fin (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length
        + i) T.length) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    )).length), (
    ∀ (X : TreeSequence G e0), TreeSequenceInitialSegment X X) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    ∀ (d : ℕ) (hd : d ≤ H.dividerCount), TreeSequenceInitialSegment (H.stage (⟨(1 : ℕ),
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨(1 : ℕ) + d,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H i t segmentRefl segmentTrans d
  induction d with
  | zero =>
      intro hd
      exact segmentRefl _
  | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      have hnext := H.nested ⟨1 + d, by omega⟩
      have hnext' : TreeSequenceInitialSegment
          (H.stage ⟨1 + d, by omega⟩)
          (H.stage ⟨1 + (d + 1), by omega⟩) := by
        simpa [Nat.add_assoc] using hnext
      exact segmentTrans hprev hnext'

private theorem helper_hAeqPositive_284.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (i : ℕ) (_ :
        Fin (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length
        + i) T.length) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    )).length),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (0 : ℕ) < H.dividerCount → A = H.stage
        (⟨H.dividerCount,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H i t q A hq
  have hlast : q =
      (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
    apply Fin.ext
    simp [q]
    omega
  dsimp [A, HierarchyStarredStage]
  rw [hlast]
  simp only [Fin.cases]
  apply congrArg H.stage
  apply Fin.ext
  simp
  omega

private theorem helper_hFirstA_298.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (i : ℕ) (_ :
        Fin (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length
        + i) T.length) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    )).length),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (
    ∀ (d : ℕ) (hd : d ≤ H.dividerCount), TreeSequenceInitialSegment (H.stage (⟨(1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨(1 : ℕ) + d,
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))))) → ((0 : ℕ) < H.dividerCount → A = H.stage
        (⟨H.dividerCount,
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    ∀ (hq : (0 : ℕ) < H.dividerCount), TreeSequenceInitialSegment (H.stage (⟨(1 : ℕ),
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H i t q A stageFromFirst hAeqPositive hq
  have hs := stageFromFirst (H.dividerCount - 1) (by omega)
  rw [hAeqPositive hq]
  convert hs using 1
  apply congrArg H.stage
  apply Fin.ext
  simp
  omega

private theorem helper_hCoreA_307.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (i : ℕ) (_ :
        Fin (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length
        + i) T.length) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    )).length),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (
    ∀ (X : TreeSequence G e0), TreeSequenceInitialSegment X X) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ (hq : (0 : ℕ) < H.dividerCount), TreeSequenceInitialSegment (H.stage (⟨(1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) A) → TreeSequenceInitialSegment base.core A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H i t q A segmentRefl segmentTrans hFirstA
  by_cases hq : H.dividerCount = 0
  · have hA : A = base.core := by
      simp [A, q, HierarchyStarredStage, Fin.last, Fin.cases, hq]
    rw [hA]
    exact segmentRefl _
  · exact segmentTrans H.coreInsideFirst (hFirstA (Nat.pos_of_ne_zero hq))

private theorem helper_finishNonparallel_499.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (i : ℕ), (1
        : ℕ) ≤ i →
    ∀ (beta : Fin k) (t : Fin (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + i) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by
                omega
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length)).length),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let Ty : ℕ → TreeSequence G e0 := fun (j : ℕ) ↦ TreeSequencePrefix T (min (A.length + j)
        T.length) (
    have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive;
    by
        omega
    ) (Nat.min_le_right (A.length + j) T.length);
    let B : TreeSequence G e0 := Ty (ell - (1 : ℕ));
    let Ti : TreeSequence G e0 := Ty i; A.length ≤ (↑t : ℕ) → phi (Ti.edge t) = some beta → (
    ∀ (X : TreeSequence G e0), TreeSequenceInitialSegment X X) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) → (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage r.castSucc)
        (H.stage (Fin.last (H.dividerCount + (1 : ℕ))))) → (
    ∀ (hq : (0 : ℕ) < H.dividerCount), TreeSequenceInitialSegment (H.stage (⟨(1 : ℕ),
    by
                omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) A) → Ti.length = A.length + i → B.length = A.length +
        (ell - (1 : ℕ)) → TreeSequenceInitialSegment A Ti → (
    ∀ {X : TreeSequence G e0}, TashkinovAugmentationSequence phi X Ti → X.length ≤ (↑t : ℕ) →
        False) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Tfinal : TreeSequence G e0 := ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)));
        TreeSequenceInitialSegment Ti Tfinal → TashkinovSeriesStep G k ett.rounds e0 input
        ett.series.data n → ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE →
    ∀ (f : E), ett.series.data.connectingEdges n = ({ f } : Finset E) →
    ∀ (seed : TreeSequence G e0), TreeSequenceAdjoinEdge Tn f seed → TashkinovClosure phi seed
        Tfinal → (phi f = some beta → beta ∈ TashkinovStoredColors ett.series.data n) →
        H.dividerCount = (0 : ℕ) ∧ base.core = ett.series.data.tree (Fin.last ett.rounds).castSucc
        ∧ (↑t : ℕ) = A.length ∧
    ∃ (f : E), TashkinovSeriesStep G k ett.rounds e0 input ett.series.data (Fin.last ett.rounds) ∧
        (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
        ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧ Ti.edge t = f
        ∧ phi f = some beta ∧ beta ∈ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H i hi beta t q A ell Ty B Ti htA hedge
      segmentRefl segmentTrans commonPrefix stageToEnd hFirstA hTiLen hBLen hATi
      augmentationContradiction n Tn Tfinal hTiFinal hstep hkind f hedges seed hadjoin hclosure
      hstored
  have hnotPE : ett.series.data.kind n ≠
      some TashkinovExtensionKind.PE := by
    intro hpe
    rcases hkind with hse | hre
    · rw [hpe] at hse
      simp at hse
    · rw [hpe] at hre
      simp at hre
  have hcore : base.core = Tn := by
    simpa [Tn, n] using base.nonparallel hnotPE
  have hseedFinal : TreeSequenceInitialSegment seed Tfinal :=
    TashkinovAugmentationSequenceInitialSegment phi seed Tfinal
      hclosure.1
  have hqzero : H.dividerCount = 0 := by
    by_contra hqzero
    have hqpos : 0 < H.dividerCount := Nat.pos_of_ne_zero hqzero
    have hfirstT : TreeSequenceInitialSegment
        (H.stage ⟨1, by omega⟩) T := by
      have hs := stageToEnd (⟨1, by omega⟩ :
        Fin (H.dividerCount + 1))
      simpa [H.terminalStage] using hs
    have hfirstFinal : TreeSequenceInitialSegment
        (H.stage ⟨1, by omega⟩) Tfinal :=
      segmentTrans hfirstT ett.belowFinal
    have hseedLen : seed.length = Tn.length + 1 := hadjoin.1
    have hTnFirst : Tn.length < (H.stage ⟨1, by omega⟩).length := by
      have hs := H.strict (0 : Fin (H.dividerCount + 1))
      have hstageZero : H.stage (Fin.castSucc
          (0 : Fin (H.dividerCount + 1))) = Tn := by
        simpa [Tn, n] using H.baseStage
      rw [hstageZero] at hs
      simpa using hs
    have hseedFirst : TreeSequenceInitialSegment seed
        (H.stage ⟨1, by omega⟩) :=
      commonPrefix hseedFinal hfirstFinal (by omega)
    have hseedA : TreeSequenceInitialSegment seed A :=
      segmentTrans hseedFirst (hFirstA hqpos)
    have hseedTi : TreeSequenceInitialSegment seed Ti :=
      segmentTrans hseedA hATi
    have hseqSeedTi : TashkinovAugmentationSequence phi seed Ti :=
      TashkinovAugmentationSequenceRestrict phi seed Ti Tfinal
        hclosure.1 hseedTi hTiFinal
    have hseqATi : TashkinovAugmentationSequence phi A Ti :=
      TashkinovAugmentationSequenceSuffix phi seed A Ti
        hseqSeedTi hseedA hATi
    exact augmentationContradiction hseqATi htA
  have hAcore : A = base.core := by
    simp [A, q, HierarchyStarredStage, Fin.last, Fin.cases, hqzero]
  have hATn : A = Tn := hAcore.trans hcore
  have htEq : t.val = A.length := by
    apply Nat.le_antisymm
    · by_contra hnotle
      have hAlt : A.length < t.val := by omega
      have hseedLen : seed.length = A.length + 1 := by
        rw [hadjoin.1, hATn]
      have hseedTi : TreeSequenceInitialSegment seed Ti :=
        commonPrefix hseedFinal hTiFinal (by omega)
      have hseqSeedTi : TashkinovAugmentationSequence phi seed Ti :=
        TashkinovAugmentationSequenceRestrict phi seed Ti Tfinal
          hclosure.1 hseedTi hTiFinal
      exact augmentationContradiction hseqSeedTi (by omega)
    · exact htA
  obtain ⟨r, hrval, hredge⟩ :=
    HierarchyNonparallelFirstEdge H f hkind hedges
  have hstageOne : H.stage ⟨1, by omega⟩ = T := by
    calc
      H.stage ⟨1, by omega⟩ =
          H.stage (Fin.last (H.dividerCount + 1)) := by
        apply congrArg H.stage
        apply Fin.ext
        simp [hqzero]
      _ = T := H.terminalStage
  have hstageOneT : TreeSequenceInitialSegment
      (H.stage ⟨1, by omega⟩) T := by
    rw [hstageOne]
    exact segmentRefl T
  have hstageOneFinal : TreeSequenceInitialSegment
      (H.stage ⟨1, by omega⟩) Tfinal :=
    segmentTrans hstageOneT ett.belowFinal
  have hedgeExact : Ti.edge t = f := by
    calc
      Ti.edge t = Tfinal.edge (Fin.castLE hTiFinal.1 t) :=
        (hTiFinal.2.2 t).symm
      _ = Tfinal.edge (Fin.castLE hstageOneFinal.1 r) := by
        congr 1
        apply Fin.ext
        simp only [Fin.val_castLE]
        rw [hrval, htEq, hATn]
      _ = (H.stage ⟨1, by omega⟩).edge r :=
        hstageOneFinal.2.2 r
      _ = f := hredge
  have hfcolor : phi f = some beta := by
    rw [← hedgeExact]
    exact hedge
  have hstored' := hstored hfcolor
  refine ⟨hqzero, ?_, htEq, f, ?_, ?_, ?_, hedgeExact, hfcolor, ?_⟩
  · simpa [Tn, n] using hcore
  · simpa [n] using hstep
  · simpa [n] using hkind
  · simpa [n] using hedges
  · simpa [n] using hstored'

private theorem helper_continuation_613.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (i : ℕ), (1
        : ℕ) ≤ i →
    ∀ (beta : Fin k) (t : Fin (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + i) T.length) (
    by
                first
                | omega
                | ( have := GoldbergSeymour.TreeSequence.positive T
                    have :=
                      GoldbergSeymour.TreeSequence.positive
                        (HierarchyStarredStage H (Fin.last H.dividerCount))
                    have := GoldbergSeymour.TreeSequence.positive T
                    all_goals omega)
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length)).length),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let Ty : ℕ → TreeSequence G e0 := fun (j : ℕ) ↦ TreeSequencePrefix T (min (A.length + j)
        T.length) (
    have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        (A.length + j) T.length) ↦
    by
          omega
    ) (Nat.min_le_right (A.length + j) T.length);
    let B : TreeSequence G e0 := Ty (ell - (1 : ℕ));
    let Ti : TreeSequence G e0 := Ty i; A.length ≤ (↑t : ℕ) → phi (Ti.edge t) = some beta → (
    ∀ (X : TreeSequence G e0), TreeSequenceInitialSegment X X) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) → (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage r.castSucc)
        (H.stage (Fin.last (H.dividerCount + (1 : ℕ))))) → (
    ∀ (hq : (0 : ℕ) < H.dividerCount), TreeSequenceInitialSegment (H.stage (⟨(1 : ℕ),
    by
                omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) A) → TreeSequenceInitialSegment base.core A → Ti.length =
        A.length + i → B.length = A.length + (ell - (1 : ℕ)) → TreeSequenceInitialSegment A Ti → (
    ∀ {X : TreeSequence G e0}, TashkinovAugmentationSequence phi X Ti → X.length ≤ (↑t : ℕ) →
        False) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Tfinal : TreeSequence G e0 := ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)));
        TreeSequenceInitialSegment Ti Tfinal → phi = ett.series.data.coloring n → n.succ =
        Fin.last (ett.rounds + (1 : ℕ)) → H.dividerCount = (0 : ℕ) ∧ base.core =
        ett.series.data.tree (Fin.last ett.rounds).castSucc ∧ (↑t : ℕ) = A.length ∧
    ∃ (f : E), TashkinovSeriesStep G k ett.rounds e0 input ett.series.data (Fin.last ett.rounds) ∧
        (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
        ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧ Ti.edge t = f
        ∧ phi f = some beta ∧ beta ∈ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H i hi beta t q A ell Ty B Ti htA hedge
      segmentRefl segmentTrans commonPrefix stageToEnd hFirstA hCoreA hTiLen hBLen hATi
      augmentationContradiction n Tn Tfinal hTiFinal hphiN hnSucc
  have finishNonparallel
      (hstep : TashkinovSeriesStep G k ett.rounds e0 input
        ett.series.data n)
      (hkind : ett.series.data.kind n =
          some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE)
      (f : E) (hedges : ett.series.data.connectingEdges n = {f})
      (seed : TreeSequence G e0)
      (hadjoin : TreeSequenceAdjoinEdge Tn f seed)
      (hclosure : TashkinovClosure phi seed Tfinal)
      (hstored : phi f = some beta →
        beta ∈ TashkinovStoredColors ett.series.data n) :
      H.dividerCount = 0 ∧
        base.core = ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
        t.val = A.length ∧
        ∃ f : E,
          TashkinovSeriesStep G k ett.rounds e0 input ett.series.data
              (Fin.last ett.rounds) ∧
            (ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.SE ∨
              ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.RE) ∧
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            Ti.edge t = f ∧ phi f = some beta ∧
            beta ∈ TashkinovStoredColors ett.series.data
              (Fin.last ett.rounds) := by
    apply helper_finishNonparallel_499 <;> assumption
  have hcert := ett.series.certified n
  generalize hn : n = j at hcert
  cases hcert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      exfalso
      have hnval := congrArg Fin.val hn
      simp [n] at hnval
      have hrounds := ett.roundsPositive
      omega
  | SE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hkindN : ett.series.data.kind n =
          some TashkinovExtensionKind.SE := by
        rw [hn]
        exact currentKind
      have hedgesN : ett.series.data.connectingEdges n = {choice.edge} := by
        rw [hn]
        exact currentEdges
      have hadjoinN : TreeSequenceAdjoinEdge Tn choice.edge adjoined := by
        simpa [Tn, hn] using adjoinedExactly
      have hclosureN : TashkinovClosure phi adjoined Tfinal := by
        have hc := closedExtension
        rw [← hn, hnSucc, ← hphiN] at hc
        exact hc
      apply finishNonparallel (ett.series.certified n) (Or.inl hkindN)
        choice.edge hedgesN adjoined hadjoinN hclosureN
      intro hfcolor
      exact SimpleExtensionSeedStoredColor G k ett.rounds e0 input
        ett.series.data n (ett.series.certified n) hkindN choice.edge
        hedgesN beta (by rw [← hphiN]; exact hfcolor)
  | PE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
      have hkindN : ett.series.data.kind n =
          some TashkinovExtensionKind.PE := by
        rw [hn]
        exact currentKind
      obtain ⟨hchosen, hbaseClosure, ⟨hunion⟩⟩ := base.parallel hkindN
      have hTnA : TreeSequenceInitialSegment Tn A :=
        segmentTrans (by simpa [Tn, n] using hunion.leftSegment) hCoreA
      have hclosureN : TashkinovClosure phi Tn Tfinal := by
        have hc := closedExtension
        rw [← hn, hnSucc, ← hphiN] at hc
        exact hc
      have hTnTi : TreeSequenceInitialSegment Tn Ti :=
        segmentTrans hTnA hATi
      have hseqTnTi : TashkinovAugmentationSequence phi Tn Ti :=
        TashkinovAugmentationSequenceRestrict phi Tn Ti Tfinal
          hclosureN.1 hTnTi hTiFinal
      have hseqATi : TashkinovAugmentationSequence phi A Ti :=
        TashkinovAugmentationSequenceSuffix phi Tn A Ti
          hseqTnTi hTnA hATi
      exact (augmentationContradiction hseqATi htA).elim
  | RE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hkindN : ett.series.data.kind n =
          some TashkinovExtensionKind.RE := by
        rw [hn]
        exact currentKind
      have hedgesN : ett.series.data.connectingEdges n = {available.edge} := by
        rw [hn]
        exact currentEdges
      have hadjoinN : TreeSequenceAdjoinEdge Tn available.edge adjoined := by
        simpa [Tn, hn] using adjoinedExactly
      have hclosureN : TashkinovClosure phi adjoined Tfinal := by
        have hc := closedExtension
        rw [← hn, hnSucc, ← hphiN] at hc
        exact hc
      apply finishNonparallel (ett.series.certified n) (Or.inr hkindN)
        available.edge hedgesN adjoined hadjoinN hclosureN
      intro hfcolor
      exact RevisitingExtensionSeedStoredColor G k ett.rounds e0 input
        ett.series.data n (ett.series.certified n) hkindN available.edge
        hedgesN beta (by rw [← hphiN]; exact hfcolor)

theorem HierarchyTailMissingColorExclusion {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (hpenultimate : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (HierarchyTailPrefix H
        (T.length - (HierarchyStarredStage H (Fin.last H.dividerCount)).length - 1)))) :
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let ell := T.length - A.length
    let Ty := fun i : ℕ =>
      TreeSequencePrefix T (min (A.length + i) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    ∀ i : ℕ, 1 ≤ i → i < ell →
      ∀ beta : Fin k,
        beta ∈ MissingColors G phi
          ((Ty i).vertex (Fin.last (Ty i).length)) →
        ∀ t : Fin (Ty i).length,
          A.length ≤ t.val → t.val < A.length + i →
          phi ((Ty i).edge t) = some beta →
          H.dividerCount = 0 ∧ base.core = Tn ∧
            t.val = A.length ∧
            ∃ f : E,
              TashkinovSeriesStep G k ett.rounds e0 input
                  ett.series.data n ∧
                (ett.series.data.kind n =
                    some TashkinovExtensionKind.SE ∨
                  ett.series.data.kind n =
                    some TashkinovExtensionKind.RE) ∧
                ett.series.data.connectingEdges n = {f} ∧
                (Ty i).edge t = f ∧ phi f = some beta ∧
                beta ∈ TashkinovStoredColors ett.series.data n := by
  classical
  dsimp only at hpenultimate ⊢
  intro i hi hilt beta hbeta t htA hti hedge
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := T.length - A.length
  let Ty := fun j : ℕ =>
    TreeSequencePrefix T (min (A.length + j) T.length)
      (by have hA := A.positive; have hT := T.positive; omega)
      (Nat.min_le_right _ _)
  let B := Ty (ell - 1)
  let Ti := Ty i
  change ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) at hpenultimate
  change beta ∈ MissingColors G phi (Ti.vertex (Fin.last Ti.length)) at hbeta
  change i < ell at hilt
  change A.length ≤ t.val at htA
  change t.val < A.length + i at hti
  change phi (Ti.edge t) = some beta at hedge
  change H.dividerCount = 0 ∧
    base.core = ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
    t.val = A.length ∧
    ∃ f : E,
      TashkinovSeriesStep G k ett.rounds e0 input ett.series.data
          (Fin.last ett.rounds) ∧
        (ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
        Ti.edge t = f ∧ phi f = some beta ∧
        beta ∈ TashkinovStoredColors ett.series.data
          (Fin.last ett.rounds)
  have segmentRefl (X : TreeSequence G e0) :
      TreeSequenceInitialSegment X X :=
    ⟨le_rfl, (by intro r; rfl), (by intro r; rfl)⟩
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    exact helper_segmentTrans_135 (@G) (@e0) (@hXY) (@hYZ)
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z)
      (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    exact helper_commonPrefix_148 (@G) (@e0) (@hXZ) (@hYZ) (@hXY)
  have prefixToTree (X : TreeSequence G e0) (m : ℕ)
      (hm : 1 ≤ m) (hmX : m ≤ X.length) :
      TreeSequenceInitialSegment (TreeSequencePrefix X m hm hmX) X := by
    exact helper_prefixToTree_173 (@G) (@e0) (@X) (@m) (@hm) (@hmX)
  have stageToEnd : ∀ r : Fin (H.dividerCount + 1),
      TreeSequenceInitialSegment (H.stage r.castSucc)
        (H.stage (Fin.last (H.dividerCount + 1))) := by
    apply helper_stageToEnd_206 <;> assumption
  have hAT : TreeSequenceInitialSegment A T := by
    exact helper_hAT_238 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@i) (@t)
        (@stageToEnd)
  have stageFromFirst : ∀ d : ℕ, ∀ hd : d ≤ H.dividerCount,
      TreeSequenceInitialSegment (H.stage ⟨1, by omega⟩)
        (H.stage ⟨1 + d, by omega⟩) := by
    apply helper_stageFromFirst_267 <;> assumption
  have hAeqPositive (hq : 0 < H.dividerCount) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    exact helper_hAeqPositive_284 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@i)
        (@t) (@hq)
  have hFirstA (hq : 0 < H.dividerCount) :
      TreeSequenceInitialSegment (H.stage ⟨1, by omega⟩) A := by
    exact helper_hFirstA_298 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@i) (@t)
        (@stageFromFirst)
        (@hAeqPositive) (@hq)
  have hCoreA : TreeSequenceInitialSegment base.core A := by
    apply helper_hCoreA_307 <;> assumption
  have hsum : A.length + ell = T.length := by
    dsimp [ell]
    exact Nat.add_sub_of_le hAT.1
  have hell : 2 ≤ ell := by omega
  have hTiBound : A.length + i ≤ T.length := by omega
  have hTiLen : Ti.length = A.length + i := by
    simp [Ti, Ty, TreeSequencePrefix, Nat.min_eq_left hTiBound]
  have htTi : t.val < Ti.length := by
    exact t.isLt
  have hBBound : A.length + (ell - 1) ≤ T.length := by omega
  have hBLen : B.length = A.length + (ell - 1) := by
    simp [B, Ty, TreeSequencePrefix, Nat.min_eq_left hBBound]
  have hTiT : TreeSequenceInitialSegment Ti T := by
    dsimp [Ti, Ty]
    exact prefixToTree T _ _ _
  have hBT : TreeSequenceInitialSegment B T := by
    dsimp [B, Ty]
    exact prefixToTree T _ _ _
  have hATi : TreeSequenceInitialSegment A Ti :=
    commonPrefix hAT hTiT (by rw [hTiLen]; omega)
  have hTiB : TreeSequenceInitialSegment Ti B :=
    commonPrefix hTiT hBT (by rw [hTiLen, hBLen]; omega)
  have augmentationContradiction {X : TreeSequence G e0}
      (hseq : TashkinovAugmentationSequence phi X Ti)
      (hXt : X.length ≤ t.val) : False := by
    obtain ⟨hstep, hlast⟩ :=
      TashkinovAugmentationSequencePosition phi X Ti hseq t hXt
    let Bt := TreeSequencePrefix Ti t.val
      (le_trans X.positive hXt) (Nat.le_of_lt htTi)
    let Bt1 := TreeSequencePrefix Ti (t.val + 1)
      (by omega) (Nat.succ_le_of_lt htTi)
    change TashkinovAugmentation phi Bt Bt1 at hstep
    change Bt1.edge (Fin.last t.val) = Ti.edge t at hlast
    rcases hstep with ⟨hstepLen, hBtBt1, c, hc, hcmissing⟩
    have hcEdge : phi (Bt1.edge (Fin.last t.val)) = some beta := by
      rw [hlast]
      exact hedge
    have hcbeta : c = beta := Option.some.inj (hc.symm.trans hcEdge)
    subst c
    simp only [TreeMissingColors, Finset.mem_biUnion] at hcmissing
    rcases hcmissing with ⟨z, hzBt, hzmissing⟩
    have hBtTi : TreeSequenceInitialSegment Bt Ti := by
      dsimp [Bt]
      exact prefixToTree Ti _ _ _
    have hzB : z ∈ TreeSequenceVertexSet B :=
      TreeSequenceInitialSegmentVertexSetSubset
        (segmentTrans hBtTi hTiB) hzBt
    have hyTi : Ti.vertex (Fin.last Ti.length) ∈
        TreeSequenceVertexSet Ti := by
      simp only [TreeSequenceVertexSet, Finset.mem_image,
        Finset.mem_univ, true_and]
      exact ⟨Fin.last Ti.length, rfl⟩
    have hyB : Ti.vertex (Fin.last Ti.length) ∈
        TreeSequenceVertexSet B :=
      TreeSequenceInitialSegmentVertexSetSubset hTiB hyTi
    have hzy : z ≠ Ti.vertex (Fin.last Ti.length) := by
      simp only [TreeSequenceVertexSet, Finset.mem_image,
        Finset.mem_univ, true_and] at hzBt
      rcases hzBt with ⟨s, rfl⟩
      intro heq
      have hvertex := hBtTi.2.1 s
      have hinj : Fin.castLE (Nat.succ_le_succ hBtTi.1) s =
          Fin.last Ti.length :=
        Ti.vertex_injective (hvertex.trans heq)
      have hvals := congrArg Fin.val hinj
      have hsle : s.val ≤ t.val := by
        have hs := s.isLt
        simp [Bt, TreeSequencePrefix] at hs
        omega
      simp only [Fin.val_castLE, Fin.val_last] at hvals
      omega
    have hdisjoint := hpenultimate hzB hyB hzy
    exact (Finset.disjoint_left.mp hdisjoint) hzmissing hbeta
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Tfinal := ett.series.data.tree (Fin.last (ett.rounds + 1))
  have hTiFinal : TreeSequenceInitialSegment Ti Tfinal :=
    segmentTrans hTiT ett.belowFinal
  have hphiN : phi = ett.series.data.coloring n := by
    simpa [n] using ett.generatingColoring
  have hnSucc : n.succ = Fin.last (ett.rounds + 1) := by
    apply Fin.ext
    simp [n]
  apply helper_continuation_613 <;> assumption
end GoldbergSeymour

end
