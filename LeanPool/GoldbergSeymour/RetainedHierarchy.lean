/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.MinusClosedTransport
public import LeanPool.GoldbergSeymour.PrefixSegmentTransport
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.GoodHierarchy

/-!
# P2813_T1_Retained Hierarchy

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_continuation_184.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H) (hq : (0 : ℕ) < H.dividerCount) (alpha beta : Fin k) (_ : alpha ≠ beta)
        (z : V ⊕ E) (sigma : PartialEdgeColoring E k) (_ : sigma = TwoColorComponentSwap G phi
        alpha beta z) (_ : IsProperEdgeColoring G phi) (_ : IsOneEdgeUncolored phi e0) (inputA :
        PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA
        (HierarchyStarredStage H (Fin.last H.dividerCount)) sigma) (baseA : HierarchyBase ettA
        sigma) (K : TashkinovHierarchy ettA baseA) (_ : ettA.series.data.tree (Fin.last
        ettA.rounds).castSucc = ett.series.data.tree (Fin.last ett.rounds).castSucc) (_ :
        ettA.series.data.kind (Fin.last ettA.rounds) = ett.series.data.kind (Fin.last ett.rounds))
        (hcount : K.dividerCount + (1 : ℕ) = H.dividerCount) (_ : baseA.core = base.core) (_ :
        baseA.closure = base.closure) (_ : (
    ∀ (j : Fin (K.dividerCount + (2 : ℕ))), K.stage j = H.stage (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))))) (_ : (
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    ∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t))) (_ : (
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    ∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v)) (_ : (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))) (c : Fin k) (_ : c = alpha ∨ c = beta) (_ : c ∈
        TreeMissingColors phi (HierarchyStarredStage H r)) (_ : TreeColorSetClosed G phi
        (HierarchyStarredStage H r) { c }), OutsideKempeRecoloring (HierarchyStarredStage H r) phi
        sigma alpha beta)) (_ : (
    ∀ (_ : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE),
    ∃ c ∈ TreeMissingColors phi base.core \ (HierarchyStoredColorsAt H (0 : Fin (H.dividerCount +
        (1 : ℕ)))).biUnion (good.gamma (0 : Fin (H.dividerCount + (1 : ℕ)))),
    ∃ f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet base.core) c, sigma f = phi f)),
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : (
    ∀ {U W Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment U W) (_ :
        TreeSequenceInitialSegment W Z), TreeSequenceInitialSegment U Z)) (_ :
        TreeSequenceInitialSegment A T) (_ : (
    ∀ (j : Fin (H.dividerCount + (2 : ℕ))) (_ : (↑j : ℕ) ≤ H.dividerCount),
        TreeSequenceInitialSegment (H.stage j) A)) (_ : TreeSequenceInitialSegment base.core A) (_
        : TreeSequenceInitialSegment Tn A) (_ : (
    ∀ (U : TreeSequence G e0) (_ : TreeSequenceInitialSegment U A), TreeMissingColors sigma U =
        TreeMissingColors phi U)),
    let oldIndex : Fin (K.dividerCount + (1 : ℕ)) → Fin (H.dividerCount + (1 : ℕ)) := fun (j : Fin
        (K.dividerCount + (1 : ℕ))) => (⟨(↑j : ℕ),
    have this : (↑j : ℕ) < K.dividerCount + (1 : ℕ) := j.isLt; Decidable.byContradiction fun (a :
        ¬(↑j : ℕ) < H.dividerCount + (1 : ℕ)) =>
    by
            omega
    ⟩ : Fin (H.dividerCount + (1 : ℕ)));
    ∀ (_ : (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))), HierarchyStarredStage K j = HierarchyStarredStage H
        (oldIndex j))) (_ : (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))), HierarchyStoredColorsAt K j = HierarchyStoredColorsAt
        H (oldIndex j))),
    ∃ (goodA : GoodHierarchy K), (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
    let jH : Fin (H.dividerCount + (1 : ℕ)) := (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (1 : ℕ))); HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H
        jH ∧
    ∀ (eta : Fin k), goodA.gamma j eta = good.gamma jH eta) ∧ TreeColorSetMinusClosed G sigma
        (H.stage (Fin.last H.dividerCount).castSucc) ((HierarchyStoredColorsAt H (Fin.last
        H.dividerCount)).biUnion (good.gamma (⟨H.dividerCount - (1 : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (1 : ℕ))))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good hq alpha beta hne z sigma hsigma hproper
      hone inputA ettA baseA K htreeA hkindA hcount hcoreA hclosureA stageEq hfixed hmissing
      houtside hPEWitness q A n Tn trans hAT ordinaryToA coreA TnA treeMissingEq oldIndex
      starredEq storedEq
  have stageMissingEq (j : Fin (K.dividerCount + 1)) :
      HierarchyStageMissingColors K j = HierarchyStageMissingColors H (oldIndex j) := by
    refine Fin.cases ?_ (fun i => ?_) j
    · change TreeMissingColors sigma
        (ettA.series.data.tree (Fin.last ettA.rounds).castSucc) = TreeMissingColors phi Tn
      rw [htreeA]
      exact treeMissingEq Tn TnA
    · change TreeMissingColors sigma (K.stage i.succ.castSucc) =
        TreeMissingColors phi (H.stage ⟨i.val + 1, by omega⟩)
      rw [stageEq i.succ.castSucc]
      have hbound : i.val + 1 ≤ H.dividerCount := by
        clear * - i hcount
        have := i.isLt
        omega
      exact treeMissingEq _ (ordinaryToA ⟨i.val + 1, by omega⟩ hbound)
  have segmentEq (j : Fin (K.dividerCount + 1)) (eta : Fin k) :
      HierarchySegmentColors K j eta = HierarchySegmentColors H (oldIndex j) eta := by
    have hnext : K.stage j.succ = H.stage (oldIndex j).succ := stageEq j.succ
    unfold HierarchySegmentColors
    dsimp only
    rw [hnext, starredEq j]
    exact P2813_T1_PrefixSegmentTransport phi sigma (H.stage (oldIndex j).succ) A T
      (ordinaryToA _ (by have := j.isLt; simp only [oldIndex, Fin.val_succ]; omega))
      hAT hfixed hmissing eta (HierarchyStarredStage H (oldIndex j)).length
  have closureA (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A := by
    obtain ⟨union⟩ := (base.parallel hp).2.2
    intro v hv
    apply TreeSequenceInitialSegmentVertexSetSubset coreA
    rw [union.vertexSet]
    exact Finset.mem_union_right _ hv
  let R0 := (HierarchyStoredColorsAt H 0).biUnion (good.gamma 0)
  have notClosedCore (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      ¬ TreeColorSetMinusClosed G sigma base.core R0 := by
    obtain ⟨c, hc, f, hf, hvalue⟩ := hPEWitness hp
    have hb := Finset.mem_filter.mp hf
    intro hnew
    have hcmNew : c ∈ TreeMissingColors sigma base.core \ R0 := by
      rw [treeMissingEq base.core coreA]
      exact hc
    have hfNew : f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet base.core) c :=
      Finset.mem_filter.mpr ⟨hb.1, hvalue.trans hb.2⟩
    rw [hnew c hcmNew] at hfNew
    exact Finset.notMem_empty f hfNew
  have transportClosed (i : Fin H.dividerCount) :
      TreeColorSetMinusClosed G sigma (H.stage i.succ.castSucc)
        ((HierarchyStoredColorsAt H i.succ).biUnion (good.gamma i.castSucc)) := by
    have hstar : HierarchyStarredStage H i.succ = H.stage i.succ.castSucc := rfl
    apply P2813_T1_MinusClosedTransport G k e0 _ phi sigma alpha beta hne z hsigma
      hproper hone _ (good.minusClosed i)
    · intro v hv
      exact hmissing v (TreeSequenceInitialSegmentVertexSetSubset
        (ordinaryToA i.succ.castSucc
            (by have := i.isLt; simp only [Fin.val_succ, Fin.val_castSucc]; omega)) hv)
    · intro c hc hm hclosed
      rw [← hstar] at hm hclosed ⊢
      exact houtside i.succ c hc hm hclosed
  let goodA : GoodHierarchy K :=
    { gamma := fun j eta => good.gamma (oldIndex j) eta
      twoColors := by
        intro j eta heta
        exact good.twoColors (oldIndex j) eta (storedEq j ▸ heta)
      avoidance := by
        intro j eta heta
        rw [stageMissingEq j, segmentEq j eta]
        exact good.avoidance (oldIndex j) eta (storedEq j ▸ heta)
      disjointPairs := by
        intro j eta theta heta htheta hne
        exact good.disjointPairs (oldIndex j) eta theta
          (storedEq j ▸ heta) (storedEq j ▸ htheta) hne
      uniqueRefresh := by
        intro i
        let io : Fin H.dividerCount := ⟨i.val, by have := i.isLt; omega⟩
        have hdifference :
            ((TreeSequenceVertexSet (H.stage io.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage H io.castSucc)).biUnion
                fun v => MissingColors G sigma v) =
            ((TreeSequenceVertexSet (H.stage io.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage H io.castSucc)).biUnion
                fun v => MissingColors G phi v) := by
          apply Finset.biUnion_congr rfl
          intro v hv
          exact hmissing v (TreeSequenceInitialSegmentVertexSetSubset
            (ordinaryToA io.succ.castSucc
                (by have := io.isLt; simp only [Fin.val_succ, Fin.val_castSucc]; omega))
            (Finset.mem_sdiff.mp hv).1)
        rw [storedEq i.succ, stageEq i.succ.castSucc, starredEq i.castSucc]
        change ∃! eta : Fin k,
          eta ∈ HierarchyStoredColorsAt H io.succ ∧
          good.gamma io.succ eta ⊆
            ((TreeSequenceVertexSet (H.stage io.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage H io.castSucc)).biUnion
                fun v => MissingColors G sigma v) ∧
          ∀ theta ∈ HierarchyStoredColorsAt H io.succ, theta ≠ eta →
            good.gamma io.succ theta = good.gamma io.castSucc theta
        rw [hdifference]
        exact good.uniqueRefresh io
      parallelBase := by
        dsimp only
        intro hp
        have hpOld : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
          hkindA.symm.trans hp
        rw [hcoreA, hclosureA, htreeA, storedEq 0]
        change ¬ TreeColorSetMinusClosed G sigma base.core R0 ∧
          4 ≤ ((TreeMissingColors sigma Tn ∩ TreeMissingColors sigma base.closure) \ R0).card
        refine ⟨notClosedCore hpOld, ?_⟩
        have hmR : TreeMissingColors sigma base.closure = TreeMissingColors phi base.closure := by
          unfold TreeMissingColors
          exact Finset.biUnion_congr rfl (fun v hv => hmissing v (closureA hpOld hv))
        rw [treeMissingEq Tn TnA, hmR]
        exact (good.parallelBase hpOld).2
      minusClosed := by
        intro i
        let io : Fin H.dividerCount := ⟨i.val, by have := i.isLt; omega⟩
        rw [stageEq i.succ.castSucc, storedEq i.succ]
        exact transportClosed io }
  refine ⟨goodA, ?_, ?_⟩
  · intro j
    exact ⟨storedEq j, fun _ => rfl⟩
  · have hh := transportClosed (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount)
    have hlast : (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ = q := by
      apply Fin.ext
      dsimp [q]
      omega
    rw [hlast] at hh
    exact hh

theorem P2813_T1_RetainedHierarchy {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hq : 0 < H.dividerCount)
    (alpha beta : Fin k) (hne : alpha ≠ beta) (z : Sum V E)
    (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hproper : IsProperEdgeColoring G phi) (hone : IsOneEdgeUncolored phi e0)
    (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0)
    (inputA : PartialEdgeColoring E k)
    (ettA : ExtendedTashkinovTree G k e0 inputA
      (HierarchyStarredStage H (Fin.last H.dividerCount)) sigma)
    (baseA : HierarchyBase ettA sigma)
    (K : TashkinovHierarchy ettA baseA)
    (htreeA : ettA.series.data.tree (Fin.last ettA.rounds).castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (hkindA : ettA.series.data.kind (Fin.last ettA.rounds) =
      ett.series.data.kind (Fin.last ett.rounds))
    (hstoredA : TashkinovStoredColors ettA.series.data (Fin.last ettA.rounds) =
      TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
    (hcount : K.dividerCount + 1 = H.dividerCount)
    (hcoreA : baseA.core = base.core) (hclosureA : baseA.closure = base.closure)
    (stageEq : ∀ j : Fin (K.dividerCount + 2),
      K.stage j = H.stage ⟨j.val, by have := j.isLt; omega⟩)
    (hfixed :
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      ∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t))
    (hmissing :
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      ∀ v ∈ TreeSequenceVertexSet A,
        MissingColors G sigma v = MissingColors G phi v)
    (houtside : ∀ (r : Fin (H.dividerCount + 1)) (c : Fin k),
      (c = alpha ∨ c = beta) →
      c ∈ TreeMissingColors phi (HierarchyStarredStage H r) →
      TreeColorSetClosed G phi (HierarchyStarredStage H r) {c} →
      OutsideKempeRecoloring (HierarchyStarredStage H r) phi sigma alpha beta)
    (hPEWitness :
      ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
      ∃ c : Fin k,
        c ∈ TreeMissingColors phi base.core \
          (HierarchyStoredColorsAt H 0).biUnion (good.gamma 0) ∧
        ∃ f : E, f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet base.core) c ∧
          sigma f = phi f) :
    ∃ goodA : GoodHierarchy K,
    (∀ j : Fin (K.dividerCount + 1),
        let jH : Fin (H.dividerCount + 1) := ⟨j.val, by have := j.isLt; omega⟩
        HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H jH ∧
          ∀ eta : Fin k, goodA.gamma j eta = good.gamma jH eta) ∧
      TreeColorSetMinusClosed G sigma (H.stage (Fin.last H.dividerCount).castSucc)
        ((HierarchyStoredColorsAt H (Fin.last H.dividerCount)).biUnion
          (good.gamma ⟨H.dividerCount - 1, by omega⟩)) := by
  classical
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  have trans {U W Z : TreeSequence G e0}
      (hUW : TreeSequenceInitialSegment U W)
      (hWZ : TreeSequenceInitialSegment W Z) :
      TreeSequenceInitialSegment U Z := by
    clear * - hUW hWZ
    refine ⟨hUW.1.trans hWZ.1, ?_, ?_⟩
    · intro j
      exact (hWZ.2.1 (Fin.castLE (Nat.succ_le_succ hUW.1) j)).trans
        (hUW.2.1 j)
    · intro j
      exact (hWZ.2.2 (Fin.castLE hUW.1 j)).trans (hUW.2.2 j)
  have stageChain : ∀ (j : ℕ) (hj : j < H.dividerCount + 2)
      (i : Fin (H.dividerCount + 2)), i.val ≤ j →
      TreeSequenceInitialSegment (H.stage i) (H.stage ⟨j, hj⟩) := by
    intro last bound first ordered
    exact H.stageInitialSegmentOfLE first ⟨last, bound⟩ ordered
  have starPositive (j : Fin (H.dividerCount + 1)) (hj : 0 < j.val) :
      HierarchyStarredStage H j = H.stage j.castSucc := by
    clear * - hj
    have hn : j ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero] at this
      omega
    rw [← Fin.succ_pred j hn]
    rfl
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
  have starToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
    by_cases hj : j = 0
    · subst j
      exact coreToStar q
    · rw [starPositive j (by
        have hne : j.val ≠ 0 := fun hh => hj (Fin.ext hh)
        omega)]
      exact ordinaryToA j.castSucc (by have := j.isLt; simp only [Fin.val_castSucc]; omega)
  have coreA : TreeSequenceInitialSegment base.core A := coreToStar q
  have TnCore : TreeSequenceInitialSegment Tn base.core := by
    exact base.lastRoundInitialSegmentCore
  have TnA := trans TnCore coreA
  have treeMissingEq (U : TreeSequence G e0)
      (hUA : TreeSequenceInitialSegment U A) :
      TreeMissingColors sigma U = TreeMissingColors phi U := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl
      (fun v hv => hmissing v (TreeSequenceInitialSegmentVertexSetSubset hUA hv))
  let oldIndex (j : Fin (K.dividerCount + 1)) : Fin (H.dividerCount + 1) :=
    ⟨j.val, by have := j.isLt; omega⟩
  have starredEq (j : Fin (K.dividerCount + 1)) :
      HierarchyStarredStage K j = HierarchyStarredStage H (oldIndex j) := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hcoreA
    · change K.stage i.succ.castSucc = H.stage ⟨i.val + 1, by omega⟩
      exact stageEq i.succ.castSucc
  have storedEq (j : Fin (K.dividerCount + 1)) :
      HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H (oldIndex j) := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [hstoredA, starredEq j, treeMissingEq _ (starToA (oldIndex j))]
  exact @helper_continuation_184 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base H good hq alpha beta hne z sigma hsigma hproper hone inputA ettA
      baseA K htreeA hkindA hcount hcoreA hclosureA stageEq hfixed hmissing houtside hPEWitness
      trans hAT ordinaryToA coreA TnA treeMissingEq starredEq storedEq
end GoldbergSeymour

end
