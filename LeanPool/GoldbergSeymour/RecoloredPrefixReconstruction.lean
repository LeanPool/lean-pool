/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TerminalRoute
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext

public import LeanPool.GoldbergSeymour.Td

/-!
# P2813_T1_Prefix Reconstruction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem P2813_T1_PrefixReconstruction_branch_184.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (sigma :
        PartialEdgeColoring E k), (
    let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
    ∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) → (
    let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
    ∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    let H := C.hierarchy;
    let q := Fin.last H.dividerCount;
    let A := HierarchyStarredStage H q;
    let n := Fin.last ett.rounds;
    let Tn := ett.series.data.tree n.castSucc; (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
        → TreeSequenceInitialSegment U Z) → TreeSequenceInitialSegment A T → (
    ∀ {S U : TreeSequence G e0}, TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
        TreeSequenceInitialSegment Tn A → ModColoring ett sigma → ¬A = Tn → HierarchyStarredStage
        C.hierarchy (Fin.last C.hierarchy.dividerCount) = ett.series.data.tree (Fin.last
        ett.rounds).castSucc ∨
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma (HierarchyStarredStage
        C.hierarchy (Fin.last C.hierarchy.dividerCount))), MaximumProperty corr.replacementETT := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma hfixed hmissing H q A n Tn trans hAT
      equalTrees TnA hmod he
  have hstrict : Tn.length < A.length := by
    have hle := TnA.1
    by_contra h
    have hlen : Tn.length = A.length := by omega
    exact he (equalTrees TnA hlen).symm
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    exact hUW.of_common_extension hSW hlen
  have transport (S : TreeSequence G e0) :
      ∀ (X : TreeSequence G e0), TashkinovAugmentationSequence phi S X →
        TreeSequenceInitialSegment X A → TashkinovAugmentationSequence sigma S X := by
    intro X hseq
    unfold TashkinovAugmentationSequence at hseq ⊢
    induction hseq with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @tail U W hSU hUW ih =>
      intro hWA
      obtain ⟨hlen, hseg, c, hcolor, hcm⟩ := hUW
      have hUA := trans hseg hWA
      have hcSigma : c ∈ TreeMissingColors sigma U := by
        obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hcm
        exact Finset.mem_biUnion.mpr ⟨v, hv, by
          rw [hmissing v (TreeSequenceInitialSegmentVertexSetSubset hUA hv)]
          exact hcv⟩
      let t : Fin W.length := Fin.cast hlen.symm (Fin.last U.length)
      have he : sigma (W.edge t) = phi (W.edge t) := by
        rw [← hWA.2.2 t]
        exact hfixed _
      exact Relation.ReflTransGen.tail (ih hUA)
        ⟨hlen, hseg, c, he.trans hcolor, hcSigma⟩
  have routeA :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn A) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence sigma seed A) := by
    rcases P2813_T1_TerminalRoute G k e0 input T phi ett with
      ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hincident, hcontrol, hseq⟩
    · have hpre := TashkinovAugmentationSequenceRestrict phi Tn A T hseq TnA hAT
      exact Or.inl ⟨hp, transport Tn A hpre ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩⟩
    · have hseedA := commonPrefix
        (TashkinovAugmentationSequenceInitialSegment phi seed T hseq) hAT
        (by have hseedLen : seed.length = Tn.length + 1 := hseed.1; omega)
      have hpre := TashkinovAugmentationSequenceRestrict phi seed A T hseq hseedA hAT
      exact Or.inr ⟨hp, f, seed, hedges, hseed,
        transport seed A hpre ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩⟩
  obtain ⟨corr⟩ := hmod.2.2 A TnA hstrict routeA
  exact Or.inr ⟨corr, MaximumPropertyTransport G k e0 ett sigma hmod A corr C.maximum⟩

theorem P2813_T1_PrefixReconstruction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (sigma : PartialEdgeColoring E k)
    (hsproper : IsProperEdgeColoring G sigma)
    (hsone : IsOneEdgeUncolored sigma e0)
    (hbase :
      let n := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ett.series.data n
      if ett.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn base.closure Dn phi sigma
      else StableColoring Tn Dn phi sigma)
    (hfixed :
      let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
      ∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t))
    (hmissing :
      let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
      ∀ v ∈ TreeSequenceVertexSet A,
        MissingColors G sigma v = MissingColors G phi v) :
    let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
    let n := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    ModColoring ett sigma ∧
      (A = Tn ∨
        ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma A,
          MaximumProperty corr.replacementETT) := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Ty := TreeSequencePrefix T
    (min (A.length + ((T.length - A.length) - 1)) T.length)
    (by have hA := A.positive; have hT := T.positive; omega)
    (Nat.min_le_right _ _)
  have trans {U W Z : TreeSequence G e0}
      (hUW : TreeSequenceInitialSegment U W)
      (hWZ : TreeSequenceInitialSegment W Z) :
      TreeSequenceInitialSegment U Z := by
    exact hUW.trans hWZ
  have stageChain : ∀ (j : ℕ) (hj : j < H.dividerCount + 2)
      (i : Fin (H.dividerCount + 2)), i.val ≤ j →
      TreeSequenceInitialSegment (H.stage i) (H.stage ⟨j, hj⟩) := by
    intro last bound first ordered
    exact H.stageInitialSegmentOfLE first ⟨last, bound⟩ ordered
  have starStage (r : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H r)
        (H.stage r.succ) := by
    clear * - H r
    refine Fin.cases ?_ (fun i => ?_) r
    · exact H.coreInsideFirst
    · exact H.nested i.succ
  have starChain (r s : Fin (H.dividerCount + 1)) (hrs : r ≤ s) :
      TreeSequenceInitialSegment (HierarchyStarredStage H r)
        (HierarchyStarredStage H s) := by
    clear * - H r s hrs stageChain starStage trans
    by_cases heq : r = s
    · subst s
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · have hrlt : r.val < s.val := by
        have := Fin.le_iff_val_le_val.mp hrs
        have : r.val ≠ s.val := fun h => heq (Fin.ext h)
        omega
      have hs : s ≠ 0 := by intro hs; subst s; simp at hrlt
      have hstar : HierarchyStarredStage H s = H.stage s.castSucc := by
        rw [← Fin.succ_pred s hs]
        rfl
      rw [hstar]
      exact trans (starStage r)
        (stageChain s.val (by omega) r.succ (by simp; omega))
  have hAT : TreeSequenceInitialSegment A T := by
    have hh := starStage q
    have hlast : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
    simpa [hlast, H.terminalStage] using hh
  have hATy : TreeSequenceInitialSegment A Ty := by
    clear * - hAT A Ty
    have hlen : A.length ≤ Ty.length := by
      change A.length ≤ min (A.length + ((T.length - A.length) - 1)) T.length
      exact Nat.le_min.mpr ⟨Nat.le_add_right _ _, hAT.1⟩
    refine ⟨hlen, ?_, ?_⟩
    · intro j
      change T.vertex _ = A.vertex j
      exact hAT.2.1 j
    · intro j
      change T.edge _ = A.edge j
      exact hAT.2.2 j
  have hTyT : TreeSequenceInitialSegment Ty T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have equalTrees {S U : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hlen : S.length = U.length) : S = U := by
    cases S with
    | mk ls ps vs es vis eis fs aas =>
      cases U with
      | mk lu pu vu eu viu eiu fu aau =>
        simp only at hlen
        subst lu
        rw [TreeSequence.mk.injEq]
        refine ⟨rfl, ?_, ?_⟩
        · apply heq_of_eq
          funext i
          simpa only [Fin.castLE] using (hSU.2.1 i).symm
        · apply heq_of_eq
          funext i
          simpa only [Fin.castLE] using (hSU.2.2 i).symm
  have coreChain : TreeSequenceInitialSegment Tn base.core := by
    exact base.lastRoundInitialSegmentCore
  have coreA : TreeSequenceInitialSegment base.core A := starChain 0 q (Fin.zero_le _)
  have TnA := trans coreChain coreA
  have hnStable : StableColoring Tn
      (TashkinovStoredColors ett.series.data n) phi sigma := by
    change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure (TashkinovStoredColors ett.series.data n) phi sigma
      else StableColoring Tn (TashkinovStoredColors ett.series.data n) phi sigma) at hbase
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (ite_eq_left hp ▸ hbase).1
    · simpa only [hp, ite_false] using hbase
  have stableLadder : StableColoring Tn
      (TashkinovStoredColors ett.series.data n) (ett.series.data.coloring n) sigma := by
    rw [show ett.series.data.coloring n = phi from ett.generatingColoring.symm]
    exact hnStable
  have hmod : ModColoring ett sigma := Td G k e0 input T phi ett C.maximum
    C.positive ctx.lowerRung sigma hsproper hsone stableLadder
  refine ⟨hmod, ?_⟩
  by_cases he : A = Tn
  · exact Or.inl he
  · exact @P2813_T1_PrefixReconstruction_branch_184 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C sigma hfixed hmissing trans hAT equalTrees TnA
      hmod he
end GoldbergSeymour

end
