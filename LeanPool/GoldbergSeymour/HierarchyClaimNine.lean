/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module


public import LeanPool.GoldbergSeymour.HierarchyClaimNineFirstUseSeed
public import LeanPool.GoldbergSeymour.HierarchyClaimNinePENormalization
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTerminalCommonMissing
public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices

/-!
# Hierarchy Claim Nine

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBranch600Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ i ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)),
     Disjoint
      (MissingColors G P.coloring
       ((HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C i).length)))
      (MissingColors G P.coloring (T.vertex (Fin.last T.length)))) →
   let corr : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
    {
     replacementInput := input, replacementSeries := ett.series, replacementETT := ett,
     rungAgreement := rfl, seriesPresentation := HEq.rfl,
     finalGeneratingColoring := ett.generatingColoring,
     ladderTreesAgree := fun (i : Fin ett.rounds) => Eq.refl (ett.series.data.tree i.succ.castSucc),
     storedColorsAgree := fun (i : Fin (ett.rounds + (1 : ℕ))) =>
      Eq.refl (ett.series.data.stored i),
     connectingEdgesAgree := fun (i : Fin (ett.rounds + (1 : ℕ))) =>
      Eq.refl (ett.series.data.connectingEdges i),
     extensionKindsAgree := fun (i : Fin (ett.rounds + (1 : ℕ))) =>
      Eq.refl (ett.series.data.kind i),
     replacementProper := fun i => (ett.series.coloringProperties i).1,
     replacementOneUncolored := fun i => (ett.series.coloringProperties i).2,
     replacementStable := fun (i : Fin ett.rounds) =>
      (⟨fun (f : E) (_ : TreeIncidentEdge (ett.series.data.tree i.succ.castSucc) f)
         (_ :
          ∃
           c ∈
            TreeMissingColors (ett.series.data.coloring i.succ)
              (ett.series.data.tree i.succ.castSucc) ∪
             TashkinovStoredColors ett.series.data i.succ,
           ett.series.data.coloring i.succ f = some c) =>
        Eq.refl (ett.series.data.coloring i.succ f),
        fun (v : V) (_ : v ∈ TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) =>
        Eq.refl (MissingColors G (ett.series.data.coloring i.succ) v)⟩ :
       (∀ (f : E),
         TreeIncidentEdge (ett.series.data.tree i.succ.castSucc) f →
          (∃
            c ∈
             TreeMissingColors (ett.series.data.coloring i.succ)
               (ett.series.data.tree i.succ.castSucc) ∪
              TashkinovStoredColors ett.series.data i.succ,
            ett.series.data.coloring i.succ f = some c) →
           ett.series.data.coloring i.succ f = ett.series.data.coloring i.succ f) ∧
        ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc),
         MissingColors G (ett.series.data.coloring i.succ) v =
          MissingColors G (ett.series.data.coloring i.succ) v) :
     CorrespondingExtendedTashkinovTree G k e0 ett phi T };
   let _ : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx :=
    {
     coloring := phi, corresponding := corr, maximum := C.maximum, replacementBase := base,
     counterexample := C,
     sameGood :=
      (⟨(⟨rfl,
          (⟨rfl,
            (⟨HEq.rfl,
              (⟨HEq.rfl,
                (⟨Iff.rfl,
                  fun
                   (_ :
                    ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) =>
                  rfl⟩ :
                 (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                   corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
                    some TashkinovExtensionKind.PE) ∧
                  (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                   base.closure = base.closure))⟩ :
               C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                  corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
                   some TashkinovExtensionKind.PE) ∧
                 (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                  base.closure = base.closure))⟩ :
             C.hierarchy.stage ≍ C.hierarchy.stage ∧
              C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
               (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                 corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
                  some TashkinovExtensionKind.PE) ∧
                (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                 base.closure = base.closure))⟩ :
           C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
            C.hierarchy.stage ≍ C.hierarchy.stage ∧
             C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
              (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
                 some TashkinovExtensionKind.PE) ∧
               (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                base.closure = base.closure))⟩ :
         base.core = base.core ∧
          C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
           C.hierarchy.stage ≍ C.hierarchy.stage ∧
            C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
             (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
               corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
                some TashkinovExtensionKind.PE) ∧
              (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
               base.closure = base.closure)),
        Exists.intro rfl fun (x : Fin (C.hierarchy.dividerCount + (1 : ℕ))) =>
         (⟨rfl, fun (x_1 : Fin k) (_ : x_1 ∈ HierarchyStoredColorsAt C.hierarchy x) => rfl⟩ :
          HierarchyStoredColorsAt C.hierarchy x =
            HierarchyStoredColorsAt C.hierarchy
             (Fin.cast
              ((by
               first
               | omega))
              x) ∧
           ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy x,
            C.good.gamma x eta =
             C.good.gamma
              (Fin.cast
               ((by
                first
                | omega))
               x)
              eta)⟩ :
       SameHierarchyStages C.hierarchy C.hierarchy ∧
        ∃ (hcount : C.hierarchy.dividerCount = C.hierarchy.dividerCount),
         ∀ (j : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
          have j₂ : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
           Fin.cast
            ((by
             first
             | omega))
            j;
          HierarchyStoredColorsAt C.hierarchy j = HierarchyStoredColorsAt C.hierarchy j₂ ∧
           ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy j, C.good.gamma j eta = C.good.gamma j₂ eta),
     minimumContext := ctx : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx };
   let H0 : TashkinovHierarchy ett base := C.hierarchy;
   let q0 : Fin (H0.dividerCount + (1 : ℕ)) := Fin.last H0.dividerCount;
   let A0 : TreeSequence G e0 := HierarchyStarredStage H0 q0;
   let ell : ℕ := HierarchyFullTailLength C;
   let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
   (2 : ℕ) ≤ ell →
    A0.length + ell = T.length →
     B.length = A0.length + (ell - (1 : ℕ)) →
      TreeSequenceInitialSegment B T →
       ∀ alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)),
        ∀ (v : V),
         alpha ∈ MissingColors G phi v →
          ∀ (r : Fin (B.length + (1 : ℕ))),
           B.vertex r = v →
            ¬(↑r : ℕ) ≤ A0.length → ∃ a ∈ TreeSequenceVertexSet A0, alpha ∈ MissingColors G phi a

private abbrev helperHaA166Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ i ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)),
     Disjoint
      (MissingColors G P.coloring
       ((HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C i).length)))
      (MissingColors G P.coloring (T.vertex (Fin.last T.length)))) →
   let corr : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
    {
     replacementInput := input, replacementSeries := ett.series, replacementETT := ett,
     rungAgreement := rfl, seriesPresentation := HEq.rfl,
     finalGeneratingColoring := ett.generatingColoring,
     ladderTreesAgree := fun (i : Fin ett.rounds) => Eq.refl (ett.series.data.tree i.succ.castSucc),
     storedColorsAgree := fun (i : Fin (ett.rounds + (1 : ℕ))) =>
      Eq.refl (ett.series.data.stored i),
     connectingEdgesAgree := fun (i : Fin (ett.rounds + (1 : ℕ))) =>
      Eq.refl (ett.series.data.connectingEdges i),
     extensionKindsAgree := fun (i : Fin (ett.rounds + (1 : ℕ))) =>
      Eq.refl (ett.series.data.kind i),
     replacementProper := fun i => (ett.series.coloringProperties i).1,
     replacementOneUncolored := fun i => (ett.series.coloringProperties i).2,
     replacementStable := fun (i : Fin ett.rounds) =>
      (⟨fun (f : E) (_ : TreeIncidentEdge (ett.series.data.tree i.succ.castSucc) f)
         (_ :
          ∃
           c ∈
            TreeMissingColors (ett.series.data.coloring i.succ)
              (ett.series.data.tree i.succ.castSucc) ∪
             TashkinovStoredColors ett.series.data i.succ,
           ett.series.data.coloring i.succ f = some c) =>
        Eq.refl (ett.series.data.coloring i.succ f),
        fun (v : V) (_ : v ∈ TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) =>
        Eq.refl (MissingColors G (ett.series.data.coloring i.succ) v)⟩ :
       (∀ (f : E),
         TreeIncidentEdge (ett.series.data.tree i.succ.castSucc) f →
          (∃
            c ∈
             TreeMissingColors (ett.series.data.coloring i.succ)
               (ett.series.data.tree i.succ.castSucc) ∪
              TashkinovStoredColors ett.series.data i.succ,
            ett.series.data.coloring i.succ f = some c) →
           ett.series.data.coloring i.succ f = ett.series.data.coloring i.succ f) ∧
        ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc),
         MissingColors G (ett.series.data.coloring i.succ) v =
          MissingColors G (ett.series.data.coloring i.succ) v) :
     CorrespondingExtendedTashkinovTree G k e0 ett phi T };
   let _ : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx :=
    {
     coloring := phi, corresponding := corr, maximum := C.maximum, replacementBase := base,
     counterexample := C,
     sameGood :=
      (⟨(⟨rfl,
          (⟨rfl,
            (⟨HEq.rfl,
              (⟨HEq.rfl,
                (⟨Iff.rfl,
                  fun
                   (_ :
                    ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) =>
                  rfl⟩ :
                 (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                   corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
                    some TashkinovExtensionKind.PE) ∧
                  (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                   base.closure = base.closure))⟩ :
               C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                  corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
                   some TashkinovExtensionKind.PE) ∧
                 (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                  base.closure = base.closure))⟩ :
             C.hierarchy.stage ≍ C.hierarchy.stage ∧
              C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
               (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                 corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
                  some TashkinovExtensionKind.PE) ∧
                (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                 base.closure = base.closure))⟩ :
           C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
            C.hierarchy.stage ≍ C.hierarchy.stage ∧
             C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
              (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
                 some TashkinovExtensionKind.PE) ∧
               (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                base.closure = base.closure))⟩ :
         base.core = base.core ∧
          C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
           C.hierarchy.stage ≍ C.hierarchy.stage ∧
            C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
             (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
               corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
                some TashkinovExtensionKind.PE) ∧
              (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
               base.closure = base.closure)),
        Exists.intro rfl fun (x : Fin (C.hierarchy.dividerCount + (1 : ℕ))) =>
         (⟨rfl, fun (x_1 : Fin k) (_ : x_1 ∈ HierarchyStoredColorsAt C.hierarchy x) => rfl⟩ :
          HierarchyStoredColorsAt C.hierarchy x =
            HierarchyStoredColorsAt C.hierarchy
             (Fin.cast
              ((by
               first
               | omega))
              x) ∧
           ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy x,
            C.good.gamma x eta =
             C.good.gamma
              (Fin.cast
               ((by
                first
                | omega))
               x)
              eta)⟩ :
       SameHierarchyStages C.hierarchy C.hierarchy ∧
        ∃ (hcount : C.hierarchy.dividerCount = C.hierarchy.dividerCount),
         ∀ (j : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
          have j₂ : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
           Fin.cast
            ((by
             first
             | omega))
            j;
          HierarchyStoredColorsAt C.hierarchy j = HierarchyStoredColorsAt C.hierarchy j₂ ∧
           ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy j, C.good.gamma j eta = C.good.gamma j₂ eta),
     minimumContext := ctx : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx };
   let H0 : TashkinovHierarchy ett base := C.hierarchy;
   let q0 : Fin (H0.dividerCount + (1 : ℕ)) := Fin.last H0.dividerCount;
   let A0 : TreeSequence G e0 := HierarchyStarredStage H0 q0;
   let ell : ℕ := HierarchyFullTailLength C;
   let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
   (2 : ℕ) ≤ ell →
    TreeSequenceInitialSegment A0 T →
     A0.length + ell = T.length →
      B.length = A0.length + (ell - (1 : ℕ)) →
       TreeSequenceInitialSegment B T →
        ∀ alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)),
         alpha ∈ TreeMissingColors phi B → alpha ∈ TreeMissingColors phi A0

private theorem helper_branch_600.{u_1, u_2} :
    helperBranch600Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx noCommon corr P0 H0 q0 A0 ell B htwo hsum
      hBlen hBT alpha haLast v hav r hr hrA
  let i := r.val - A0.length
  have hri : r.val = A0.length + i := by dsimp [i]; omega
  have hii : i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1) := by
    have := r.isLt
    change i ∈ Finset.Icc 1 (ell - 1)
    simp only [Finset.mem_Icc]
    omega
  let X := HierarchyFullTailPrefix C i
  have hXlen : X.length = r.val := by
    change min (A0.length + i) T.length = r.val
    have := r.isLt
    omega
  have hXT : TreeSequenceInitialSegment X T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hidx : Fin.castLE (Nat.succ_le_succ hXT.1) (Fin.last X.length) =
      Fin.castLE (Nat.succ_le_succ hBT.1) r := Fin.ext hXlen
  have hxv : X.vertex (Fin.last X.length) = v := by
    rw [← hXT.2.1 _, hidx, hBT.2.1 r, hr]
  have hd := noCommon P0 i hii
  change Disjoint (MissingColors G phi (X.vertex (Fin.last X.length)))
    (MissingColors G phi (T.vertex (Fin.last T.length))) at hd
  rw [hxv] at hd
  exact False.elim (Finset.disjoint_left.mp hd hav haLast)

private theorem helper_haA_166.{u_1, u_2} :
    helperHaA166Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx noCommon corr P0 H0 q0 A0 ell B htwo hAT
      hsum hBlen hBT alpha haLast haB
  simp only [TreeMissingColors, Finset.mem_biUnion] at haB ⊢
  obtain ⟨v, hv, hav⟩ := haB
  simp only [TreeSequenceVertexSet, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  obtain ⟨r, hr⟩ := hv
  by_cases hrA : r.val ≤ A0.length
  · let a : Fin (A0.length + 1) := ⟨r.val, by omega⟩
    have hidx : Fin.castLE (Nat.succ_le_succ hAT.1) a =
        Fin.castLE (Nat.succ_le_succ hBT.1) r := Fin.ext rfl
    have havert : A0.vertex a = v := by
      rw [← hAT.2.1 a, hidx, hBT.2.1 r, hr]
    refine ⟨v, ?_, hav⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image,
      Finset.mem_univ, true_and]
    exact ⟨a, havert⟩
  · exact @helper_branch_600 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx noCommon htwo hsum hBlen hBT alpha haLast v hav r hr hrA
private theorem helper_finish_205.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    HierarchyPathNumber C.hierarchy = (1 : ℕ) →
    (∀ (mu : PartialEdgeColoring E k),
        IsProperEdgeColoring G mu →
          IsOneEdgeUncolored mu e0 → ∀ (v : V), (MissingColors G mu v).Nonempty) →
    let eligible : Finset ℕ :=
      HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ∀ i ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)),
          Disjoint
            (MissingColors G P.coloring
              ((HierarchyFullTailPrefix C i).vertex
                (Fin.last (HierarchyFullTailPrefix C i).length)))
            (MissingColors G P.coloring (T.vertex (Fin.last T.length)))) →
    let H0 : TashkinovHierarchy ett base := C.hierarchy;
    let q0 : Fin (H0.dividerCount + (1 : ℕ)) := Fin.last H0.dividerCount;
    let A0 : TreeSequence G e0 := HierarchyStarredStage H0 q0;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    A0.length + ell = T.length →
    B.length = A0.length + (ell - (1 : ℕ)) →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k),
    c ∈
          TreeMissingColors P.coloring
            (HierarchyStarredStage P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount)) ∧
        c ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) →
    (0 : ℕ) < P.counterexample.hierarchy.dividerCount ∧
          c ∈
            TreeMissingColors P.coloring
              (P.counterexample.hierarchy.stage
                (⟨P.counterexample.hierarchy.dividerCount, by omega⟩ :
                  Fin (P.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        P.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧
          c ∈
            TreeMissingColors P.coloring
              (P.corresponding.replacementETT.series.data.tree
                (Fin.last P.corresponding.replacementETT.rounds).castSucc) →
    eligible.Nonempty := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation hvertexMissing eligible noCommon
      H0 q0 A0 ell B hsum hBlen P c hstart hnormalized
  let H := P.counterexample.hierarchy
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  have hmeasures := P2752_T2_HierarchyMeasures C.hierarchy H P.sameGood.1
  have hstar : A0 = A := hmeasures.1
  have hsit : HierarchyPathNumber H = 1 := hmeasures.2.1.symm.trans hsituation
  have hsumP : A.length + ell = T.length := by rw [← hstar]; exact hsum
  let uses : Finset (Fin T.length) :=
    Finset.univ.filter fun t => A.length ≤ t.val ∧ P.coloring (T.edge t) = some c
  by_cases huse : uses.Nonempty
  · let ej := uses.min' huse
    have heMem : ej ∈ uses := Finset.min'_mem uses huse
    have he := (Finset.mem_filter.mp heMem).2
    have hfirst : ∀ t : Fin T.length, A.length ≤ t.val → t.val < ej.val →
        P.coloring (T.edge t) ≠ some c := by
      intro t ht hlt hcolor
      have htMem : t ∈ uses := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hcolor⟩
      have hle : ej ≤ t := Finset.min'_le uses t htMem
      have hval : ej.val ≤ t.val := hle
      omega
    let j := ej.val - A.length + 1
    have hjLower : 1 ≤ j := by dsimp [j]; omega
    have hjUpper : j ≤ HierarchyFullTailLength C := by
      have := ej.isLt
      change j ≤ ell
      dsimp [j]
      omega
    have hej : ej.val = A.length + (j - 1) := by dsimp [j]; omega
    by_cases hjTwo : 2 ≤ j
    · exact ⟨j - 1, HierarchyClaimNineFirstUseAfterSeed
        G k e0 input T phi ett base C ctx hvertexMissing P hsit c
        hstart hnormalized (noCommon P) j hjTwo hjUpper ej hej ⟨he.2, hfirst⟩⟩
    · have hjOne : j = 1 := by omega
      have heSeed : ej.val = A.length := by rw [hjOne] at hej; simpa using hej
      exact HierarchyClaimNineFirstUseSeed G k e0 input T phi ett base C ctx
        hvertexMissing P hsit c hstart hnormalized (noCommon P) ej heSeed he.2
  · have hunused : ∀ t : Fin T.length, A.length ≤ t.val →
        P.coloring (T.edge t) ≠ some c := by
      intro t ht hcolor
      exact huse ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hcolor⟩⟩
    exact ⟨ell - 1, HierarchyClaimNineUnusedTailColor
      G k e0 input T phi ett base C ctx hvertexMissing P hsit c
      hstart hnormalized (noCommon P) hunused⟩

theorem HierarchyClaimNine {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hsituation : HierarchyPathNumber C.hierarchy = 1)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty) :
    (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty := by
  classical
  let eligible := HierarchyEligibleCommonMissingIndices
    G k e0 input T phi ett base C ctx
  by_contra hnone
  have noCommon (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
      (i : ℕ) (hi : i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1)) :
      Disjoint
        (MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)))
        (MissingColors G P.coloring (T.vertex (Fin.last T.length))) := by
    apply Finset.disjoint_left.mpr
    intro c hc hcLast
    apply hnone
    refine ⟨i, ?_⟩
    exact Finset.mem_filter.mpr ⟨hi, P, c, hc, hcLast⟩
  let corr : CorrespondingExtendedTashkinovTree G k e0 ett phi T := by
    refine ⟨input, ett.series, ett, rfl, HEq.rfl, ett.generatingColoring,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
    · intro i
      rfl
    · intro i
      rfl
    · intro i
      have hs := ett.series.certified i
      cases hs with
      | initial triple _ hi _ _ _ _ _ _ _ _ =>
          simpa [hi] using triple.2.2.2.1
      | SE i _ _ _ _ _ choice _ hcolor _ _ _ _ _ _ _ _ _ _ _ =>
          rw [hcolor]
          exact choice.selectedProper
      | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hproper _ _ _ _ _ _ _ _ _ _ _ =>
          exact hproper
      | RE i hprev _ _ _ _ hcolor _ _ _ _ _ _ _ _ _ _ _ _ =>
          rw [hcolor]
          exact hprev
    · intro i
      have hs := ett.series.certified i
      cases hs with
      | initial triple _ hi _ _ _ _ _ _ _ _ =>
          simpa [hi] using triple.2.2.2.2
      | SE i _ _ _ _ _ choice _ hcolor _ _ _ _ _ _ _ _ _ _ _ =>
          rw [hcolor]
          exact choice.selectedOneUncolored
      | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcurrent _ _ _ _ _ _ _ _ _ _ =>
          exact hcurrent
      | RE i _ hone _ _ _ hcolor _ _ _ _ _ _ _ _ _ _ _ _ =>
          rw [hcolor]
          exact hone
    · intro i
      constructor
      · intro f hf h
        rfl
      · intro v hv
        rfl
  let P0 : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx := by
    refine ⟨phi, corr, C.maximum, base, C, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact ⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩
      · exact ⟨rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
    · exact ctx
  let H0 := C.hierarchy
  let q0 : Fin (H0.dividerCount + 1) := Fin.last H0.dividerCount
  let A0 := HierarchyStarredStage H0 q0
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 1)
  have htwo : 2 ≤ ell :=
    HierarchyCounterexampleTailAtLeastTwo G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have hAT : TreeSequenceInitialSegment A0 T := by
    have hs : TreeSequenceInitialSegment
        (HierarchyStarredStage H0 q0) (H0.stage q0.succ) := by
      refine Fin.cases ?_ (fun i => ?_) q0
      · exact H0.coreInsideFirst
      · exact H0.nested i.succ
    have hlast : q0.succ = Fin.last (H0.dividerCount + 1) := Fin.ext rfl
    simpa only [hlast, H0.terminalStage] using hs
  have hsum : A0.length + ell = T.length := Nat.add_sub_of_le hAT.1
  have hBlen : B.length = A0.length + (ell - 1) := by
    change min (A0.length + (ell - 1)) T.length = A0.length + (ell - 1)
    omega
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨alpha, haB, haLast⟩ :=
    HierarchyCounterexampleTerminalCommonMissing G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  change alpha ∈ TreeMissingColors phi B at haB
  have haA : alpha ∈ TreeMissingColors phi A0 := by
    exact @helper_haA_166 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C ctx noCommon htwo hAT hsum hBlen hBT alpha haLast haB
  have finish (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) (c : Fin k)
      (hstart : c ∈ TreeMissingColors P.coloring
          (HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount)) ∧
        c ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)))
      (hnormalized :
        (0 < P.counterexample.hierarchy.dividerCount ∧
          c ∈ TreeMissingColors P.coloring
            (P.counterexample.hierarchy.stage
              ⟨P.counterexample.hierarchy.dividerCount, by omega⟩)) ∨
        (P.counterexample.hierarchy.dividerCount = 0 ∧
          c ∈ TreeMissingColors P.coloring
            (P.corresponding.replacementETT.series.data.tree
              (Fin.last P.corresponding.replacementETT.rounds).castSucc))) :
      eligible.Nonempty := by
    exact @helper_finish_205 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C ctx hsituation hvertexMissing noCommon hsum hBlen P c hstart
        hnormalized
  have hstart : alpha ∈ TreeMissingColors P0.coloring
      (HierarchyStarredStage P0.counterexample.hierarchy
        (Fin.last P0.counterexample.hierarchy.dividerCount)) ∧
      alpha ∈ MissingColors G P0.coloring (T.vertex (Fin.last T.length)) :=
    ⟨haA, haLast⟩
  by_cases hpos : 0 < H0.dividerCount
  · have lastStage (d : ℕ) (s : Fin (d + 2) → TreeSequence G e0)
        (core : TreeSequence G e0) (hd : 0 < d) :
        Fin.cases core (fun i : Fin d => s i.succ.castSucc) (Fin.last d) =
          s ⟨d, by omega⟩ := by
      cases d with
      | zero => omega
      | succ n =>
          have hi : Fin.last (n + 1) = (Fin.last n).succ := Fin.ext rfl
          rw [hi]
          rfl
    have hAeq : A0 = H0.stage ⟨H0.dividerCount, by omega⟩ :=
      lastStage _ _ _ hpos
    apply hnone
    apply finish P0 alpha hstart
    exact Or.inl ⟨hpos, hAeq ▸ haA⟩
  · have hzero : H0.dividerCount = 0 := Nat.eq_zero_of_not_pos hpos
    have hAcore : A0 = base.core := by
      have hi : q0 = 0 := Fin.ext (by simp [q0, hzero])
      dsimp only [A0]
      rw [hi]
      rfl
    by_cases haTn : alpha ∈ TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    · exact hnone (finish P0 alpha hstart (Or.inr ⟨hzero, haTn⟩))
    · have hpe : ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE := by
        by_contra hnotPE
        have hcore := base.nonparallel hnotPE
        exact haTn (by simpa only [hAcore, hcore] using haA)
      rcases HierarchyClaimNinePENormalization
          G k e0 input T phi ett base C ctx hvertexMissing P0 alpha
          hzero hpe hstart haTn (noCommon P0) with hdone | ⟨P, c, hTn, hA, hLast, _⟩
      · exact hnone hdone
      · have hcount : P.counterexample.hierarchy.dividerCount = 0 :=
          P.sameGood.1.2.1.symm.trans hzero
        exact hnone (finish P c ⟨hA, hLast⟩ (Or.inr ⟨hcount, hTn⟩))

end GoldbergSeymour

end
