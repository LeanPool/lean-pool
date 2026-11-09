/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceTransport

public import LeanPool.GoldbergSeymour.TashkinovSeriesTreeFacts

public import LeanPool.GoldbergSeymour.SharedFacts.ParallelSupportClosureProperties

public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TechnicalInductionContext
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts
public import LeanPool.GoldbergSeymour.TashkinovAugmentationBeforeVertex

/-!
# Parallel Support Closure Properties

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation805Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : TechnicalInductionContext G k e0 ett.rounds) (hpositive : (0 : ℕ) <
        ett.rounds) (sigma : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G sigma) (_ :
        IsOneEdgeUncolored sigma e0) (base : HierarchyBase ett sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    let P : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    ∀ (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (_ : (
    ∀ {A B : TreeSequence G e0} {rho : PartialEdgeColoring E k} (_ : TreeSequenceInitialSegment A
        B), TreeMissingColors rho A ⊆ TreeMissingColors rho B)) (hvT : v ∈ TreeSequenceVertexSet
        T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (hfirstDef : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)),
    let j : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvT - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬ETTFirstAppearanceIndex ett v hvT - (1 : ℕ) <
        ett.rounds) ↦
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : StableColoringBeforeVertex T v hvT (TashkinovStoredColors ett.series.data j.castSucc)
        (ett.series.data.coloring j.castSucc) sigma ∧ ((0 : ℕ) < (↑j.castSucc : ℕ) →
        StableColoring (ett.series.data.tree j.castSucc.castSucc) (TashkinovStoredColors
        ett.series.data j.castSucc) (ett.series.data.coloring j.castSucc) sigma)) (_ :
        TreeSequenceInitialSegment P base.closure) (_ : ColoredVertexSetClosed G sigma
        (TreeSequenceVertexSet base.closure)) (_ : (0 : ℕ) < (↑j : ℕ)),
    let Tprev : TreeSequence G e0 := ett.series.data.tree j.castSucc.castSucc;
    ∀ (_ : Tprev.length < P.length) (_ : TreeSequenceInitialSegment Tprev P) (seed : TreeSequence
        G e0) (_ : (ett.series.data.kind j.castSucc = some TashkinovExtensionKind.PE ∧ seed =
        Tprev ∨ (ett.series.data.kind j.castSucc = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind j.castSucc = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges j.castSucc = { f } ∧ TreeSequenceAdjoinEdge Tprev f
        seed)) (_ : TashkinovAugmentationSequence sigma seed base.closure) (lower :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (⟨(↑j : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hround : lower.rounds = (↑j : ℕ)) (_ : MaximumProperty
        lower),
    let lowerTerminal : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
    ∀ (_ : lower.series.data.tree lowerTerminal.castSucc = Tprev) (_ :
        lower.series.data.connectingEdges lowerTerminal = ett.series.data.connectingEdges
        (Fin.castLE (
    by omega
    ) lowerTerminal)) (_ : lower.series.data.kind lowerTerminal = ett.series.data.kind (Fin.castLE
        (
    by omega
    ) lowerTerminal)) (_ : TashkinovStoredColors lower.series.data lowerTerminal =
        TashkinovStoredColors ett.series.data (Fin.castLE (
    by omega
    ) lowerTerminal)) (_ : lower.series.data.coloring lowerTerminal = ett.series.data.coloring
        j.castSucc), ColoredVertexSetElementary G sigma (TreeSequenceVertexSet base.closure) ∧
        ColoredVertexSetClosed G sigma (TreeSequenceVertexSet base.closure) ∧
    ∀ (alpha beta : Fin k), alpha ∈ TreeMissingColors sigma base.closure ∨ beta ∈
        TreeMissingColors sigma base.closure → TreeInterchangeable G base.closure sigma alpha beta

private abbrev helperBranch413Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : TechnicalInductionContext G k e0 ett.rounds) (_ : MaximumProperty ett)
        (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (_ :
        IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (base : HierarchyBase ett
        sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    let P : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    ∀ (_ : ett.series.data.chosenVertex n = some v ∧ TashkinovClosure sigma P base.closure ∧
        Nonempty (OrderedTreeUnion Tn base.closure base.core)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (_ : (
    ∀ {A B : TreeSequence G e0} {rho : PartialEdgeColoring E k} (_ : TashkinovAugmentationSequence
        rho A B), TreeSequenceInitialSegment A B)) (_ : (
    ∀ {A B : TreeSequence G e0} {rho : PartialEdgeColoring E k} (_ : TreeSequenceInitialSegment A
        B), TreeMissingColors rho A ⊆ TreeMissingColors rho B)) (_ : TreeSequenceInitialSegment P
        Tn) (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (hfirstDef : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)),
    let j : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvT - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬ETTFirstAppearanceIndex ett v hvT - (1 : ℕ) <
        ett.rounds) ↦
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : ETTFirstAppearanceIndex ett v hvT = (↑j : ℕ) + (1 : ℕ)) (_ : StableColoringBeforeVertex
        T v hvT (TashkinovStoredColors ett.series.data j.castSucc) (ett.series.data.coloring
        j.castSucc) sigma ∧ ((0 : ℕ) < (↑j.castSucc : ℕ) → StableColoring (ett.series.data.tree
        j.castSucc.castSucc) (TashkinovStoredColors ett.series.data j.castSucc)
        (ett.series.data.coloring j.castSucc) sigma)) (_ : (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))) (_ : (0 : ℕ) < (↑i : ℕ)), TreeSequenceInitialSegment
        (ett.series.data.tree i.castSucc) (ett.series.data.tree i.succ))),
    let Tj : TreeSequence G e0 := ett.series.data.tree j.succ.castSucc;
    ∀ (_ : TreeSequenceInitialSegment Tj Tn) (_ : P.length = (↑base.supportPosition : ℕ)) (_ :
        TreeSequenceInitialSegment P Tj) (_ : (
    ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence (ett.series.data.coloring
        j.castSucc) S P), TashkinovAugmentationSequence sigma S P)) (_ :
        TreeSequenceInitialSegment P base.closure) (_ : ColoredVertexSetClosed G sigma
        (TreeSequenceVertexSet base.closure)) (_ : v ∈ TreeSequenceVertexSet P) (_ : (0 : ℕ) < (↑j
        : ℕ)), ColoredVertexSetElementary G sigma (TreeSequenceVertexSet base.closure) ∧
        ColoredVertexSetClosed G sigma (TreeSequenceVertexSet base.closure) ∧
    ∀ (alpha beta : Fin k), alpha ∈ TreeMissingColors sigma base.closure ∨ beta ∈
        TreeMissingColors sigma base.closure → TreeInterchangeable G base.closure sigma alpha beta

private theorem helper_hNotPrev_228.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (base :
        HierarchyBase ett sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    ∀ (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (hfirstDef : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)),
    let j : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvT - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬ETTFirstAppearanceIndex ett v hvT - (1 : ℕ) <
        ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : ETTFirstAppearanceIndex ett v hvT = (↑j : ℕ) + (1 : ℕ)) (_ : (0 : ℕ) < (↑j : ℕ)),
    let Tprev : TreeSequence G e0 := ett.series.data.tree j.castSucc.castSucc; v ∉
        TreeSequenceVertexSet Tprev := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive sigma base n q Tn v hvT candidates hqmem
      candidatesNonempty minimum hfirstDef hfirstUpper j hjFirst hjPositive Tprev hvPrev
  let jp : Fin ett.rounds := ⟨j.val - 1, by omega⟩
  have hjpSucc : jp.succ = j.castSucc := by
    apply Fin.ext
    simp [jp]
    omega
  have hjpMem : jp.castSucc ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold ExtendedTashkinovLadderStage
    rw [Fin.lastCases_castSucc]
    have hindex : jp.succ.castSucc = j.castSucc.castSucc :=
      congrArg Fin.castSucc hjpSucc
    rw [hindex]
    exact hvPrev
  have hle : minimum ≤ jp.castSucc := by
    exact Finset.min'_le candidates jp.castSucc hjpMem
  have hvals := Fin.le_iff_val_le_val.mp hle
  dsimp [jp] at hvals
  omega

private theorem helper_branch_280.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (base :
        HierarchyBase ett sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    let P : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    ∀ (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)) (_ : (
    ∀ {A B : TreeSequence G e0} {rho : PartialEdgeColoring E k} (_ : TashkinovAugmentationSequence
        rho A B), TreeSequenceInitialSegment A B)) (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (hfirstDef : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)),
    let j : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvT - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬ETTFirstAppearanceIndex ett v hvT - (1 : ℕ) <
        ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tj : TreeSequence G e0 := ett.series.data.tree j.succ.castSucc;
    ∀ (_ : P.length = (↑base.supportPosition : ℕ)) (_ : TreeSequenceInitialSegment P Tj),
    let Tprev : TreeSequence G e0 := ett.series.data.tree j.castSucc.castSucc;
    ∀ (_ : Tprev.length < P.length) (ci : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree ci.succ.castSucc) (TashkinovStoredColors ett.series.data
        ci.castSucc) (ett.series.data.coloring ci.castSucc)) (_ : ett.series.data.connectingEdges
        ci.succ = { choice.edge }) (_ : ett.series.data.kind ci.succ = some
        TashkinovExtensionKind.SE) (adjoined : TreeSequence G e0) (_ : TreeSequenceAdjoinEdge
        (ett.series.data.tree ci.succ.castSucc) choice.edge adjoined) (_ : TashkinovClosure
        (ett.series.data.coloring ci.succ) adjoined (ett.series.data.tree ci.succ.succ)) (_ :
        j.castSucc = ci.succ),
    ∃ (seed : TreeSequence G e0), (ett.series.data.kind ci.succ = some TashkinovExtensionKind.PE ∧
        seed = Tprev ∨ (ett.series.data.kind ci.succ = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind ci.succ = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges ci.succ = { f } ∧ TreeSequenceAdjoinEdge Tprev f
        seed) ∧ TashkinovAugmentationSequence (ett.series.data.coloring ci.succ) seed Tj ∧
        TreeSequenceInitialSegment seed P := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive sigma base n q Tn v P commonPrefix
      sequenceSegment hvT candidates hqmem candidatesNonempty minimum hfirstDef hfirstUpper j Tj
      hPLength hPStage Tprev hPrevStrictP ci choice currentEdges currentKind adjoined
      adjoinedExactly closedExtension htarget
  have hciSucc : ci.succ = j.castSucc := htarget.symm
  have hnext : ci.succ.succ = j.succ.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc]
    have hvals := congrArg Fin.val hciSucc
    simpa using congrArg Nat.succ hvals
  have hroute : TashkinovAugmentationSequence
      (ett.series.data.coloring ci.succ) adjoined Tj := by
    simpa only [Tj, hnext] using closedExtension.1
  have hadjoin : TreeSequenceAdjoinEdge Tprev choice.edge adjoined := by
    simpa only [Tprev, hciSucc] using adjoinedExactly
  refine ⟨adjoined, ?_, hroute,
    hadjoin.initialSegment_of_route hroute hPStage hPrevStrictP⟩
  right
  exact ⟨Or.inl (by simpa only [hciSucc] using currentKind), choice.edge,
    by simpa only [hciSucc] using currentEdges, hadjoin⟩

private theorem helper_branch_332.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (base :
        HierarchyBase ett sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    let P : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    ∀ (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)) (_ : (
    ∀ {A B : TreeSequence G e0} {rho : PartialEdgeColoring E k} (_ : TashkinovAugmentationSequence
        rho A B), TreeSequenceInitialSegment A B)) (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (hfirstDef : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)),
    let j : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvT - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬ETTFirstAppearanceIndex ett v hvT - (1 : ℕ) <
        ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tj : TreeSequence G e0 := ett.series.data.tree j.succ.castSucc;
    ∀ (_ : P.length = (↑base.supportPosition : ℕ)) (_ : TreeSequenceInitialSegment P Tj),
    let Tprev : TreeSequence G e0 := ett.series.data.tree j.castSucc.castSucc;
    ∀ (_ : Tprev.length < P.length) (ci : Fin ett.rounds) (available :
        RevisitingExtensionCertificate ett.series.data ci.castSucc) (_ :
        ett.series.data.connectingEdges ci.succ = { available.edge }) (_ : ett.series.data.kind
        ci.succ = some TashkinovExtensionKind.RE) (adjoined : TreeSequence G e0) (_ :
        TreeSequenceAdjoinEdge (ett.series.data.tree ci.succ.castSucc) available.edge adjoined) (_
        : TashkinovClosure (ett.series.data.coloring ci.succ) adjoined (ett.series.data.tree
        ci.succ.succ)) (_ : j.castSucc = ci.succ),
    ∃ (seed : TreeSequence G e0), (ett.series.data.kind ci.succ = some TashkinovExtensionKind.PE ∧
        seed = Tprev ∨ (ett.series.data.kind ci.succ = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind ci.succ = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges ci.succ = { f } ∧ TreeSequenceAdjoinEdge Tprev f
        seed) ∧ TashkinovAugmentationSequence (ett.series.data.coloring ci.succ) seed Tj ∧
        TreeSequenceInitialSegment seed P := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive sigma base n q Tn v P commonPrefix
      sequenceSegment hvT candidates hqmem candidatesNonempty minimum hfirstDef hfirstUpper j Tj
      hPLength hPStage Tprev hPrevStrictP ci available currentEdges currentKind adjoined
      adjoinedExactly closedExtension htarget
  have hciSucc : ci.succ = j.castSucc := htarget.symm
  have hnext : ci.succ.succ = j.succ.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc]
    have hvals := congrArg Fin.val hciSucc
    simpa using congrArg Nat.succ hvals
  have hroute : TashkinovAugmentationSequence
      (ett.series.data.coloring ci.succ) adjoined Tj := by
    simpa only [Tj, hnext] using closedExtension.1
  have hadjoin : TreeSequenceAdjoinEdge Tprev available.edge adjoined := by
    simpa only [Tprev, hciSucc] using adjoinedExactly
  refine ⟨adjoined, ?_, hroute,
    hadjoin.initialSegment_of_route hroute hPStage hPrevStrictP⟩
  right
  exact ⟨Or.inr (by simpa only [hciSucc] using currentKind), available.edge,
    by simpa only [hciSucc] using currentEdges, hadjoin⟩

private theorem helper_branch_490.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (base :
        HierarchyBase ett sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    let P : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    ∀ (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (hfirstDef : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)),
    let j : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvT - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬ETTFirstAppearanceIndex ett v hvT - (1 : ℕ) <
        ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tj : TreeSequence G e0 := ett.series.data.tree j.succ.castSucc;
    let Tprev : TreeSequence G e0 := ett.series.data.tree j.castSucc.castSucc;
    ∀ (_ : TreeSequenceInitialSegment Tprev P) (ci : Fin ett.rounds) (_ : ett.series.data.kind
        ci.succ = some TashkinovExtensionKind.PE) (_ : TashkinovClosure (ett.series.data.coloring
        ci.succ) (ett.series.data.tree ci.succ.castSucc) (ett.series.data.tree ci.succ.succ)) (_ :
        j.castSucc = ci.succ),
    ∃ (seed : TreeSequence G e0), (ett.series.data.kind ci.succ = some TashkinovExtensionKind.PE ∧
        seed = Tprev ∨ (ett.series.data.kind ci.succ = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind ci.succ = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges ci.succ = { f } ∧ TreeSequenceAdjoinEdge Tprev f
        seed) ∧ TashkinovAugmentationSequence (ett.series.data.coloring ci.succ) seed Tj ∧
        TreeSequenceInitialSegment seed P := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive sigma base n q Tn v P hvT candidates hqmem
      candidatesNonempty minimum hfirstDef hfirstUpper j Tj Tprev hPrevP ci currentKind
      closedExtension htarget
  have hciSucc : ci.succ = j.castSucc := htarget.symm
  have hnext : ci.succ.succ = j.succ.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc]
    have hvals := congrArg Fin.val hciSucc
    simpa using congrArg Nat.succ hvals
  have hroute : TashkinovAugmentationSequence
      (ett.series.data.coloring ci.succ) Tprev Tj := by
    have hroute' := closedExtension.1
    rw [hnext] at hroute'
    simpa only [Tprev, Tj, hciSucc] using hroute'
  refine ⟨Tprev, ?_, hroute, hPrevP⟩
  left
  exact ⟨by simpa only [hciSucc] using currentKind, rfl⟩

private theorem helper_hEligibilityLower_608.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (base :
        HierarchyBase ett sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    ∀ (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (hfirstDef : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)),
    let j : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvT - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬ETTFirstAppearanceIndex ett v hvT - (1 : ℕ) <
        ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tprev : TreeSequence G e0 := ett.series.data.tree j.castSucc.castSucc;
    ∀ (seed : TreeSequence G e0) (_ : (ett.series.data.kind j.castSucc = some
        TashkinovExtensionKind.PE ∧ seed = Tprev ∨ (ett.series.data.kind j.castSucc = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind j.castSucc = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges j.castSucc = { f } ∧ TreeSequenceAdjoinEdge Tprev f
        seed)) (_ : TashkinovAugmentationSequence sigma seed base.closure) (lower :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (⟨(↑j : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))),
    let lowerTerminal : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
    ∀ (_ : lower.series.data.tree lowerTerminal.castSucc = Tprev) (_ : lower.series.data.kind
        lowerTerminal = ett.series.data.kind j.castSucc) (_ : lower.series.data.connectingEdges
        lowerTerminal = ett.series.data.connectingEdges j.castSucc), lower.series.data.kind
        lowerTerminal = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence sigma
        (lower.series.data.tree lowerTerminal.castSucc) base.closure ∨ (lower.series.data.kind
        lowerTerminal = some TashkinovExtensionKind.SE ∨ lower.series.data.kind lowerTerminal =
        some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed' : TreeSequence G e0), lower.series.data.connectingEdges lowerTerminal = { f }
        ∧ TreeSequenceAdjoinEdge (lower.series.data.tree lowerTerminal.castSucc) f seed' ∧
        TashkinovAugmentationSequence sigma seed' base.closure := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive sigma base n q Tn v hvT candidates hqmem
      candidatesNonempty minimum hfirstDef hfirstUpper j Tprev seed hEligibility
      hrouteSigmaClosure lower lowerTerminal htreeLower hkindLower' hconnectingLower'
  rcases hEligibility with hparallelSeed | hnonparallelSeed
  · left
    refine ⟨hkindLower'.trans hparallelSeed.1, ?_⟩
    rw [htreeLower]
    simpa only [hparallelSeed.2] using hrouteSigmaClosure
  · right
    rcases hnonparallelSeed with ⟨hkind, f, hedgeSet, hadjoin⟩
    refine ⟨?_, f, seed, ?_, ?_, hrouteSigmaClosure⟩
    · rcases hkind with hse | hre
      · exact Or.inl (hkindLower'.trans hse)
      · exact Or.inr (hkindLower'.trans hre)
    · exact hconnectingLower'.trans hedgeSet
    · rw [htreeLower]
      exact hadjoin

private theorem helper_hselfStable_659.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (_ :
        IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (base : HierarchyBase ett
        sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    ∀ (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (hfirstDef : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)),
    let j : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvT - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬ETTFirstAppearanceIndex ett v hvT - (1 : ℕ) <
        ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    ∀ (lower : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (⟨(↑j : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0 lower
        sigma base.closure),
    let replacementTerminal : Fin (corr.replacementETT.rounds + (1 : ℕ)) := Fin.last
        corr.replacementETT.rounds;
    let L : TreeSequence G e0 := corr.replacementETT.series.data.tree (Fin.last
        (corr.replacementETT.rounds + (1 : ℕ))); StableColoring L (TashkinovStoredColors
        corr.replacementETT.series.data replacementTerminal)
        (corr.replacementETT.series.data.coloring replacementTerminal) sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive sigma hproper hone base n q Tn v hvT
      candidates hqmem candidatesNonempty minimum hfirstDef hfirstUpper j lower corr
      replacementTerminal L
  have hgenerating : sigma =
      corr.replacementETT.series.data.coloring replacementTerminal := by
    simpa [replacementTerminal] using
      corr.replacementETT.generatingColoring
  rw [← hgenerating]
  let a : {rho : PartialEdgeColoring E k //
      IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0} :=
    ⟨sigma, hproper, hone⟩
  have hrefl := (sc2 G e0 L
    (TashkinovStoredColors corr.replacementETT.series.data
      replacementTerminal)).refl a
  simpa [a] using hrefl

private theorem helper_hinterchangeable_678.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : TechnicalInductionContext G k e0 ett.rounds) (hpositive : (0 : ℕ) <
        ett.rounds) (sigma : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G sigma) (_ :
        IsOneEdgeUncolored sigma e0) (base : HierarchyBase ett sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    ∀ (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (_ : (
    ∀ {A B : TreeSequence G e0} {rho : PartialEdgeColoring E k} (_ : TreeSequenceInitialSegment A
        B), TreeMissingColors rho A ⊆ TreeMissingColors rho B)) (hvT : v ∈ TreeSequenceVertexSet
        T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (hfirstDef : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)),
    let j : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvT - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬ETTFirstAppearanceIndex ett v hvT - (1 : ℕ) <
        ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    ∀ (lower : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (⟨(↑j : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0 lower
        sigma base.closure) (_ : MaximumProperty corr.replacementETT) (_ : (0 : ℕ) <
        corr.replacementETT.rounds) (_ : corr.replacementETT.rounds < ett.rounds),
    let replacementTerminal : Fin (corr.replacementETT.rounds + (1 : ℕ)) := Fin.last
        corr.replacementETT.rounds;
    let L : TreeSequence G e0 := corr.replacementETT.series.data.tree (Fin.last
        (corr.replacementETT.rounds + (1 : ℕ)));
    ∀ (_ : StableColoring L (TashkinovStoredColors corr.replacementETT.series.data
        replacementTerminal) (corr.replacementETT.series.data.coloring replacementTerminal) sigma)
        (_ : TreeSequenceInitialSegment base.closure L) (alpha beta : Fin k) (_ : alpha ∈
        TreeMissingColors sigma base.closure ∨ beta ∈ TreeMissingColors sigma base.closure),
        TreeInterchangeable G base.closure sigma alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hpositive sigma hproper hone base n q Tn v
      vertexTransfer missingTransfer hvT candidates hqmem candidatesNonempty minimum hfirstDef
      hfirstUpper j lower corr hreplacementMP hreplacementPositive hreplacementBefore
      replacementTerminal L hselfStable hclosureL alpha beta hmissing
  have hmissingL : alpha ∈ TreeMissingColors sigma L ∨
      beta ∈ TreeMissingColors sigma L := by
    rcases hmissing with ha | hb
    · exact Or.inl (missingTransfer hclosureL ha)
    · exact Or.inr (missingTransfer hclosureL hb)
  have hinterL : TreeInterchangeable G L sigma alpha beta := by
    have h := ctx.lowerTwo corr.replacementETT hreplacementPositive
      hreplacementBefore hreplacementMP sigma hproper hone
      (by simpa [replacementTerminal, L] using hselfStable)
      alpha beta (by simpa [L] using hmissingL)
    simpa [L] using h
  unfold TreeInterchangeable at hinterL ⊢
  intro z w hz hw hzMeet hwMeet
  apply hinterL z w hz hw
  · obtain ⟨x, hx, hxComponent⟩ := hzMeet
    exact ⟨x, vertexTransfer hclosureL hx, hxComponent⟩
  · obtain ⟨x, hx, hxComponent⟩ := hwMeet
    exact ⟨x, vertexTransfer hclosureL hx, hxComponent⟩

private theorem helper_continuation_805.{u_1, u_2} :
    helperContinuation805Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hpositive sigma hproper hone base n q Tn v P
      segmentTrans vertexTransfer missingTransfer hvT candidates hqmem candidatesNonempty minimum
      hfirstDef hfirstUpper j hcurrent hPClosure hclosed hjPositive Tprev hPrevStrictP hPrevP
      seed hEligibility hrouteSigmaClosure lower hround hlowerMP lowerTerminal htreeLower
      hconnectingLower hkindLower hstoredLower hcolorLower'
  have hstoredLower' : TashkinovStoredColors lower.series.data
      lowerTerminal = TashkinovStoredColors ett.series.data j.castSucc := by
    calc
      TashkinovStoredColors lower.series.data lowerTerminal =
          TashkinovStoredColors ett.series.data
            (Fin.castLE (by omega) lowerTerminal) := hstoredLower
      _ = TashkinovStoredColors ett.series.data j.castSucc := by
        congr 1
        apply Fin.ext
        simp [lowerTerminal, hround]
  have hkindLower' : lower.series.data.kind lowerTerminal =
      ett.series.data.kind j.castSucc := by
    calc
      lower.series.data.kind lowerTerminal =
          ett.series.data.kind (Fin.castLE (by omega) lowerTerminal) :=
        hkindLower
      _ = ett.series.data.kind j.castSucc := by
        congr 1
        apply Fin.ext
        simp [lowerTerminal, hround]
  have hconnectingLower' : lower.series.data.connectingEdges lowerTerminal =
      ett.series.data.connectingEdges j.castSucc := by
    calc
      lower.series.data.connectingEdges lowerTerminal =
          ett.series.data.connectingEdges
            (Fin.castLE (by omega) lowerTerminal) := hconnectingLower
      _ = ett.series.data.connectingEdges j.castSucc := by
        congr 1
        apply Fin.ext
        simp [lowerTerminal, hround]
  have hstableLower : StableColoring
      (lower.series.data.tree lowerTerminal.castSucc)
      (TashkinovStoredColors lower.series.data lowerTerminal)
      (lower.series.data.coloring lowerTerminal) sigma := by
    rw [htreeLower, hstoredLower', hcolorLower']
    simpa [Tprev] using hcurrent.2 (by simpa using hjPositive)
  have hmod : ModColoring lower sigma :=
    ctx.lowerSix lower (by omega) (by omega) hlowerMP sigma hproper hone
      (by simpa [lowerTerminal] using hstableLower)
  have hPrevClosure : TreeSequenceInitialSegment Tprev base.closure :=
    segmentTrans hPrevP hPClosure
  have hLowerTerminalClosure : TreeSequenceInitialSegment
      (lower.series.data.tree lowerTerminal.castSucc) base.closure := by
    rw [htreeLower]
    exact hPrevClosure
  have hLowerStrict :
      (lower.series.data.tree lowerTerminal.castSucc).length <
        base.closure.length := by
    rw [htreeLower]
    exact lt_of_lt_of_le hPrevStrictP hPClosure.1
  have hEligibilityLower := @helper_hEligibilityLower_608 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 input T phi ett hpositive sigma base hvT hqmem hfirstDef
      hfirstUpper seed hEligibility hrouteSigmaClosure lower htreeLower hkindLower'
      hconnectingLower'
  obtain ⟨corr⟩ : Nonempty
      (CorrespondingExtendedTashkinovTree G k e0 lower sigma base.closure) :=
    hmod.2.2 base.closure
      (by simpa [lowerTerminal] using hLowerTerminalClosure)
      (by simpa [lowerTerminal] using hLowerStrict)
      (by simpa [lowerTerminal] using hEligibilityLower)
  have hreplacementMP : MaximumProperty corr.replacementETT :=
    MaximumPropertyTransport G k e0 lower sigma hmod base.closure corr
      hlowerMP
  have hreplacementPositive : 0 < corr.replacementETT.rounds := by
    exact corr.replacementETT.roundsPositive
  have hreplacementBefore : corr.replacementETT.rounds < ett.rounds := by
    rw [corr.rungAgreement, hround]
    exact j.isLt
  have helementary : ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet base.closure) :=
    ctx.lowerOne corr.replacementETT hreplacementPositive
      hreplacementBefore hreplacementMP
  let replacementTerminal : Fin (corr.replacementETT.rounds + 1) :=
    Fin.last corr.replacementETT.rounds
  let L : TreeSequence G e0 :=
    corr.replacementETT.series.data.tree
      (Fin.last (corr.replacementETT.rounds + 1))
  have hselfStable := @helper_hselfStable_659 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett hpositive sigma hproper hone base hvT hqmem hfirstDef
      hfirstUpper lower corr
  have hclosureL : TreeSequenceInitialSegment base.closure L := by
    simpa [L] using corr.replacementETT.belowFinal
  have hinterchangeable := @helper_hinterchangeable_678 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 input T phi ett ctx hpositive sigma hproper hone base
      vertexTransfer missingTransfer hvT hqmem hfirstDef hfirstUpper lower corr hreplacementMP
      hreplacementPositive hreplacementBefore hselfStable hclosureL
  exact ⟨helementary, hclosed, hinterchangeable⟩

private theorem helper_branch_413.{u_1, u_2} :
    helperBranch413Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hMP hpositive sigma hproper hone base n q Tn v P
      hparallel segmentTrans commonPrefix vertexTransfer sequenceSegment missingTransfer hP_Tn
      hvT candidates hqmem candidatesNonempty minimum hfirstDef hfirstUpper j hjFirst hcurrent
      stepSegment Tj hStageTn hPLength hPStage transportRoute hPClosure hclosed hvP hjPositive
  let Tprev : TreeSequence G e0 :=
    ett.series.data.tree j.castSucc.castSucc
  have hPrevStage : TreeSequenceInitialSegment Tprev Tj := by
    have hseg := stepSegment j.castSucc (by simpa using hjPositive)
    change TreeSequenceInitialSegment
      (ett.series.data.tree j.castSucc.castSucc)
      (ett.series.data.tree j.succ.castSucc)
    convert hseg using 1; congr 1
  have hNotPrev := @helper_hNotPrev_228 V E inferInstance inferInstance inferInstance inferInstance
      G k e0 input T phi ett hpositive sigma base hvT hqmem hfirstDef hfirstUpper hjFirst hjPositive
  have hPrevTn : TreeSequenceInitialSegment Tprev Tn :=
    segmentTrans hPrevStage hStageTn
  have hPrevStrictP : Tprev.length < P.length := by
    by_contra hnot
    have hPPrev : TreeSequenceInitialSegment P Tprev :=
      commonPrefix hP_Tn hPrevTn (by omega)
    exact hNotPrev (vertexTransfer hPPrev hvP)
  have hPrevP : TreeSequenceInitialSegment Tprev P :=
    commonPrefix hPrevStage hPStage (Nat.le_of_lt hPrevStrictP)
  obtain ⟨seed, hEligibility, hrouteOld, hseedP⟩ :
      ∃ seed : TreeSequence G e0,
        ((ett.series.data.kind j.castSucc =
              some TashkinovExtensionKind.PE ∧ seed = Tprev) ∨
          ((ett.series.data.kind j.castSucc =
                some TashkinovExtensionKind.SE ∨
              ett.series.data.kind j.castSucc =
                some TashkinovExtensionKind.RE) ∧
            ∃ f : E, ett.series.data.connectingEdges j.castSucc = {f} ∧
              TreeSequenceAdjoinEdge Tprev f seed)) ∧
        TashkinovAugmentationSequence
            (ett.series.data.coloring j.castSucc) seed Tj ∧
        TreeSequenceInitialSegment seed P := by
    have hcert := ett.series.certified j.castSucc
    generalize htarget : j.castSucc = target at hcert
    cases hcert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        have hvals := congrArg Fin.val htarget
        simp at hvals
        omega
    | SE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
            exact @helper_branch_280 V E inferInstance inferInstance inferInstance inferInstance
                G k e0 input T phi ett hpositive sigma base commonPrefix sequenceSegment hvT
                hqmem hfirstDef hfirstUpper hPLength hPStage hPrevStrictP ci choice currentEdges
                currentKind adjoined adjoinedExactly closedExtension htarget
    | PE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
            exact @helper_branch_490 V E inferInstance inferInstance inferInstance inferInstance
                G k e0 input T phi ett hpositive sigma base hvT hqmem hfirstDef hfirstUpper
                hPrevP ci currentKind closedExtension htarget
    | RE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
            exact @helper_branch_332 V E inferInstance inferInstance inferInstance inferInstance
                G k e0 input T phi ett hpositive sigma base commonPrefix sequenceSegment hvT
                hqmem hfirstDef hfirstUpper hPLength hPStage hPrevStrictP ci available
                currentEdges currentKind adjoined adjoinedExactly closedExtension htarget
  have hrouteOldP : TashkinovAugmentationSequence
      (ett.series.data.coloring j.castSucc) seed P :=
    TashkinovAugmentationSequenceRestrict
      (ett.series.data.coloring j.castSucc) seed P Tj
      hrouteOld hseedP hPStage
  have hrouteSigmaP : TashkinovAugmentationSequence sigma seed P :=
    transportRoute seed hrouteOldP
  have hrouteSigmaClosure : TashkinovAugmentationSequence
      sigma seed base.closure :=
    Relation.ReflTransGen.trans hrouteSigmaP hparallel.2.1.1
  have hclosureSeed : TashkinovClosure sigma seed base.closure :=
    ⟨hrouteSigmaClosure, hclosed⟩
  obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
    CertifiedETTRestriction G k e0 input T phi ett hMP j.val
      (by omega) (by exact j.isLt)
  let lowerTerminal : Fin (lower.rounds + 1) := Fin.last lower.rounds
  have htreeLower : lower.series.data.tree lowerTerminal.castSucc =
      Tprev := by
    calc
      lower.series.data.tree lowerTerminal.castSucc =
          ett.series.data.tree
            (Fin.castLE (by omega) lowerTerminal.castSucc) :=
        htrees lowerTerminal.castSucc
      _ = Tprev := by
        change ett.series.data.tree _ =
          ett.series.data.tree j.castSucc.castSucc
        congr 1
        apply Fin.ext
        simp [lowerTerminal, hround]
  obtain ⟨hcolorLower, hstoredRawLower, hconnectingLower,
      hkindLower, hchosenLower, houtsideLower, hdeltaLower, hgammaLower,
      hstoredLower, hcertLower⟩ := hdata lowerTerminal
  have hcolorLower' : lower.series.data.coloring lowerTerminal =
      ett.series.data.coloring j.castSucc := by
    calc
      lower.series.data.coloring lowerTerminal =
          ett.series.data.coloring (Fin.castLE (by omega) lowerTerminal) :=
        hcolorLower
      _ = ett.series.data.coloring j.castSucc := by
        congr 1
        apply Fin.ext
        simp [lowerTerminal, hround]
  exact @helper_continuation_805 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett ctx hpositive sigma hproper hone base segmentTrans vertexTransfer
      missingTransfer hvT hqmem hfirstDef hfirstUpper hcurrent hPClosure hclosed hjPositive
      hPrevStrictP hPrevP seed hEligibility hrouteSigmaClosure lower hround hlowerMP htreeLower
      hconnectingLower hkindLower hstoredLower hcolorLower'
private theorem helper_branch_742.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (_ :
        IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (base : HierarchyBase ett
        sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    let P : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    ∀ (_ : ett.series.data.chosenVertex n = some v ∧ TashkinovClosure sigma P base.closure ∧
        Nonempty (OrderedTreeUnion Tn base.closure base.core)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)) (_ : (
    ∀ {A B : TreeSequence G e0} {rho : PartialEdgeColoring E k} (_ : TashkinovAugmentationSequence
        rho A B), TreeSequenceInitialSegment A B)) (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (hfirstDef : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)),
    let j : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvT - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬ETTFirstAppearanceIndex ett v hvT - (1 : ℕ) <
        ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : ETTFirstAppearanceIndex ett v hvT = (↑j : ℕ) + (1 : ℕ)),
    let Tj : TreeSequence G e0 := ett.series.data.tree j.succ.castSucc;
    ∀ (_ : P.length = (↑base.supportPosition : ℕ)) (_ : TreeSequenceInitialSegment P Tj) (_ : (
    ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence (ett.series.data.coloring
        j.castSucc) S P), TashkinovAugmentationSequence sigma S P)) (_ : ColoredVertexSetClosed G
        sigma (TreeSequenceVertexSet base.closure)) (_ : ¬(0 : ℕ) < (↑j : ℕ)),
        ColoredVertexSetElementary G sigma (TreeSequenceVertexSet base.closure) ∧
        ColoredVertexSetClosed G sigma (TreeSequenceVertexSet base.closure) ∧
    ∀ (alpha beta : Fin k), alpha ∈ TreeMissingColors sigma base.closure ∨ beta ∈
        TreeMissingColors sigma base.closure → TreeInterchangeable G base.closure sigma alpha beta
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive sigma hproper hone base n q Tn v P hparallel
      commonPrefix sequenceSegment hvT candidates hqmem candidatesNonempty minimum hfirstDef
      hfirstUpper j hjFirst Tj hPLength hPStage transportRoute hclosed hjPositive
  have hjZero : j.val = 0 := by omega
  have hjZeroIndex : j.castSucc = (0 : Fin (ett.rounds + 1)) := by
    apply Fin.ext
    simpa using hjZero
  have hTjOne : Tj = ett.series.data.tree
      (1 : Fin (ett.rounds + 2)) := by
    change ett.series.data.tree j.succ.castSucc =
      ett.series.data.tree (1 : Fin (ett.rounds + 2))
    congr 1
    apply Fin.ext
    simp only [Fin.castSucc_succ, Fin.val_succ, Fin.val_castSucc, Fin.coe_ofNat_eq_mod, Nat.one_mod,
  Nat.add_eq_right]
    exact hjZero
  have hcert := ett.series.certified j.castSucc
  generalize htarget : j.castSucc = target at hcert
  cases hcert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      let seed : TreeSequence G e0 := ett.series.data.tree 0
      have hrouteOld : TashkinovAugmentationSequence
          (ett.series.data.coloring j.castSucc) seed Tj := by
        simpa only [seed, hjZeroIndex, hTjOne] using initialClosure.1
      have hseedStage : TreeSequenceInitialSegment seed Tj :=
        sequenceSegment hrouteOld
      have hseedLe : seed.length ≤ P.length := by
        have hseedLength : seed.length = 1 := by
          simpa only [seed] using seedLength
        rw [hseedLength, hPLength]
        exact base.supportPositive
      have hseedP : TreeSequenceInitialSegment seed P :=
        commonPrefix hseedStage hPStage hseedLe
      have hrouteOldP : TashkinovAugmentationSequence
          (ett.series.data.coloring j.castSucc) seed P :=
        TashkinovAugmentationSequenceRestrict
          (ett.series.data.coloring j.castSucc) seed P Tj
          hrouteOld hseedP hPStage
      have hrouteSigmaP : TashkinovAugmentationSequence sigma seed P :=
        transportRoute seed hrouteOldP
      have hrouteSigmaClosure : TashkinovAugmentationSequence
          sigma seed base.closure :=
        Relation.ReflTransGen.trans hrouteSigmaP hparallel.2.1.1
      have hclosureSigma : TashkinovClosure sigma seed base.closure :=
        ⟨hrouteSigmaClosure, hclosed⟩
      let zeroData : TashkinovSeriesData G k 0 e0 := {
        tree := Fin.cases seed (fun _ => base.closure)
        coloring := fun _ => sigma
        stored := fun _ => ∅
        connectingEdges := fun _ => ∅
        kind := fun _ => none
        chosenVertex := fun _ => none
        outsideVertex := fun _ => none
        delta := fun _ => none
        gamma := fun _ => none }
      have htripleSigma : KTriple G k e0 sigma :=
        ⟨triple.1, triple.2.1, triple.2.2.1, hproper, hone⟩
      let zeroSeries : TashkinovSeries G k 0 e0 sigma := {
        data := zeroData
        certified := by
          intro i
          have hi : i = 0 := Fin.eq_zero i
          subst i
          exact TashkinovSeriesStep.initial htripleSigma
            (by simpa [zeroData, seed] using seedLength)
            rfl rfl rfl rfl rfl rfl rfl rfl hclosureSigma }
      have htreeOne : zeroSeries.data.tree (1 : Fin 2) =
          base.closure := by
        rfl
      have htechnical := TechnicalTheoremBase G k 0 e0 sigma zeroSeries
      have helementary : ColoredVertexSetElementary G sigma
          (TreeSequenceVertexSet base.closure) := by
        rw [← htreeOne]
        exact htechnical.1
      have hselfStable : StableColoring base.closure
          (TashkinovStoredColors zeroSeries.data (0 : Fin 1))
          (zeroSeries.data.coloring 0) sigma := by
        have hstoredZero : TashkinovStoredColors zeroSeries.data
            (0 : Fin 1) = ∅ := by
          simp [TashkinovStoredColors]
        have hcolorZero : zeroSeries.data.coloring (0 : Fin 1) = sigma := by
          rfl
        rw [hstoredZero, hcolorZero]
        let a : {rho : PartialEdgeColoring E k //
            IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0} :=
          ⟨sigma, hproper, hone⟩
        have hrefl := (sc2 G e0 base.closure (∅ : Finset (Fin k))).refl a
        simpa [a] using hrefl
      have hinterchangeable :
    ∀ alpha beta : Fin k, (alpha ∈ TreeMissingColors sigma base.closure ∨ beta ∈ TreeMissingColors
        sigma base.closure) → TreeInterchangeable G base.closure sigma alpha beta := by
        intro alpha beta hmissing
        have h := htechnical.2 sigma hproper hone
          (by simpa [htreeOne] using hselfStable) alpha beta
          (by simpa [htreeOne] using hmissing)
        simpa [htreeOne] using h
      exact ⟨helementary, hclosed, hinterchangeable⟩
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hvals := congrArg Fin.val htarget
      simp at hvals
      omega
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
      have hvals := congrArg Fin.val htarget
      simp at hvals
      omega
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hvals := congrArg Fin.val htarget
      simp at hvals
      omega

private theorem helper_hvStage_1145.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (base :
        HierarchyBase ett sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    ∀ (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (hfirstDef : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)),
    let j : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvT - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬ETTFirstAppearanceIndex ett v hvT - (1 : ℕ) <
        ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : ETTFirstAppearanceIndex ett v hvT = (↑j : ℕ) + (1 : ℕ)),
    let Tj : TreeSequence G e0 := ett.series.data.tree j.succ.castSucc; v ∈ TreeSequenceVertexSet
        Tj := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive sigma base n q Tn v hvT candidates hqmem
      candidatesNonempty minimum hfirstDef hfirstUpper j hjFirst Tj
  rw [hfirstDef] at hjFirst
  change v ∈ TreeSequenceVertexSet
    (ett.series.data.tree j.succ.castSucc)
  have hminVal : minimum.val = j.val := by omega
  have hminEq : minimum = j.castSucc := by
    apply Fin.ext
    exact hminVal
  have hminimumMember : minimum ∈ candidates := by
    exact Finset.min'_mem candidates candidatesNonempty
  have hjMember : j.castSucc ∈ candidates := by
    rw [← hminEq]
    exact hminimumMember
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    at hjMember
  simpa [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc] using
    hjMember

private theorem helper_segmentVertexBefore_1187.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (base :
        HierarchyBase ett sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦
    by
            omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    let P : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    ∀ (_ : TreeSequenceInitialSegment Tn T) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (_ : TreeSequenceInitialSegment P T) (hvT : v ∈
        TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : q.castSucc ∈ candidates),
    let candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem;
    let minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty;
    ∀ (_ : ETTFirstAppearanceIndex ett v hvT = (↑minimum : ℕ) + (1 : ℕ)) (_ :
        ETTFirstAppearanceIndex ett v hvT ≤ (↑q : ℕ) + (1 : ℕ)) (_ : P.length =
        (↑base.supportPosition : ℕ)) {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A P)
        (_ : A.length < P.length) {x : V} (_ : x ∈ TreeSequenceVertexSet A), x ∈
        TreeVerticesBefore T v hvT := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive sigma base n q Tn v P hTnT segmentTrans
      vertexTransfer hP_T hvT candidates hqmem candidatesNonempty minimum hfirstDef hfirstUpper
      hPLength A hAP hAlen x hxA
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hxA
  obtain ⟨i, rfl⟩ := hxA
  unfold TreeVerticesBefore
  apply Finset.mem_filter.mpr
  let iP : Fin (P.length + 1) :=
    Fin.castLE (Nat.succ_le_succ hAP.1) i
  let iT : Fin (T.length + 1) :=
    Fin.castLE (Nat.succ_le_succ hP_T.1) iP
  let vT : Fin (T.length + 1) :=
    Fin.castLE (Nat.succ_le_succ hTnT.1) base.supportPosition
  refine ⟨vertexTransfer (segmentTrans hAP hP_T) (by
    simp [TreeSequenceVertexSet]), iT, vT, ?_, ?_, ?_⟩
  · exact (hP_T.2.1 iP).trans (hAP.2.1 i)
  · exact hTnT.2.1 base.supportPosition
  · change i.val < base.supportPosition.val
    rw [← hPLength]
    omega

private theorem helper_continuation_1407.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : TechnicalInductionContext G k e0 ett.rounds) (_ : MaximumProperty ett)
        (hpositive : (0 : ℕ) < ett.rounds) (_ : ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.PE) (sigma : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G
        sigma) (_ : IsOneEdgeUncolored sigma e0) (_ : StableColoring (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds)) phi sigma) (base : HierarchyBase ett sigma) (_ : ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = (Fin.last ett.rounds : Fin (ett.rounds + (1 :
        ℕ)))) (_ : ett.series.data.chosenVertex (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ)))
        = some ((ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc
        : TreeSequence G e0).vertex base.supportPosition : V) ∧ TashkinovClosure sigma
        (TreeSequencePrefix (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 :
        ℕ))).castSucc : TreeSequence G e0) (↑base.supportPosition : ℕ) base.supportPositive
        (Nat.le_of_lt_succ base.supportPosition.isLt) : TreeSequence G e0) base.closure ∧ Nonempty
        (OrderedTreeUnion (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 :
        ℕ))).castSucc : TreeSequence G e0) base.closure base.core)) (_ :
        TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds +
        (1 : ℕ))).castSucc : TreeSequence G e0) T) (_ : (
    ∀ (A : TreeSequence G e0), TreeSequenceInitialSegment A A)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (_ : (
    ∀ {A B : TreeSequence G e0} {rho : PartialEdgeColoring E k} (_ : TashkinovAugmentationSequence
        rho A B), TreeSequenceInitialSegment A B)) (_ : (
    ∀ {A B : TreeSequence G e0} {rho : PartialEdgeColoring E k} (_ : TreeSequenceInitialSegment A
        B), TreeMissingColors rho A ⊆ TreeMissingColors rho B)) (_ : TreeSequenceInitialSegment
        (TreeSequencePrefix (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 :
        ℕ))).castSucc : TreeSequence G e0) (↑base.supportPosition : ℕ) base.supportPositive
        (Nat.le_of_lt_succ base.supportPosition.isLt) : TreeSequence G e0) (ett.series.data.tree
        (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc : TreeSequence G e0)) (_ :
        TreeSequenceInitialSegment (TreeSequencePrefix (ett.series.data.tree (Fin.last ett.rounds
        : Fin (ett.rounds + (1 : ℕ))).castSucc : TreeSequence G e0) (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt) : TreeSequence G e0) T)
        (hvT : ((ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc
        : TreeSequence G e0).vertex base.supportPosition : V) ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) |
        ((ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc :
        TreeSequence G e0).vertex base.supportPosition : V) ∈ TreeSequenceVertexSet
        (ExtendedTashkinovLadderStage ett i)};
    ∀ (hqmem : ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc ∈ candidates) (_ : ETTFirstAppearanceIndex ett
        ((ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc :
        TreeSequence G e0).vertex base.supportPosition : V) hvT = (↑(candidates.min' (Exists.intro
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc hqmem : candidates.Nonempty) : Fin (ett.rounds
        + (1 : ℕ))) : ℕ) + (1 : ℕ)), ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        base.closure) ∧ ColoredVertexSetClosed G sigma (TreeSequenceVertexSet base.closure) ∧
    ∀ (alpha beta : Fin k), alpha ∈ TreeMissingColors sigma base.closure ∨ beta ∈
        TreeMissingColors sigma base.closure → TreeInterchangeable G base.closure sigma alpha beta
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hMP hpositive hPE sigma hproper hone hstable base
  set n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds
  set q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ :
                            Fin ett.rounds)
  intro hqSucc
  set Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  set v : V := Tn.vertex base.supportPosition
  set P : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
      base.supportPositive
                              (Nat.le_of_lt_succ base.supportPosition.isLt)
  intro hparallel hTnT segmentRefl segmentTrans commonPrefix vertexTransfer sequenceSegment
      missingTransfer hP_Tn hP_T hvT candidates hqmem
  set candidatesNonempty : candidates.Nonempty := Exists.intro q.castSucc hqmem
  set minimum : Fin (ett.rounds + (1 : ℕ)) := candidates.min' candidatesNonempty
  intro hfirstDef
  have hfirstPositive : 0 < ETTFirstAppearanceIndex ett v hvT := by
    rw [hfirstDef]
    omega
  have hfirstUpper : ETTFirstAppearanceIndex ett v hvT ≤ q.val + 1 := by
    rw [hfirstDef]
    have hle : minimum ≤ q.castSucc := by
      exact Finset.min'_le candidates q.castSucc hqmem
    have hnat := Fin.le_iff_val_le_val.mp hle
    simpa only [Fin.val_castSucc] using Nat.add_le_add_right hnat 1
  let j : Fin ett.rounds :=
    ⟨ETTFirstAppearanceIndex ett v hvT - 1, by omega⟩
  have hjFirst : ETTFirstAppearanceIndex ett v hvT = j.val + 1 := by
    simp only [j]
    omega
  have hjq : j.val ≤ q.val := by
    dsimp [j]
    omega
  have hkindQ : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE := by
    simpa [hqSucc, n] using hPE
  have hvertexQ : ett.series.data.chosenVertex q.succ = some v := by
    simpa [hqSucc] using hparallel.1
  have hcurrent := (ctx.currentThree ett rfl hMP).1 q v hkindQ hvertexQ
    hvT j.castSucc (by simpa using hjFirst) sigma hproper hone
    (by
      have hgenN : phi = ett.series.data.coloring n := by
        simpa [n] using ett.generatingColoring
      have hs : StableColoring Tn
          (TashkinovStoredColors ett.series.data n)
          (ett.series.data.coloring n) sigma := by
        rw [← hgenN]
        simpa [Tn, n] using hstable
      simpa [hqSucc] using hs)
  have hsigmaBefore : StableColoringBeforeVertex T v hvT
      (TashkinovStoredColors ett.series.data j.castSucc)
      (ett.series.data.coloring j.castSucc) sigma := hcurrent.1
  have stepSegment : ∀ i : Fin (ett.rounds + 1), 0 < i.val →
      TreeSequenceInitialSegment (ett.series.data.tree i.castSucc)
        (ett.series.data.tree i.succ) := by
    intro i hi
    exact ett.series.positiveStepInitialSegment i hi
  have stageToStage (first last : ℕ) (positive : 1 ≤ first)
      (ordered : first ≤ last) (bounded : last ≤ ett.rounds) :
      TreeSequenceInitialSegment
        (ett.series.data.tree
          ⟨first, lt_of_le_of_lt ordered (Nat.lt_succ_of_le (Nat.le_succ_of_le bounded))⟩)
        (ett.series.data.tree ⟨last, Nat.lt_succ_of_le (Nat.le_succ_of_le bounded)⟩) :=
    ett.series.stageInitialSegmentOfLE _ _
      (Nat.lt_of_lt_of_le Nat.zero_lt_one positive) ordered
  let Tj : TreeSequence G e0 := ett.series.data.tree j.succ.castSucc
  have hvStage := @helper_hvStage_1145 V E inferInstance inferInstance inferInstance inferInstance G
      k e0 input T phi ett hpositive sigma base hvT hqmem hfirstDef hfirstUpper hjFirst
  have hStageTn : TreeSequenceInitialSegment Tj Tn := by
    have hseg := stageToStage (j.val + 1) ett.rounds (by omega)
      (by omega) le_rfl
    change TreeSequenceInitialSegment
      (ett.series.data.tree j.succ.castSucc)
      (ett.series.data.tree n.castSucc)
    convert hseg using 1 <;> congr 1
  have hPLength : P.length = base.supportPosition.val := by
    simp [P, TreeSequencePrefix]
  have hPLeStage : P.length ≤
      Tj.length := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hvStage
    obtain ⟨i, hi⟩ := hvStage
    have hindex : Fin.castLE (Nat.succ_le_succ hStageTn.1) i =
        base.supportPosition := by
      apply Tn.vertex_injective
      exact (hStageTn.2.1 i).trans (hi.trans (by rfl))
    rw [hPLength]
    have := congrArg Fin.val hindex
    dsimp at this
    omega
  have hPStage : TreeSequenceInitialSegment P
      Tj :=
    commonPrefix hP_Tn hStageTn hPLeStage
  have segmentVertexBefore := @helper_segmentVertexBefore_1187 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 input T phi ett hpositive sigma base hTnT segmentTrans
      vertexTransfer hP_T hvT hqmem hfirstDef hfirstUpper hPLength
  have transportStep {A B : TreeSequence G e0}
      (hstep : TashkinovAugmentation (ett.series.data.coloring j.castSucc) A B)
      (hBP : TreeSequenceInitialSegment B P) : TashkinovAugmentation sigma A B :=
    TashkinovAugmentation.transportBeforeVertex T P
      (ett.series.data.coloring j.castSucc) sigma
      (TashkinovStoredColors ett.series.data j.castSucc) v hvT hsigmaBefore
      segmentVertexBefore hstep hBP
  have transportRoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence
        (ett.series.data.coloring j.castSucc) S P) :
      TashkinovAugmentationSequence sigma S P := by
    exact TashkinovAugmentationSequence.transport transportStep hroute
  have hPClosure : TreeSequenceInitialSegment P base.closure :=
    sequenceSegment hparallel.2.1.1
  have hclosed : ColoredVertexSetClosed G sigma
      (TreeSequenceVertexSet base.closure) := hparallel.2.1.2
  have hminimumVal : minimum.val = j.val := by
    rw [hfirstDef] at hjFirst
    omega
  have hvP : v ∈ TreeSequenceVertexSet P := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    let lastP : Fin (P.length + 1) := Fin.last P.length
    refine ⟨lastP, ?_⟩
    have hlastIndex : Fin.castLE (Nat.succ_le_succ hP_Tn.1) lastP =
        base.supportPosition := by
      apply Fin.ext
      simp [lastP, hPLength]
    exact (hP_Tn.2.1 lastP).symm.trans (congrArg Tn.vertex hlastIndex)
  by_cases hjPositive : 0 < j.val
  · exact @helper_branch_413 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett ctx hMP hpositive sigma hproper hone base hparallel segmentTrans
      commonPrefix vertexTransfer sequenceSegment missingTransfer hP_Tn hvT hqmem hfirstDef
      hfirstUpper hjFirst hcurrent stepSegment hStageTn hPLength hPStage transportRoute hPClosure
      hclosed hvP hjPositive
  · exact @helper_branch_742 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett hpositive sigma hproper hone base hparallel commonPrefix sequenceSegment
      hvT hqmem hfirstDef hfirstUpper hjFirst hPLength hPStage transportRoute hclosed hjPositive

theorem ParallelSupportClosureProperties {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma)
    (base : HierarchyBase ett sigma) :
    ColoredVertexSetElementary G sigma (TreeSequenceVertexSet base.closure) ∧
      ColoredVertexSetClosed G sigma (TreeSequenceVertexSet base.closure) ∧
        ∀ alpha beta : Fin k,
          (alpha ∈ TreeMissingColors sigma base.closure ∨
              beta ∈ TreeMissingColors sigma base.closure) →
            TreeInterchangeable G base.closure sigma alpha beta := by
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hqSucc : q.succ = n := by
    apply Fin.ext
    simp [q, n]
    omega
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  let v : V := Tn.vertex base.supportPosition
  let P : TreeSequence G e0 :=
    TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
      (Nat.le_of_lt_succ base.supportPosition.isLt)
  have hparallel :
      ett.series.data.chosenVertex n = some v ∧
        TashkinovClosure sigma P base.closure ∧
        Nonempty (OrderedTreeUnion Tn base.closure base.core) := by
    simpa [n, Tn, v, P] using base.parallel hPE
  have hTnT : TreeSequenceInitialSegment Tn T := by
    have hindex : n.castSucc =
        (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp [n]
    change TreeSequenceInitialSegment (ett.series.data.tree n.castSucc) T
    rw [hindex]
    exact ett.abovePenultimate
  have segmentRefl (A : TreeSequence G e0) :
      TreeSequenceInitialSegment A A :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    exact hAB.trans hBC
  have commonPrefix := @SharedFacts.ParallelSupportClosureProperties.comparableInitialSegments
      V E G e0
  have vertexTransfer {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro x hx
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hx ⊢
    obtain ⟨i, rfl⟩ := hx
    exact ⟨Fin.castLE (Nat.succ_le_succ hAB.1) i, hAB.2.1 i⟩
  have sequenceSegment {A B : TreeSequence G e0}
      {rho : PartialEdgeColoring E k}
      (hAB : TashkinovAugmentationSequence rho A B) :
      TreeSequenceInitialSegment A B := by
    exact TashkinovAugmentationSequenceInitialSegment rho A B hAB
  have missingTransfer {A B : TreeSequence G e0}
      {rho : PartialEdgeColoring E k}
      (hAB : TreeSequenceInitialSegment A B) :
      TreeMissingColors rho A ⊆ TreeMissingColors rho B := by
    intro c hc
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    obtain ⟨x, hx, hxc⟩ := hc
    exact ⟨x, vertexTransfer hAB hx, hxc⟩
  have hP_Tn : TreeSequenceInitialSegment P Tn := by
    refine ⟨Nat.le_of_lt_succ base.supportPosition.isLt, ?_, ?_⟩
    · intro i
      simp [P, TreeSequencePrefix]
    · intro i
      simp [P, TreeSequencePrefix]
  have hP_T : TreeSequenceInitialSegment P T := segmentTrans hP_Tn hTnT
  have hvTn : v ∈ TreeSequenceVertexSet Tn := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨base.supportPosition, rfl⟩
  have hvT : v ∈ TreeSequenceVertexSet T := vertexTransfer hTnT hvTn
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hqmem : q.castSucc ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold ExtendedTashkinovLadderStage
    rw [Fin.lastCases_castSucc]
    have hindex : q.succ.castSucc = n.castSucc := by
      exact congrArg Fin.castSucc hqSucc
    rw [hindex]
    exact hvTn
  let candidatesNonempty : candidates.Nonempty := ⟨q.castSucc, hqmem⟩
  let minimum : Fin (ett.rounds + 1) :=
    candidates.min' candidatesNonempty
  have hfirstDef : ETTFirstAppearanceIndex ett v hvT = minimum.val + 1 := by
    unfold ETTFirstAppearanceIndex
    dsimp
    change _ = (candidates.min' candidatesNonempty).val + 1
    congr
  exact @helper_continuation_1407 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett ctx hMP hpositive hPE sigma hproper hone hstable base hqSucc hparallel
      hTnT segmentRefl segmentTrans commonPrefix vertexTransfer sequenceSegment missingTransfer
      hP_Tn hP_T hvT hqmem hfirstDef
end GoldbergSeymour

end
