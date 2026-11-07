/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CombinedStableClosurePreserved
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.ParallelTerminalFacts
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Interchange PEClosure Constituent

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_transportRoute_255.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : (0 : ℕ) < ett.rounds) (base :
        HierarchyBase ett generating) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    let v : V := Tn.vertex base.supportPosition;
    ∀ (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hcandidates : candidates.Nonempty),
    let j : Fin (ett.rounds + (1 : ℕ)) := candidates.min' hcandidates;
    ∀ (_ : (↑j : ℕ) + (1 : ℕ) ≤ ett.rounds),
    let A : TreeSequence G e0 := ett.series.data.tree j.succ;
    ∀ (_ : TreeSequenceInitialSegment B A) (_ : StableColoringBeforeVertex T v hvT
        (TashkinovStoredColors ett.series.data j) (ett.series.data.coloring j) sigma ∧ ((0 : ℕ) <
        (↑j : ℕ) → StableColoring (ett.series.data.tree j.castSucc) (TashkinovStoredColors
        ett.series.data j) (ett.series.data.coloring j) sigma)) (_ : (
    ∀ {X : TreeSequence G e0} (_ : TreeSequenceInitialSegment X B) (_ : X.length < B.length)
        {x : V} (_ : x ∈ TreeSequenceVertexSet X), x ∈ TreeVerticesBefore T v hvT)) (S :
        TreeSequence G e0) (_ : TashkinovAugmentationSequence (ett.series.data.coloring j) S A) (_
        : TreeSequenceInitialSegment S B), TashkinovAugmentationSequence sigma S B := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hpositive base segmentTrans n Tn B v hvT
      candidates hcandidates j hjbound A hBA hbefore vertexBefore S hSA hSB
  have hroute := TashkinovAugmentationSequenceRestrict _ S B A hSA hSB hBA
  clear hSA hSB
  unfold TashkinovAugmentationSequence at hroute ⊢
  induction hroute using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head X Y hstep htail ih =>
    have hYB := TashkinovAugmentationSequenceInitialSegment _ _ _ htail
    rcases hstep with ⟨hlen, hXY, c, hcolor, hcmissing⟩
    have hXB := segmentTrans hXY hYB
    have hlt : X.length < B.length := by have := hYB.1; omega
    have beforeX : ∀ x ∈ TreeSequenceVertexSet X,
        x ∈ TreeVerticesBefore T v hvT := fun x hx => vertexBefore hXB hlt hx
    obtain ⟨x, hx, hxc⟩ := Finset.mem_biUnion.mp hcmissing
    have hcsigma : c ∈ TreeMissingColors sigma X := by
      apply Finset.mem_biUnion.mpr
      exact ⟨x, hx, (hbefore.1.2 x (beforeX x hx)) ▸ hxc⟩
    let last : Fin Y.length := Fin.cast hlen.symm (Fin.last X.length)
    obtain ⟨i, hi⟩ := Y.attaches last
    let ix : Fin (X.length + 1) := ⟨i.val, by
      have := i.isLt
      change i.val < last.val + 1 at this
      dsimp [last] at this
      omega⟩
    have hinc : Incident G (X.vertex ix) (Y.edge last) := by
      change X.vertex ix ∈ G.ends (Y.edge last)
      rw [hi]
      have heq : Y.vertex (Fin.castLT i
          (Nat.lt_trans i.isLt (Nat.succ_lt_succ last.isLt))) = X.vertex ix := by
        exact hXY.2.1 ix
      rw [heq]
      exact Sym2.mem_mk_right _ _
    have hix : X.vertex ix ∈ TreeSequenceVertexSet X := by
      simp [TreeSequenceVertexSet]
    have heq := hbefore.1.1 (Y.edge last)
      ⟨X.vertex ix, beforeX _ hix, hinc⟩
      ⟨c, Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨x, beforeX x hx, hxc⟩), hcolor⟩
    exact Relation.ReflTransGen.head
      ⟨hlen, hXY, c, heq.trans hcolor, hcsigma⟩ ih

private theorem helper_branch_368.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett) (_ : (0 : ℕ) <
        ett.rounds) (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (base : HierarchyBase
        ett generating) (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0)
        (alpha beta : Fin k) (_ : alpha ∈ TreeMissingColors sigma base.closure) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    let v : V := Tn.vertex base.supportPosition;
    ∀ (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hcandidates : candidates.Nonempty),
    let j : Fin (ett.rounds + (1 : ℕ)) := candidates.min' hcandidates;
    ∀ (hjbound : (↑j : ℕ) + (1 : ℕ) ≤ ett.rounds),
    let p : Fin ett.rounds := (⟨(↑j : ℕ), Decidable.byContradiction fun (a : ¬(↑j : ℕ) <
        ett.rounds) =>
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : p.castSucc = j),
    let A : TreeSequence G e0 := ett.series.data.tree j.succ;
    let P : TreeSequence G e0 := ett.series.data.tree j.castSucc;
    ∀ (_ : TreeSequenceInitialSegment P A) (_ : TreeSequenceInitialSegment B A) (_ :
        StableColoringBeforeVertex T v hvT (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma ∧ ((0 : ℕ) < (↑j : ℕ) → StableColoring
        (ett.series.data.tree j.castSucc) (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma)) (_ : (
    ∀ (_ : (0 : ℕ) < (↑j : ℕ)), P.length < B.length)) (S : TreeSequence G e0) (_ : ((↑j : ℕ) = (0
        : ℕ) ∧ S = ett.series.data.tree (0 : Fin (ett.rounds + (2 : ℕ))) ∧ S.length = (1 : ℕ) ∨
        ett.series.data.kind j = some TashkinovExtensionKind.PE ∧ S = ett.series.data.tree
        j.castSucc ∨ (ett.series.data.kind j = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind j = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges j = { f } ∧ TreeSequenceAdjoinEdge
        (ett.series.data.tree j.castSucc) f S)) (_ : TashkinovAugmentationSequence sigma S
        base.closure) (_ : TreeSequenceInitialSegment B base.closure) (_ : (0 : ℕ) < (↑j : ℕ)),
        TreeInterchangeable G base.closure sigma alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hMP hpositive hlower base hproper hone
      alpha beta hmissing segmentTrans commonPrefix n Tn B v hvT candidates hcandidates j hjbound
      p hpj A P hPA hBA hbefore hPBstrict S hseed hSR hBR hj
  have hjlt : j.val < ett.rounds := by omega
  obtain ⟨restricted, hr, hmax, htrees, hdata⟩ :=
    CertifiedETTRestriction G k e0 input T generating ett hMP j.val hj hjlt
  let rn : Fin (restricted.rounds + 1) := Fin.last restricted.rounds
  have hidx : Fin.castLE (by omega : restricted.rounds + 1 ≤ ett.rounds + 1) rn = j := by
    apply Fin.ext
    simpa only [rn, Fin.val_castLE, Fin.val_last] using hr
  have htidx : Fin.castLE (by omega : restricted.rounds + 2 ≤ ett.rounds + 2)
      rn.castSucc = j.castSucc := by
    apply Fin.ext
    simpa only [rn, Fin.val_castLE, Fin.val_castSucc, Fin.val_last] using hr
  have htree : restricted.series.data.tree rn.castSucc = P := by
    simpa only [htidx, P] using htrees rn.castSucc
  have hcolor : restricted.series.data.coloring rn = ett.series.data.coloring j := by
    simpa only [hidx] using (hdata rn).1
  have hstored : TashkinovStoredColors restricted.series.data rn =
      TashkinovStoredColors ett.series.data j := by
    simpa only [hidx] using (hdata rn).2.2.2.2.2.2.2.2.1
  have hkind : restricted.series.data.kind rn = ett.series.data.kind j := by
    simpa only [hidx] using (hdata rn).2.2.2.1
  have hedges : restricted.series.data.connectingEdges rn =
      ett.series.data.connectingEdges j := by
    simpa only [hidx] using (hdata rn).2.2.1
  have hmod : ModColoring restricted sigma := by
    apply Td G k e0 input _ _ restricted hmax (by omega)
      (fun lower hp hlt hmax => hlower lower hp (by omega) hmax)
      sigma hproper hone
    change StableColoring (restricted.series.data.tree rn.castSucc)
      (TashkinovStoredColors restricted.series.data rn)
      (restricted.series.data.coloring rn) sigma
    rw [htree, hstored, hcolor]
    exact hbefore.2 hj
  have hPR : TreeSequenceInitialSegment P base.closure :=
    segmentTrans (commonPrefix hPA hBA (le_of_lt (hPBstrict hj))) hBR
  have hstrict : P.length < base.closure.length :=
    lt_of_lt_of_le (hPBstrict hj) hBR.1
  have hextension :
      ((restricted.series.data.kind rn = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma
            (restricted.series.data.tree rn.castSucc) base.closure) ∨
        ((restricted.series.data.kind rn = some TashkinovExtensionKind.SE ∨
            restricted.series.data.kind rn = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            restricted.series.data.connectingEdges rn = {f} ∧
              TreeSequenceAdjoinEdge (restricted.series.data.tree rn.castSucc) f seed ∧
              TashkinovAugmentationSequence sigma seed base.closure)) := by
    rw [hkind, htree, hedges]
    rcases hseed with ⟨hjzero, _, _⟩ | ⟨hPEj, hs⟩ | ⟨hSEj, f, hf, hadjoin⟩
    · omega
    · exact Or.inl ⟨hPEj, by simpa only [hs, P] using hSR⟩
    · exact Or.inr ⟨hSEj, f, S, hf, hadjoin, hSR⟩
  obtain ⟨corr⟩ := hmod.2.2 base.closure
    (by change TreeSequenceInitialSegment (restricted.series.data.tree rn.castSucc) _
        rw [htree]
        exact hPR)
    (by change (restricted.series.data.tree rn.castSucc).length < _
        rw [htree]
        exact hstrict) hextension
  have hmaxCorr := MaximumPropertyTransport G k e0 restricted sigma hmod
    base.closure corr hmax
  have hroundCorr : corr.replacementETT.rounds < ett.rounds := by
    rw [corr.rungAgreement, hr]
    exact hjlt
  have htwo := (hlower corr.replacementETT
    (by have := corr.replacementETT.roundsPositive; omega) hroundCorr hmaxCorr).2.1
  let L := corr.replacementETT.series.data.tree
    (Fin.last (corr.replacementETT.rounds + 1))
  have hRL : TreeSequenceInitialSegment base.closure L :=
    corr.replacementETT.belowFinal
  have hmissingL : alpha ∈ TreeMissingColors sigma L := by
    obtain ⟨x, hx, hxc⟩ := Finset.mem_biUnion.mp hmissing
    exact Finset.mem_biUnion.mpr
      ⟨x, TreeSequenceInitialSegmentVertexSetSubset hRL hx, hxc⟩
  have hreflexive : StableColoring L
      (TashkinovStoredColors corr.replacementETT.series.data
        (Fin.last corr.replacementETT.rounds))
      (corr.replacementETT.series.data.coloring
        (Fin.last corr.replacementETT.rounds)) sigma := by
    rw [← corr.replacementETT.generatingColoring]
    exact ⟨(by intro f hf hc; rfl), (by intro x hx; rfl)⟩
  have hinterchange := htwo sigma hproper hone hreflexive alpha beta (Or.inl hmissingL)
  intro z w hz hw hzR hwR
  obtain ⟨x, hx, hxz⟩ := hzR
  obtain ⟨y, hy, hyw⟩ := hwR
  exact hinterchange z w hz hw
    ⟨x, TreeSequenceInitialSegmentVertexSetSubset hRL hx, hxz⟩
    ⟨y, TreeSequenceInitialSegmentVertexSetSubset hRL hy, hyw⟩

private theorem helper_branch_455.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : (0 : ℕ) < ett.rounds) (base :
        HierarchyBase ett generating) (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored
        sigma e0) (alpha beta : Fin k) (_ : alpha ∈ TreeMissingColors sigma base.closure),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    let v : V := Tn.vertex base.supportPosition;
    ∀ (_ : v ∈ TreeSequenceVertexSet T) (_ : TashkinovClosure sigma B base.closure),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hcandidates : candidates.Nonempty),
    let j : Fin (ett.rounds + (1 : ℕ)) := candidates.min' hcandidates;
    ∀ (hjbound : (↑j : ℕ) + (1 : ℕ) ≤ ett.rounds),
    let p : Fin ett.rounds := (⟨(↑j : ℕ), Decidable.byContradiction fun (a : ¬(↑j : ℕ) <
        ett.rounds) =>
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : p.castSucc = j) (S : TreeSequence G e0) (_ : ((↑j : ℕ) = (0 : ℕ) ∧ S =
        ett.series.data.tree (0 : Fin (ett.rounds + (2 : ℕ))) ∧ S.length = (1 : ℕ) ∨
        ett.series.data.kind j = some TashkinovExtensionKind.PE ∧ S = ett.series.data.tree
        j.castSucc ∨ (ett.series.data.kind j = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind j = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges j = { f } ∧ TreeSequenceAdjoinEdge
        (ett.series.data.tree j.castSucc) f S)) (_ : TashkinovAugmentationSequence sigma S
        base.closure) (_ : ¬(0 : ℕ) < (↑j : ℕ)), TreeInterchangeable G base.closure sigma alpha
        beta := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hpositive base hproper hone alpha beta
      hmissing n Tn B v hvT hclosure candidates hcandidates j hjbound p hpj S hseed hSR hj
  have hjzero : j = 0 := by apply Fin.ext; change j.val = 0; omega
  have hkindzero : ett.series.data.kind 0 = none := by
    cases ett.series.certified 0 with
    | initial => assumption
  have hs : S = ett.series.data.tree 0 := by
    rcases hseed with ⟨_, hs, _⟩ | ⟨hkind, _⟩ | ⟨hkind, _⟩
    · exact hs
    · rw [hjzero, hkindzero] at hkind
      cases hkind
    · rw [hjzero, hkindzero] at hkind
      rcases hkind with hkind | hkind <;> cases hkind
  have hseedLength : (ett.series.data.tree 0).length = 1 := by
    cases ett.series.certified 0 with
    | initial => assumption
  have htriple : KTriple G k e0 sigma := by
    have hinput : KTriple G k e0 input := by
      cases ett.series.certified 0 with
      | initial => assumption
    exact ⟨hinput.1, hinput.2.1, hinput.2.2.1, hproper, hone⟩
  -- First appearance in T1 uses an actual zero-round series, not a zero-rung ETT.
  let data0 : TashkinovSeriesData G k 0 e0 :=
    { tree := fun i => if i.val = 0 then ett.series.data.tree 0 else base.closure
      coloring := fun _ => sigma
      stored := fun _ => ∅
      connectingEdges := fun _ => ∅
      kind := fun _ => none
      chosenVertex := fun _ => none
      outsideVertex := fun _ => none
      delta := fun _ => none
      gamma := fun _ => none }
  have hclosure0 : TashkinovClosure sigma (ett.series.data.tree 0) base.closure :=
    ⟨hs ▸ hSR, hclosure.2⟩
  let series0 : TashkinovSeries G k 0 e0 sigma :=
    { data := data0
      certified := by
        intro i
        have hi : i = 0 := by
          apply Fin.ext
          have := i.isLt
          change i.val = 0
          omega
        subst i
        apply TashkinovSeriesStep.initial
        · exact htriple
        · exact hseedLength
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact hclosure0 }
  have htwo := (TechnicalTheoremBase G k 0 e0 sigma series0).2
  have hreflexive : StableColoring (series0.data.tree ⟨1, by omega⟩)
      (TashkinovStoredColors series0.data 0) (series0.data.coloring 0) sigma :=
    ⟨(by intro f hf hc; rfl), (by intro x hx; rfl)⟩
  exact htwo sigma hproper hone hreflexive alpha beta (Or.inl hmissing)

private theorem helper_seedData_592.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (t : Fin (ett.rounds + (1 : ℕ))),
    ∃ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring t) S
        (ett.series.data.tree t.succ) ∧ ((↑t : ℕ) = (0 : ℕ) ∧ S = ett.series.data.tree (0 : Fin
        (ett.rounds + (2 : ℕ))) ∧ S.length = (1 : ℕ) ∨ ett.series.data.kind t = some
        TashkinovExtensionKind.PE ∧ S = ett.series.data.tree t.castSucc ∨ (ett.series.data.kind t
        = some TashkinovExtensionKind.SE ∨ ett.series.data.kind t = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges t = { f } ∧ TreeSequenceAdjoinEdge
        (ett.series.data.tree t.castSucc) f S) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett t
  cases ett.series.certified t with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact ⟨_, initialClosure.1, Or.inl ⟨rfl, rfl, seedLength⟩⟩
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    exact ⟨adjoined, closedExtension.1,
      Or.inr (Or.inr ⟨Or.inl currentKind, choice.edge, currentEdges, adjoinedExactly⟩)⟩
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    exact ⟨_, closedExtension.1, Or.inr (Or.inl ⟨currentKind, rfl⟩)⟩
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    exact ⟨adjoined, closedExtension.1,
      Or.inr (Or.inr ⟨Or.inr currentKind, available.edge, currentEdges, adjoinedExactly⟩)⟩

private theorem helper_hSlen_631.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : (0 : ℕ) < ett.rounds) (base : HierarchyBase ett generating),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    let v : V := Tn.vertex base.supportPosition;
    ∀ (_ : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := {i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)};
    ∀ (hcandidates : candidates.Nonempty),
    let j : Fin (ett.rounds + (1 : ℕ)) := candidates.min' hcandidates;
    ∀ (hjbound : (↑j : ℕ) + (1 : ℕ) ≤ ett.rounds),
    let p : Fin ett.rounds := (⟨(↑j : ℕ), Decidable.byContradiction fun (a : ¬(↑j : ℕ) <
        ett.rounds) =>
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : p.castSucc = j),
    let P : TreeSequence G e0 := ett.series.data.tree j.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑j : ℕ)), P.length < B.length)) (S : TreeSequence G e0) (_ : ((↑j : ℕ) = (0
        : ℕ) ∧ S = ett.series.data.tree (0 : Fin (ett.rounds + (2 : ℕ))) ∧ S.length = (1 : ℕ) ∨
        ett.series.data.kind j = some TashkinovExtensionKind.PE ∧ S = ett.series.data.tree
        j.castSucc ∨ (ett.series.data.kind j = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind j = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges j = { f } ∧ TreeSequenceAdjoinEdge
        (ett.series.data.tree j.castSucc) f S)), S.length ≤ B.length := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive base n Tn B v hvT candidates
      hcandidates j hjbound p hpj P hPBstrict S hseed
  rcases hseed with ⟨hj, hs, hlen⟩ | ⟨hkind, hs⟩ | ⟨hkind, f, hf, hadjoin⟩
  · rw [hlen]
    exact B.positive
  · rw [hs]
    by_cases hj : 0 < j.val
    · exact le_of_lt (hPBstrict hj)
    · have hjzero : j = 0 := by apply Fin.ext; change j.val = 0; omega
      have hkindzero : ett.series.data.kind 0 = none := by
        cases ett.series.certified 0 with
        | initial => assumption
      rw [hjzero, hkindzero] at hkind
      cases hkind
  · obtain ⟨hlen, _, _⟩ := hadjoin
    have hj : 0 < j.val := by
      by_contra hn
      have hjzero : j = 0 := by apply Fin.ext; change j.val = 0; omega
      have hkindzero : ett.series.data.kind 0 = none := by
        cases ett.series.certified 0 with
        | initial => assumption
      rw [hjzero, hkindzero] at hkind
      rcases hkind with hkind | hkind <;> cases hkind
    have hstrict := hPBstrict hj
    dsimp [P] at hstrict
    omega

private theorem helper_segmentTrans_553.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B
        C → TreeSequenceInitialSegment A C := by
  classical
  intro V E G e0 A B C hAB hBC
  refine ⟨hAB.1.trans hBC.1, ?_, ?_⟩
  · intro i
    exact (hBC.2.1 (Fin.castLE (Nat.succ_le_succ hAB.1) i)).trans
      (hAB.2.1 i)
  · intro i
    exact (hBC.2.2 (Fin.castLE hAB.1 i)).trans (hAB.2.2 i)

private theorem helper_commonPrefix_563.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B
        C → A.length ≤ B.length → TreeSequenceInitialSegment A B := by
  classical
  intro V E G e0 A B C hAC hBC hlen
  refine ⟨hlen, ?_, ?_⟩
  · intro i
    exact (hBC.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans
      (hAC.2.1 i)
  · intro i
    exact (hBC.2.2 (Fin.castLE hlen i)).symm.trans (hAC.2.2 i)

private theorem helper_stepSegment_573.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (i : Fin (ett.rounds + (1 : ℕ))), TreeSequenceInitialSegment
        (ett.series.data.tree i.castSucc) (ett.series.data.tree i.succ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett i
  cases ett.series.certified i with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact TashkinovAugmentationSequenceInitialSegment _ _ _ initialClosure.1
  | SE => assumption
  | PE => assumption
  | RE => assumption

private theorem helper_stageSegment_584.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : HierarchyBase ett generating), (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) → (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), TreeSequenceInitialSegment (ett.series.data.tree
        i.castSucc) (ett.series.data.tree i.succ)) →
    ∀ (a b : ℕ) (hab : a ≤ b) (hb : b ≤ ett.rounds + (1 : ℕ)), TreeSequenceInitialSegment
        (ett.series.data.tree (⟨a,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett base segmentTrans stepSegment a b hab hb
  induction b, hab using Nat.le_induction with
  | base => exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
  | succ b hab ih =>
    have hprev := ih (by omega)
    have hstep := stepSegment ⟨b, by omega⟩
    exact segmentTrans hprev hstep

private theorem helper_hfirst_628.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (base : HierarchyBase ett generating),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    ∀ (hvT : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := ({i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)} : Finset (Fin (ett.rounds + (1
        : ℕ))));
    ∀ (hcandidates : candidates.Nonempty),
    let j : Fin (ett.rounds + (1 : ℕ)) := candidates.min' hcandidates; ETTFirstAppearanceIndex ett
        v hvT = (↑j : ℕ) + (1 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett base n Tn v hvT candidates hcandidates j
  unfold ETTFirstAppearanceIndex
  dsimp
  apply congrArg (fun i : Fin (ett.rounds + 1) => i.val + 1)
  apply (Finset.min'_eq_iff _ _ j).mpr
  constructor
  · have hmem := Finset.min'_mem candidates hcandidates
    change j ∈ candidates at hmem
    simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  · intro b hb
    exact Finset.min'_le candidates b (by
      simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using hb)

private theorem helper_hjbound_645.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds), ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.PE →
    ∀ (base : HierarchyBase ett generating),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    ∀ (hvT : v ∈ TreeSequenceVertexSet T), ett.series.data.chosenVertex n = some v →
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := ({i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)} : Finset (Fin (ett.rounds + (1
        : ℕ))));
    ∀ (hcandidates : candidates.Nonempty),
    let j : Fin (ett.rounds + (1 : ℕ)) := candidates.min' hcandidates; ETTFirstAppearanceIndex ett
        v hvT = (↑j : ℕ) + (1 : ℕ) →
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); q.succ = n → (↑j : ℕ) + (1 : ℕ) ≤ ett.rounds := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive hPE base n Tn v hvT hchosen
      candidates hcandidates j hfirst q hq
  have hbound := ExtensionRulesPEFirstAppearanceBound G k e0 input T
    generating ett q v (by simpa [hq] using hPE)
    (by simpa [hq] using hchosen) hvT
  rw [hfirst] at hbound
  dsimp [q] at hbound
  omega

private theorem helper_hvA_656.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : (0 : ℕ) < ett.rounds) (base : HierarchyBase ett generating),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    ∀ (_ : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := ({i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)} : Finset (Fin (ett.rounds + (1
        : ℕ))));
    ∀ (hcandidates : candidates.Nonempty),
    let j : Fin (ett.rounds + (1 : ℕ)) := candidates.min' hcandidates;
    ∀ (hjbound : (↑j : ℕ) + (1 : ℕ) ≤ ett.rounds),
    let p : Fin ett.rounds := (⟨(↑j : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive Tn
          omega
    ⟩ : Fin ett.rounds); p.castSucc = j →
    let A : TreeSequence G e0 := ett.series.data.tree j.succ; v ∈ TreeSequenceVertexSet A := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive base n Tn v hvT candidates
      hcandidates j hjbound p hpj A
  have hmem := Finset.min'_mem candidates hcandidates
  have hvstage : v ∈ TreeSequenceVertexSet
      (ExtendedTashkinovLadderStage ett j) := (Finset.mem_filter.mp hmem).2
  rw [← hpj, ExtendedTashkinovLadderStage, Fin.lastCases_castSucc] at hvstage
  have hidx : p.succ.castSucc = j.succ := by apply Fin.ext; rfl
  simpa only [hidx, A] using hvstage

private theorem helper_hvNotP_682.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : (0 : ℕ) < ett.rounds) (base : HierarchyBase ett generating),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let v : V := Tn.vertex base.supportPosition;
    ∀ (_ : v ∈ TreeSequenceVertexSet T),
    let candidates : Finset (Fin (ett.rounds + (1 : ℕ))) := ({i : Fin (ett.rounds + (1 : ℕ)) | v ∈
        TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)} : Finset (Fin (ett.rounds + (1
        : ℕ))));
    ∀ (hcandidates : candidates.Nonempty),
    let j : Fin (ett.rounds + (1 : ℕ)) := candidates.min' hcandidates;
    ∀ (hjbound : (↑j : ℕ) + (1 : ℕ) ≤ ett.rounds),
    let p : Fin ett.rounds := (⟨(↑j : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive Tn
          omega
    ⟩ : Fin ett.rounds); p.castSucc = j →
    let P : TreeSequence G e0 := ett.series.data.tree j.castSucc; (0 : ℕ) < (↑j : ℕ) → v ∉
        TreeSequenceVertexSet P := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive base n Tn v hvT candidates
      hcandidates j hjbound p hpj P hj hvP
  let u : Fin ett.rounds := ⟨j.val - 1, by omega⟩
  have huj : u.succ = j := by apply Fin.ext; dsimp [u]; omega
  have huMem : u.castSucc ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc, huj]
    exact hvP
  have hle := Finset.min'_le candidates u.castSucc huMem
  change j ≤ u.castSucc at hle
  have := Fin.le_iff_val_le_val.mp hle
  dsimp [u] at this
  omega

theorem InterchangePEClosureConstituent {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett generating)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      generating sigma)
    (alpha beta : Fin k) :
    alpha ∈ TreeMissingColors sigma base.closure →
      TreeInterchangeable G base.closure sigma alpha beta := by
  classical
  intro hmissing
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    exact @helper_segmentTrans_553 (@V) (@E) (@G) (@e0) (@A) (@B) (@C) (@hAB) (@hBC)
  have commonPrefix {A B C : TreeSequence G e0}
      (hAC : TreeSequenceInitialSegment A C)
      (hBC : TreeSequenceInitialSegment B C) (hlen : A.length ≤ B.length) :
      TreeSequenceInitialSegment A B := by
    exact @helper_commonPrefix_563 (@V) (@E) (@G) (@e0) (@A) (@B) (@C) (@hAC) (@hBC) (@hlen)
  have stepSegment (i : Fin (ett.rounds + 1)) :
      TreeSequenceInitialSegment (ett.series.data.tree i.castSucc)
        (ett.series.data.tree i.succ) := by
    exact @helper_stepSegment_573 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@i)
  have stageSegment (a b : ℕ) (hab : a ≤ b) (hb : b ≤ ett.rounds + 1) :
      TreeSequenceInitialSegment
        (ett.series.data.tree ⟨a, by omega⟩)
        (ett.series.data.tree ⟨b, by omega⟩) := by
    exact @helper_stageSegment_584 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@base) (@segmentTrans)
        (@stepSegment) (@a) (@b) (@hab) (@hb)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let B := TreeSequencePrefix Tn base.supportPosition.val
    base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)
  let v := Tn.vertex base.supportPosition
  have hBTn : TreeSequenceInitialSegment B Tn :=
    ⟨Nat.le_of_lt_succ base.supportPosition.isLt,
      (fun _ => rfl), (fun _ => rfl)⟩
  have hTnT : TreeSequenceInitialSegment Tn T := ett.abovePenultimate
  have hBT := segmentTrans hBTn hTnT
  have hvTn : v ∈ TreeSequenceVertexSet Tn := by
    simp [v, TreeSequenceVertexSet]
  have hvT : v ∈ TreeSequenceVertexSet T :=
    TreeSequenceInitialSegmentVertexSetSubset hTnT hvTn
  have hvB : B.vertex (Fin.last B.length) = v := by
    dsimp [B, TreeSequencePrefix, v]
    congr 1
  have hchosen : ett.series.data.chosenVertex n = some v :=
    (base.parallel hPE).1
  obtain ⟨hproperGen, honeGen, _⟩ := P2634_T1_PETerminalFacts ett hPE
  have hclosure : TashkinovClosure sigma B base.closure :=
    (CombinedStableClosurePreserved G k e0 input T generating generating sigma
      ett hpositive base ett.generatingColoring hPE hproperGen honeGen
      hproper hone hstable).2.2
  -- The zero-based index j corresponds to first appearance in stage j + 1.
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hcandidates : candidates.Nonempty := by
    refine ⟨Fin.last ett.rounds, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ExtendedTashkinovLadderStage, Fin.lastCases_last]
    exact hvT
  let j := candidates.min' hcandidates
  have hfirst : ETTFirstAppearanceIndex ett v hvT = j.val + 1 := by
    exact @helper_hfirst_628 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@base) (@hvT) (@hcandidates)
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hq : q.succ = n := by
    apply Fin.ext
    dsimp [q, n]
    omega
  have hjbound : j.val + 1 ≤ ett.rounds := by
    exact @helper_hjbound_645 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@hPE) (@base) (@hvT)
        (@hchosen) (@hcandidates) (@hfirst) (@hq)
  let p : Fin ett.rounds := ⟨j.val, by omega⟩
  have hpj : p.castSucc = j := by apply Fin.ext; rfl
  let A := ett.series.data.tree j.succ
  let P := ett.series.data.tree j.castSucc
  have hvA : v ∈ TreeSequenceVertexSet A := by
    exact @helper_hvA_656 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@base) (@hvT) (@hcandidates)
        (@hjbound) (@hpj)
  have hATn : TreeSequenceInitialSegment A Tn :=
    stageSegment (j.val + 1) ett.rounds hjbound (by omega)
  have hPA : TreeSequenceInitialSegment P A := stepSegment j
  have hBA : TreeSequenceInitialSegment B A := by
    obtain ⟨iv, hiv⟩ := (show ∃ iv, A.vertex iv = v from by
      simpa [TreeSequenceVertexSet] using hvA)
    have hivEq : Fin.castLE (Nat.succ_le_succ hATn.1) iv =
        base.supportPosition :=
      Tn.vertex_injective ((hATn.2.1 iv).trans hiv)
    have hlen : B.length ≤ A.length := by
      have := congrArg Fin.val hivEq
      dsimp [B, TreeSequencePrefix] at ⊢
      simp only [Fin.val_castLE] at this
      omega
    exact commonPrefix hBTn hATn hlen
  have hbefore := (ExtensionRules G k e0 input T generating ett hMP hpositive
    (fun lower hp hlt hmax => hlower lower hp hlt hmax)).1 q v
      (by simpa [hq] using hPE) (by simpa [hq] using hchosen) hvT j hfirst
      sigma hproper hone (by simpa only [hq, n, ← ett.generatingColoring] using hstable.1)
  have hvNotP (hj : 0 < j.val) : v ∉ TreeSequenceVertexSet P := by
    exact @helper_hvNotP_682 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@base) (@hvT)
        (@hcandidates) (@hjbound) (@hpj) (@hj)
  have hPBstrict (hj : 0 < j.val) : P.length < B.length := by
    by_contra hnot
    have hBP := commonPrefix hBA hPA (by omega)
    apply hvNotP hj
    apply TreeSequenceInitialSegmentVertexSetSubset hBP
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last B.length, hvB⟩
  have vertexBefore {X : TreeSequence G e0}
      (hXB : TreeSequenceInitialSegment X B) (hlen : X.length < B.length)
      {x : V} (hx : x ∈ TreeSequenceVertexSet X) :
      x ∈ TreeVerticesBefore T v hvT := by
    obtain ⟨ix, hix⟩ := (show ∃ ix, X.vertex ix = x from by
      simpa [TreeSequenceVertexSet] using hx)
    have hXT := segmentTrans hXB hBT
    refine Finset.mem_filter.mpr
      ⟨TreeSequenceInitialSegmentVertexSetSubset hXT hx, ?_⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hXT.1) ix,
      Fin.castLE (Nat.succ_le_succ hBT.1) (Fin.last B.length),
      (hXT.2.1 ix).trans hix, (hBT.2.1 _).trans hvB, ?_⟩
    simp only [Fin.val_castLE, Fin.val_last]
    omega
  -- This transports the step adjoining the support as well as all earlier steps.
  have transportRoute (S : TreeSequence G e0)
      (hSA : TashkinovAugmentationSequence (ett.series.data.coloring j) S A)
      (hSB : TreeSequenceInitialSegment S B) :
      TashkinovAugmentationSequence sigma S B := by
    exact @helper_transportRoute_255 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 input T generating sigma ett hpositive base segmentTrans hvT hcandidates hjbound
        hBA hbefore vertexBefore S hSA hSB
  have seedData (t : Fin (ett.rounds + 1)) :
      ∃ S : TreeSequence G e0,
        TashkinovAugmentationSequence (ett.series.data.coloring t) S
          (ett.series.data.tree t.succ) ∧
        ((t.val = 0 ∧ S = ett.series.data.tree 0 ∧ S.length = 1) ∨
          (ett.series.data.kind t = some TashkinovExtensionKind.PE ∧
            S = ett.series.data.tree t.castSucc) ∨
          ((ett.series.data.kind t = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind t = some TashkinovExtensionKind.RE) ∧
            ∃ f : E, ett.series.data.connectingEdges t = {f} ∧
              TreeSequenceAdjoinEdge (ett.series.data.tree t.castSucc) f S)) := by
    exact @helper_seedData_592 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett t
  obtain ⟨S, hSA, hseed⟩ := seedData j
  have hSlen : S.length ≤ B.length := by
    exact @helper_hSlen_631 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T generating ett hpositive base hvT hcandidates hjbound hpj hPBstrict S hseed
  have hSB : TreeSequenceInitialSegment S B :=
    commonPrefix (TashkinovAugmentationSequenceInitialSegment _ _ _ hSA) hBA hSlen
  have hSR : TashkinovAugmentationSequence sigma S base.closure :=
    (transportRoute S hSA hSB).trans hclosure.1
  have hBR := TashkinovAugmentationSequenceInitialSegment _ _ _ hclosure.1
  by_cases hj : 0 < j.val
  · exact @helper_branch_368 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating sigma ett hMP hpositive hlower base hproper hone alpha beta hmissing
      segmentTrans commonPrefix hvT hcandidates hjbound hpj hPA hBA hbefore hPBstrict S hseed hSR
      hBR hj
  · exact @helper_branch_455 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating sigma ett hpositive base hproper hone alpha beta hmissing hvT hclosure
      hcandidates hjbound hpj S hseed hSR hj
end GoldbergSeymour

end
