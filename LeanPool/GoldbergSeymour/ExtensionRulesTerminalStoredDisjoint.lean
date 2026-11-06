/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseStepLemmas

public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex
public import LeanPool.GoldbergSeymour.EarlierPECycleFirstNonrevisitingInternal
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.ExtensionRulesPEFirstAppearanceBound
public import LeanPool.GoldbergSeymour.HkuParallelBoundaryStructure
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.SameColorSeriesPreserved
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TwoColorInterchangeableDistinctComponentCycle

/-!
# Extension Rules Terminal Stored Disjoint

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation1661Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett → (0 : ℕ) < ett.rounds → (
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating'), (0 : ℕ) < lower.rounds → lower.rounds
        < ett.rounds → MaximumProperty lower →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (lower.series.data.tree (Fin.last (lower.rounds + (1 : ℕ))))
        (TashkinovStoredColors lower.series.data (Fin.last lower.rounds))
        (lower.series.data.coloring (Fin.last lower.rounds)) sigma →
    ∀ (alpha beta : Fin k), alpha ∈ TreeMissingColors sigma (lower.series.data.tree (Fin.last
        (lower.rounds + (1 : ℕ)))) ∨ beta ∈ TreeMissingColors sigma (lower.series.data.tree
        (Fin.last (lower.rounds + (1 : ℕ)))) → TreeInterchangeable G (lower.series.data.tree
        (Fin.last (lower.rounds + (1 : ℕ)))) sigma alpha beta) →
    ∀ (r : Fin ett.rounds), r.succ ≠ Fin.last ett.rounds → ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.PE → ett.series.data.kind r.succ = some
        TashkinovExtensionKind.PE → (
    ∀ (r p : Fin ett.rounds), (↑r : ℕ) < (↑p : ℕ) → TreeMissingColors (ett.series.data.coloring
        r.succ) (ett.series.data.tree r.succ.succ) ∪ TashkinovStoredColors ett.series.data r.succ
        ⊆ TreeMissingColors (ett.series.data.coloring p.castSucc) (ett.series.data.tree
        p.succ.castSucc) ∪ TashkinovStoredColors ett.series.data p.castSucc) →
    ∀ (gammaR : Fin k) (secondStableR : PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice
        G e0 (ett.series.data.tree r.succ.castSucc) (TashkinovStoredColors ett.series.data
        r.castSucc) (ett.series.data.coloring r.castSucc)), ett.series.data.coloring r.succ =
        TwoColorComponentSwap G secondStableR gammaR choiceR.color (Sum.inl choiceR.vertex) →
        IsProperEdgeColoring G (ett.series.data.coloring r.succ) → IsOneEdgeUncolored
        (ett.series.data.coloring r.succ) e0 → ett.series.data.stored r.succ = (insert
        choiceR.color ({ gammaR } : Finset (Fin k)) : Finset (Fin k)) → ett.series.data.delta
        r.succ = some choiceR.color → ett.series.data.gamma r.succ = some gammaR →
        TreeSequenceInitialSegment (ett.series.data.tree r.succ.castSucc) (ett.series.data.tree
        r.succ.succ) → r.succ = r.succ →
    ∀ (hvr : choiceR.vertex ∈ TreeSequenceVertexSet T), (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (hab : a ≤ b) (hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by
                             have := GoldbergSeymour.TreeSequence.positive T
                             omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by
                             have := GoldbergSeymour.TreeSequence.positive T
                             omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) →
    ∀ (q : Fin ett.rounds) (choiceN : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (gammaN : Fin k), ParallelExtensionColor
        ett.series.data q.castSucc choiceN.selected choiceN.vertex gammaN →
    ∀ (secondStableN : PartialEdgeColoring E k), StableColoring (ett.series.data.tree
        q.succ.castSucc) (insert choiceN.color (TashkinovStoredColors ett.series.data q.castSucc)
        : Finset (Fin k)) choiceN.selected secondStableN → ett.series.data.coloring q.succ =
        TwoColorComponentSwap G secondStableN gammaN choiceN.color (Sum.inl choiceN.vertex) →
        IsProperEdgeColoring G (ett.series.data.coloring q.succ) → ett.series.data.stored q.succ =
        (insert choiceN.color ({ gammaN } : Finset (Fin k)) : Finset (Fin k)) →
        ett.series.data.connectingEdges q.succ = ({ choiceN.edge } : Finset E) →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some choiceN.vertex → ett.series.data.delta q.succ =
        some choiceN.color → ett.series.data.gamma q.succ = some gammaN →
    ∀ (hvn : choiceN.vertex ∈ TreeSequenceVertexSet T), ETTFirstAppearanceIndex ett choiceN.vertex
        hvn = ETTFirstAppearanceIndex ett choiceR.vertex hvr → q.succ = Fin.last ett.rounds → (↑r
        : ℕ) + (1 : ℕ) < ett.rounds →
    let _ : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc;
    let _ : TreeSequence G e0 := ett.series.data.tree r.succ.succ; (
    have Th : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc; choiceN.vertex ∈
        TreeSequenceVertexSet Th) → gammaR ∈ MissingColors G secondStableR choiceR.vertex → gammaR
        ≠ choiceR.color →
    ∀ (f : E), Incident G choiceN.vertex f → secondStableR f = some gammaR →
    ∀ (g : E), Incident G choiceN.vertex g → secondStableR g = some choiceR.color →
        TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl choiceR.vertex) ≠
        TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl choiceN.vertex) →
        TwoColorPathComponent G secondStableR gammaR choiceR.color (Sum.inl choiceR.vertex) →
        TwoColorIncidenceGraph G (ett.series.data.coloring r.succ) gammaR choiceR.color =
        TwoColorIncidenceGraph G secondStableR gammaR choiceR.color → Disjoint
        (ett.series.data.stored q.succ) (ett.series.data.stored r.succ)

private theorem helper_stageToStage_128.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (vn vr : V) (_ : vn ∈ TreeSequenceVertexSet T) (_ : vr ∈
        TreeSequenceVertexSet T), (
    ∀ (A : TreeSequence G e0), TreeSequenceInitialSegment A A) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) → (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (0 : ℕ) < (↑i : ℕ) → TreeSequenceInitialSegment
        (ett.series.data.tree i.castSucc) (ett.series.data.tree i.succ)) →
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (hab : a ≤ b) (hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett vn vr hvn hvr segmentRefl segmentTrans
      stepSegment a b ha hab hb
  have chain (d : ℕ) (hd : a + d ≤ b) :
      TreeSequenceInitialSegment
        (ett.series.data.tree ⟨a, by omega⟩)
        (ett.series.data.tree ⟨a + d, by omega⟩) := by
    induction d with
    | zero => simpa using segmentRefl (ett.series.data.tree ⟨a, by omega⟩)
    | succ d ih =>
        have hprev := ih (by omega)
        let idx : Fin (ett.rounds + 1) := ⟨a + d, by omega⟩
        have hnext := stepSegment idx (by dsimp [idx]; omega)
        have hnext' : TreeSequenceInitialSegment
            (ett.series.data.tree ⟨a + d, by omega⟩)
            (ett.series.data.tree ⟨a + (d + 1), by omega⟩) := by
          simpa [idx, Nat.add_assoc] using hnext
        exact segmentTrans hprev hnext'
  have hchain := chain (b - a) (by omega)
  convert hchain using 1; apply congrArg ett.series.data.tree;
    apply Fin.ext; simp; omega

private theorem helper_controlCarry_158.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (vn vr : V) (hvn : vn ∈ TreeSequenceVertexSet T) (hvr : vr ∈
        TreeSequenceVertexSet T), ETTFirstAppearanceIndex ett vn hvn = ETTFirstAppearanceIndex ett
        vr hvr →
    ∀ (r p : Fin ett.rounds), (↑r : ℕ) < (↑p : ℕ) → TreeMissingColors (ett.series.data.coloring
        r.succ) (ett.series.data.tree r.succ.succ) ∪ TashkinovStoredColors ett.series.data r.succ
        ⊆ TreeMissingColors (ett.series.data.coloring p.castSucc) (ett.series.data.tree
        p.succ.castSucc) ∪ TashkinovStoredColors ett.series.data p.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett vn vr hvn hvr hfirst r p hrp
  have carryNat :
    ∀ n : ℕ, r.val + 1 ≤ n → n < ett.rounds →
    ∀ q : Fin ett.rounds, q.val = n → TreeMissingColors (ett.series.data.coloring r.succ)
        (ett.series.data.tree r.succ.succ) ∪ TashkinovStoredColors ett.series.data r.succ ⊆
        TreeMissingColors (ett.series.data.coloring q.castSucc) (ett.series.data.tree
        q.succ.castSucc) ∪ TashkinovStoredColors ett.series.data q.castSucc := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        intro hnround q hq
        have hqeq : q.castSucc = r.succ := by
          apply Fin.ext
          simp only [Fin.val_castSucc, Fin.val_succ]
          omega
        have htree : q.succ.castSucc = r.succ.succ := by
          apply Fin.ext
          simp only [Fin.val_castSucc, Fin.val_succ]
          omega
        simp [hqeq, htree]
    | succ n hn ih =>
        intro hnround q hq
        let prev : Fin ett.rounds := ⟨n, by omega⟩
        have hold := ih (by omega) prev rfl
        have hfirst := (HkuMissingStoredMonotone G k ett.rounds e0 input
          ett.series prev).1
        have hsecond := (HkuMissingStoredMonotone G k ett.rounds e0 input
          ett.series prev).2
        intro c hc
        have hc1 := hold hc
        have hc2 := hfirst hc1
        have hc3 := hsecond hc2
        have hcolor : q.castSucc = prev.succ := by apply Fin.ext; simp [prev]; omega
        have htree : q.succ.castSucc = prev.succ.succ := by
          apply Fin.ext
          simp [prev]
          omega
        simpa [hcolor, htree] using hc3
  exact carryNat p.val (by omega) p.isLt p rfl

private theorem helper_hrBefore_273.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (r : Fin ett.rounds),
    r.succ ≠ Fin.last ett.rounds →
    (↑r : ℕ) + (1 : ℕ) < ett.rounds := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r hrEarlier
  have hle : r.succ.val ≤ (Fin.last ett.rounds).val :=
    Fin.le_last r.succ
  have hne : r.succ.val ≠ (Fin.last ett.rounds).val := by
    intro heq
    exact hrEarlier (Fin.ext heq)
  simpa using lt_of_le_of_ne hle hne

private theorem helper_hvnTh_282.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds), ett.series.data.kind r.succ = some
        TashkinovExtensionKind.PE →
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree r.succ.castSucc)
        (TashkinovStoredColors ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)),
        r.succ = r.succ → ett.series.data.chosenVertex r.succ = some choiceR.vertex →
    ∀ (hvr : choiceR.vertex ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds) (choiceN :
        MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)) (hvn : choiceN.vertex ∈
        TreeSequenceVertexSet T), ETTFirstAppearanceIndex ett choiceN.vertex hvn =
        ETTFirstAppearanceIndex ett choiceR.vertex hvr → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (hab : a ≤ b) (hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) → (↑r : ℕ) + (1 : ℕ) < ett.rounds →
    let Th : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc; choiceN.vertex ∈
        TreeSequenceVertexSet Th := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r hkindr this choiceR hrTarget hvertexr hvr q
      choiceN hvn hfirst stageToStage hrBefore Th
  have hboundR := ExtensionRulesPEFirstAppearanceBound G k e0 input T
    generating ett r choiceR.vertex
    (by simpa [hrTarget] using hkindr)
    (by simpa [hrTarget] using hvertexr) hvr
  have hboundN : ETTFirstAppearanceIndex ett choiceN.vertex hvn ≤
      r.val + 1 := by
    rw [hfirst]
    exact hboundR
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun a =>
      choiceN.vertex ∈ TreeSequenceVertexSet
        (ExtendedTashkinovLadderStage ett a)
  have hlastStage : ExtendedTashkinovLadderStage ett
      (Fin.last ett.rounds) = T := by
    unfold ExtendedTashkinovLadderStage
    exact Fin.lastCases_last
  have hcandidates : candidates.Nonempty := by
    refine ⟨Fin.last ett.rounds, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hlastStage]
    exact hvn
  let m := candidates.min' hcandidates
  have hmMem : m ∈ candidates := Finset.min'_mem candidates hcandidates
  have hmVal : m.val ≤ r.val := by
    unfold ETTFirstAppearanceIndex at hboundN
    dsimp at hboundN
    change m.val + 1 ≤ r.val + 1 at hboundN
    omega
  let s : Fin ett.rounds := ⟨m.val, by omega⟩
  have hsm : s.castSucc = m := by apply Fin.ext; rfl
  have hvMin : choiceN.vertex ∈ TreeSequenceVertexSet
      (ett.series.data.tree s.succ.castSucc) := by
    have hmStage : choiceN.vertex ∈ TreeSequenceVertexSet
        (ExtendedTashkinovLadderStage ett m) := by
      simpa [candidates] using hmMem
    rw [← hsm] at hmStage
    simpa [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc] using hmStage
  have hseg : TreeSequenceInitialSegment
      (ett.series.data.tree s.succ.castSucc) Th := by
    have hs := stageToStage (s.val + 1) (r.val + 1)
      (by omega) (by simpa [s] using hmVal) (by omega)
    convert hs using 1 <;> apply congrArg ett.series.data.tree <;>
      apply Fin.ext <;> simp [s]
  exact TreeSequenceInitialSegmentVertexSetSubset hseg hvMin

private theorem helper_hchoiceSecondR_335.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (secondStableR : PartialEdgeColoring E k)
        (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree r.succ.castSucc)
        (TashkinovStoredColors ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)),
        StableColoring (ett.series.data.tree r.succ.castSucc) (insert choiceR.color
        (TashkinovStoredColors ett.series.data r.castSucc) : Finset (Fin k)) choiceR.selected
        secondStableR →
    let _ : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc; secondStableR choiceR.edge
        = some choiceR.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r secondStableR choiceR secondRelationR Th
  exact (secondRelationR.1 choiceR.edge
    ⟨choiceR.vertex, by simpa [Th] using choiceR.vertexDefective.1,
      choiceR.edgeIncident⟩
    ⟨choiceR.color, Finset.mem_union_right _
      (Finset.mem_insert_self _ _), choiceR.edgeColor⟩).trans
    choiceR.edgeColor

private theorem helper_hgammaNeR_342.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree
        r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)), gammaR ∈ MissingColors G secondStableR
        choiceR.vertex → secondStableR choiceR.edge = some choiceR.color → gammaR ≠ choiceR.color
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR choiceR hgammaMissingR
      hchoiceSecondR heq
  have hp : gammaR ∈ PresentColors G secondStableR choiceR.vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨choiceR.edge, choiceR.edgeIncident, by simpa [heq] using hchoiceSecondR⟩
  have hnot : gammaR ∉ PresentColors G secondStableR choiceR.vertex := by
    simpa [MissingColors] using hgammaMissingR
  exact hnot hp

private theorem helper_hclosedSelectedR_350.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds), (
    ∀ {A : TreeSequence G e0} {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet A) →
        TreeIncidentEdge A f) → IsProperEdgeColoring G (ett.series.data.coloring r.castSucc) →
        IsOneEdgeUncolored (ett.series.data.coloring r.castSucc) e0 → ColoredVertexSetClosed G
        (ett.series.data.coloring r.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        r.succ.castSucc)) →
    ∀ (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree r.succ.castSucc)
        (TashkinovStoredColors ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)),
    let Th : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc; ColoredVertexSetClosed G
        choiceR.selected (TreeSequenceVertexSet Th) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r boundaryIncident previousProperR previousOneR
      previousClosedR choiceR Th f c x hf hx hfc hmiss
  have hmissOld : c ∈ MissingColors G
      (ett.series.data.coloring r.castSucc) x := by
    rw [← choiceR.selectedStable.2 x (by simpa [Th] using hx)]
    exact hmiss
  have htreeOld : c ∈ TreeMissingColors
      (ett.series.data.coloring r.castSucc) Th := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨x, hx, hmissOld⟩
  have heq := (sc1 G e0 Th
    (TashkinovStoredColors ett.series.data r.castSucc)
    (ett.series.data.coloring r.castSucc) choiceR.selected
    previousProperR previousOneR choiceR.selectedProper
    choiceR.selectedOneUncolored).mp choiceR.selectedStable f
      (boundaryIncident hf)
      (Or.inr ⟨c, Finset.mem_union_left _ htreeOld, hfc⟩)
  exact previousClosedR (by simpa [Th] using hf) hx (heq.symm.trans hfc)
    hmissOld

private theorem helper_hclosedSecondR_370.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds), (
    ∀ {A : TreeSequence G e0} {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet A) →
        TreeIncidentEdge A f) →
    ∀ (secondStableR : PartialEdgeColoring E k), IsProperEdgeColoring G secondStableR →
        IsOneEdgeUncolored secondStableR e0 →
    ∀ (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree r.succ.castSucc)
        (TashkinovStoredColors ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)),
        StableColoring (ett.series.data.tree r.succ.castSucc) (insert choiceR.color
        (TashkinovStoredColors ett.series.data r.castSucc) : Finset (Fin k)) choiceR.selected
        secondStableR →
    let Th : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc; ColoredVertexSetClosed G
        choiceR.selected (TreeSequenceVertexSet Th) → ColoredVertexSetClosed G secondStableR
        (TreeSequenceVertexSet Th) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r boundaryIncident secondStableR secondProperR
      secondOneR choiceR secondRelationR Th hclosedSelectedR f c x hf hx hfc hmiss
  have hmissSel : c ∈ MissingColors G choiceR.selected x := by
    rw [← secondRelationR.2 x hx]
    exact hmiss
  have htreeSel : c ∈ TreeMissingColors choiceR.selected Th := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨x, hx, hmissSel⟩
  have heq := (sc1 G e0 Th
    (insert choiceR.color
      (TashkinovStoredColors ett.series.data r.castSucc))
    choiceR.selected secondStableR choiceR.selectedProper
    choiceR.selectedOneUncolored secondProperR secondOneR).mp
    secondRelationR f (boundaryIncident hf)
      (Or.inr ⟨c, Finset.mem_union_left _ htreeSel, hfc⟩)
  exact hclosedSelectedR hf hx (heq.symm.trans hfc) hmissSel

private theorem helper_helemPrevR_387.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett → (0 : ℕ) < ett.rounds → (
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating'), (0 : ℕ) < lower.rounds → lower.rounds
        < ett.rounds → MaximumProperty lower → ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T')) →
    ∀ (r : Fin ett.rounds),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree r.succ.castSucc)
        (TashkinovStoredColors ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)),
        choiceR.vertex ∈ TreeSequenceVertexSet T →
    ∀ (q : Fin ett.rounds) (choiceN : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)), choiceN.vertex ∈ TreeSequenceVertexSet T → (↑r :
        ℕ) + (1 : ℕ) < ett.rounds →
    let Th : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc; ColoredVertexSetElementary
        G (ett.series.data.coloring r.castSucc) (TreeSequenceVertexSet Th) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hLowerOne r this choiceR hvr q
      choiceN hvn hrBefore Th
  by_cases hrzero : r.val = 0
  · have hr0 : r = ⟨0, by omega⟩ := Fin.ext hrzero
    have hbase : ColoredVertexSetElementary G
        (ett.series.data.coloring 0)
        (TreeSequenceVertexSet
          (ett.series.data.tree ⟨1, by omega⟩)) :=
      (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
    simpa [Th, hr0] using hbase
  · obtain ⟨lower, hlowerRounds, hlowerMP, htree, hdata⟩ :=
      CertifiedETTRestriction G k e0 input T generating ett hMP r.val
        (by omega) r.isLt
    have helem : ColoredVertexSetElementary G
        (ett.series.data.coloring ⟨r.val, by omega⟩)
        (TreeSequenceVertexSet
          (ett.series.data.tree ⟨r.val + 1, by omega⟩)) :=
      hLowerOne lower (by omega) (by simp [hlowerRounds]) hlowerMP
    have hcolorIndex : (⟨r.val, by omega⟩ : Fin (ett.rounds + 1)) =
        r.castSucc := by apply Fin.ext; rfl
    have htreeIndex : (⟨r.val + 1, by omega⟩ :
        Fin (ett.rounds + 2)) = r.succ.castSucc := by
      apply Fin.ext
      simp
    rw [hcolorIndex, htreeIndex] at helem
    simpa [Th] using helem

private theorem helper_helemSecondR_413.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (secondStableR : PartialEdgeColoring E k)
        (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree r.succ.castSucc)
        (TashkinovStoredColors ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)),
        StableColoring (ett.series.data.tree r.succ.castSucc) (insert choiceR.color
        (TashkinovStoredColors ett.series.data r.castSucc) : Finset (Fin k)) choiceR.selected
        secondStableR →
    let Th : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc; ColoredVertexSetElementary
        G (ett.series.data.coloring r.castSucc) (TreeSequenceVertexSet Th) →
        ColoredVertexSetElementary G secondStableR (TreeSequenceVertexSet Th) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r secondStableR choiceR secondRelationR Th
      helemPrevR u hu v hv huv
  have hd := helemPrevR hu hv huv
  simpa only [← choiceR.selectedStable.2 u hu,
    ← choiceR.selectedStable.2 v hv,
    ← secondRelationR.2 u hu, ← secondRelationR.2 v hv] using hd

private theorem helper_hcompDistinct_441.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree
        r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)) (q : Fin ett.rounds) (choiceN :
        MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)), choiceN.vertex ≠
        choiceR.vertex →
    let Th : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc; choiceN.vertex ∈
        TreeSequenceVertexSet Th → (
    ∀ w ∈ TreeSequenceVertexSet Th, Sum.inl w ∈ TwoColorComponent G secondStableR gammaR
        choiceR.color (Sum.inl choiceR.vertex) ↔ w = choiceR.vertex) → TwoColorComponent G
        secondStableR gammaR choiceR.color (Sum.inl choiceR.vertex) ≠ TwoColorComponent G
        secondStableR gammaR choiceR.color (Sum.inl choiceN.vertex) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR choiceR q choiceN hvnvr Th
      hvnTh hcomponentOnly heq
  have hmem : Sum.inl choiceN.vertex ∈
      TwoColorComponent G secondStableR gammaR choiceR.color
        (Sum.inl choiceR.vertex) := by
    rw [heq]
    rfl
  exact hvnvr ((hcomponentOnly choiceN.vertex hvnTh).mp hmem)

private theorem helper_hpathR_452.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k), IsProperEdgeColoring G secondStableR →
    ∀ (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree r.succ.castSucc)
        (TashkinovStoredColors ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)),
        gammaR ∈ MissingColors G secondStableR choiceR.vertex → gammaR ≠ choiceR.color →
        TwoColorPathComponent G secondStableR gammaR choiceR.color (Sum.inl choiceR.vertex) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR secondProperR choiceR
      hgammaMissingR hgammaNeR
  refine ⟨hgammaNeR, Sum.inl choiceR.vertex, rfl, ?_⟩
  intro x hx y hy
  cases x with
  | inl x => simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hx
  | inr ex =>
    cases y with
    | inl y => simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hy
    | inr ey =>
      simp only [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hx hy
      have hex : secondStableR ex = some choiceR.color :=
        hx.2.resolve_left (by
          intro he
          have hnot : gammaR ∉ PresentColors G secondStableR
              choiceR.vertex := by
            simpa [MissingColors] using hgammaMissingR
          exact hnot (by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨ex, hx.1, he⟩))
      have hey : secondStableR ey = some choiceR.color :=
        hy.2.resolve_left (by
          intro he
          have hnot : gammaR ∉ PresentColors G secondStableR
              choiceR.vertex := by
            simpa [MissingColors] using hgammaMissingR
          exact hnot (by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨ey, hy.1, he⟩))
      by_cases he : ex = ey
      · exact congrArg Sum.inr he
      · exact (secondProperR he ⟨choiceR.vertex, hx.1, hy.1⟩ hex hey).elim

private theorem helper_swapColorsR_484.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree
        r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)), gammaR ≠ choiceR.color →
    ∀ (e : E), TwoColorComponentSwap G secondStableR gammaR choiceR.color (Sum.inl choiceR.vertex)
        e = some gammaR ∨ TwoColorComponentSwap G secondStableR gammaR choiceR.color (Sum.inl
        choiceR.vertex) e = some choiceR.color ↔ secondStableR e = some gammaR ∨ secondStableR e =
        some choiceR.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR choiceR hgammaNeR e
  unfold TwoColorComponentSwap
  by_cases hc : Sum.inr e ∈ TwoColorComponent G secondStableR gammaR
      choiceR.color (Sum.inl choiceR.vertex)
  · rw [ite_eq_left hc]
    by_cases hg : secondStableR e = some gammaR
    · simp [hg, hgammaNeR, hgammaNeR.symm]
    · by_cases hd : secondStableR e = some choiceR.color
      · simp [hd, hgammaNeR, hgammaNeR.symm]
      · simp [hg, hd]
  · rw [ite_eq_right hc]

private theorem helper_graphSwapR_501.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree
        r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)) (_ : E), (
    ∀ (e : E), TwoColorComponentSwap G secondStableR gammaR choiceR.color (Sum.inl choiceR.vertex)
        e = some gammaR ∨ TwoColorComponentSwap G secondStableR gammaR choiceR.color (Sum.inl
        choiceR.vertex) e = some choiceR.color ↔ secondStableR e = some gammaR ∨ secondStableR e =
        some choiceR.color) → TwoColorIncidenceGraph G (TwoColorComponentSwap G secondStableR
        gammaR choiceR.color (Sum.inl choiceR.vertex)) gammaR choiceR.color =
        TwoColorIncidenceGraph G secondStableR gammaR choiceR.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR choiceR f swapColorsR
  ext x y
  cases x with
  | inl x =>
    cases y with
    | inl y => simp [TwoColorIncidenceGraph]
    | inr e =>
      simp only [TwoColorIncidenceGraph]
      exact and_congr Iff.rfl (swapColorsR e)
  | inr e =>
    cases y with
    | inl y =>
      simp only [TwoColorIncidenceGraph]
      exact and_congr Iff.rfl (swapColorsR e)
    | inr f => simp [TwoColorIncidenceGraph]

private theorem helper_hpathCurrentR_530.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree
        r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)), TwoColorPathComponent G secondStableR gammaR
        choiceR.color (Sum.inl choiceR.vertex) → TwoColorIncidenceGraph G
        (ett.series.data.coloring r.succ) gammaR choiceR.color = TwoColorIncidenceGraph G
        secondStableR gammaR choiceR.color → (
    ∀ (z : V ⊕ E), TwoColorComponent G (ett.series.data.coloring r.succ) gammaR choiceR.color z =
        TwoColorComponent G secondStableR gammaR choiceR.color z) → TwoColorPathComponent G
        (ett.series.data.coloring r.succ) gammaR choiceR.color (Sum.inl choiceR.vertex) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR choiceR hpathR
      graphCurrentR componentCurrentR
  rcases hpathR with ⟨hne, x, hx, hsub⟩
  refine ⟨hne, x, ?_, ?_⟩
  · rw [componentCurrentR]
    exact hx
  · rw [graphCurrentR]
    exact hsub

private theorem helper_hdeltaCurrentR_539.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree
        r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)), ett.series.data.coloring r.succ =
        TwoColorComponentSwap G secondStableR gammaR choiceR.color (Sum.inl choiceR.vertex) →
        gammaR ∈ MissingColors G secondStableR choiceR.vertex → gammaR ≠ choiceR.color →
        choiceR.color ∈ MissingColors G (ett.series.data.coloring r.succ) choiceR.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR choiceR currentColoringR
      hgammaMissingR hgammaNeR
  rw [currentColoringR]
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hp
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hp
  rcases hp with ⟨e, he, hec⟩
  have heComp : Sum.inr e ∈ TwoColorComponent G secondStableR gammaR
      choiceR.color (Sum.inl choiceR.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    by_cases hge : secondStableR e = some gammaR
    · exact (by simp [TwoColorIncidenceGraph, he, hge])
    · by_cases hde : secondStableR e = some choiceR.color
      · exact (by simp [TwoColorIncidenceGraph, he, hde])
      · simp [TwoColorComponentSwap, hge, hde] at hec
  rw [TwoColorComponentSwap] at hec
  simp only [ite_eq_left heComp] at hec
  by_cases hge : secondStableR e = some gammaR
  · have hnot : gammaR ∉ PresentColors G secondStableR
        choiceR.vertex := by
      simpa [MissingColors] using hgammaMissingR
    exact hnot (by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨e, he, hge⟩)
  · by_cases hde : secondStableR e = some choiceR.color
    · simp [hde, hgammaNeR, hgammaNeR.symm] at hec
    · exact hde (by simp [hge, hde] at hec)

private theorem helper_hinterR_568.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett → (
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating'), (0 : ℕ) < lower.rounds → lower.rounds
        < ett.rounds → MaximumProperty lower →
    let n : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
    let Tnext : TreeSequence G e0 := lower.series.data.tree (Fin.last (lower.rounds + (1 : ℕ)));
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tnext (TashkinovStoredColors lower.series.data n)
        (lower.series.data.coloring n) sigma →
    ∀ (alpha beta : Fin k), alpha ∈ TreeMissingColors sigma Tnext ∨ beta ∈ TreeMissingColors sigma
        Tnext → TreeInterchangeable G Tnext sigma alpha beta) →
    ∀ (r : Fin ett.rounds) (gammaR : Fin k) (choiceR : MaximumDefectiveChoice G e0
        (ett.series.data.tree r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)), IsProperEdgeColoring G (ett.series.data.coloring
        r.succ) → IsOneEdgeUncolored (ett.series.data.coloring r.succ) e0 →
        TreeSequenceInitialSegment (ett.series.data.tree r.succ.castSucc) (ett.series.data.tree
        r.succ.succ) → choiceR.vertex ∈ TreeSequenceVertexSet T →
    ∀ (q : Fin ett.rounds) (choiceN : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)), choiceN.vertex ∈ TreeSequenceVertexSet T → (↑r :
        ℕ) + (1 : ℕ) < ett.rounds →
    let _ : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc;
    let Thnext : TreeSequence G e0 := ett.series.data.tree r.succ.succ; choiceR.color ∈
        MissingColors G (ett.series.data.coloring r.succ) choiceR.vertex → TreeInterchangeable G
        Thnext (ett.series.data.coloring r.succ) gammaR choiceR.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hLowerTwo r gammaR choiceR currentProperR
      currentOneR orderedExtensionR hvr q choiceN hvn hrBefore Th Thnext hdeltaCurrentR
  obtain ⟨lower, hlowerRounds, hlowerMP, htree, hdata⟩ :=
    CertifiedETTRestriction G k e0 input T generating ett hMP
      (r.val + 1) (by omega) hrBefore
  have hcolorRaw := (hdata (Fin.last lower.rounds)).1
  have htreeLast := htree (Fin.last (lower.rounds + 1))
  have hcolor : lower.series.data.coloring (Fin.last lower.rounds) =
      ett.series.data.coloring r.succ := by
    calc
      _ = ett.series.data.coloring
          (Fin.castLE (by omega) (Fin.last lower.rounds)) := hcolorRaw
      _ = ett.series.data.coloring r.succ := by
        congr 1
        apply Fin.ext
        simp [hlowerRounds]
  have htreeEq : lower.series.data.tree
      (Fin.last (lower.rounds + 1)) = Thnext := by
    calc
      _ = ett.series.data.tree
          (Fin.castLE (by omega) (Fin.last (lower.rounds + 1))) := htreeLast
      _ = Thnext := by
        congr 1
        apply Fin.ext
        simp [hlowerRounds]
  have hinter := hLowerTwo lower (by omega)
    (by simpa [hlowerRounds]) hlowerMP
  dsimp at hinter
  have hstableRefl : StableColoring
      (lower.series.data.tree (Fin.last (lower.rounds + 1)))
      (TashkinovStoredColors lower.series.data (Fin.last lower.rounds))
      (lower.series.data.coloring (Fin.last lower.rounds))
      (lower.series.data.coloring (Fin.last lower.rounds)) := by
    unfold StableColoring
    exact ⟨(by intros; rfl), (by intros; rfl)⟩
  have hmissingLower : choiceR.color ∈ TreeMissingColors
      (lower.series.data.coloring (Fin.last lower.rounds))
      (lower.series.data.tree (Fin.last (lower.rounds + 1))) := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    refine ⟨choiceR.vertex, ?_, ?_⟩
    · have hvNext : choiceR.vertex ∈ TreeSequenceVertexSet Thnext :=
        TreeSequenceInitialSegmentVertexSetSubset orderedExtensionR
          (by simpa [Th] using choiceR.vertexDefective.1)
      rw [htreeEq]
      exact hvNext
    · have hm : choiceR.color ∈ MissingColors G
          (ett.series.data.coloring r.succ) choiceR.vertex := hdeltaCurrentR
      rw [hcolor]
      exact hm
  have result := hinter
    (lower.series.data.coloring (Fin.last lower.rounds))
    (by rw [hcolor]; exact currentProperR)
    (by rw [hcolor]; exact currentOneR)
    hstableRefl gammaR choiceR.color (Or.inr hmissingLower)
  rw [htreeEq, hcolor] at result
  exact result

private theorem helper_hfNotP_644.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree
        r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)) (q : Fin ett.rounds) (choiceN :
        MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)) (f : E),
        TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl choiceR.vertex) ≠
        TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl choiceN.vertex) → Sum.inr
        f ∈ TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl choiceN.vertex) →
        Sum.inr f ∉ TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl
        choiceR.vertex) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR choiceR q choiceN f
      hcompDistinct hfQ hfP
  apply hcompDistinct
  apply Set.Subset.antisymm
  · intro x hx
    change (TwoColorIncidenceGraph G secondStableR gammaR
        choiceR.color).connectedComponentMk x = _ at hx ⊢
    exact hx.trans ((show Sum.inr f ∈ TwoColorComponent G secondStableR
      gammaR choiceR.color (Sum.inl choiceR.vertex) from hfP).symm.trans hfQ)
  · intro x hx
    change (TwoColorIncidenceGraph G secondStableR gammaR
        choiceR.color).connectedComponentMk x = _ at hx ⊢
    exact hx.trans (hfQ.symm.trans hfP)

private theorem helper_hgNotP_658.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree
        r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)) (q : Fin ett.rounds) (choiceN :
        MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)) (g : E),
        TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl choiceR.vertex) ≠
        TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl choiceN.vertex) → Sum.inr
        g ∈ TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl choiceN.vertex) →
        Sum.inr g ∉ TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl
        choiceR.vertex) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR choiceR q choiceN g
      hcompDistinct hgQ hgP
  apply hcompDistinct
  apply Set.Subset.antisymm
  · intro x hx
    change (TwoColorIncidenceGraph G secondStableR gammaR
        choiceR.color).connectedComponentMk x = _ at hx ⊢
    exact hx.trans (hgP.symm.trans hgQ)
  · intro x hx
    change (TwoColorIncidenceGraph G secondStableR gammaR
        choiceR.color).connectedComponentMk x = _ at hx ⊢
    exact hx.trans (hgQ.symm.trans hgP)

private theorem helper_hgammaControlR_702.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (choiceR :
        MaximumDefectiveChoice G e0 (ett.series.data.tree r.succ.castSucc) (TashkinovStoredColors
        ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)), ett.series.data.stored
        r.succ = (insert choiceR.color ({ gammaR } : Finset (Fin k)) : Finset (Fin k)) →
        TreeSequenceInitialSegment (ett.series.data.tree r.succ.castSucc) (ett.series.data.tree
        r.succ.succ) →
    let _ : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc;
    let Thnext : TreeSequence G e0 := ett.series.data.tree r.succ.succ; gammaR ∈ TreeMissingColors
        (ett.series.data.coloring r.succ) Thnext ∪ TashkinovStoredColors ett.series.data r.succ
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR choiceR currentStoredR orderedExtensionR
      Th Thnext
  by_cases hm : gammaR ∈ TreeMissingColors
      (ett.series.data.coloring r.succ) Thnext
  · exact Finset.mem_union_left _ hm
  · apply Finset.mem_union_right
    have hmTh : gammaR ∉ TreeMissingColors
        (ett.series.data.coloring r.succ) Th := by
      intro hmOld
      apply hm
      simp only [TreeMissingColors, Finset.mem_biUnion] at hmOld ⊢
      rcases hmOld with ⟨v, hv, hvm⟩
      exact ⟨v, TreeSequenceInitialSegmentVertexSetSubset
        orderedExtensionR hv, hvm⟩
    unfold TashkinovStoredColors
    have hrsucc : r.succ.val ≠ 0 := by simp
    rw [ite_eq_right hrsucc]
    simp only [Finset.mem_sdiff]
    refine ⟨?_, hmTh⟩
    simp only [Finset.mem_biUnion]
    refine ⟨r.succ, Finset.mem_univ _, ?_⟩
    simp [currentStoredR]

private theorem helper_hchoiceSecondN_769.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (q : Fin ett.rounds) (choiceN : MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (secondStableN : PartialEdgeColoring E k),
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert choiceN.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) choiceN.selected
        secondStableN → secondStableN choiceN.edge = some choiceN.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett q choiceN secondStableN secondRelationN
  exact (secondRelationN.1 choiceN.edge
    ⟨choiceN.vertex, choiceN.vertexDefective.1, choiceN.edgeIncident⟩
    ⟨choiceN.color, Finset.mem_union_right _
      (Finset.mem_insert_self _ _), choiceN.edgeColor⟩).trans
    choiceN.edgeColor

private theorem helper_hgammaNeN_779.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (q : Fin ett.rounds) (choiceN : MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (gammaN : Fin k) (secondStableN :
        PartialEdgeColoring E k), secondStableN choiceN.edge = some choiceN.color → gammaN ∈
        MissingColors G secondStableN choiceN.vertex → gammaN ≠ choiceN.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett q choiceN gammaN secondStableN hchoiceSecondN
      hgammaMissingN heq
  have hp : gammaN ∈ PresentColors G secondStableN choiceN.vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨choiceN.edge, choiceN.edgeIncident, by simpa [heq] using hchoiceSecondN⟩
  have hnot : gammaN ∉ PresentColors G secondStableN choiceN.vertex := by
    simpa [MissingColors] using hgammaMissingN
  exact hnot hp

private theorem helper_hchoiceCurrentQ_795.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (q : Fin ett.rounds) (choiceN : MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (gammaN : Fin k), BoundaryColorEdges G
        (ett.series.data.coloring q.succ) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) gammaN = ({ choiceN.edge } : Finset E) ∧ (
    ∀ g ∈ BoundaryColorEdges G (ett.series.data.coloring q.succ) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choiceN.color,
    ∃ (w : V), TreeVertexOrder (ett.series.data.tree q.succ.castSucc) w choiceN.vertex ∧ Incident
        G w g) ∧ (ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
    ∀ alpha ∈ TreeMissingColors (ett.series.data.coloring q.succ) (ett.series.data.tree
        q.succ.castSucc), alpha ≠ choiceN.color → BoundaryColorEdges G (ett.series.data.coloring
        q.succ) (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) alpha = ∅) →
        ett.series.data.coloring q.succ choiceN.edge = some gammaN := by
  classical
  intro V E _ _ _ G k e0 input T generating ett q choiceN gammaN hparallelN
  have hm : choiceN.edge ∈ BoundaryColorEdges G
      (ett.series.data.coloring q.succ)
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      gammaN := by
    rw [hparallelN.1]
    simp
  exact (Finset.mem_filter.mp hm).2

private theorem helper_hdeltaMissingN_808.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (q : Fin ett.rounds) (choiceN : MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (gammaN : Fin k) (secondStableN :
        PartialEdgeColoring E k), ett.series.data.coloring q.succ = TwoColorComponentSwap G
        secondStableN gammaN choiceN.color (Sum.inl choiceN.vertex) → q.succ = Fin.last ett.rounds
        → gammaN ∈ MissingColors G secondStableN choiceN.vertex → gammaN ≠ choiceN.color →
        choiceN.color ∈ MissingColors G (ett.series.data.coloring (Fin.last ett.rounds))
        choiceN.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett q choiceN gammaN secondStableN currentColoringN
      hqLast hgammaMissingN hgammaNeN
  rw [← hqLast, currentColoringN]
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hpresent
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hpresent
  rcases hpresent with ⟨e, he, hec⟩
  have heComp : Sum.inr e ∈ TwoColorComponent G secondStableN gammaN
      choiceN.color (Sum.inl choiceN.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    by_cases hge : secondStableN e = some gammaN
    · exact (by simp [TwoColorIncidenceGraph, he, hge])
    · by_cases hde : secondStableN e = some choiceN.color
      · exact (by simp [TwoColorIncidenceGraph, he, hde])
      · simp [TwoColorComponentSwap, hge, hde] at hec
  rw [TwoColorComponentSwap] at hec
  simp only [ite_eq_left heComp] at hec
  by_cases hge : secondStableN e = some gammaN
  · have hnot : gammaN ∉ PresentColors G secondStableN
        choiceN.vertex := by
      simpa [MissingColors] using hgammaMissingN
    exact hnot (by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨e, he, hge⟩)
  · by_cases hde : secondStableN e = some choiceN.color
    · simp [hde, hgammaNeN, hgammaNeN.symm] at hec
    · exact hde (by simp [hge, hde] at hec)

private theorem helper_hfInternalN_837.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (choiceR : MaximumDefectiveChoice G e0
        (ett.series.data.tree r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)) (_ : choiceR.vertex ∈ TreeSequenceVertexSet T) (q :
        Fin ett.rounds) (choiceN : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (_ : choiceN.vertex ∈ TreeSequenceVertexSet T), (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (hab : a ≤ b) (hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) →
    ∀ (f : E) (p : Fin ett.rounds), f ∈ InternalEdges G (TreeSequenceVertexSet
        (ett.series.data.tree p.succ.castSucc)) → f ∈ InternalEdges G (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r choiceR hvr q choiceN hvn stageToStage f p
      hfInternal
  have hseg : TreeSequenceInitialSegment
      (ett.series.data.tree p.succ.castSucc)
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
    have hs := stageToStage (p.val + 1) ett.rounds (by omega)
      (by omega) le_rfl
    convert hs using 1 <;> apply congrArg ett.series.data.tree <;>
      apply Fin.ext <;> simp
  simp only [InternalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  intro v hvf
  exact TreeSequenceInitialSegmentVertexSetSubset hseg
    ((Finset.mem_filter.mp hfInternal).2 v hvf)

private theorem helper_hgInternalN_851.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (choiceR : MaximumDefectiveChoice G e0
        (ett.series.data.tree r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)) (_ : choiceR.vertex ∈ TreeSequenceVertexSet T) (q :
        Fin ett.rounds) (choiceN : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (_ : choiceN.vertex ∈ TreeSequenceVertexSet T), (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (hab : a ≤ b) (hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) →
    ∀ (g : E) (p : Fin ett.rounds), g ∈ InternalEdges G (TreeSequenceVertexSet
        (ett.series.data.tree p.succ.castSucc)) → g ∈ InternalEdges G (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r choiceR hvr q choiceN hvn stageToStage g p
      hgInternal
  have hseg : TreeSequenceInitialSegment
      (ett.series.data.tree p.succ.castSucc)
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
    have hs := stageToStage (p.val + 1) ett.rounds (by omega)
      (by omega) le_rfl
    convert hs using 1 <;> apply congrArg ett.series.data.tree <;>
      apply Fin.ext <;> simp
  simp only [InternalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  intro v hvg
  exact TreeSequenceInitialSegmentVertexSetSubset hseg
    ((Finset.mem_filter.mp hgInternal).2 v hvg)

private theorem helper_hfNeChoice_865.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree
        r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)) (q : Fin ett.rounds) (choiceN :
        MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)) (f : E), Incident G
        choiceN.vertex f → secondStableR f = some gammaR →
    ∀ (cycle : TwoColorCycle G (ett.series.data.coloring r.succ) gammaR choiceR.color), Sum.inr f
        ∈ TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl choiceN.vertex) →
        Sum.inr f ∉ TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl
        choiceR.vertex) → ett.series.data.coloring r.succ f = some gammaR → Sum.inr f ∈
        cycle.walk.support →
    ∀ (p : Fin ett.rounds), f ∈ InternalEdges G (TreeSequenceVertexSet (ett.series.data.tree
        p.succ.castSucc)) → TreeIncidentEdge (ett.series.data.tree p.succ.castSucc) f →
        ett.series.data.coloring p.castSucc f = some gammaR → ett.series.data.coloring q.succ f =
        ett.series.data.coloring p.castSucc f → ett.series.data.coloring (Fin.last ett.rounds) f =
        some gammaR → choiceN.edge ∈ BoundaryEdges G (TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) → f ∈ InternalEdges G (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) → f ≠ choiceN.edge := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR choiceR q choiceN f hfInc
      hfColor cycle hfQ hfNotP hfCurrent hfCycle p hfInternal hfIncidentP hfAtP hfFinalRaw
      hfFinal hchoiceBoundaryN hfInternalN heq
  subst f
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] at hchoiceBoundaryN
  rcases hchoiceBoundaryN with ⟨u, hu, v, hv, huv⟩
  have hvin : Incident G v choiceN.edge := by simp [Incident, huv]
  exact hv ((Finset.mem_filter.mp hfInternalN).2 v hvin)

private theorem helper_hgNeChoice_873.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree
        r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)) (q : Fin ett.rounds) (choiceN :
        MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)) (g : E), Incident G
        choiceN.vertex g → secondStableR g = some choiceR.color →
    ∀ (cycle : TwoColorCycle G (ett.series.data.coloring r.succ) gammaR choiceR.color), Sum.inr g
        ∈ TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl choiceN.vertex) →
        Sum.inr g ∉ TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl
        choiceR.vertex) → ett.series.data.coloring r.succ g = some choiceR.color → Sum.inr g ∈
        cycle.walk.support →
    ∀ (p : Fin ett.rounds), g ∈ InternalEdges G (TreeSequenceVertexSet (ett.series.data.tree
        p.succ.castSucc)) → TreeIncidentEdge (ett.series.data.tree p.succ.castSucc) g →
        ett.series.data.coloring p.castSucc g = some choiceR.color → ett.series.data.coloring
        q.succ g = ett.series.data.coloring p.castSucc g → ett.series.data.coloring (Fin.last
        ett.rounds) g = some choiceR.color → choiceN.edge ∈ BoundaryEdges G (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) → g ∈ InternalEdges G
        (TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc)) → g ≠
        choiceN.edge := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR choiceR q choiceN g hgInc
      hgColor cycle hgQ hgNotP hgCurrent hgCycle p hgInternal hgIncidentP hgAtP hgFinalRaw
      hgFinal hchoiceBoundaryN hgInternalN heq
  subst g
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] at hchoiceBoundaryN
  rcases hchoiceBoundaryN with ⟨u, hu, v, hv, huv⟩
  have hvin : Incident G v choiceN.edge := by simp [Incident, huv]
  exact hv ((Finset.mem_filter.mp hgInternalN).2 v hvin)

private theorem helper_hgammaRGammaN_881.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (gammaR : Fin k) (q : Fin ett.rounds) (choiceN :
        MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)) (gammaN : Fin k),
        IsProperEdgeColoring G (ett.series.data.coloring q.succ) → q.succ = Fin.last ett.rounds →
    ∀ (f : E), Incident G choiceN.vertex f → ett.series.data.coloring (Fin.last ett.rounds) f =
        some gammaR → ett.series.data.coloring q.succ choiceN.edge = some gammaN → f ≠
        choiceN.edge → gammaR ≠ gammaN := by
  classical
  intro V E _ _ _ G k e0 input T generating ett gammaR q choiceN gammaN currentProperN hqLast f
      hfInc hfFinal hchoiceCurrentQ hfNeChoice heq
  have hfFinalQ : ett.series.data.coloring q.succ f = some gammaR := by
    rw [hqLast]
    exact hfFinal
  exact (currentProperN hfNeChoice
    ⟨choiceN.vertex, hfInc, choiceN.edgeIncident⟩ hfFinalQ)
    (by simpa [heq] using hchoiceCurrentQ)

private theorem helper_hdeltaRGammaN_889.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (choiceR : MaximumDefectiveChoice G e0
        (ett.series.data.tree r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)) (q : Fin ett.rounds) (choiceN :
        MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)) (gammaN : Fin k),
        IsProperEdgeColoring G (ett.series.data.coloring q.succ) → q.succ = Fin.last ett.rounds →
    ∀ (g : E), Incident G choiceN.vertex g → ett.series.data.coloring (Fin.last ett.rounds) g =
        some choiceR.color → ett.series.data.coloring q.succ choiceN.edge = some gammaN → g ≠
        choiceN.edge → choiceR.color ≠ gammaN := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r choiceR q choiceN gammaN currentProperN hqLast
      g hgInc hgFinal hchoiceCurrentQ hgNeChoice heq
  have hgFinalQ : ett.series.data.coloring q.succ g =
      some choiceR.color := by
    rw [hqLast]
    exact hgFinal
  exact (currentProperN hgNeChoice
    ⟨choiceN.vertex, hgInc, choiceN.edgeIncident⟩ hgFinalQ)
    (by simpa [heq] using hchoiceCurrentQ)

private theorem helper_hgammaRDeltaN_898.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (gammaR : Fin k) (q : Fin ett.rounds) (choiceN :
        MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)) (f : E), Incident G
        choiceN.vertex f → ett.series.data.coloring (Fin.last ett.rounds) f = some gammaR →
        choiceN.color ∈ MissingColors G (ett.series.data.coloring (Fin.last ett.rounds))
        choiceN.vertex → gammaR ≠ choiceN.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett gammaR q choiceN f hfInc hfFinal hdeltaMissingN heq
  have hp : choiceN.color ∈ PresentColors G
      (ett.series.data.coloring (Fin.last ett.rounds)) choiceN.vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨f, hfInc, by simpa [heq] using hfFinal⟩
  have hnot : choiceN.color ∉ PresentColors G
      (ett.series.data.coloring (Fin.last ett.rounds)) choiceN.vertex := by
    simpa [MissingColors] using hdeltaMissingN
  exact hnot hp

private theorem helper_hdeltaRDeltaN_908.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (choiceR : MaximumDefectiveChoice G e0
        (ett.series.data.tree r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)) (q : Fin ett.rounds) (choiceN :
        MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)) (g : E), Incident G
        choiceN.vertex g → ett.series.data.coloring (Fin.last ett.rounds) g = some choiceR.color →
        choiceN.color ∈ MissingColors G (ett.series.data.coloring (Fin.last ett.rounds))
        choiceN.vertex → choiceR.color ≠ choiceN.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r choiceR q choiceN g hgInc hgFinal
      hdeltaMissingN heq
  have hp : choiceN.color ∈ PresentColors G
      (ett.series.data.coloring (Fin.last ett.rounds)) choiceN.vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨g, hgInc, by simpa [heq] using hgFinal⟩
  have hnot : choiceN.color ∉ PresentColors G
      (ett.series.data.coloring (Fin.last ett.rounds)) choiceN.vertex := by
    simpa [MissingColors] using hdeltaMissingN
  exact hnot hp

private theorem helper_continuation_1704.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (r : Fin ett.rounds) (gammaR : Fin k) (secondStableR :
        PartialEdgeColoring E k) (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree
        r.succ.castSucc) (TashkinovStoredColors ett.series.data r.castSucc)
        (ett.series.data.coloring r.castSucc)), ett.series.data.stored r.succ = (insert
        choiceR.color ({ gammaR } : Finset (Fin k)) : Finset (Fin k)) → choiceR.vertex ∈
        TreeSequenceVertexSet T → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (hab : a ≤ b) (hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a_2 : ¬a <
        ett.rounds + (2 : ℕ)) ↦
    by
                      omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a_2 : ¬b <
        ett.rounds + (2 : ℕ)) ↦
    by
                      omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) →
    ∀ (q : Fin ett.rounds) (choiceN : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (gammaN : Fin k) (secondStableN :
        PartialEdgeColoring E k), ett.series.data.coloring q.succ = TwoColorComponentSwap G
        secondStableN gammaN choiceN.color (Sum.inl choiceN.vertex) → IsProperEdgeColoring G
        (ett.series.data.coloring q.succ) → ett.series.data.stored q.succ = (insert choiceN.color
        ({ gammaN } : Finset (Fin k)) : Finset (Fin k)) → ett.series.data.connectingEdges q.succ =
        ({ choiceN.edge } : Finset E) → ett.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → ett.series.data.chosenVertex q.succ = some choiceN.vertex →
        ett.series.data.delta q.succ = some choiceN.color → ett.series.data.gamma q.succ = some
        gammaN → choiceN.vertex ∈ TreeSequenceVertexSet T → q.succ = Fin.last ett.rounds →
    ∀ (f : E), Incident G choiceN.vertex f → secondStableR f = some gammaR →
    ∀ (g : E), Incident G choiceN.vertex g → secondStableR g = some choiceR.color →
    ∀ (cycle : TwoColorCycle G (ett.series.data.coloring r.succ) gammaR choiceR.color), Sum.inr f
        ∈ TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl choiceN.vertex) →
        Sum.inr g ∈ TwoColorComponent G secondStableR gammaR choiceR.color (Sum.inl
        choiceN.vertex) → Sum.inr f ∉ TwoColorComponent G secondStableR gammaR choiceR.color
        (Sum.inl choiceR.vertex) → Sum.inr g ∉ TwoColorComponent G secondStableR gammaR
        choiceR.color (Sum.inl choiceR.vertex) → ett.series.data.coloring r.succ f = some gammaR →
        ett.series.data.coloring r.succ g = some choiceR.color → Sum.inr f ∈ cycle.walk.support →
        Sum.inr g ∈ cycle.walk.support →
    ∀ (p : Fin ett.rounds), f ∈ InternalEdges G (TreeSequenceVertexSet (ett.series.data.tree
        p.succ.castSucc)) → g ∈ InternalEdges G (TreeSequenceVertexSet (ett.series.data.tree
        p.succ.castSucc)) → TreeIncidentEdge (ett.series.data.tree p.succ.castSucc) f →
        TreeIncidentEdge (ett.series.data.tree p.succ.castSucc) g → ett.series.data.coloring
        p.castSucc f = some gammaR → ett.series.data.coloring p.castSucc g = some choiceR.color →
        ett.series.data.coloring q.succ f = ett.series.data.coloring p.castSucc f →
        ett.series.data.coloring q.succ g = ett.series.data.coloring p.castSucc g →
        ett.series.data.coloring (Fin.last ett.rounds) f = some gammaR → ett.series.data.coloring
        (Fin.last ett.rounds) g = some choiceR.color → choiceN.edge ∈ BoundaryEdges G
        (TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc)) → gammaN ∈
        MissingColors G secondStableN choiceN.vertex → gammaN ≠ choiceN.color → Disjoint
        (ett.series.data.stored q.succ) (ett.series.data.stored r.succ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r gammaR secondStableR choiceR currentStoredR hvr
      stageToStage q choiceN gammaN secondStableN currentColoringN currentProperN currentStoredN
      currentEdgesN currentKindN currentVertexN currentDeltaN currentGammaN hvn hqLast f hfInc
      hfColor g hgInc hgColor cycle hfQ hgQ hfNotP hgNotP hfCurrent hgCurrent hfCycle hgCycle p
      hfInternal hgInternal hfIncidentP hgIncidentP hfAtP hgAtP hfFinalRaw hgFinalRaw hfFinal
      hgFinal hchoiceBoundaryN hgammaMissingN hgammaNeN
  have hparallelN := HkuParallelBoundaryStructure G k ett.rounds e0 input
    ett.series q choiceN.edge choiceN.color gammaN choiceN.vertex
    currentKindN currentEdgesN currentDeltaN currentGammaN currentVertexN
  have hchoiceCurrentQ :=
    @helper_hchoiceCurrentQ_795 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@q) (@choiceN) (@gammaN) (@hparallelN)
  have hchoiceCurrentN : ett.series.data.coloring
      (Fin.last ett.rounds) choiceN.edge = some gammaN := by
    rw [← hqLast]
    exact hchoiceCurrentQ
  have hdeltaMissingN :=
    @helper_hdeltaMissingN_808 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@q) (@choiceN) (@gammaN) (@secondStableN)
        (@currentColoringN) (@hqLast) (@hgammaMissingN) (@hgammaNeN)
  have hfInternalN :=
    @helper_hfInternalN_837 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@choiceR) (@hvr) (@q) (@choiceN) (@hvn)
        (@stageToStage) (@f) (@p) (@hfInternal)
  have hgInternalN :=
    @helper_hgInternalN_851 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@choiceR) (@hvr) (@q) (@choiceN) (@hvn)
        (@stageToStage) (@g) (@p) (@hgInternal)
  have hfNeChoice :=
    @helper_hfNeChoice_865 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@choiceR) (@q)
        (@choiceN) (@f) (@hfInc) (@hfColor) (@cycle) (@hfQ) (@hfNotP) (@hfCurrent) (@hfCycle)
        (@p) (@hfInternal) (@hfIncidentP) (@hfAtP) (@hfFinalRaw) (@hfFinal) (@hchoiceBoundaryN)
        (@hfInternalN)
  have hgNeChoice :=
    @helper_hgNeChoice_873 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@choiceR) (@q)
        (@choiceN) (@g) (@hgInc) (@hgColor) (@cycle) (@hgQ) (@hgNotP) (@hgCurrent) (@hgCycle)
        (@p) (@hgInternal) (@hgIncidentP) (@hgAtP) (@hgFinalRaw) (@hgFinal) (@hchoiceBoundaryN)
        (@hgInternalN)
  have hgammaRGammaN :=
    @helper_hgammaRGammaN_881 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@gammaR) (@q) (@choiceN) (@gammaN) (@currentProperN)
        (@hqLast) (@f) (@hfInc) (@hfFinal) (@hchoiceCurrentQ) (@hfNeChoice)
  have hdeltaRGammaN :=
    @helper_hdeltaRGammaN_889 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@choiceR) (@q) (@choiceN) (@gammaN)
        (@currentProperN) (@hqLast) (@g) (@hgInc) (@hgFinal) (@hchoiceCurrentQ) (@hgNeChoice)
  have hgammaRDeltaN :=
    @helper_hgammaRDeltaN_898 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@gammaR) (@q) (@choiceN) (@f) (@hfInc) (@hfFinal)
        (@hdeltaMissingN)
  have hdeltaRDeltaN :=
    @helper_hdeltaRDeltaN_908 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@choiceR) (@q) (@choiceN) (@g) (@hgInc)
        (@hgFinal) (@hdeltaMissingN)
  rw [currentStoredN, currentStoredR]
  apply Finset.disjoint_left.mpr
  intro c hcN hcR
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcN hcR
  rcases hcN with hcN | hcN <;> rcases hcR with hcR | hcR
  · exact hdeltaRDeltaN (hcR.symm.trans hcN)
  · exact hgammaRDeltaN (hcR.symm.trans hcN)
  · exact hdeltaRGammaN (hcR.symm.trans hcN)
  · exact hgammaRGammaN (hcR.symm.trans hcN)

private theorem helper_continuation_1661.{u_1, u_2} :
    helperContinuation1661Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hLowerTwo r hrEarlier hkindn hkindr
      controlCarry gammaR secondStableR choiceR currentColoringR currentProperR currentOneR
      currentStoredR currentDeltaR currentGammaR orderedExtensionR hrTarget hvr stageToStage q
      choiceN gammaN gammaRuleN secondStableN secondRelationN currentColoringN currentProperN
      currentStoredN currentEdgesN currentKindN currentVertexN currentDeltaN currentGammaN hvn
      hfirst hqLast hrBefore Th Thnext hvnTh hgammaMissingR hgammaNeR f hfInc hfColor g hgInc
      hgColor hcompDistinct hpathR graphCurrentR
  have componentCurrentR (z : Sum V E) :
      TwoColorComponent G (ett.series.data.coloring r.succ) gammaR
          choiceR.color z =
        TwoColorComponent G secondStableR gammaR choiceR.color z := by
    unfold TwoColorComponent
    rw [graphCurrentR]
  have hpathCurrentR :=
    @helper_hpathCurrentR_530 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@choiceR) (@hpathR)
        (@graphCurrentR) (@componentCurrentR)
  have hdeltaCurrentR :=
    @helper_hdeltaCurrentR_539 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@choiceR)
        (@currentColoringR) (@hgammaMissingR) (@hgammaNeR)
  have hinterR :=
    @helper_hinterR_568 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@hMP) (@hLowerTwo) (@r) (@gammaR) (@choiceR)
        (@currentProperR) (@currentOneR) (@orderedExtensionR) (@hvr) (@q) (@choiceN) (@hvn)
        (@hrBefore) (@hdeltaCurrentR)
  have hrVertexNext : choiceR.vertex ∈ TreeSequenceVertexSet Thnext :=
    TreeSequenceInitialSegmentVertexSetSubset orderedExtensionR
      (by simpa [Th] using choiceR.vertexDefective.1)
  have hnVertexNext : choiceN.vertex ∈ TreeSequenceVertexSet Thnext :=
    TreeSequenceInitialSegmentVertexSetSubset orderedExtensionR hvnTh
  have cycleComp := TwoColorInterchangeableDistinctComponentCycle G Thnext
    (ett.series.data.coloring r.succ) gammaR choiceR.color currentProperR
    (Sum.inl choiceR.vertex) (Sum.inl choiceN.vertex) hpathCurrentR hinterR
    ⟨choiceR.vertex, hrVertexNext, by rw [componentCurrentR]; rfl⟩
    ⟨choiceN.vertex, hnVertexNext, by rw [componentCurrentR]; rfl⟩
    (by simpa only [componentCurrentR] using hcompDistinct)
  rcases cycleComp with ⟨cycle, hcycleSupport⟩
  have hfQ : Sum.inr f ∈ TwoColorComponent G secondStableR gammaR
      choiceR.color (Sum.inl choiceN.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, hfInc, hfColor]
  have hgQ : Sum.inr g ∈ TwoColorComponent G secondStableR gammaR
      choiceR.color (Sum.inl choiceN.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, hgInc, hgColor]
  have hfNotP :=
    @helper_hfNotP_644 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@choiceR) (@q)
        (@choiceN) (@f) (@hcompDistinct) (@hfQ)
  have hgNotP :=
    @helper_hgNotP_658 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@choiceR) (@q)
        (@choiceN) (@g) (@hcompDistinct) (@hgQ)
  have hfCurrent : ett.series.data.coloring r.succ f = some gammaR := by
    rw [currentColoringR]
    simpa [TwoColorComponentSwap, hfNotP] using hfColor
  have hgCurrent : ett.series.data.coloring r.succ g = some choiceR.color := by
    rw [currentColoringR]
    simpa [TwoColorComponentSwap, hgNotP] using hgColor
  have hfCycle : Sum.inr f ∈ cycle.walk.support := by
    rw [hcycleSupport, componentCurrentR]
    exact hfQ
  have hgCycle : Sum.inr g ∈ cycle.walk.support := by
    rw [hcycleSupport, componentCurrentR]
    exact hgQ
  have hcycleMeets : ∃ v ∈ TreeSequenceVertexSet
      (ett.series.data.tree r.succ.castSucc),
      Sum.inl v ∈ cycle.walk.support := by
    refine ⟨choiceN.vertex, hvnTh, ?_⟩
    rw [hcycleSupport, componentCurrentR]
    rfl
  obtain ⟨p, hrp, hpKind, hpRevisiting, hpColor, hpInternal⟩ :=
    EarlierPECycleFirstNonrevisitingInternal G k ett.rounds e0 input
      ett.series r hrEarlier gammaR choiceR.color
      (by simpa [hrTarget] using hkindr)
      (by simpa [hrTarget] using currentGammaR)
      (by simpa [hrTarget] using currentDeltaR)
      cycle hcycleMeets hkindn
  have hdeltaControlR : choiceR.color ∈
      TreeMissingColors (ett.series.data.coloring r.succ) Thnext ∪
        TashkinovStoredColors ett.series.data r.succ := by
    apply Finset.mem_union_left
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨choiceR.vertex, hrVertexNext, hdeltaCurrentR⟩
  have hgammaControlR :=
    @helper_hgammaControlR_702 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@choiceR) (@currentStoredR)
        (@orderedExtensionR)
  have hdeltaControlP := controlCarry r p hrp hdeltaControlR
  have hgammaControlP := controlCarry r p hrp hgammaControlR
  have hfInternal := hpInternal f hfCycle
  have hgInternal := hpInternal g hgCycle
  have hfIncidentP : TreeIncidentEdge
      (ett.series.data.tree p.succ.castSucc) f := by
    refine ⟨choiceN.vertex, ?_, hfInc⟩
    simpa [InternalEdges] using
      (Finset.mem_filter.mp hfInternal).2 choiceN.vertex hfInc
  have hgIncidentP : TreeIncidentEdge
      (ett.series.data.tree p.succ.castSucc) g := by
    refine ⟨choiceN.vertex, ?_, hgInc⟩
    simpa [InternalEdges] using
      (Finset.mem_filter.mp hgInternal).2 choiceN.vertex hgInc
  have hfAtP : ett.series.data.coloring p.castSucc f = some gammaR := by
    rw [hpColor]
    exact hfCurrent
  have hgAtP : ett.series.data.coloring p.castSucc g = some choiceR.color := by
    rw [hpColor]
    exact hgCurrent
  have hpq : p.val ≤ q.val := by
    have hqv := congrArg Fin.val hqLast
    simp at hqv
    omega
  have hfFinalRaw := (SameColorSeriesPreserved G k ett.rounds e0 input
    ett.series p q hpq f gammaR hfIncidentP hfAtP
    (by simpa [Thnext] using hgammaControlP)).2 hfInternal
  have hgFinalRaw := (SameColorSeriesPreserved G k ett.rounds e0 input
    ett.series p q hpq g choiceR.color hgIncidentP hgAtP
    (by simpa [Thnext] using hdeltaControlP)).2 hgInternal
  have hfFinal : ett.series.data.coloring (Fin.last ett.rounds) f =
      some gammaR := by
    rw [← hqLast]
    exact hfFinalRaw.trans hfAtP
  have hgFinal : ett.series.data.coloring (Fin.last ett.rounds) g =
      some choiceR.color := by
    rw [← hqLast]
    exact hgFinalRaw.trans hgAtP
  have hchoiceBoundaryN : choiceN.edge ∈ BoundaryEdges G
      (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
    rcases choiceN.edgeDefective with ⟨c, hc, he⟩
    have hb := (Finset.mem_filter.mp he).1
    simpa [hqLast] using hb
  have hchoiceSecondN :=
    @helper_hchoiceSecondN_769 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@q) (@choiceN) (@secondStableN) (@secondRelationN)
  have hgammaMissingN : gammaN ∈ MissingColors G secondStableN
      choiceN.vertex := by
    rw [secondRelationN.2 choiceN.vertex choiceN.vertexDefective.1]
    exact gammaRuleN.1
  have hgammaNeN :=
    @helper_hgammaNeN_779 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@q) (@choiceN) (@gammaN) (@secondStableN)
        (@hchoiceSecondN) (@hgammaMissingN)
  have hchoiceCompN : Sum.inr choiceN.edge ∈
      TwoColorComponent G secondStableN gammaN choiceN.color
        (Sum.inl choiceN.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, choiceN.edgeIncident, hchoiceSecondN]
  exact @helper_continuation_1704 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@choiceR)
      (@currentStoredR) (@hvr) (@stageToStage) (@q) (@choiceN) (@gammaN) (@secondStableN)
      (@currentColoringN) (@currentProperN) (@currentStoredN) (@currentEdgesN) (@currentKindN)
      (@currentVertexN) (@currentDeltaN) (@currentGammaN) (@hvn) (@hqLast) (@f) (@hfInc)
      (@hfColor) (@g) (@hgInc) (@hgColor) (@cycle) (@hfQ) (@hgQ) (@hfNotP) (@hgNotP) (@hfCurrent)
      (@hgCurrent) (@hfCycle) (@hgCycle) (@p) (@hfInternal) (@hgInternal) (@hfIncidentP)
      (@hgIncidentP) (@hfAtP) (@hgAtP) (@hfFinalRaw) (@hgFinalRaw) (@hfFinal) (@hgFinal)
      (@hchoiceBoundaryN) (@hgammaMissingN) (@hgammaNeN)
private theorem helper_branch_1399.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett → (0 : ℕ) < ett.rounds → (
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating'), (0 : ℕ) < lower.rounds → lower.rounds
        < ett.rounds → MaximumProperty lower → ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T')) → (
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating'), (0 : ℕ) < lower.rounds → lower.rounds
        < ett.rounds → MaximumProperty lower →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (lower.series.data.tree (Fin.last (lower.rounds + (1 : ℕ))) :
        TreeSequence G e0) (TashkinovStoredColors lower.series.data (Fin.last lower.rounds : Fin
        (lower.rounds + (1 : ℕ)))) (lower.series.data.coloring (Fin.last lower.rounds : Fin
        (lower.rounds + (1 : ℕ)))) sigma →
    ∀ (alpha beta : Fin k), alpha ∈ TreeMissingColors sigma (lower.series.data.tree (Fin.last
        (lower.rounds + (1 : ℕ))) : TreeSequence G e0) ∨ beta ∈ TreeMissingColors sigma
        (lower.series.data.tree (Fin.last (lower.rounds + (1 : ℕ))) : TreeSequence G e0) →
        TreeInterchangeable G (lower.series.data.tree (Fin.last (lower.rounds + (1 : ℕ))) :
        TreeSequence G e0) sigma alpha beta) →
    ∀ (r : Fin ett.rounds) (vn : V), r.succ ≠ Fin.last ett.rounds → ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.PE → ett.series.data.kind r.succ = some
        TashkinovExtensionKind.PE → ett.series.data.chosenVertex (Fin.last ett.rounds) = some vn →
    ∀ (hvn : vn ∈ TreeSequenceVertexSet T), (
    ∀ {A : TreeSequence G e0} {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet A) →
        TreeIncidentEdge A f) → (
    ∀ (r p : Fin ett.rounds), (↑r : ℕ) < (↑p : ℕ) → TreeMissingColors (ett.series.data.coloring
        r.succ) (ett.series.data.tree r.succ.succ) ∪ TashkinovStoredColors ett.series.data r.succ
        ⊆ TreeMissingColors (ett.series.data.coloring p.castSucc) (ett.series.data.tree
        p.succ.castSucc) ∪ TashkinovStoredColors ett.series.data p.castSucc) →
    ∀ (gammaR : Fin k) (secondStableR : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStableR → IsOneEdgeUncolored secondStableR e0 → IsProperEdgeColoring G
        (ett.series.data.coloring r.castSucc) → IsOneEdgeUncolored (ett.series.data.coloring
        r.castSucc) e0 → ColoredVertexSetClosed G (ett.series.data.coloring r.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)) →
    ∀ (choiceR : MaximumDefectiveChoice G e0 (ett.series.data.tree r.succ.castSucc)
        (TashkinovStoredColors ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)),
        ParallelExtensionColor ett.series.data r.castSucc choiceR.selected choiceR.vertex gammaR →
        StableColoring (ett.series.data.tree r.succ.castSucc) (insert choiceR.color
        (TashkinovStoredColors ett.series.data r.castSucc) : Finset (Fin k)) choiceR.selected
        secondStableR → TreeExit (ett.series.data.tree r.succ.castSucc) secondStableR gammaR
        choiceR.color choiceR.vertex → ett.series.data.coloring r.succ = TwoColorComponentSwap G
        secondStableR gammaR choiceR.color (Sum.inl choiceR.vertex) → IsProperEdgeColoring G
        (ett.series.data.coloring r.succ) → IsOneEdgeUncolored (ett.series.data.coloring r.succ)
        e0 → ett.series.data.stored r.succ = (insert choiceR.color ({ gammaR } : Finset (Fin k)) :
        Finset (Fin k)) → ett.series.data.delta r.succ = some choiceR.color →
        ett.series.data.gamma r.succ = some gammaR → TreeSequenceInitialSegment
        (ett.series.data.tree r.succ.castSucc) (ett.series.data.tree r.succ.succ) → r.succ =
        r.succ → vn ≠ choiceR.vertex → ett.series.data.chosenVertex r.succ = some choiceR.vertex →
    ∀ (hvr : choiceR.vertex ∈ TreeSequenceVertexSet T), ETTFirstAppearanceIndex ett vn hvn =
        ETTFirstAppearanceIndex ett choiceR.vertex hvr → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (hab : a ≤ b) (hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) →
    ∀ (q : Fin ett.rounds) (choiceN : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (gammaN : Fin k), ParallelExtensionColor
        ett.series.data q.castSucc choiceN.selected choiceN.vertex gammaN →
    ∀ (secondStableN : PartialEdgeColoring E k), StableColoring (ett.series.data.tree
        q.succ.castSucc) (insert choiceN.color (TashkinovStoredColors ett.series.data q.castSucc)
        : Finset (Fin k)) choiceN.selected secondStableN → ett.series.data.coloring q.succ =
        TwoColorComponentSwap G secondStableN gammaN choiceN.color (Sum.inl choiceN.vertex) →
        IsProperEdgeColoring G (ett.series.data.coloring q.succ) → ett.series.data.stored q.succ =
        (insert choiceN.color ({ gammaN } : Finset (Fin k)) : Finset (Fin k)) →
        ett.series.data.connectingEdges q.succ = ({ choiceN.edge } : Finset E) →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some choiceN.vertex → ett.series.data.delta q.succ =
        some choiceN.color → ett.series.data.gamma q.succ = some gammaN → Fin.last ett.rounds =
        q.succ → Disjoint (ett.series.data.stored q.succ) (ett.series.data.stored r.succ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hLowerOne hLowerTwo r vn hrEarlier
      hkindn hkindr hvertexn hvn boundaryIncident controlCarry gammaR secondStableR secondProperR
      secondOneR previousProperR previousOneR previousClosedR choiceR gammaRuleR secondRelationR
      exitR currentColoringR currentProperR currentOneR currentStoredR currentDeltaR
      currentGammaR orderedExtensionR hrTarget hvnvr hvertexr hvr hfirst stageToStage q choiceN
      gammaN gammaRuleN secondStableN secondRelationN currentColoringN currentProperN
      currentStoredN currentEdgesN currentKindN currentVertexN currentDeltaN currentGammaN hnTarget
  have hvnChoice : choiceN.vertex = vn :=
    Option.some.inj (currentVertexN.symm.trans
      (by simpa [hnTarget] using hvertexn))
  subst vn
  have hqLast : q.succ = Fin.last ett.rounds := hnTarget.symm
  have hrBefore :=
    @helper_hrBefore_273 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@hrEarlier)
  let Th := ett.series.data.tree r.succ.castSucc
  let Thnext := ett.series.data.tree r.succ.succ
  have hvnTh :=
    @helper_hvnTh_282 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@hkindr) (@choiceR) (@hrTarget) (@hvertexr)
        (@hvr) (@q) (@choiceN) (@hvn) (@hfirst) (@stageToStage) (@hrBefore)
  have hgammaMissingR : gammaR ∈ MissingColors G secondStableR
      choiceR.vertex := by
    rw [secondRelationR.2 choiceR.vertex choiceR.vertexDefective.1]
    exact gammaRuleR.1
  have hchoiceBoundaryR : choiceR.edge ∈
      BoundaryEdges G (TreeSequenceVertexSet Th) := by
    rcases choiceR.edgeDefective with ⟨c, hc, he⟩
    simpa [Th, BoundaryColorEdges] using (Finset.mem_filter.mp he).1
  have hchoiceSecondR :=
    @helper_hchoiceSecondR_335 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@r) (@secondStableR) (@choiceR) (@secondRelationR)
  have hgammaNeR :=
    @helper_hgammaNeR_342 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@choiceR)
        (@hgammaMissingR) (@hchoiceSecondR)
  have hclosedSelectedR :=
    @helper_hclosedSelectedR_350 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@r) (@boundaryIncident) (@previousProperR)
        (@previousOneR) (@previousClosedR) (@choiceR)
  have hclosedSecondR :=
    @helper_hclosedSecondR_370 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@r) (@boundaryIncident) (@secondStableR)
        (@secondProperR) (@secondOneR) (@choiceR) (@secondRelationR) (@hclosedSelectedR)
  have helemPrevR :=
    @helper_helemPrevR_387 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@hLowerOne) (@r) (@choiceR)
        (@hvr) (@q) (@choiceN) (@hvn) (@hrBefore)
  have helemSecondR :=
    @helper_helemSecondR_413 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@secondStableR) (@choiceR) (@secondRelationR)
        (@helemPrevR)
  have hgammaNotMissingN : gammaR ∉ MissingColors G secondStableR
      choiceN.vertex := by
    intro hm
    have hd := helemSecondR hvnTh
      (by simpa [Th] using choiceR.vertexDefective.1) hvnvr
    exact (Finset.disjoint_left.mp hd) hm hgammaMissingR
  have hdeltaNotMissingN : choiceR.color ∉ MissingColors G secondStableR
      choiceN.vertex :=
    hclosedSecondR hchoiceBoundaryR hvnTh hchoiceSecondR
  obtain ⟨f, hfInc, hfColor⟩ : ∃ f : E, Incident G choiceN.vertex f ∧
      secondStableR f = some gammaR := by
    have hp : gammaR ∈ PresentColors G secondStableR choiceN.vertex := by
      simpa [MissingColors] using hgammaNotMissingN
    simpa [PresentColors] using hp
  obtain ⟨g, hgInc, hgColor⟩ : ∃ g : E, Incident G choiceN.vertex g ∧
      secondStableR g = some choiceR.color := by
    have hp : choiceR.color ∈ PresentColors G secondStableR choiceN.vertex := by
      simpa [MissingColors] using hdeltaNotMissingN
    simpa [PresentColors] using hp
  have hcomponentOnly := TreeExitComponentMeetsTreeOnlyAtExit Th secondStableR
    gammaR choiceR.color choiceR.vertex secondProperR hgammaMissingR exitR
  have hcompDistinct :=
    @helper_hcompDistinct_441 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@choiceR) (@q)
        (@choiceN) (@hvnvr) (@hvnTh) (@hcomponentOnly)
  have hpathR :=
    @helper_hpathR_452 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@secondProperR)
        (@choiceR) (@hgammaMissingR) (@hgammaNeR)
  have swapColorsR := @helper_swapColorsR_484 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@choiceR)
      (@hgammaNeR)
  have graphSwapR :=
    @helper_graphSwapR_501 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@r) (@gammaR) (@secondStableR) (@choiceR) (@f)
        (@swapColorsR)
  have graphCurrentR : TwoColorIncidenceGraph G
      (ett.series.data.coloring r.succ) gammaR choiceR.color =
      TwoColorIncidenceGraph G secondStableR gammaR choiceR.color := by
    rw [currentColoringR]
    exact graphSwapR
  exact @helper_continuation_1661 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@hLowerTwo) (@r) (@hrEarlier)
      (@hkindn) (@hkindr) (@controlCarry) (@gammaR) (@secondStableR) (@choiceR)
      (@currentColoringR) (@currentProperR) (@currentOneR) (@currentStoredR) (@currentDeltaR)
      (@currentGammaR) (@orderedExtensionR) (@hrTarget) (@hvr) (@stageToStage) (@q) (@choiceN)
      (@gammaN) (@gammaRuleN) (@secondStableN) (@secondRelationN) (@currentColoringN)
      (@currentProperN) (@currentStoredN) (@currentEdgesN) (@currentKindN) (@currentVertexN)
      (@currentDeltaN) (@currentGammaN) (@hvn) (@hfirst) (@hqLast) (@hrBefore) (@hvnTh)
      (@hgammaMissingR) (@hgammaNeR) (@f) (@hfInc) (@hfColor) (@g) (@hgInc) (@hgColor)
      (@hcompDistinct) (@hpathR) (@graphCurrentR)
theorem ExtensionRulesTerminalStoredDisjoint {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hLowerOne : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T'))
    (hLowerTwo : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
       let Tnext : TreeSequence G e0 :=
         lower.series.data.tree (Fin.last (lower.rounds + 1))
       ∀ sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
         StableColoring Tnext
           (TashkinovStoredColors lower.series.data n)
           (lower.series.data.coloring n) sigma →
         ∀ alpha beta : Fin k,
           (alpha ∈ TreeMissingColors sigma Tnext ∨
             beta ∈ TreeMissingColors sigma Tnext) →
           TreeInterchangeable G Tnext sigma alpha beta))
    (r : Fin ett.rounds) (vn vr : V)
    (hrEarlier : r.succ ≠ Fin.last ett.rounds)
    (hvnvr : vn ≠ vr)
    (hkindn : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hkindr : ett.series.data.kind r.succ = some TashkinovExtensionKind.PE)
    (hvertexn : ett.series.data.chosenVertex (Fin.last ett.rounds) = some vn)
    (hvertexr : ett.series.data.chosenVertex r.succ = some vr)
    (hvn : vn ∈ TreeSequenceVertexSet T) (hvr : vr ∈ TreeSequenceVertexSet T)
    (hfirst : ETTFirstAppearanceIndex ett vn hvn =
      ETTFirstAppearanceIndex ett vr hvr) :
    Disjoint (ett.series.data.stored (Fin.last ett.rounds)) (ett.series.data.stored r.succ) := by
  classical
  let : DecidableEq V := Classical.decEq V
  have segmentRefl (A : TreeSequence G e0) : TreeSequenceInitialSegment A A :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    apply TreeSequenceInitialSegment.trans <;> assumption
  have stepSegment :=
    @_root_.GoldbergSeymour.ExtensionBaseProof.helper_stepSegment_2099 (@V) (@E) inferInstance
        inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett)
  have stageToStage := @helper_stageToStage_128 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@vn) (@vr) (@hvn) (@hvr) (@segmentRefl)
      (@segmentTrans) (@stepSegment)
  have boundaryIncident {A : TreeSequence G e0} {f : E}
      (hf : f ∈ BoundaryEdges G (TreeSequenceVertexSet A)) :
      TreeIncidentEdge A f := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hf
    rcases hf with ⟨u, hu, v, hv, huv⟩
    exact ⟨u, hu, by simp [Incident, huv]⟩
  have controlCarry := @helper_controlCarry_158 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@vn) (@vr) (@hvn) (@hvr) (@hfirst)
  generalize hrTarget : r.succ = targetR
  have certR := ett.series.certified targetR
  cases certR with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure => exact (Fin.succ_ne_zero r hrTarget).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hbad := currentKind.symm.trans (by simpa [hrTarget] using hkindr)
      simp at hbad
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hbad := currentKind.symm.trans (by simpa [hrTarget] using hkindr)
      simp at hbad
  | PE i previousProperR previousOneR previousClosedR previousNotStrongR
      noRevisitingR choiceR seriesAlternativeFailsR gammaR gammaRuleR
      secondStableR secondProperR secondOneR secondRelationR exitR
      currentColoringR currentProperR currentOneR currentStoredR currentEdgesR
      currentKindR currentVertexR currentOutsideR currentDeltaR currentGammaR
      closedExtensionR orderedExtensionR strictExtensionR =>
    have hi : i = r := by
      apply Fin.ext
      simpa using (congrArg Fin.val hrTarget).symm
    subst i
    have hvrChoice : choiceR.vertex = vr :=
      Option.some.inj (currentVertexR.symm.trans (by simpa [hrTarget] using hvertexr))
    subst vr
    generalize hnTarget : Fin.last ett.rounds = targetN
    have certN := ett.series.certified targetN
    cases certN with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        have hv := congrArg Fin.val hnTarget
        simp at hv
        omega
    | SE q previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hbad := currentKind.symm.trans (by simpa [hnTarget] using hkindn)
        simp at hbad
    | RE q previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        have hbad := currentKind.symm.trans (by simpa [hnTarget] using hkindn)
        simp at hbad
    | PE q previousProperN previousOneN previousClosedN previousNotStrongN
        noRevisitingN choiceN seriesAlternativeFailsN gammaN gammaRuleN
        secondStableN secondProperN secondOneN secondRelationN exitN
        currentColoringN currentProperN currentOneN currentStoredN currentEdgesN
        currentKindN currentVertexN currentOutsideN currentDeltaN currentGammaN
        closedExtensionN orderedExtensionN strictExtensionN =>
            exact @helper_branch_1399 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@hLowerOne)
                (@hLowerTwo) (@r) (@vn) (@hrEarlier) (@hkindn) (@hkindr) (@hvertexn) (@hvn)
                (@boundaryIncident) (@controlCarry) (@gammaR) (@secondStableR) (@secondProperR)
                (@secondOneR) (@previousProperR) (@previousOneR) (@previousClosedR) (@choiceR)
                (@gammaRuleR) (@secondRelationR) (@exitR) (@currentColoringR) (@currentProperR)
                (@currentOneR) (@currentStoredR) (@currentDeltaR) (@currentGammaR)
                (@orderedExtensionR) (@hrTarget) (@hvnvr) (@hvertexr) (@hvr) (@hfirst)
                (@stageToStage) (@q) (@choiceN) (@gammaN) (@gammaRuleN) (@secondStableN)
                (@secondRelationN) (@currentColoringN) (@currentProperN) (@currentStoredN)
                (@currentEdgesN) (@currentKindN) (@currentVertexN) (@currentDeltaN)
                (@currentGammaN) (@hnTarget)
end GoldbergSeymour

end
