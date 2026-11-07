/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.SharedFacts.StableChangeCasesOneTwoSplitTail

public import LeanPool.GoldbergSeymour.SharedFacts.ChangeLemmaBothOutsidePreparation1

public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePosition
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceComponentSwap
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# StableChangeCaseThree: supporting constructions, part 1

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.StableChangeCaseThreePreparation

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperPrefixMaximum1187Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (alpha beta : Fin k) (sigma : PartialEdgeColoring E k),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
   (∀ {S U W : TreeSequence G e0},
     TreeSequenceInitialSegment S W →
      TreeSequenceInitialSegment U W → S.length ≤ U.length → TreeSequenceInitialSegment S U) →
    (∀ {S U : TreeSequence G e0}, TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
     TreeSequenceInitialSegment Tn A →
      TreeSequenceInitialSegment A T →
       A.length < (↑ib : ℕ) →
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
           TashkinovAugmentationSequence phi Tn T ∨
          (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
           ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
             TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence phi seed T ∧ phi f ≠ some alpha ∧ phi f ≠ some beta) →
         ModColoring ett sigma →
          (∀ (S U : TreeSequence G e0),
            TashkinovAugmentationSequence phi S U →
             TreeSequenceInitialSegment U T →
              U.length ≤ (↑ib : ℕ) → TashkinovAugmentationSequence sigma S U) →
           A = Tn ∨
            ∃ (inputA : PartialEdgeColoring E k) (ettA :
             ExtendedTashkinovTree G k e0 inputA A sigma), MaximumProperty ettA

alias helper_equalTrees_536 :=
  SharedFacts.StableChangeCasesOneTwoSplitTail.equalTrees

theorem helper_terminalRoute_392.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (_ : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S W →
          TreeSequenceInitialSegment U W →
            S.length ≤ U.length → TreeSequenceInitialSegment S U) →
    (∀ (c : Fin k), c = alpha ∨ c = beta → c ∉ TreeMissingColors phi Tn ∪ Dn) →
    (∀ c ∈ ett.series.data.stored n, c ∈ TreeMissingColors phi Tn ∪ Dn) →
    ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi Tn T ∨
      (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = { f } ∧
            TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence phi seed T ∧
                phi f ≠ some alpha ∧ phi f ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta n Tn Dn commonPrefix notControlled
      storedOrMissing
  have step := ett.series.certified n
  generalize hi : n = i at step
  cases step with
  | initial => have hv := congrArg Fin.val hi; simp [n] at hv; have := C.positive; omega
  | SE j _ _ _ _ _ choice _ coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hroute : TashkinovAugmentationSequence phi seed
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      simpa [hj, hlast, ← ett.generatingColoring, n] using closure.1
    have hseedT : TreeSequenceInitialSegment seed T :=
      commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
        ett.belowFinal (by
          have hl := adjoin.1; rw [hj] at hl
          change seed.length = Tn.length + 1 at hl
          have hs := ett.strictAbovePenultimate
          change Tn.length < T.length at hs
          omega)
    have hcol : phi choice.edge = some choice.color := by
      have hg : phi = choice.selected := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      simpa only [hg] using choice.edgeColor
    have hc : choice.color ∈ ett.series.data.stored n := by rw [← hj, stored]; simp
    have hnot (c : Fin k) (he : c = alpha ∨ c = beta) : phi choice.edge ≠ some c := by
      intro hc'
      have heq := Option.some.inj (hcol.symm.trans hc')
      exact notControlled c he (heq ▸ storedOrMissing choice.color hc)
    exact Or.inr ⟨Or.inl (by simpa [hj] using kind), choice.edge, seed,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
      TashkinovAugmentationSequenceRestrict phi seed T _ hroute hseedT ett.belowFinal,
      hnot alpha (Or.inl rfl), hnot beta (Or.inr rfl)⟩
  | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
      edges kind vertex outside delta gammaEq closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    refine Or.inl ⟨by simpa [hj] using kind, ?_⟩
    apply TashkinovAugmentationSequenceRestrict phi Tn T _ _ ett.abovePenultimate ett.belowFinal
    simpa [Tn, hj, hlast, ← ett.generatingColoring, n] using closure.1
  | RE j _ _ _ _ available coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hroute : TashkinovAugmentationSequence phi seed
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      simpa [hj, hlast, ← ett.generatingColoring, n] using closure.1
    have hseedT : TreeSequenceInitialSegment seed T :=
      commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
        ett.belowFinal (by
          have hl := adjoin.1; rw [hj] at hl
          change seed.length = Tn.length + 1 at hl
          have hs := ett.strictAbovePenultimate
          change Tn.length < T.length at hs
          omega)
    have hcol : phi available.edge = some available.gamma ∨
        phi available.edge = some available.delta := by
      have hg : phi = ett.series.data.coloring j.castSucc := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      simp only [hg]
      have hadj := available.returnPath.adj_snd
        (SimpleGraph.Walk.not_nil_of_ne (by intro he; cases he))
      cases hh : available.returnPath.snd with
      | inl v =>
        have hc : (TwoColorIncidenceGraph G (ett.series.data.coloring j.castSucc)
            available.gamma available.delta).Adj (Sum.inr available.edge) (Sum.inl v) :=
          hh ▸ hadj
        exact hc.2
      | inr f =>
        have hc : (TwoColorIncidenceGraph G (ett.series.data.coloring j.castSucc)
            available.gamma available.delta).Adj (Sum.inr available.edge) (Sum.inr f) :=
          hh ▸ hadj
        exact False.elim hc
    have hcontrol : ∃ c, phi available.edge = some c ∧
        c ∈ TreeMissingColors phi Tn ∪ Dn := by
      rcases hcol with h | h
      · exact ⟨available.gamma, h, storedOrMissing _ (by rw [← hj, stored]; simp)⟩
      · exact ⟨available.delta, h, storedOrMissing _ (by rw [← hj, stored]; simp)⟩
    have hnot (c : Fin k) (he : c = alpha ∨ c = beta) : phi available.edge ≠ some c := by
      intro hc'
      obtain ⟨d, hd, hdmem⟩ := hcontrol
      have heq := Option.some.inj (hd.symm.trans hc')
      exact notControlled c he (heq ▸ hdmem)
    exact Or.inr ⟨Or.inr (by simpa [hj] using kind), available.edge, seed,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
      TashkinovAugmentationSequenceRestrict phi seed T _ hroute hseedT ett.belowFinal,
      hnot alpha (Or.inl rfl), hnot beta (Or.inr rfl)⟩

theorem helper_missingA_629.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (z : V ⊕ E) (sigma : PartialEdgeColoring E k),
    sigma = TwoColorComponentSwap G phi alpha beta z →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    alpha ∉ TreeMissingColors phi A →
    beta ∉ TreeMissingColors phi A →
    (have C : Set (V ⊕ E) := TwoColorComponent G phi alpha beta z;
      have phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta z;
      (∀ (v : V), Sum.inl v ∉ C → MissingColors G phi' v = MissingColors G phi v) ∧
        (∀ (v : V),
            Sum.inl v ∈ C → alpha ∈ MissingColors G phi v → beta ∈ MissingColors G phi' v) ∧
          (∀ (v : V),
              Sum.inl v ∈ C →
                beta ∈ MissingColors G phi v → alpha ∈ MissingColors G phi' v) ∧
            ∀ (v : V) (c : Fin k),
              c ≠ alpha →
                c ≠ beta → (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G phi v)) →
    (∀ (v : V) (c : Fin k),
        c ≠ alpha → c ≠ beta → (c ∈ MissingColors G sigma v ↔ c ∈ MissingColors G phi v)) →
    ∀ v ∈ TreeSequenceVertexSet A,
    MissingColors G sigma v = MissingColors G phi v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne z sigma hsigma H q A halphaA
      hbetaA behavior missingUnaffected v hv
  by_cases hvQ : Sum.inl v ∈ TwoColorComponent G phi alpha beta z
  · have han : alpha ∉ MissingColors G phi v := fun hc =>
      halphaA (Finset.mem_biUnion.mpr ⟨v, hv, hc⟩)
    have hbn : beta ∉ MissingColors G phi v := fun hc =>
      hbetaA (Finset.mem_biUnion.mpr ⟨v, hv, hc⟩)
    have hpa : ∃ f, Incident G v f ∧ phi f = some alpha := by
      simpa [MissingColors, PresentColors] using han
    have hpb : ∃ f, Incident G v f ∧ phi f = some beta := by
      simpa [MissingColors, PresentColors] using hbn
    obtain ⟨fa, hfa, hfca⟩ := hpa
    obtain ⟨fb, hfb, hfcb⟩ := hpb
    have edgeOfVertex {f : E} (hf : Incident G v f)
        (hc : phi f = some alpha ∨ phi f = some beta) :
        Sum.inr f ∈ TwoColorComponent G phi alpha beta z := by
      have hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inr f) (Sum.inl v) :=
        ⟨hf, hc⟩
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hvQ
    have hnewa : sigma fb = some alpha := by
      rw [hsigma]
      simp [TwoColorComponentSwap, edgeOfVertex hfb (Or.inr hfcb), hfcb, hne.symm]
    have hnewb : sigma fa = some beta := by
      rw [hsigma]
      simp [TwoColorComponentSwap, edgeOfVertex hfa (Or.inl hfca), hfca]
    have hana : alpha ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
        PresentColors, Finset.mem_filter, not_not]
      exact ⟨fb, hfb, hnewa⟩
    have hbnb : beta ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
        PresentColors, Finset.mem_filter, not_not]
      exact ⟨fa, hfa, hnewb⟩
    ext c
    by_cases hca : c = alpha
    · subst c; simp [hana, han]
    · by_cases hcb : c = beta
      · subst c; simp [hbnb, hbn]
      · exact missingUnaffected v c hca hcb
  · rw [hsigma]
    exact behavior.1 v hvQ

theorem helper_fullBase_847.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (beta : Fin k) (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ell : ℕ := T.length - A.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        have this_1 : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction
          fun (a : ¬(1 : ℕ) ≤ min (A.length + (ell - (1 : ℕ))) T.length) ↦ by omega)
        (Nat.min_le_right (A.length + (ell - (1 : ℕ))) T.length);
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE →
        CombinedStableColoring Tn base.closure Dn phi sigma) →
    ModColoring ett sigma →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn T ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = { f } ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence sigma seed T) →
    (∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
        corr.replacementETT.series.data.tree
              (Fin.last corr.replacementETT.rounds).castSucc =
            Tn ∧
          corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
              ett.series.data.kind n ∧
            TashkinovStoredColors corr.replacementETT.series.data
                (Fin.last corr.replacementETT.rounds) =
              Dn) →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    MaximumProperty corr.replacementETT ∧
    ∃ (baseT : HierarchyBase corr.replacementETT sigma),
    baseT.core = base.core ∧
    baseT.closure = base.closure := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower beta sigma H q A n Tn Dn
      ell Y hb sigmaProper sigmaOne combined hmod sigmaRoute corrData
  by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · have hb : TashkinovAugmentationSequence sigma Tn T := by
      rcases sigmaRoute with ⟨_, hseq⟩ | ⟨hk, rest⟩
      · exact hseq
      · rcases hk with hk | hk <;> rw [hp] at hk <;> cases hk
    obtain ⟨corr, hMP, baseT, K0, hsame⟩ := HierarchySplitter G k e0 input T phi sigma
      ett C.maximum C.positive hlower base H hp hproper hone sigmaProper sigmaOne (combined hp) hb
    exact ⟨corr, hMP, baseT, hsame.1.symm, (hsame.2.2.2.2.2 hp).symm⟩
  · obtain ⟨corr⟩ := hmod.2.2 T ett.abovePenultimate ett.strictAbovePenultimate sigmaRoute
    have hd := corrData corr
    let pos : Fin ((corr.replacementETT.series.data.tree
        (Fin.last corr.replacementETT.rounds).castSucc).length + 1) :=
      Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1) hd.1.symm)
        base.supportPosition
    let baseT : HierarchyBase corr.replacementETT sigma := {
      core := base.core
      closure := base.closure
      supportPosition := pos
      supportPositive := by simpa [pos] using base.supportPositive
      terminalMissingColors := rfl
      parallel := by
        dsimp only
        intro hPE
        exact False.elim (hp (hd.2.1.symm.trans hPE))
      nonparallel := by
        dsimp only
        intro _
        exact (base.nonparallel hp).trans hd.1.symm }
    exact ⟨corr, MaximumPropertyTransport G k e0 ett sigma hmod T corr C.maximum,
      baseT, rfl, rfl⟩

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_segTrans_511.{u_1, u_2} :
    SharedFacts.ChangeLemmaBothOutsidePreparation1.initialSegmentTransitiveStatement.{u_1, u_2} :=
  SharedFacts.ChangeLemmaBothOutsidePreparation1.initialSegmentTransitive.{u_1, u_2}

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_commonPrefix_520.{u_1, u_2} :
    SharedFacts.ChangeLemmaBothOutsidePreparation1.comparableInitialSegmentsStatement.{u_1, u_2} :=
  SharedFacts.ChangeLemmaBothOutsidePreparation1.comparableInitialSegments.{u_1, u_2}

alias helper_stageToT_552 :=
  SharedFacts.ChangeLemmaBothOutsidePreparation1.ordinaryStageInitialSegmentOfTerminal

alias helper_lastPositive_561 :=
  SharedFacts.ChangeLemmaBothOutsidePreparation1.lastStarredStageOfPositiveCount

theorem helper_coreToA_572.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage
            (⟨a, by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))
          (H.stage
            (⟨a + d, by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    (H.dividerCount ≠ (0 : ℕ) →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    TreeSequenceInitialSegment base.core A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A segRefl segTrans stageSegment lastZero
      lastPositive
  by_cases hz : H.dividerCount = 0
  · rw [lastZero hz]; exact segRefl _
  · rw [lastPositive hz]
    have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
    have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
    simpa [he] using segTrans H.coreInsideFirst hs

theorem helper_ordinaryToA_589.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage
            (⟨a, by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))
          (H.stage
            (⟨a + d, by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))) →
    (H.dividerCount ≠ (0 : ℕ) →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    TreeSequenceInitialSegment Tn A →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (H.stage j.castSucc) A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A n Tn stageSegment lastPositive TnToA j
  by_cases hz : H.dividerCount = 0
  · have hj : j.castSucc = (0 : Fin (H.dividerCount + 2)) := Fin.ext (by simp; omega)
    rw [hj, H.baseStage]; exact TnToA
  · have hs := stageSegment j.val (H.dividerCount - j.val) (by omega)
    rw [lastPositive hz]
    convert hs using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;>
      simp only [Fin.val_castSucc]; omega

theorem helper_firstMissing_607.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        have this_1 : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction
          fun (a : ¬(1 : ℕ) ≤ min (A.length + (ell - (1 : ℕ))) T.length) ↦ by omega)
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive A
          omega);
    TreeSequenceInitialSegment Y T →
    ∀ c ∈ TreeMissingColors phi Y,
    c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
    (↑(HierarchyFirstMissingPosition phi T c) : ℕ) ≤ Y.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A ell Y YToT c hc
  exact TreeSequenceFirstMissingPositionPrefixWitness YToT hc

theorem helper_firstLe_627.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
    c ∈ MissingColors G phi (T.vertex i) →
    (↑(HierarchyFirstMissingPosition phi T c) : ℕ) ≤ (↑i : ℕ) := by
  classical
  intro V E _ G k e0 T phi c i hc
  exact TreeSequenceFirstMissingPositionLe hc

theorem helper_hout_642.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
      ∀ u ∈ TreeSequenceVertexSet A, TreeVertexOrder T u va) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let va : V := T.vertex ia;
    let vb : V := T.vertex ib;
    (↑ia : ℕ) < (↑ib : ℕ) →
    va ∉ TreeSequenceVertexSet A ∧
    vb ∉ TreeSequenceVertexSet A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hAprecedes H q A ia ib va vb habIndex
  constructor
  · intro hv
    obtain ⟨i, j, hi, hj, hij⟩ := hAprecedes va hv
    have he := T.vertex_injective (hi.trans hj.symm)
    have hv := congrArg Fin.val he
    omega
  · intro hv
    obtain ⟨i, j, hi, hj, hij⟩ := hAprecedes vb hv
    have hei := T.vertex_injective hi
    have hej := T.vertex_injective hj
    have hvi := congrArg Fin.val hei
    have hvj := congrArg Fin.val hej
    change i.val = ib.val at hvi
    change j.val = ia.val at hvj
    omega

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_outsideIndex_658.{u_1, u_2} :
    SharedFacts.ChangeLemmaBothOutsidePreparation1.missingPositionOutsidePrefixStatement.{u_1,
        u_2} :=
  SharedFacts.ChangeLemmaBothOutsidePreparation1.missingPositionOutsidePrefix.{u_1, u_2}

alias helper_missingNotA_674 :=
  SharedFacts.ChangeLemmaBothOutsidePreparation1.missingColorOutsideStarredPrefix

theorem helper_hDn_690.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
      alpha ∉ Dnq ∧ beta ∉ Dnq) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    alpha ∉ TreeMissingColors phi A →
    beta ∉ TreeMissingColors phi A →
    alpha ∉ Dn ∧
    beta ∉ Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hnotStored H q A n Dn halphaA hbetaA
  constructor
  · intro hc
    exact hnotStored.1 (Finset.mem_sdiff.mpr ⟨hc, halphaA⟩)
  · intro hc
    exact hnotStored.2 (Finset.mem_sdiff.mpr ⟨hc, hbetaA⟩)

theorem helper_storedOrMissing_706.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (_ : HierarchyCounterexample base)
      (_ _ : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    ∀ c ∈ ett.series.data.stored n,
    c ∈ TreeMissingColors phi Tn ∪ Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta n Tn Dn c hc
  by_cases hm : c ∈ TreeMissingColors phi Tn
  · exact Finset.mem_union_left _ hm
  · apply Finset.mem_union_right
    unfold Dn TashkinovStoredColors
    have hn : n.val ≠ 0 := by dsimp [n]; have := C.positive; omega
    simp only [ite_eq_right hn]
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_univ _, by simp [hc]⟩
    · have hg : ett.series.data.coloring n = phi := ett.generatingColoring.symm
      simpa only [hg, Tn] using hm

theorem helper_treeControlled_729.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (_ : HierarchyCounterexample base),
    IsOneEdgeUncolored phi e0 →
    ∀ (alpha beta : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    (∀ (c : Fin k), c = alpha ∨ c = beta → c ∉ TreeMissingColors phi Tn ∪ Dn) →
    ∀ (t : Fin Tn.length),
    phi (Tn.edge t) ≠ some alpha ∧
    phi (Tn.edge t) ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hone alpha beta n Tn Dn notControlled t
  by_cases ht : t.val = 0
  · have he : Tn.edge t = e0 := by
      rw [show t = ⟨0, Tn.positive⟩ from Fin.ext ht]; exact Tn.first_edge
    simp [he, hone.1]
  · let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
    have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
    have hused (c : Fin k) (hc : phi (Tn.edge t) = some c) :
        c ∈ TreeMissingColors phi Tn ∪ Dn := by
      have hu : c ∈ TreeUsedColors (ett.series.data.coloring j.succ)
          (ett.series.data.tree j.succ.castSucc) := by
        simp only [hj, ← ett.generatingColoring, n]
        simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨t, by omega, hc⟩
      simpa [hj, ← ett.generatingColoring, Tn, Dn, n] using
        (HkuTreeColorsControlled G k ett.rounds e0 input ett.series j).2.1 hu
    exact ⟨fun hc => notControlled alpha (Or.inl rfl) (hused alpha hc),
      fun hc => notControlled beta (Or.inr rfl) (hused beta hc)⟩

theorem helper_augmentationControlled_748.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (_ : HierarchyCounterexample base)
      (alpha beta : Fin k),
    (let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      alpha ∉
        ({c : Fin k |
            ∃ (t : Fin T.length),
              (↑ia : ℕ) ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑ib : ℕ) ∧ phi (T.edge t) = some c} :
          Finset (Fin k))) →
    let _ : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    (∀ (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
        c ∈ MissingColors G phi (T.vertex i) →
          (↑(HierarchyFirstMissingPosition phi T c) : ℕ) ≤ (↑i : ℕ)) →
    ∀ (S : TreeSequence G e0),
    TashkinovAugmentationSequence phi S T →
    ∀ (t : Fin T.length),
    S.length ≤ (↑t : ℕ) →
    (↑t : ℕ) < (↑ib : ℕ) →
    phi (T.edge t) ≠ some alpha ∧
    phi (T.edge t) ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hunused ia ib firstLe S hseq t ht htb
  have hstep := (TashkinovAugmentationSequencePosition phi S T hseq t ht).1
  obtain ⟨hl, hinit, c, hcol, hm⟩ := hstep
  have hcolT : phi (T.edge t) = some c := by
    convert hcol using 1; congr 2
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
  obtain ⟨iv, hiv⟩ := hv
  let ivT : Fin (T.length + 1) := ⟨iv.val, by
    have := iv.isLt; change iv.val < t.val + 1 at this; omega⟩
  have hcvT : c ∈ MissingColors G phi (T.vertex ivT) := by
    have he : (TreeSequencePrefix T t.val (le_trans S.positive ht)
        (Nat.le_of_lt t.isLt)).vertex iv = T.vertex ivT := rfl
    rw [← he, hiv]; exact hcv
  have hiv : ivT.val ≤ t.val := Nat.le_of_lt_succ iv.isLt
  have hnotAlpha : c ≠ alpha := by
    intro he; subst c
    by_cases hta : t.val < ia.val
    · have hle := firstLe alpha ivT hcvT
      change ia.val ≤ ivT.val at hle
      omega
    · apply hunused
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, by omega, htb, hcolT⟩
  have hnotBeta : c ≠ beta := by
    intro he; subst c
    have hle := firstLe beta ivT hcvT
    change ib.val ≤ ivT.val at hle
    omega
  exact ⟨fun he => hnotAlpha (Option.some.inj (hcolT.symm.trans he)),
    fun he => hnotBeta (Option.some.inj (hcolT.symm.trans he))⟩

theorem helper_prefixControlled_781.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (_ : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn T ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed T ∧
                  phi f ≠ some alpha ∧ phi f ≠ some beta) →
    (∀ (t : Fin Tn.length), phi (Tn.edge t) ≠ some alpha ∧ phi (Tn.edge t) ≠ some beta) →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S T →
          ∀ (t : Fin T.length),
            S.length ≤ (↑t : ℕ) →
              (↑t : ℕ) < (↑ib : ℕ) →
                phi (T.edge t) ≠ some alpha ∧ phi (T.edge t) ≠ some beta) →
    ∀ (t : Fin T.length),
    (↑t : ℕ) < (↑ib : ℕ) →
    phi (T.edge t) ≠ some alpha ∧
    phi (T.edge t) ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta n Tn ib terminalRoute treeControlled
      augmentationControlled t htb
  by_cases htn : t.val < Tn.length
  · let tn : Fin Tn.length := ⟨t.val, htn⟩
    have he : Fin.castLE ett.abovePenultimate.1 tn = t := Fin.ext rfl
    rw [← he, ett.abovePenultimate.2.2 tn]
    exact treeControlled tn
  · rcases terminalRoute with ⟨hkind, hseq⟩ | ⟨hkind, f, seed, hedges, hseed, hseq, hfa, hfb⟩
    · exact augmentationControlled Tn hseq t (by omega) htb
    · by_cases htseed : t.val < seed.length
      · have ht : t.val = Tn.length := by have := hseed.1; omega
        have hs := TashkinovAugmentationSequenceInitialSegment phi seed T hseq
        let ts : Fin seed.length := ⟨t.val, htseed⟩
        have he : Fin.castLE hs.1 ts = t := Fin.ext rfl
        rw [← he, hs.2.2 ts]
        have hlast : ts = Fin.cast hseed.1.symm (Fin.last Tn.length) := Fin.ext ht
        rw [hlast, hseed.2.2]
        exact ⟨hfa, hfb⟩
      · exact augmentationControlled seed hseq t (by omega) htb

theorem helper_horderedUnused_800.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    (let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
      let vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
      TreeVertexOrder T va vb) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let va : V := T.vertex ia;
    let vb : V := T.vertex ib;
    (∀ (t : Fin T.length),
        (↑t : ℕ) < (↑ib : ℕ) → phi (T.edge t) ≠ some alpha ∧ phi (T.edge t) ≠ some beta) →
    alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A →
    TreeVertexOrder T va vb ∧
    alpha ∉
      ({c : Fin k |
          ∃ (t : Fin T.length),
            A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑ib : ℕ) ∧ phi (T.edge t) = some c} :
        Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hordered H q A ia ib va vb
      prefixControlled _
  refine ⟨hordered, ?_⟩
  intro hc
  obtain ⟨_, t, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hc
  exact (prefixControlled t hhi).1 hcol

theorem helper_unaffected_835.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
          PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k),
      alpha ≠ beta →
        ∀ (z : V ⊕ E) (sigma : PartialEdgeColoring E k),
          sigma = TwoColorComponentSwap G phi alpha beta z →
            let H : TashkinovHierarchy ett base := C.hierarchy;
            let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
            let A : TreeSequence G e0 := HierarchyStarredStage H q;
            let ell : ℕ := T.length - A.length;
            let Y : TreeSequence G e0 :=
              TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
                (have this : (1 : ℕ) ≤ A.length := A.positive;
                have this_1 : (1 : ℕ) ≤ T.length := T.positive;
                Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min (A.length + (ell - (1 : ℕ)))
                    T.length) ↦ by omega)
                (by
                  have := GoldbergSeymour.TreeSequence.positive T
                  have := GoldbergSeymour.TreeSequence.positive A
                  omega);
            alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
                (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
              beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
                  (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
                ∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)
                   := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne z sigma hsigma H q A ell Y ha hb
      f c hca hcb
  rw [hsigma]
  by_cases hf : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
  · by_cases ha : phi f = some alpha
    · simp [TwoColorComponentSwap, hf, ha, hca.symm, hcb.symm]
    · by_cases hb : phi f = some beta
      · simp [TwoColorComponentSwap, hf, hb, hne.symm, hca.symm, hcb.symm]
      · simp [TwoColorComponentSwap, hf, ha, hb]
  · simp [TwoColorComponentSwap, hf]

theorem helper_sigmaOne_852.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsOneEdgeUncolored phi e0 →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (z : V ⊕ E) (sigma : PartialEdgeColoring E k),
    sigma = TwoColorComponentSwap G phi alpha beta z →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        have this_1 : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction
          fun (a : ¬(1 : ℕ) ≤ min (A.length + (ell - (1 : ℕ))) T.length) ↦ by omega)
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive A
          omega);
    alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
        (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    (∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
    IsOneEdgeUncolored sigma e0 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hone alpha beta hne z sigma hsigma H q A ell Y
      ha hb unaffected
  refine ⟨?_, ?_⟩
  · rw [hsigma]; simp [TwoColorComponentSwap, hone.1]
  · intro f hf
    obtain ⟨c, hc⟩ := hone.2 f hf
    by_cases ha : c = alpha
    · subst c
      by_cases hQ : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
      · exact ⟨beta, by rw [hsigma]; simp [TwoColorComponentSwap, hQ, hc]⟩
      · exact ⟨alpha, by rw [hsigma]; simp [TwoColorComponentSwap, hQ, hc]⟩
    · by_cases hb : c = beta
      · subst c
        by_cases hQ : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
        · exact ⟨alpha, by rw [hsigma]; simp [TwoColorComponentSwap, hQ, hc, hne.symm]⟩
        · exact ⟨beta, by rw [hsigma]; simp [TwoColorComponentSwap, hQ, hc]⟩
      · exact ⟨c, (unaffected f c ha hb).mpr hc⟩

theorem helper_stable_876.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    alpha ∉ TreeMissingColors phi A →
    beta ∉ TreeMissingColors phi A →
    (∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    ∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
    ∀ (D : Finset (Fin k)),
    alpha ∉ D ∧ beta ∉ D →
    StableColoring S D phi sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma H q A halphaA hbetaA
      unaffected missingA S hS D hD
  refine ⟨?_, fun v hv => missingA v (hS hv)⟩
  intro f hf hcontrol
  obtain ⟨c, hc, hcol⟩ := hcontrol
  have hnot (d : Fin k) (hdA : d ∉ TreeMissingColors phi A) (hdD : d ∉ D) : c ≠ d := by
    intro he; subst c
    rcases Finset.mem_union.mp hc with hm | hm
    · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
      exact hdA (Finset.mem_biUnion.mpr ⟨v, hS hv, hcv⟩)
    · exact hdD hm
  exact ((unaffected f c (hnot alpha halphaA hD.1)
    (hnot beta hbetaA hD.2)).mpr hcol).trans hcol.symm

theorem helper_closureInsideA_893.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    TreeSequenceInitialSegment base.core A →
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
    TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A n coreToA hPE
  have ordered := Classical.choice (base.parallel hPE).2.2
  intro v hv
  apply TreeSequenceInitialSegmentVertexSetSubset coreToA
  rw [ordered.vertexSet]
  exact Finset.mem_union_right _ hv

theorem helper_invariant_903.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    TreeSequenceInitialSegment A T →
    (↑ia : ℕ) < (↑ib : ℕ) →
    A.length < (↑ia : ℕ) →
    (∀ (t : Fin T.length),
        (↑t : ℕ) < (↑ib : ℕ) → phi (T.edge t) ≠ some alpha ∧ phi (T.edge t) ≠ some beta) →
    (∀ (f : E), phi f ≠ some alpha → phi f ≠ some beta → sigma f = phi f) →
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    ∀ (S : TreeSequence G e0),
    TreeSequenceInitialSegment S A →
    TreeColoringInvariant S phi sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma H q A ia ib segTrans AToT
      habIndex hAia prefixControlled fixedValue missingA S hSA
  refine ⟨?_, fun v hv => missingA v (TreeSequenceInitialSegmentVertexSetSubset hSA hv)⟩
  intro t ht
  have hST := segTrans hSA AToT
  have hc := prefixControlled (Fin.castLE hST.1 t) (by
    have := t.isLt; have := hSA.1; simp only [Fin.val_castLE]; omega)
  rw [hST.2.2 t] at hc
  exact fixedValue _ hc.1 hc.2

theorem helper_weak_912.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (H.stage j.castSucc) A) →
    StableColoring Tn Dn phi sigma →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE →
        CombinedStableColoring Tn base.closure Dn phi sigma) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceInitialSegment S A → TreeColoringInvariant S phi sigma) →
    HierarchyWeaklyStable H q sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A n Tn Dn ordinaryToA stableTn
      combined invariant
  have bs : (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure Dn phi sigma else StableColoring Tn Dn phi sigma) := by
    split
    · rename_i hp; exact combined hp
    · exact stableTn
  have allWeak (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma := by
    refine Fin.cases bs (fun i => ⟨bs, invariant _ (ordinaryToA i.succ)⟩) j
  exact allWeak q

theorem helper_together_938.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (z : V ⊕ E),
      let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let va : V := T.vertex ia;
      let vb : V := T.vertex ib;
      TwoColorComponent G phi alpha beta (Sum.inl va) = TwoColorComponent G phi alpha beta
          (Sum.inl vb) →
        (Sum.inl va ∈ TwoColorComponent G phi alpha beta z ↔ Sum.inl vb ∈ TwoColorComponent G phi
            alpha beta z) := by
  classical
  intro V E _ _ G k e0 T phi alpha beta z ia ib va vb sameComponent
  let _ := Fintype.ofFinite V
  have hab : Sum.inl va ∈ TwoColorComponent G phi alpha beta (Sum.inl vb) := by
    rw [← sameComponent]; exact rfl
  change (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk (Sum.inl va) =
    (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk (Sum.inl vb) at hab
  change (_ = _) ↔ (_ = _)
  rw [hab]

theorem helper_bothMissingB_946.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (z : V ⊕ E) (sigma : PartialEdgeColoring E k),
    sigma = TwoColorComponentSwap G phi alpha beta z →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
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
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive A
          omega);
    alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
        (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    (have C : Set (V ⊕ E) := TwoColorComponent G phi alpha beta z;
      have phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta z;
      (∀ (v : V), Sum.inl v ∉ C → MissingColors G phi' v = MissingColors G phi v) ∧
        (∀ (v : V),
            Sum.inl v ∈ C → alpha ∈ MissingColors G phi v → beta ∈ MissingColors G phi' v) ∧
          (∀ (v : V),
              Sum.inl v ∈ C →
                beta ∈ MissingColors G phi v → alpha ∈ MissingColors G phi' v) ∧
            ∀ (v : V) (c : Fin k),
              c ≠ alpha →
                c ≠ beta → (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G phi v)) →
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    va ∈ TreeSequenceVertexSet B →
    vb ∈ TreeSequenceVertexSet B →
    (Sum.inl va ∈ TwoColorComponent G phi alpha beta z ↔
        Sum.inl vb ∈ TwoColorComponent G phi alpha beta z) →
    alpha ∈ TreeMissingColors sigma B ∧
    beta ∈ TreeMissingColors sigma B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta z sigma hsigma H q A ia ib va vb ell
      Y ha hb hAib behavior B haB hbB together
  by_cases hva : Sum.inl va ∈ TwoColorComponent G phi alpha beta z
  · have hvb := together.mp hva
    constructor
    · exact Finset.mem_biUnion.mpr ⟨vb, hbB, by
        rw [hsigma]; exact behavior.2.2.1 vb hvb hb.1⟩
    · exact Finset.mem_biUnion.mpr ⟨va, haB, by
        rw [hsigma]; exact behavior.2.1 va hva ha.1⟩
  · have hvb : Sum.inl vb ∉ TwoColorComponent G phi alpha beta z := fun h => hva (together.mpr h)
    constructor
    · exact Finset.mem_biUnion.mpr ⟨va, haB, by rw [hsigma, behavior.1 va hva]; exact ha.1⟩
    · exact Finset.mem_biUnion.mpr ⟨vb, hbB, by rw [hsigma, behavior.1 vb hvb]; exact hb.1⟩

theorem helper_transportBefore_958.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (_ : HierarchyCounterexample base) (alpha beta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    (∀ (t : Fin T.length),
        (↑t : ℕ) < (↑ib : ℕ) → phi (T.edge t) ≠ some alpha ∧ phi (T.edge t) ≠ some beta) →
    (∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
    (∀ (v : V) (c : Fin k),
        c ≠ alpha → c ≠ beta → (c ∈ MissingColors G sigma v ↔ c ∈ MissingColors G phi v)) →
    ∀ (S U : TreeSequence G e0),
    TashkinovAugmentationSequence phi S U →
    TreeSequenceInitialSegment U T →
    U.length ≤ (↑ib : ℕ) →
    TashkinovAugmentationSequence sigma S U := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma ib segTrans prefixControlled
      unaffected missingUnaffected S U hseq hUT hU
  unfold TashkinovAugmentationSequence at hseq ⊢
  induction hseq with
  | refl => exact Relation.ReflTransGen.refl
  | @tail U W hSU hUW ih =>
    have hlen := hUW.1
    have hinit := hUW.2.1
    obtain ⟨c, hcol, hm⟩ := hUW.2.2
    let t := Fin.cast hlen.symm (Fin.last U.length)
    let tt := Fin.castLE hUT.1 t
    have hct := prefixControlled tt (by
      change U.length < ib.val; have := hU; omega)
    rw [hUT.2.2 t] at hct
    have hca : c ≠ alpha := by intro he; subst c; exact hct.1 hcol
    have hcb : c ≠ beta := by intro he; subst c; exact hct.2 hcol
    have hm' : c ∈ TreeMissingColors sigma U := by
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
      exact Finset.mem_biUnion.mpr ⟨v, hv, (missingUnaffected v c hca hcb).mpr hcv⟩
    exact Relation.ReflTransGen.tail (ih (segTrans hinit hUT) (by omega))
      ⟨hlen, hinit, c, (unaffected _ c hca hcb).mpr hcol, hm'⟩

theorem helper_transportRoute_981.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (z : V ⊕ E) (sigma : PartialEdgeColoring E k),
    sigma = TwoColorComponentSwap G phi alpha beta z →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    TreeSequenceInitialSegment B T →
    alpha ∈ TreeMissingColors sigma B ∧ beta ∈ TreeMissingColors sigma B →
    (∀ (S U : TreeSequence G e0),
        TashkinovAugmentationSequence phi S U →
          TreeSequenceInitialSegment U T →
            U.length ≤ (↑ib : ℕ) → TashkinovAugmentationSequence sigma S U) →
    ∀ (S : TreeSequence G e0),
    TashkinovAugmentationSequence phi S T →
    TreeSequenceInitialSegment S B →
    TashkinovAugmentationSequence sigma S T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne z sigma hsigma H q A ib hAib B
      BToT bothMissingB transportBefore S hseq hSB
  have hpre := TashkinovAugmentationSequenceRestrict phi S B T hseq hSB BToT
  have hsuf := TashkinovAugmentationSequenceSuffix phi S B T hseq hSB BToT
  have hpreSigma := transportBefore S B hpre BToT le_rfl
  have hsufSigma : TashkinovAugmentationSequence sigma B T := by
    rw [hsigma] at bothMissingB ⊢
    exact TashkinovAugmentationSequenceComponentSwap G k e0 phi alpha beta hne z
      B T hsuf bothMissingB.1 bothMissingB.2
  exact hpreSigma.trans hsufSigma

theorem helper_sigmaRoute_993.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S W →
          TreeSequenceInitialSegment U W →
            S.length ≤ U.length → TreeSequenceInitialSegment S U) →
    TreeSequenceInitialSegment Tn A →
    (↑ia : ℕ) < (↑ib : ℕ) →
    A.length < (↑ia : ℕ) →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn T ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed T ∧
                  phi f ≠ some alpha ∧ phi f ≠ some beta) →
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    TreeSequenceInitialSegment B T →
    TreeSequenceInitialSegment A B →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S T →
          TreeSequenceInitialSegment S B → TashkinovAugmentationSequence sigma S T) →
    ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T ∨
      (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
            TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma H q A n Tn ia ib segTrans
      commonPrefix TnToA habIndex hAia hAib terminalRoute B BToT AToB transportRoute
  rcases terminalRoute with ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hseq, hfa, hfb⟩
  · exact Or.inl ⟨hp, transportRoute Tn hseq (segTrans TnToA AToB)⟩
  · have hseedB : TreeSequenceInitialSegment seed B :=
      commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hseq) BToT
        (by have := hseed.1; have := TnToA.1; change _ ≤ ib.val; omega)
    exact Or.inr ⟨hp, f, seed, hedges, hseed, transportRoute seed hseq hseedB⟩

theorem helper_stageMissingEq_1044.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E]
      [inst_2 : DecidableEq V] [inst_3 : DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    TreeSequenceInitialSegment Tn A →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (H.stage j.castSucc) A) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
      (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core)
      (terminalData :
        corrT.replacementETT.series.data.tree
              (Fin.last corrT.replacementETT.rounds).castSucc =
            Tn ∧
          corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
              ett.series.data.kind n ∧
            TashkinovStoredColors corrT.replacementETT.series.data
                (Fin.last corrT.replacementETT.rounds) =
              Dn),
    let K : TashkinovHierarchy corrT.replacementETT baseT :=
      { dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst :
        TashkinovHierarchy corrT.replacementETT baseT };
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A n Tn Dn TnToA ordinaryToA
      treeMissingEq corrT baseT hcoreT terminalData K j
  refine Fin.cases ?_ (fun a => ?_) j
  · change TreeMissingColors sigma
      (corrT.replacementETT.series.data.tree
        (Fin.last corrT.replacementETT.rounds).castSucc) = TreeMissingColors phi Tn
    rw [terminalData.1]
    exact treeMissingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA)
  · exact treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA a.succ))

theorem helper_firstEq_1065.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
      (sigma : PartialEdgeColoring E k),
    (∀ (v : V) (c : Fin k),
        c ≠ alpha → c ≠ beta → (c ∈ MissingColors G sigma v ↔ c ∈ MissingColors G phi v)) →
    ∀ (c : Fin k),
    c ≠ alpha →
    c ≠ beta →
    HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition phi T c := by
  classical
  intro V E _ G k e0 T phi alpha beta sigma missingUnaffected c hca hcb
  exact TreeSequenceFirstMissingPositionMembershipCongr
    (fun index => missingUnaffected (T.vertex index) c hca hcb)

theorem helper_segmentTransfer_1077.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E]
      [inst_2 : DecidableEq V] [inst_3 : DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    (∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
    ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
      (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core)
      (terminalData :
        corrT.replacementETT.series.data.tree
              (Fin.last corrT.replacementETT.rounds).castSucc =
            Tn ∧
          corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
              ett.series.data.kind n ∧
            TashkinovStoredColors corrT.replacementETT.series.data
                (Fin.last corrT.replacementETT.rounds) =
              Dn),
    let K : TashkinovHierarchy corrT.replacementETT baseT :=
      { dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst :
        TashkinovHierarchy corrT.replacementETT baseT };
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        HierarchyStarredStage K j = HierarchyStarredStage H j) →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        ∀ eta ∈ HierarchyStoredColorsAt H j, eta ≠ alpha ∧ eta ≠ beta) →
    (∀ (c : Fin k),
        c ≠ alpha →
          c ≠ beta →
            HierarchyFirstMissingPosition sigma T c =
              HierarchyFirstMissingPosition phi T c) →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    ∀ eta ∈ HierarchyStoredColorsAt H j,
    ∀ (c : Fin k),
    c ≠ alpha →
    c ≠ beta →
    c ∈ HierarchySegmentColors K j eta →
    c ∈ HierarchySegmentColors H j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma H n Tn Dn unaffected corrT
      baseT hcoreT terminalData K starredEq ownerNot firstEq j eta heta c hca hcb hc
  unfold HierarchySegmentColors at hc ⊢
  dsimp only at hc ⊢
  rw [starredEq j, firstEq eta (ownerNot j eta heta).1 (ownerNot j eta heta).2] at hc
  obtain ⟨_, t, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hc
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo, hhi,
    (unaffected _ c hca hcb).mp hcol⟩

theorem helper_minusEq_1094.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    alpha ∉ TreeMissingColors phi A →
    beta ∉ TreeMissingColors phi A →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    (∀ (S : TreeSequence G e0) (c : Fin k),
        c ≠ alpha →
          c ≠ beta →
            BoundaryColorEdges G sigma (TreeSequenceVertexSet S) c =
              BoundaryColorEdges G phi (TreeSequenceVertexSet S) c) →
    ∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
    ∀ (R : Finset (Fin k)),
    TreeColorSetMinusClosed G sigma S R ↔ TreeColorSetMinusClosed G phi S R := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma H q A halphaA hbetaA
      treeMissingEq boundaryEq S hS R
  unfold TreeColorSetMinusClosed TreeColorSetClosed
  rw [treeMissingEq S hS]
  have hnot (c : Fin k) (hc : c ∈ TreeMissingColors phi S) : c ≠ alpha ∧ c ≠ beta := by
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    have hm := Finset.mem_biUnion.mpr ⟨v, hS hv, hcv⟩
    exact ⟨fun he => halphaA (he ▸ hm), fun he => hbetaA (he ▸ hm)⟩
  constructor <;> intro h c hc
  · have hh := h c hc
    rw [boundaryEq S c (hnot c (Finset.mem_sdiff.mp hc).1).1
      (hnot c (Finset.mem_sdiff.mp hc).1).2] at hh
    exact hh
  · rw [boundaryEq S c (hnot c (Finset.mem_sdiff.mp hc).1).1
      (hnot c (Finset.mem_sdiff.mp hc).1).2]
    exact h c hc

theorem helper_branch_1161.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E]
      [inst_2 : DecidableEq V] [inst_3 : DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    TreeSequenceInitialSegment base.core A →
    ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
      (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core)
      (terminalData :
        corrT.replacementETT.series.data.tree
              (Fin.last corrT.replacementETT.rounds).castSucc =
            Tn ∧
          corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
              ett.series.data.kind n ∧
            TashkinovStoredColors corrT.replacementETT.series.data
                (Fin.last corrT.replacementETT.rounds) =
              Dn),
    let K : TashkinovHierarchy corrT.replacementETT baseT :=
      { dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst :
        TashkinovHierarchy corrT.replacementETT baseT };
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          ∀ (R : Finset (Fin k)),
            TreeColorSetMinusClosed G sigma S R ↔ TreeColorSetMinusClosed G phi S R) →
    ¬TreeColorSetMinusClosed G phi base.core
          ((HierarchyStoredColorsAt C.hierarchy
                (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ)))).biUnion
            (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))) →
    ¬TreeColorSetMinusClosed G sigma baseT.core
        ((HierarchyStoredColorsAt K (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
          (C.good.gamma (0 : Fin (K.dividerCount + (1 : ℕ))))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A n Tn Dn coreToA corrT baseT hcoreT
      terminalData K storedEq minusEq hnot
  change ¬ TreeColorSetMinusClosed G sigma baseT.core
    ((HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0))
  rw [hcoreT, storedEq 0,
    minusEq base.core (TreeSequenceInitialSegmentVertexSetSubset coreToA)]
  exact hnot

theorem helper_branch_1166.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E]
      [inst_2 : DecidableEq V] [inst_3 : DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    TreeSequenceInitialSegment Tn A →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE →
        TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A) →
    ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
      (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core),
    baseT.closure = base.closure →
    ∀
      (terminalData :
        corrT.replacementETT.series.data.tree
              (Fin.last corrT.replacementETT.rounds).castSucc =
            Tn ∧
          corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
              ett.series.data.kind n ∧
            TashkinovStoredColors corrT.replacementETT.series.data
                (Fin.last corrT.replacementETT.rounds) =
              Dn),
    let K : TashkinovHierarchy corrT.replacementETT baseT :=
      { dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst :
        TashkinovHierarchy corrT.replacementETT baseT };
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j) →
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
    (4 : ℕ) ≤
        ((TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
                TreeMissingColors phi base.closure :
              Finset (Fin k)) \
            (HierarchyStoredColorsAt C.hierarchy
                  (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ)))).biUnion
              (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card →
    (4 : ℕ) ≤
      ((TreeMissingColors sigma
                (corrT.replacementETT.series.data.tree
                  (Fin.last corrT.replacementETT.rounds).castSucc) ∩
              TreeMissingColors sigma baseT.closure :
            Finset (Fin k)) \
          (HierarchyStoredColorsAt K (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
            (C.good.gamma (0 : Fin (K.dividerCount + (1 : ℕ))))).card := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A n Tn Dn TnToA treeMissingEq
      closureInsideA corrT baseT hcoreT hclosureT terminalData K storedEq hpOld hcard
  change 4 ≤ ((TreeMissingColors sigma
    (corrT.replacementETT.series.data.tree
      (Fin.last corrT.replacementETT.rounds).castSucc) ∩
    TreeMissingColors sigma baseT.closure) \
      (HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0)).card
  rw [terminalData.1, hclosureT, storedEq 0,
    treeMissingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA),
    treeMissingEq base.closure (closureInsideA hpOld)]
  exact hcard

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch1953Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (alpha beta : Fin k) (sigma : PartialEdgeColoring E k),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
   (∀ {S U W : TreeSequence G e0},
     TreeSequenceInitialSegment S W →
      TreeSequenceInitialSegment U W → S.length ≤ U.length → TreeSequenceInitialSegment S U) →
    (∀ {S U : TreeSequence G e0}, TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
     TreeSequenceInitialSegment Tn A →
      TreeSequenceInitialSegment A T →
       A.length < (↑ib : ℕ) →
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
           TashkinovAugmentationSequence phi Tn T ∨
          (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
           ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
             TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence phi seed T ∧ phi f ≠ some alpha ∧ phi f ≠ some beta) →
         ModColoring ett sigma →
          (∀ (S U : TreeSequence G e0),
            TashkinovAugmentationSequence phi S U →
             TreeSequenceInitialSegment U T →
              U.length ≤ (↑ib : ℕ) → TashkinovAugmentationSequence sigma S U) →
           ¬A = Tn →
            A = Tn ∨
             ∃ (inputA : PartialEdgeColoring E k) (ettA :
              ExtendedTashkinovTree G k e0 inputA A sigma), MaximumProperty ettA

theorem helper_branch_1953.{u_1, u_2} :
    helperBranch1953Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma H q A n Tn ib commonPrefix
      equalTrees TnToA AToT hAib terminalRoute hmod transportBefore he
  have hstrict : Tn.length < A.length := by
    have hle := TnToA.1
    by_contra h
    have hlen : Tn.length = A.length := by omega
    exact he (equalTrees TnToA hlen).symm
  have routeA :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn A) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence sigma seed A) := by
    rcases terminalRoute with ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hseq, hfa, hfb⟩
    · have hpre := TashkinovAugmentationSequenceRestrict phi Tn A T hseq TnToA AToT
      exact Or.inl ⟨hp, transportBefore Tn A hpre AToT (le_of_lt hAib)⟩
    · have hseedA : TreeSequenceInitialSegment seed A :=
        commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hseq) AToT
          (by have := hseed.1; omega)
      have hpre := TashkinovAugmentationSequenceRestrict phi seed A T hseq hseedA AToT
      exact Or.inr ⟨hp, f, seed, hedges, hseed, transportBefore seed A hpre AToT (le_of_lt hAib)⟩
  obtain ⟨corrA⟩ := hmod.2.2 A TnToA hstrict routeA
  exact Or.inr ⟨corrA.replacementInput, corrA.replacementETT,
    MaximumPropertyTransport G k e0 ett sigma hmod A corrA C.maximum⟩

end GoldbergSeymour.StableChangeCaseThreePreparation

end
