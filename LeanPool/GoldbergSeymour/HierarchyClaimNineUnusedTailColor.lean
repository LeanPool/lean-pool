/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices
public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTrans
public import LeanPool.GoldbergSeymour.HierarchyClaimNinePENormalization
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTailAtLeastTwo
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchyPathNumber
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.HierarchyTailMissingColorExclusion
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificate
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.SameHierarchyStages
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwo
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwoFullTail
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.TwoColorPathComponent
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.BaseControl
public import LeanPool.GoldbergSeymour.HierarchyMeasures
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentationTrans
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior

/-!
# Hierarchy Claim Nine Unused Tail Color

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hmissingB_355.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); ColoredVertexSetElementary G mu
        (TreeSequenceVertexSet B) →
    ∀ (hBlen : B.length = T.length - (1 : ℕ)) (hBT : TreeSequenceInitialSegment B T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨B.length,
    by have this : B.length ≤ T.length := hBT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let yp : V := T.vertex ip; yp ∈ TreeSequenceVertexSet B →
    ∀ beta ∈ MissingColors G mu yp, alpha ≠ beta →
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let a : V := T.vertex ia; alpha ∈ MissingColors G mu a → a ∈ TreeSequenceVertexSet B →
        TwoColorComponent G mu alpha beta (Sum.inl a) = TwoColorComponent G mu alpha beta (Sum.inl
        yp) →
    let Q : Set (V ⊕ E) := TwoColorComponent G mu alpha beta (Sum.inl y); (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G mu alpha beta (Sum.inl v)) → Disjoint Q
        (TwoColorComponent G mu alpha beta (Sum.inl a)) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y); (
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G mu alpha beta (Sum.inl y) → MissingColors G
        (TwoColorComponentSwap G mu alpha beta (Sum.inl y)) v = MissingColors G mu v) → (
    ∀ (v : V) (c : Fin k), c ≠ alpha → c ≠ beta → (c ∈ MissingColors G (TwoColorComponentSwap G mu
        alpha beta (Sum.inl y)) v ↔ c ∈ MissingColors G mu v)) → (
    ∀ {v : V} {f : E}, Sum.inl v ∈ Q → Incident G v f → mu f = some alpha ∨ mu f = some beta →
        Sum.inr f ∈ Q) →
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G mu v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu Cm ell B y helem hBlen hBT ip yp
      hypB beta hbeta hne ia a ha haB hsame Q self hdisjoint sigma missingOutside missingOther
      edgeOfVertex v hv
  by_cases hvQ : Sum.inl v ∈ Q
  · have hva : v ≠ a := by
      intro he
      subst v
      exact Set.disjoint_left.mp hdisjoint hvQ (self a)
    have hvb : v ≠ yp := by
      intro he
      subst v
      apply Set.disjoint_left.mp hdisjoint hvQ
      rw [hsame]
      exact self yp
    have hna : alpha ∉ MissingColors G mu v := fun hm =>
      Finset.disjoint_left.mp (helem hv haB hva) hm ha
    have hnb : beta ∉ MissingColors G mu v := fun hm =>
      Finset.disjoint_left.mp (helem hv hypB hvb) hm hbeta
    obtain ⟨fa, hfa, hfca⟩ : ∃ f, Incident G v f ∧ mu f = some alpha := by
      simpa [MissingColors, PresentColors] using hna
    obtain ⟨fb, hfb, hfcb⟩ : ∃ f, Incident G v f ∧ mu f = some beta := by
      simpa [MissingColors, PresentColors] using hnb
    have hfaQ := edgeOfVertex hvQ hfa (Or.inl hfca)
    have hfbQ := edgeOfVertex hvQ hfb (Or.inr hfcb)
    simp only [Q] at hfaQ hfbQ
    have hnewa : sigma fb = some alpha := by
      simp [sigma, TwoColorComponentSwap, hfbQ, hfcb, hne.symm]
    have hnewb : sigma fa = some beta := by
      simp [sigma, TwoColorComponentSwap, hfaQ, hfca]
    have hnsa : alpha ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fb, hfb, hnewa⟩
    have hnsb : beta ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fa, hfa, hnewb⟩
    ext c
    by_cases hca : c = alpha
    · subst c; simp only [hna, hnsa]
    by_cases hcb : c = beta
    · subst c; simp only [hnb, hnsb]
    exact missingOther v c hca hcb
  · exact missingOutside v hvQ

private theorem helper_htail_457.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k), (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → P.coloring (T.edge t) ≠ some alpha) →
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); (2 : ℕ) ≤ ell → ColoredVertexSetElementary G mu
        (TreeSequenceVertexSet B) → A.length + ell = T.length →
    ∀ (hBlen : B.length = T.length - (1 : ℕ)) (hBT : TreeSequenceInitialSegment B T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨B.length,
    by have this : B.length ≤ T.length := hBT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let yp : V := T.vertex ip; B.vertex (Fin.last B.length) = yp →
    ∀ beta ∈ MissingColors G mu yp, alpha ≠ beta → (
    let H : TashkinovHierarchy em bm := Cm.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors em.series.data n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition mu T alpha);
    have vb : V := T.vertex (HierarchyFirstMissingPosition mu T beta);
    have sameComponent : Prop := TwoColorComponent G mu alpha beta (Sum.inl va) =
        TwoColorComponent G mu alpha beta (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (alpha ∈
        TreeMissingColors mu Tnq ∨ Disjoint { alpha, beta } Dnq) → sameComponent) ∧
        (H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors mu Tn ∨ Disjoint { alpha, beta }
        Dn) → sameComponent) ∧ (alpha ∈ TreeMissingColors mu A ∧ TreeColorSetClosed G mu A
        { alpha } → sameComponent ∧ TreeInterchangeable G A mu alpha beta)) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y); (0 :
        ℕ) < H.dividerCount ∧ alpha ∈ TreeMissingColors mu (H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        mu (em.series.data.tree (Fin.last em.rounds).castSucc) ∨ alpha ∈ TreeMissingColors mu A ∧
        alpha ∉ TashkinovStoredColors em.series.data (Fin.last em.rounds) ∧ beta ∉
        TashkinovStoredColors em.series.data (Fin.last em.rounds)) → (if em.series.data.kind
        (Fin.last em.rounds) = some TashkinovExtensionKind.PE then CombinedStableColoring
        (em.series.data.tree (Fin.last em.rounds).castSucc) bm.closure (TashkinovStoredColors
        em.series.data (Fin.last em.rounds)) mu sigma else StableColoring (em.series.data.tree
        (Fin.last em.rounds).castSucc) (TashkinovStoredColors em.series.data (Fin.last em.rounds))
        mu sigma) → (
    ∀ (f : E), TashkinovSeriesStep G k em.rounds e0 P.corresponding.replacementInput
        em.series.data (Fin.last em.rounds) → em.series.data.kind (Fin.last em.rounds) = some
        TashkinovExtensionKind.SE ∨ em.series.data.kind (Fin.last em.rounds) = some
        TashkinovExtensionKind.RE → em.series.data.connectingEdges (Fin.last em.rounds) = { f } →
        TreeIncidentEdge (em.series.data.tree (Fin.last em.rounds).castSucc) f) → (
    ∀ (t : Fin T.length), (↑t : ℕ) = B.length → Incident G yp (T.edge t)) →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → sigma (T.edge t) = mu (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha hunused mu em bm Cm H q A ell B y
      htwo helem hsum hBlen hBT ip yp hyp beta hbeta hne changeResult sigma hcase hbaseStable
      seedIncident hlastEnds t ht
  have hna : mu (T.edge t) ≠ some alpha := hunused t ht
  by_cases hb : mu (T.edge t) = some beta
  · by_cases htB : t.val < B.length
    · let tB : Fin B.length := ⟨t.val, htB⟩
      have hcast : Fin.castLE hBT.1 tB = t := Fin.ext rfl
      have heB : mu (B.edge tB) = some beta := by
        rw [← hBT.2.2 tB, hcast]
        exact hb
      obtain ⟨hzero, hcore, hpos, f, hstep, hkind, hedges, hedge, hcolor, hstored⟩ :=
        HierarchyTailMissingColorExclusion G k e0 P.corresponding.replacementInput T mu em bm H
          helem (ell - 1) (by omega) (by change ell - 1 < ell; omega)
          beta (hyp.symm ▸ hbeta) tB ht
          (by change t.val < A.length + (ell - 1); omega) heB
      have hnotPE : em.series.data.kind (Fin.last em.rounds) ≠
          some TashkinovExtensionKind.PE := by
        rcases hkind with hs | hr
        · rw [hs]; simp
        · rw [hr]; simp
      have hstable : StableColoring (em.series.data.tree (Fin.last em.rounds).castSucc)
          (TashkinovStoredColors em.series.data (Fin.last em.rounds)) mu sigma := by
        simpa only [ite_eq_right hnotPE] using hbaseStable
      have hf := hstable.1 f (seedIncident f hstep hkind hedges)
        ⟨beta, Finset.mem_union_right _ hstored, hcolor⟩
      have he : T.edge t = f := by rw [← hcast, hBT.2.2 tB]; exact hedge
      simpa only [he] using hf
    · have hlast : t.val = B.length := by have := t.isLt; omega
      have hinc := hlastEnds t hlast
      have hnot : beta ∉ PresentColors G mu yp := by simpa [MissingColors] using hbeta
      exact (hnot (by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨T.edge t, hinc, hb⟩)).elim
  · simp [sigma, TwoColorComponentSwap, hna, hb]

private theorem helper_hdisjoint_511.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length);
    ∀ (hBlen : B.length = T.length - (1 : ℕ)) (hBT : TreeSequenceInitialSegment B T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨B.length,
    by have this : B.length ≤ T.length := hBT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let yp : V := T.vertex ip;
    ∀ beta ∈ MissingColors G mu yp, alpha ∈ MissingColors G mu y →
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let a : V := T.vertex ia; alpha ∈ MissingColors G mu a → a ≠ yp → TwoColorComponent G mu alpha
        beta (Sum.inl a) = TwoColorComponent G mu alpha beta (Sum.inl yp) →
    let J : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G mu alpha beta;
    let Q : Set (V ⊕ E) := TwoColorComponent G mu alpha beta (Sum.inl y); (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G mu alpha beta (Sum.inl v)) → (
    ∀ (v : V), alpha ∈ MissingColors G mu v ∨ beta ∈ MissingColors G mu v → (J.neighborSet
        (Sum.inl v)).Subsingleton) → a ≠ y → yp ≠ y → Disjoint Q (TwoColorComponent G mu alpha
        beta (Sum.inl a)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu Cm cm ell B y hBlen hBT ip yp
      beta hbeta haY ia a ha hab hsame J Q self leaf hay hypy
  rcases TwoColorComponentsDisjoint G mu alpha beta (Sum.inl y) (Sum.inl a) with heq | hd
  · obtain ⟨u, v, path, hp, hs⟩ :=
      TwoColorComponentSpanningPath G mu alpha beta cm.proper (Sum.inl y)
    have endpoint (w : V) (hw : Sum.inl w ∈ Q)
        (hl : Set.Subsingleton (J.neighborSet (Sum.inl w))) :
        Sum.inl w = u ∨ Sum.inl w = v := by
      have hm : Sum.inl w ∈ path.support := by
        change Sum.inl w ∈ {x | x ∈ path.support}
        rw [hs]
        exact hw
      by_contra hn
      push Not at hn
      exact hp.isTrail.notMem_support_of_subsingleton_neighborSet hn.1 hn.2 hl hm
    change Q = TwoColorComponent G mu alpha beta (Sum.inl a) at heq
    have haQ : Sum.inl a ∈ Q := by rw [heq]; exact self a
    have hbQ : Sum.inl yp ∈ Q := by rw [heq, hsame]; exact self yp
    have hae := endpoint a haQ (leaf a (Or.inl ha))
    have hbe := endpoint yp hbQ (leaf yp (Or.inr hbeta))
    have hye := endpoint y (self y) (leaf y (Or.inl haY))
    have hnab : (Sum.inl a : Sum V E) ≠ Sum.inl yp := fun h => hab (Sum.inl.inj h)
    have hnay : (Sum.inl a : Sum V E) ≠ Sum.inl y := fun h => hay (Sum.inl.inj h)
    have hnby : (Sum.inl yp : Sum V E) ≠ Sum.inl y := fun h => hypy (Sum.inl.inj h)
    rcases hae with hae | hae <;> rcases hbe with hbe | hbe <;>
      rcases hye with hye | hye <;> simp_all
  · exact hd

private theorem helper_seedIncident_571.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    ∀ (f : E), TashkinovSeriesStep G k em.rounds e0 P.corresponding.replacementInput
        em.series.data (Fin.last em.rounds) → em.series.data.kind (Fin.last em.rounds) = some
        TashkinovExtensionKind.SE ∨ em.series.data.kind (Fin.last em.rounds) = some
        TashkinovExtensionKind.RE → em.series.data.connectingEdges (Fin.last em.rounds) = { f } →
        TreeIncidentEdge (em.series.data.tree (Fin.last em.rounds).castSucc) f := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P em f hstep hkind hedges
  generalize hn : Fin.last em.rounds = j at hstep hkind hedges ⊢
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      rw [initialKind] at hkind
      simp at hkind
  | SE r previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
      have he : choice.edge = f := Finset.singleton_injective (currentEdges.symm.trans hedges)
      rw [← he]
      exact ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
  | PE r previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable
      secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension =>
      rw [currentKind] at hkind
      simp at hkind
  | RE r previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      available currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
      have he : available.edge = f := Finset.singleton_injective (currentEdges.symm.trans hedges)
      rw [← he]
      refine ⟨available.insideEndpoint, available.insideInCurrent, ?_⟩
      simp only [Incident, available.edgeEnds, Sym2.mem_iff, true_or]

private theorem helper_hstoredFirst_629.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); ColoredVertexSetElementary G mu
        (TreeSequenceVertexSet B) →
    ∀ (hBlen : B.length = T.length - (1 : ℕ)) (hBT : TreeSequenceInitialSegment B T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨B.length,
    by have this : B.length ≤ T.length := hBT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let yp : V := T.vertex ip; yp ∈ TreeSequenceVertexSet B →
    ∀ beta ∈ MissingColors G mu yp, alpha ∈ TreeMissingColors mu A → (
    ∀ (rho : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G rho (T.vertex i) → c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ HierarchyFirstMissingPosition rho T c ≤ i) →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T beta; ib = ip →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y); (
    ∀ (v : V) (c : Fin k), c ≠ alpha → c ≠ beta → (c ∈ MissingColors G (TwoColorComponentSwap G mu
        alpha beta (Sum.inl y)) v ↔ c ∈ MissingColors G mu v)) → (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G mu v) →
    ∀ eta ∈ HierarchyStoredColorsAt H q, HierarchyFirstMissingPosition sigma T eta =
        HierarchyFirstMissingPosition mu T eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu Cm H q A ell B y helem hBlen hBT
      ip yp hypB beta hbeta haA firstSpec ib hib sigma missingOther hmissingB eta heta
  have hnotA : eta ∉ TreeMissingColors mu A := (Finset.mem_sdiff.mp heta).2
  have hna : eta ≠ alpha := by intro he; exact hnotA (he.symm ▸ haA)
  by_cases heb : eta = beta
  · subst eta
    have hbnew : beta ∈ MissingColors G sigma yp := by rw [hmissingB yp hypB]; exact hbeta
    have hs := firstSpec sigma beta ip hbnew
    let is := HierarchyFirstMissingPosition sigma T beta
    have hbound : is.val ≤ B.length := hs.2
    let j : Fin (B.length + 1) := ⟨is.val, by omega⟩
    have hj : Fin.castLE (Nat.succ_le_succ hBT.1) j = is := Fin.ext rfl
    have hvB : T.vertex is ∈ TreeSequenceVertexSet B := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, (hBT.2.1 j).symm.trans (congrArg T.vertex hj)⟩
    have hbOld : beta ∈ MissingColors G mu (T.vertex is) := by
      rw [← hmissingB _ hvB]
      exact hs.1
    have hv : T.vertex is = yp := by
      by_contra hn
      exact Finset.disjoint_left.mp (helem hvB hypB hn) hbOld hbeta
    exact (T.vertex_injective hv).trans hib.symm
  · have heq : (Finset.univ.filter fun i : Fin (T.length + 1) =>
          eta ∈ MissingColors G sigma (T.vertex i)) =
        (Finset.univ.filter fun i : Fin (T.length + 1) =>
          eta ∈ MissingColors G mu (T.vertex i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact missingOther _ eta hna heb
    simp only [HierarchyFirstMissingPosition, heq]

private theorem helper_leaf_681.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    ∀ (beta : Fin k), alpha ≠ beta →
    let J : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G mu alpha beta;
    ∀ (v : V), alpha ∈ MissingColors G mu v ∨ beta ∈ MissingColors G mu v → (J.neighborSet
        (Sum.inl v)).Subsingleton := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu cm beta hne J v hv
  have hd : @SimpleGraph.degree _ J (Sum.inl v) (Fintype.ofFinite _) ≤ 1 := by
    rcases hv with hv | hv
    · exact MissingColorIncidenceEndpoint G mu alpha beta hne cm.proper v hv
    · have hj : J = TwoColorIncidenceGraph G mu beta alpha := by
        ext x z
        cases x <;> cases z <;> simp [J, TwoColorIncidenceGraph, or_comm]
      rw [hj]
      exact MissingColorIncidenceEndpoint G mu beta alpha hne.symm cm.proper v hv
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
  intro x hx z hz
  exact Finset.card_le_one_iff.mp hd
    (by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using hx)
    (by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using hz)

private theorem helper_hlastEnds_743.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ)); (2 : ℕ) ≤ ell →
        A.length + ell = T.length →
    ∀ (hBlen : B.length = T.length - (1 : ℕ)) (hBT : TreeSequenceInitialSegment B T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨B.length,
    by have this : B.length ≤ T.length := hBT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let yp : V := T.vertex ip;
    ∀ (beta : Fin k), alpha ≠ beta → (
    let H : TashkinovHierarchy em bm := Cm.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors em.series.data n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition mu T alpha);
    have vb : V := T.vertex (HierarchyFirstMissingPosition mu T beta);
    have sameComponent : Prop := TwoColorComponent G mu alpha beta (Sum.inl va) =
        TwoColorComponent G mu alpha beta (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (alpha ∈
        TreeMissingColors mu Tnq ∨ Disjoint { alpha, beta } Dnq) → sameComponent) ∧
        (H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors mu Tn ∨ Disjoint { alpha, beta }
        Dn) → sameComponent) ∧ (alpha ∈ TreeMissingColors mu A ∧ TreeColorSetClosed G mu A
        { alpha } → sameComponent ∧ TreeInterchangeable G A mu alpha beta)) → (0 : ℕ) <
        H.dividerCount ∧ alpha ∈ TreeMissingColors mu (H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        mu (em.series.data.tree (Fin.last em.rounds).castSucc) ∨ alpha ∈ TreeMissingColors mu A ∧
        alpha ∉ TashkinovStoredColors em.series.data (Fin.last em.rounds) ∧ beta ∉
        TashkinovStoredColors em.series.data (Fin.last em.rounds)) →
    ∀ (t : Fin T.length), (↑t : ℕ) = B.length → Incident G yp (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha mu em bm Cm H q A ell B
      htwo hsum hBlen hBT ip yp beta hne changeResult hcase
  let candidates := (Finset.Icc 1 ell).filter fun i =>
    ∀ r : Fin T.length, A.length + i ≤ r.val →
      G.ends (T.edge r) = Sym2.mk (T.vertex r.castSucc) (T.vertex r.succ)
  have hpathNumber : (if hc : candidates.Nonempty then candidates.min' hc else ell) = 1 :=
    hsituation
  have hc : candidates.Nonempty := by
    by_contra hc
    rw [dite_eq_right hc] at hpathNumber
    omega
  have hmin : candidates.min' hc = 1 := by simpa only [dite_eq_left hc] using hpathNumber
  have hmem : 1 ∈ candidates := hmin ▸ Finset.min'_mem candidates hc
  have hconsecutive := (Finset.mem_filter.mp hmem).2
  intro t ht
  have hends := hconsecutive t (by omega)
  have hi : t.castSucc = ip := Fin.ext ht
  unfold Incident
  rw [hends, hi]
  exact Sym2.mem_mk_left _ _

private theorem helper_continuation_770.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k), (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → P.coloring (T.edge t) ≠ some alpha) →
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); HierarchyFullTailLength C = ell → (
    ∀ (i : ℕ), HierarchyFullTailPrefix C i = HierarchyFullTailPrefix Cm i) → (2 : ℕ) ≤ ell →
        ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) → A.length + ell = T.length →
    ∀ (hBlen : B.length = T.length - (1 : ℕ)) (hBT : TreeSequenceInitialSegment B T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨B.length,
    by have this : B.length ≤ T.length := hBT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let yp : V := T.vertex ip; B.vertex (Fin.last B.length) = yp → yp ∈ TreeSequenceVertexSet B →
        ell - (1 : ℕ) ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)) →
    ∀ beta ∈ MissingColors G mu yp, alpha ∈ TreeMissingColors mu A → alpha ∈ MissingColors G mu y
        → alpha ≠ beta → (
    ∀ (rho : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G rho (T.vertex i) → c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ HierarchyFirstMissingPosition rho T c ≤ i) →
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T beta;
    let a : V := T.vertex ia; ib = ip → alpha ∈ TreeMissingColors mu B ∧ beta ∈ TreeMissingColors
        mu B → (
    let H : TashkinovHierarchy em bm := Cm.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors em.series.data n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition mu T alpha);
    have vb : V := T.vertex (HierarchyFirstMissingPosition mu T beta);
    have sameComponent : Prop := TwoColorComponent G mu alpha beta (Sum.inl va) =
        TwoColorComponent G mu alpha beta (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (alpha ∈
        TreeMissingColors mu Tnq ∨ Disjoint { alpha, beta } Dnq) → sameComponent) ∧
        (H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors mu Tn ∨ Disjoint { alpha, beta }
        Dn) → sameComponent) ∧ (alpha ∈ TreeMissingColors mu A ∧ TreeColorSetClosed G mu A
        { alpha } → sameComponent ∧ TreeInterchangeable G A mu alpha beta)) →
    let Q : Set (V ⊕ E) := TwoColorComponent G mu alpha beta (Sum.inl y); (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G mu alpha beta (Sum.inl v)) → yp ≠ y → Disjoint Q
        (TwoColorComponent G mu alpha beta (Sum.inl a)) → TwoColorPathComponent G mu alpha beta
        (Sum.inl y) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y); (0 :
        ℕ) < H.dividerCount ∧ alpha ∈ TreeMissingColors mu (H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        mu (em.series.data.tree (Fin.last em.rounds).castSucc) ∨ alpha ∈ TreeMissingColors mu A ∧
        alpha ∉ TashkinovStoredColors em.series.data (Fin.last em.rounds) ∧ beta ∉
        TashkinovStoredColors em.series.data (Fin.last em.rounds)) → (if em.series.data.kind
        (Fin.last em.rounds) = some TashkinovExtensionKind.PE then CombinedStableColoring
        (em.series.data.tree (Fin.last em.rounds).castSucc) bm.closure (TashkinovStoredColors
        em.series.data (Fin.last em.rounds)) mu sigma else StableColoring (em.series.data.tree
        (Fin.last em.rounds).castSucc) (TashkinovStoredColors em.series.data (Fin.last em.rounds))
        mu sigma) → (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G mu alpha beta (Sum.inl y) → alpha ∈ MissingColors G
        mu v → beta ∈ MissingColors G (TwoColorComponentSwap G mu alpha beta (Sum.inl y)) v) → (
    ∀ (v : V) (c : Fin k), c ≠ alpha → c ≠ beta → (c ∈ MissingColors G (TwoColorComponentSwap G mu
        alpha beta (Sum.inl y)) v ↔ c ∈ MissingColors G mu v)) → (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G mu v) →
        HierarchyFullTailLength C - (1 : ℕ) ∈ HierarchyEligibleCommonMissingIndices G k e0 input T
        phi ett base C ctx := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha hunused mu em bm Cm cm H
      q A ell B y hell hprefix htwo helem hsum hBlen hBT ip yp hyp hypB hinterval beta hbeta haA
      haY hne firstSpec ia ib a hib hmissing changeResult Q self hypy hdisjoint hpath sigma hcase
      hbaseStable missingAlphaToBeta missingOther hmissingB
  have hbetaNewY : beta ∈ MissingColors G sigma y :=
    missingAlphaToBeta y (self y) haY
  -- Recover incidence of the individual stored seed from its certified step.
  have seedIncident := @helper_seedIncident_571 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C ctx P
  have hlastEnds :=
    @helper_hlastEnds_743 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C ctx P hsituation alpha htwo hsum hBlen hBT beta hne
        changeResult hcase
  have htail :=
    @helper_htail_457 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C ctx P alpha hunused htwo helem hsum hBlen hBT hyp beta hbeta hne
        changeResult hcase hbaseStable seedIncident hlastEnds
  -- Stored colors other than beta are unaffected; beta's first vertex remains yp.
  have hstoredFirst :=
    @helper_hstoredFirst_629 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base C ctx P alpha helem hBlen hBT hypB beta hbeta haA firstSpec hib
        missingOther hmissingB
  -- Reconstruct only after the exact tail and first-position agreements hold.
  obtain ⟨_, _, _, _, corr, hmax, bs, K, good, same⟩ :=
    StableChangeCasesOneTwoFullTail G k e0 P.corresponding.replacementInput T mu em bm Cm cm
      alpha beta hne hmissing (Sum.inl y) hpath sigma rfl hcase hdisjoint htail hmissingB
          hstoredFirst
  have hypT : yp ∈ TreeSequenceVertexSet T := TreeSequenceInitialSegmentVertexSetSubset hBT hypB
  have hyT : y ∈ TreeSequenceVertexSet T := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last T.length, rfl⟩
  let Cs : HierarchyCounterexample bs := {
    positive := by rw [corr.rungAgreement]; exact Cm.positive
    hierarchy := K
    good := good
    maximum := hmax
    notElementary := by
      intro he
      have hbnew : beta ∈ MissingColors G sigma yp := by rw [hmissingB yp hypB]; exact hbeta
      exact Finset.disjoint_left.mp (he hypT hyT hypy) hbnew hbetaNewY }
  -- This registered composition also transports all six minimum-context fields.
  obtain ⟨Pnew, hPnew⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    P sigma corr bs Cs same
  apply Finset.mem_filter.mpr
  refine ⟨?_, Pnew, beta, ?_, ?_⟩
  · simpa only [hell] using hinterval
  · rw [hPnew, hell, hprefix, hyp, hmissingB yp hypB]
    exact hbeta
  · rw [hPnew]
    exact hbetaNewY

private theorem helper_continuation_739.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k), (
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let _ : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc; (0 :
        ℕ) < H.dividerCount ∧ alpha ∈ TreeMissingColors P.coloring Tnq ∨ H.dividerCount = (0 : ℕ)
        ∧ alpha ∈ TreeMissingColors P.coloring Tn) → (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → P.coloring (T.edge t) ≠ some alpha) →
    let mu : PartialEdgeColoring E k := P.coloring;
    let _ : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let _ : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); HierarchyFullTailLength C = ell → (
    ∀ (i : ℕ), HierarchyFullTailPrefix C i = HierarchyFullTailPrefix Cm i) → (2 : ℕ) ≤ ell →
        ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) →
    ∀ (hAT : TreeSequenceInitialSegment A T), A.length + ell = T.length →
    ∀ (hBlen : B.length = T.length - (1 : ℕ)) (hBT : TreeSequenceInitialSegment B T),
        TreeSequenceInitialSegment A B →
    let ip : Fin (T.length + (1 : ℕ)) := (⟨B.length,
    by have this : B.length ≤ T.length := hBT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let yp : V := T.vertex ip; B.vertex (Fin.last B.length) = yp → yp ∈ TreeSequenceVertexSet B →
        y ∉ TreeSequenceVertexSet B → ell - (1 : ℕ) ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength
        C - (1 : ℕ)) →
    ∀ beta ∈ MissingColors G mu yp, alpha ∈ TreeMissingColors mu A → alpha ∈ MissingColors G mu y
        → alpha ≠ beta → (
    ∀ (rho : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G rho (T.vertex i) → c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ HierarchyFirstMissingPosition rho T c ≤ i) →
    ∀ (iaA : Fin (A.length + (1 : ℕ))),
    let iaT : Fin T.length.succ := Fin.castLE (Nat.succ_le_succ hAT.1) iaA; alpha ∈ MissingColors
        G mu (T.vertex iaT) →
    let _ : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let _ : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T beta;
        HierarchyFullTailLength C - (1 : ℕ) ∈ HierarchyEligibleCommonMissingIndices G k e0 input T
        phi ett base C ctx := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha hnormalized hunused mu
      em bm Cm cm H q A ell B y hell hprefix htwo helem hAT hsum hBlen hBT hAB ip yp hyp hypB
      hyNotB hinterval beta hbeta haA haY hne firstSpec iaA iaT haia ia ib
  let a := T.vertex ia
  have ha : alpha ∈ MissingColors G mu a := (firstSpec mu alpha iaT haia).1
  have hia : ia.val ≤ A.length := by
    have hm := (firstSpec mu alpha iaT haia).2
    change ia.val ≤ iaA.val at hm
    have := iaA.isLt
    omega
  have hib : ib = ip := by
    have hs := firstSpec mu beta ip hbeta
    have hbound : ib.val ≤ B.length := hs.2
    let j : Fin (B.length + 1) := ⟨ib.val, by omega⟩
    have hj : Fin.castLE (Nat.succ_le_succ hBT.1) j = ib := Fin.ext rfl
    have hbB : T.vertex ib ∈ TreeSequenceVertexSet B := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, (hBT.2.1 j).symm.trans (congrArg T.vertex hj)⟩
    have hv : T.vertex ib = yp := by
      by_contra hn
      exact Finset.disjoint_left.mp (helem hbB hypB hn) hs.1 hbeta
    exact T.vertex_injective hv
  have haB : a ∈ TreeSequenceVertexSet B := by
    let j : Fin (A.length + 1) := ⟨ia.val, by omega⟩
    have hj : Fin.castLE (Nat.succ_le_succ hAT.1) j = ia := Fin.ext rfl
    apply TreeSequenceInitialSegmentVertexSetSubset hAB
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, (hAT.2.1 j).symm.trans (congrArg T.vertex hj)⟩
  have hab : a ≠ yp := by
    intro h
    have hv := congrArg Fin.val (T.vertex_injective h)
    change ia.val = B.length at hv
    omega
  have hmissing : alpha ∈ TreeMissingColors mu B ∧ beta ∈ TreeMissingColors mu B := by
    constructor
    · exact Finset.mem_biUnion.mpr ⟨a, haB, ha⟩
    · exact Finset.mem_biUnion.mpr ⟨yp, hypB, hbeta⟩
  have hordered :
      (alpha ∉ TreeMissingColors mu A ∨ beta ∉ TreeMissingColors mu A) →
        TreeVertexOrder T a (T.vertex ib) ∧
          alpha ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
            A.length ≤ t.val ∧ t.val < ib.val ∧ mu (T.edge t) = some c) := by
    intro _
    refine ⟨⟨ia, ib, rfl, rfl, ?_⟩, ?_⟩
    · rw [hib]
      change ia.val < B.length
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨t, ht, _, he⟩
      exact hunused t ht he
  have changeResult := ChangeLemma G k e0 P.corresponding.replacementInput T mu em bm Cm
    cm.proper cm.oneEdgeUncolored cm.lowerRung cm.fewerDividers cm.lexicographicMinimality
    helem cm.largeMissingSet alpha beta hne hmissing hordered
  have hsame : TwoColorComponent G mu alpha beta (Sum.inl a) =
      TwoColorComponent G mu alpha beta (Sum.inl yp) := by
    have hc : TwoColorComponent G mu alpha beta (Sum.inl a) =
        TwoColorComponent G mu alpha beta (Sum.inl (T.vertex ib)) := by
      rcases hnormalized with hp | hz
      · exact changeResult.1 ⟨hp.1, Or.inl hp.2⟩
      · exact changeResult.2.1 ⟨hz.1, Or.inl hz.2⟩
    simpa only [hib] using hc
  let J := TwoColorIncidenceGraph G mu alpha beta
  let Q := TwoColorComponent G mu alpha beta (Sum.inl y)
  have self (v : V) : Sum.inl v ∈ TwoColorComponent G mu alpha beta (Sum.inl v) := by
    change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk (Sum.inl v)
    rfl
  have leaf := @helper_leaf_681 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx P alpha beta hne
  have hay : a ≠ y := fun he => hyNotB (he ▸ haB)
  have hypy : yp ≠ y := fun he => hyNotB (he ▸ hypB)
  -- Three distinct missing-color endpoints cannot share one spanning path.
  have hdisjoint :=
    @helper_hdisjoint_511 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C ctx P alpha hBlen hBT beta hbeta haY ha hab hsame self leaf hay
        hypy
  have hpath : TwoColorPathComponent G mu alpha beta (Sum.inl y) :=
    ⟨hne, Sum.inl y, self y, leaf y (Or.inl haY)⟩
  let sigma := TwoColorComponentSwap G mu alpha beta (Sum.inl y)
  have hcase :
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors mu
        (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧
        (alpha ∈ TreeMissingColors mu (em.series.data.tree (Fin.last em.rounds).castSucc) ∨
          (alpha ∈ TreeMissingColors mu A ∧
            alpha ∉ TashkinovStoredColors em.series.data (Fin.last em.rounds) ∧
            beta ∉ TashkinovStoredColors em.series.data (Fin.last em.rounds)))) := by
    rcases hnormalized with hp | hz
    · exact Or.inl hp
    · exact Or.inr ⟨hz.1, Or.inl hz.2⟩
  obtain ⟨hbaseStable, hmissingA, hsproper, hsone, houtside⟩ :=
    P2813_T1_BaseControl G k e0 P.corresponding.replacementInput T mu em bm Cm cm
      helem alpha beta hne hmissing (Sum.inl y) hpath sigma rfl hcase hdisjoint
  obtain ⟨missingOutside, missingAlphaToBeta, missingBetaToAlpha, missingOther⟩ :=
    TwoColorComponentSwapMissingBehavior G mu alpha beta hne cm.proper (Sum.inl y)
  have edgeOfVertex {v : V} {f : E} (hv : Sum.inl v ∈ Q)
      (hf : Incident G v f) (hc : mu f = some alpha ∨ mu f = some beta) :
      Sum.inr f ∈ Q := by
    change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk (Sum.inl y) at hv
    change J.connectedComponentMk (Sum.inr f) = J.connectedComponentMk (Sum.inl y)
    have hadj : J.Adj (Sum.inr f) (Sum.inl v) := by
      simpa only [J, TwoColorIncidenceGraph] using And.intro hf hc
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
  -- Internal component vertices in B retain both affected colors as present.
  have hmissingB :=
    @helper_hmissingB_355 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C ctx P alpha helem hBlen hBT hypB beta hbeta hne ha haB hsame
        self hdisjoint missingOutside missingOther edgeOfVertex
  exact @helper_continuation_770 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx P hsituation alpha hunused hell hprefix htwo helem hsum hBlen
      hBT hyp hypB hinterval beta hbeta haA haY hne firstSpec hib hmissing changeResult self hypy
      hdisjoint hpath hcase hbaseStable missingAlphaToBeta missingOther hmissingB
theorem HierarchyClaimNineUnusedTailColor {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (hsituation : HierarchyPathNumber P.counterexample.hierarchy = 1)
    (alpha : Fin k)
    (hstart :
      let H := P.counterexample.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      alpha ∈ TreeMissingColors P.coloring A ∧
        alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)))
    (hnormalized :
      let H := P.counterexample.hierarchy
      let _ : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors P.coloring Tnq) ∨
        (H.dividerCount = 0 ∧ alpha ∈ TreeMissingColors P.coloring Tn))
    (hnoCommon : ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
      Disjoint
        (MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)))
        (MissingColors G P.coloring (T.vertex (Fin.last T.length))))
    (hunused :
      let A := HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val →
        P.coloring (T.edge t) ≠ some alpha) :
    HierarchyFullTailLength C - 1 ∈
      HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx := by
  classical
  let mu := P.coloring
  let em := P.corresponding.replacementETT
  let bm := P.replacementBase
  let Cm := P.counterexample
  let cm := P.minimumContext
  let H := Cm.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength Cm
  let B := HierarchyFullTailPrefix Cm (ell - 1)
  let y := T.vertex (Fin.last T.length)
  have hstar := (P2752_T2_HierarchyMeasures C.hierarchy H P.sameGood.1).1
  have hell : HierarchyFullTailLength C = ell := by
    simp only [HierarchyFullTailLength, hstar]
    rfl
  have hprefix (i : ℕ) : HierarchyFullTailPrefix C i =
      HierarchyFullTailPrefix Cm i := by
    simp only [HierarchyFullTailPrefix, hstar]
    rfl
  have htwo : 2 ≤ ell :=
    HierarchyCounterexampleTailAtLeastTwo G k e0
      P.corresponding.replacementInput T mu em bm Cm cm.proper cm.oneEdgeUncolored
      cm.lowerRung cm.fewerDividers cm.lexicographicMinimality cm.largeMissingSet
  have helem : ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0
      P.corresponding.replacementInput T mu em bm Cm cm.proper cm.oneEdgeUncolored
      cm.lowerRung cm.fewerDividers cm.lexicographicMinimality cm.largeMissingSet
  have hAT : TreeSequenceInitialSegment A T := by
    have hs : TreeSequenceInitialSegment (HierarchyStarredStage H q) (H.stage q.succ) := by
      refine Fin.cases ?_ (fun i => ?_) q
      · exact H.coreInsideFirst
      · exact H.nested i.succ
    have hlast : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
    simpa only [hlast, H.terminalStage] using hs
  have hsum : A.length + ell = T.length := Nat.add_sub_of_le hAT.1
  have hBlen : B.length = T.length - 1 := by
    dsimp [B, HierarchyFullTailPrefix]
    change min (A.length + (ell - 1)) T.length = T.length - 1
    omega
  have hBT : TreeSequenceInitialSegment B T := by
    refine ⟨Nat.min_le_right _ _, ?_, ?_⟩ <;> intro i <;> rfl
  have hAB : TreeSequenceInitialSegment A B := by
    have hlen : A.length ≤ B.length := by omega
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hBT.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hAT.2.1 i)
    · intro i
      exact (hBT.2.2 (Fin.castLE hlen i)).symm.trans (hAT.2.2 i)
  let ip : Fin (T.length + 1) := ⟨B.length, by have := hBT.1; omega⟩
  let yp := T.vertex ip
  have hyp : B.vertex (Fin.last B.length) = yp := (hBT.2.1 _).symm
  have hypB : yp ∈ TreeSequenceVertexSet B := by
    rw [← hyp]
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last B.length, rfl⟩
  have hyNotB : y ∉ TreeSequenceVertexSet B := by
    intro hy
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨i, hi⟩ := hy
    have he := T.vertex_injective ((hBT.2.1 i).trans hi)
    have hv := congrArg Fin.val he
    have := i.isLt
    simp only [Fin.val_castLE, Fin.val_last] at hv
    omega
  have hinterval : ell - 1 ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1) := by
    rw [hell]
    simp only [Finset.mem_Icc]
    omega
  obtain ⟨beta, hbeta⟩ := hvertexMissing mu cm.proper cm.oneEdgeUncolored yp
  have hbNotY : beta ∉ MissingColors G mu y := by
    have hd := hnoCommon (ell - 1) hinterval
    rw [hprefix, hyp] at hd
    exact Finset.disjoint_left.mp hd hbeta
  have haA : alpha ∈ TreeMissingColors mu A := hstart.1
  have haY : alpha ∈ MissingColors G mu y := hstart.2
  have hne : alpha ≠ beta := by
    intro he
    exact hbNotY (he ▸ haY)
  have firstSpec (rho : PartialEdgeColoring E k) (c : Fin k)
      (i : Fin (T.length + 1)) (hi : c ∈ MissingColors G rho (T.vertex i)) :
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
        HierarchyFirstMissingPosition rho T c ≤ i := by
    let s : Finset (Fin (T.length + 1)) :=
      Finset.univ.filter fun j => c ∈ MissingColors G rho (T.vertex j)
    have his : i ∈ s := by simp [s, hi]
    have hs : s.Nonempty := ⟨i, his⟩
    have hp : HierarchyFirstMissingPosition rho T c = s.min' hs := by
      simp only [HierarchyFirstMissingPosition, s, dite_eq_left hs]
    rw [hp]
    exact ⟨(Finset.mem_filter.mp (Finset.min'_mem s hs)).2, Finset.min'_le s i his⟩
  obtain ⟨va, hvaA, hava⟩ := Finset.mem_biUnion.mp haA
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hvaA
  obtain ⟨iaA, hiaA⟩ := hvaA
  let iaT := Fin.castLE (Nat.succ_le_succ hAT.1) iaA
  have haia : alpha ∈ MissingColors G mu (T.vertex iaT) := by
    rw [hAT.2.1 iaA, hiaA]
    exact hava
  let ia := HierarchyFirstMissingPosition mu T alpha
  let ib := HierarchyFirstMissingPosition mu T beta
  exact @helper_continuation_739 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx P hsituation alpha hnormalized hunused hell hprefix htwo
      helem hAT hsum hBlen hBT hAB hyp hypB hyNotB hinterval beta hbeta haA haY hne firstSpec iaA
      haia
end GoldbergSeymour

end
