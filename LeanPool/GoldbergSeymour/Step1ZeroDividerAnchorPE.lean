/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryColorVertex
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.DefectiveColor
public import LeanPool.GoldbergSeymour.Degree
public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyPrefixRepackage
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HierarchyLEMStable
public import LeanPool.GoldbergSeymour.HierarchyOutsideKempeStable
public import LeanPool.GoldbergSeymour.HierarchySegmentColors
public import LeanPool.GoldbergSeymour.HierarchyStageMissingColors
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAntitone
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsCardinality
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloring
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable
public import LeanPool.GoldbergSeymour.ParallelCommonMissingClosed
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.SameHierarchyStages
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovExtensionKind
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed
public import LeanPool.GoldbergSeymour.TreeExitPath
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeVertexOrder
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.TwoColorPathComponent
public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent
public import LeanPool.GoldbergSeymour.ParallelInterchangeability
public import LeanPool.GoldbergSeymour.StableColoringEquivalence

public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Step1Zero Divider Anchor PE

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_exitBoundary_285.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (alpha beta : Fin k),
    let X : Finset V := TreeSequenceVertexSet base.core; TreeColorSetClosed G phi base.core
        { alpha } →
    ∀ (u v : V) (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath base.core phi alpha beta u v P →
    ∃ f ∈ BoundaryColorEdges G phi X beta, Incident G v f ∧ Sum.inr f ∈ P.support := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base alpha beta X halphaClosed u v P hP
  rcases hP with ⟨_, _, huX, hvX, _, honly⟩
  let graph := TwoColorIncidenceGraph G phi alpha beta
  let S : Set (Sum V E) := {y | match y with
    | Sum.inl q => q ∈ X
    | Sum.inr f => ∀ q, Incident G q f → q ∈ X}
  have hSv : Sum.inl v ∈ S := by
    simpa [S, X] using hvX
  have hSu : Sum.inl u ∉ S := by
    simpa [S, X] using huX
  obtain ⟨d, hd, hds, hdt⟩ :=
    P.reverse.exists_boundary_dart S hSv hSu
  have hadj := d.adj
  have hdmem : d.toProd.1 ∈ P.reverse.support :=
    P.reverse.dart_fst_mem_support_of_mem_darts hd
  have hdtmem : d.toProd.2 ∈ P.reverse.support :=
    P.reverse.dart_snd_mem_support_of_mem_darts hd
  have hfirst : ∃ q : V, d.toProd.1 = Sum.inl q ∧ q ∈ X := by
    cases h : d.toProd.1 with
    | inl q =>
        rw [h] at hds
        exact ⟨q, rfl, by simpa [S] using hds⟩
    | inr f =>
        exfalso
        cases h2 : d.toProd.2 with
        | inl r =>
            rw [h, h2] at hadj
            change Incident G r f ∧
              (phi f = some alpha ∨ phi f = some beta) at hadj
            rw [h] at hds
            have hall : ∀ q, Incident G q f → q ∈ X := by
              simpa [S] using hds
            have hrnot : r ∉ X := by
              intro hr
              apply hdt
              simpa [S, h2] using hr
            exact hrnot (hall r hadj.1)
        | inr e =>
            rw [h, h2] at hadj
            exact hadj.elim
  obtain ⟨q, hq, hqX⟩ := hfirst
  have hsecond : ∃ f : E, d.toProd.2 = Sum.inr f := by
    cases h : d.toProd.2 with
    | inl r =>
        rw [hq, h] at hadj
        exact False.elim hadj
    | inr f => exact ⟨f, rfl⟩
  obtain ⟨f, hf⟩ := hsecond
  have hfadj : graph.Adj (Sum.inl q) (Sum.inr f) := by
    rw [hq, hf] at hadj
    exact hadj
  have hfdata : Incident G q f ∧
      (phi f = some alpha ∨ phi f = some beta) := by
    simpa [graph, TwoColorIncidenceGraph] using hfadj
  have hnotall : ¬ ∀ r, Incident G r f → r ∈ X := by
    intro hall
    apply hdt
    simpa [S, hf, hall]
  obtain ⟨r, hrf, hrX⟩ : ∃ r, Incident G r f ∧ r ∉ X := by
    push Not at hnotall
    exact hnotall
  have hqr : q ≠ r := by
    intro h
    exact hrX (h ▸ hqX)
  have hend : G.ends f = Sym2.mk q r :=
    (Sym2.mem_and_mem_iff hqr).mp ⟨hfdata.1, hrf⟩
  have hfb : f ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨q, hqX, r, hrX, hend⟩
  have hfcolor : phi f = some beta := by
    rcases hfdata.2 with hfa | hfbeta
    · have hfalpha : f ∈ BoundaryColorEdges G phi X alpha := by
        simp [BoundaryColorEdges, hfb, hfa]
      have hempty := halphaClosed alpha (by simp)
      rw [hempty] at hfalpha
      simp at hfalpha
    · exact hfbeta
  have hqP : Sum.inl q ∈ P.support := by
    have hqrev : Sum.inl q ∈ P.reverse.support := by
      rw [← hq]
      exact hdmem
    simpa [SimpleGraph.Walk.support_reverse] using hqrev
  have hqv : q = v := (honly q (by simpa [X] using hqX)).mp hqP
  have hfP : Sum.inr f ∈ P.support := by
    have hfrev : Sum.inr f ∈ P.reverse.support := by
      rw [← hf]
      exact hdtmem
    simpa [SimpleGraph.Walk.support_reverse] using hfrev
  subst q
  exact ⟨f, by simp [BoundaryColorEdges, hfb, hfcolor], hfdata.1, hfP⟩

private theorem helper_finish_411.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), MaximumProperty ett → (0 : ℕ) < ett.rounds → LowerRoundInductionHypothesis G
        k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi) (beta : Fin k) (a₁ b₁ a₂ b₂ : V), a₁ ≠ a₂ →
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let X : Finset V := TreeSequenceVertexSet base.core;
    let x : V := Tn.vertex base.supportPosition; x ∈ TreeSequenceVertexSet Tn → x ∈
        TreeSequenceVertexSet base.closure → x ∈ X →
    ∀ c ∈ MissingColors G phi x, c ≠ beta →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → CombinedStableColoring Tn base.closure (TashkinovStoredColors ett.series.data n) phi
        sigma → c ∈ TreeMissingColors sigma base.core → TreeColorSetClosed G sigma base.core { c }
        →
    ∀ (Q₁ : (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₁) (Sum.inl b₁)) (Q₂ :
        (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₂) (Sum.inl b₂)), TreeExitPath
        base.core sigma c beta a₁ b₁ Q₁ → TreeExitPath base.core sigma c beta a₂ b₂ Q₂ → False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hMP hpositive hlower base beta a₁ b₁ a₂ b₂ ha hPE n Tn
      X x hxT hxR hxX c hcxMissing hcNeBeta sigma hsProper hsOne hsCombined hcMissingCore
      hcClosedCore Q₁ Q₂ hQ₁ hQ₂
  let graph := TwoColorIncidenceGraph G sigma c beta
  have missingLeaf : ∀ (v : V),
      (c ∈ MissingColors G sigma v ∨ beta ∈ MissingColors G sigma v) →
      Set.Subsingleton (graph.neighborSet (Sum.inl v)) := by
    intro v hmissing z hz w hw
    cases hzv : z with
    | inl u =>
        rw [hzv] at hz
        simp [graph, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hz
    | inr e =>
        cases hwv : w with
        | inl u =>
            rw [hwv] at hw
            simp [graph, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hw
        | inr f =>
            rw [hzv] at hz
            rw [hwv] at hw
            have he : Incident G v e ∧
                (sigma e = some c ∨ sigma e = some beta) := by
              simpa [graph, SimpleGraph.mem_neighborSet,
                TwoColorIncidenceGraph] using hz
            have hf : Incident G v f ∧
                (sigma f = some c ∨ sigma f = some beta) := by
              simpa [graph, SimpleGraph.mem_neighborSet,
                TwoColorIncidenceGraph] using hw
            apply congrArg Sum.inr
            by_contra hef
            rcases hmissing with hcm | hbm
            · have hnc : c ∉ PresentColors G sigma v := by
                simpa [MissingColors] using hcm
              have hec : sigma e = some beta := he.2.resolve_left (by
                intro hec
                apply hnc
                simpa [PresentColors] using
                  (show ∃ q, Incident G v q ∧ sigma q = some c from
                    ⟨e, he.1, hec⟩))
              have hfc : sigma f = some beta := hf.2.resolve_left (by
                intro hfc
                apply hnc
                simpa [PresentColors] using
                  (show ∃ q, Incident G v q ∧ sigma q = some c from
                    ⟨f, hf.1, hfc⟩))
              exact (hsProper hef ⟨v, he.1, hf.1⟩ hec) hfc
            · have hnb : beta ∉ PresentColors G sigma v := by
                simpa [MissingColors] using hbm
              have heb : sigma e = some c := he.2.resolve_right (by
                intro heb
                apply hnb
                simpa [PresentColors] using
                  (show ∃ q, Incident G v q ∧ sigma q = some beta from
                    ⟨e, he.1, heb⟩))
              have hfb : sigma f = some c := hf.2.resolve_right (by
                intro hfb
                apply hnb
                simpa [PresentColors] using
                  (show ∃ q, Incident G v q ∧ sigma q = some beta from
                    ⟨f, hf.1, hfb⟩))
              exact (hsProper hef ⟨v, he.1, hf.1⟩ heb) hfb
  have hcxSigma : c ∈ MissingColors G sigma x := by
    rw [hsCombined.1.2 x hxT]
    exact hcxMissing
  have hxLeaf : Set.Subsingleton (graph.neighborSet (Sum.inl x)) :=
    missingLeaf x (Or.inl hcxSigma)
  have ha₁Leaf : Set.Subsingleton (graph.neighborSet (Sum.inl a₁)) :=
    missingLeaf a₁ hQ₁.2.2.2.2.1
  have ha₂Leaf : Set.Subsingleton (graph.neighborSet (Sum.inl a₂)) :=
    missingLeaf a₂ hQ₂.2.2.2.2.1
  have hpathX : TwoColorPathComponent G sigma c beta (Sum.inl x) :=
    ⟨hcNeBeta, Sum.inl x, rfl, hxLeaf⟩
  have hpath₁ : TwoColorPathComponent G sigma c beta (Sum.inl a₁) :=
    ⟨hcNeBeta, Sum.inl a₁, rfl, ha₁Leaf⟩
  have hpath₂ : TwoColorPathComponent G sigma c beta (Sum.inl a₂) :=
    ⟨hcNeBeta, Sum.inl a₂, rfl, ha₂Leaf⟩
  have hmeetX : ∃ v ∈ TreeSequenceVertexSet base.core,
      Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl x) :=
    ⟨x, by simpa [X] using hxX, rfl⟩
  have hmeet₁ : ∃ v ∈ TreeSequenceVertexSet base.core,
      Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl a₁) := by
    refine ⟨b₁, hQ₁.2.2.2.1, ?_⟩
    change graph.connectedComponentMk (Sum.inl b₁) =
      graph.connectedComponentMk (Sum.inl a₁)
    exact (SimpleGraph.ConnectedComponent.sound Q₁.reachable).symm
  have hmeet₂ : ∃ v ∈ TreeSequenceVertexSet base.core,
      Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl a₂) := by
    refine ⟨b₂, hQ₂.2.2.2.1, ?_⟩
    change graph.connectedComponentMk (Sum.inl b₂) =
      graph.connectedComponentMk (Sum.inl a₂)
    exact (SimpleGraph.ConnectedComponent.sound Q₂.reachable).symm
  have ha₁x : a₁ ≠ x := by
    intro h
    exact hQ₁.2.2.1 (h ▸ (by simpa [X] using hxX))
  have ha₂x : a₂ ≠ x := by
    intro h
    exact hQ₂.2.2.1 (h ▸ (by simpa [X] using hxX))
  have hdistinct :
      TwoColorComponent G sigma c beta (Sum.inl x) ≠
          TwoColorComponent G sigma c beta (Sum.inl a₁) ∨
      TwoColorComponent G sigma c beta (Sum.inl x) ≠
          TwoColorComponent G sigma c beta (Sum.inl a₂) := by
    by_contra hnot
    push Not at hnot
    obtain ⟨u, v, R, hRpath, hRsupport⟩ :=
      TwoColorComponentSpanningPath G sigma c beta hsProper (Sum.inl x)
    have hxR : Sum.inl x ∈ R.support := by
      change Sum.inl x ∈ {z | z ∈ R.support}
      rw [hRsupport]
      rfl
    have ha₁R : Sum.inl a₁ ∈ R.support := by
      change Sum.inl a₁ ∈ {z | z ∈ R.support}
      rw [hRsupport, hnot.1]
      rfl
    have ha₂R : Sum.inl a₂ ∈ R.support := by
      change Sum.inl a₂ ∈ {z | z ∈ R.support}
      rw [hRsupport, hnot.2]
      rfl
    have endpointOfLeaf :
    ∀ (z : Sum V E), Set.Subsingleton (graph.neighborSet z) → z ∈ R.support → z = u ∨ z = v := by
      intro z hzLeaf hzR
      by_contra hzEnds
      push Not at hzEnds
      exact (hRpath.isTrail.notMem_support_of_subsingleton_neighborSet
        hzEnds.1 hzEnds.2 hzLeaf) hzR
    have hxEnds := endpointOfLeaf (Sum.inl x) hxLeaf hxR
    have ha₁Ends := endpointOfLeaf (Sum.inl a₁) ha₁Leaf ha₁R
    have ha₂Ends := endpointOfLeaf (Sum.inl a₂) ha₂Leaf ha₂R
    rcases hxEnds with hxu | hxv <;>
      rcases ha₁Ends with h₁u | h₁v <;>
      rcases ha₂Ends with h₂u | h₂v
    · exact ha₁x (Sum.inl.inj (h₁u.trans hxu.symm))
    · exact ha₁x (Sum.inl.inj (h₁u.trans hxu.symm))
    · exact ha₂x (Sum.inl.inj (h₂u.trans hxu.symm))
    · exact ha (Sum.inl.inj (h₁v.trans h₂v.symm))
    · exact ha (Sum.inl.inj (h₁u.trans h₂u.symm))
    · exact ha₂x (Sum.inl.inj (h₂v.trans hxv.symm))
    · exact ha₁x (Sum.inl.inj (h₁v.trans hxv.symm))
    · exact ha₁x (Sum.inl.inj (h₁v.trans hxv.symm))
  have hinter := (interchange G k e0 input T phi sigma ett hMP hpositive
    hlower hPE base hsProper hsOne hsCombined c beta).2.2.1
    hcMissingCore hcClosedCore
  rcases hdistinct with hneComp | hneComp
  · exact hneComp (hinter (Sum.inl x) (Sum.inl a₁)
      hpathX hpath₁ hmeetX hmeet₁)
  · exact hneComp (hinter (Sum.inl x) (Sum.inl a₂)
      hpathX hpath₂ hmeetX hmeet₂)

private theorem helper_componentOutside_422.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (alpha : Fin k),
    let X : Finset V := TreeSequenceVertexSet base.core;
    ∀ (c : Fin k), TreeColorSetClosed G phi base.core { c } → TreeColorSetClosed G phi base.core
        { alpha } →
    ∀ u ∉ X,
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G phi alpha c (Sum.inl u) → v ∉ X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base alpha X c hcClosed halphaClosed u hu v
      hvComponent hv
  let graph := TwoColorIncidenceGraph G phi alpha c
  change graph.connectedComponentMk (Sum.inl v) =
    graph.connectedComponentMk (Sum.inl u) at hvComponent
  have reach : graph.Reachable (Sum.inl u) (Sum.inl v) :=
    (SimpleGraph.ConnectedComponent.eq.mp hvComponent).symm
  apply reach.elim
  intro P
  let S : Set (Sum V E) := {y | match y with
    | Sum.inl q => q ∈ X
    | Sum.inr f => ∀ q, Incident G q f → q ∈ X}
  have hSv : Sum.inl v ∈ S := by simpa [S] using hv
  have hSu : Sum.inl u ∉ S := by simpa [S] using hu
  obtain ⟨d, hd, hds, hdt⟩ :=
    P.reverse.exists_boundary_dart S hSv hSu
  have hadj := d.adj
  have hfirst : ∃ q : V, d.toProd.1 = Sum.inl q ∧ q ∈ X := by
    cases h : d.toProd.1 with
    | inl q =>
        rw [h] at hds
        exact ⟨q, rfl, by simpa [S] using hds⟩
    | inr f =>
        exfalso
        cases h2 : d.toProd.2 with
        | inl r =>
            rw [h, h2] at hadj
            change Incident G r f ∧
              (phi f = some alpha ∨ phi f = some c) at hadj
            rw [h] at hds
            have hall : ∀ q, Incident G q f → q ∈ X := by
              simpa [S] using hds
            have hrnot : r ∉ X := by
              intro hr
              apply hdt
              simpa [S, h2] using hr
            exact hrnot (hall r hadj.1)
        | inr e =>
            rw [h, h2] at hadj
            exact hadj.elim
  obtain ⟨q, hq, hqX⟩ := hfirst
  have hsecond : ∃ f : E, d.toProd.2 = Sum.inr f := by
    cases h : d.toProd.2 with
    | inl r =>
        rw [hq, h] at hadj
        exact False.elim hadj
    | inr f => exact ⟨f, rfl⟩
  obtain ⟨f, hf⟩ := hsecond
  have hfadj : graph.Adj (Sum.inl q) (Sum.inr f) := by
    rw [hq, hf] at hadj
    exact hadj
  have hfdata : Incident G q f ∧
      (phi f = some alpha ∨ phi f = some c) := by
    simpa [graph, TwoColorIncidenceGraph] using hfadj
  have hnotall : ¬ ∀ r, Incident G r f → r ∈ X := by
    intro hall
    apply hdt
    simpa [S, hf, hall]
  obtain ⟨r, hrf, hrX⟩ : ∃ r, Incident G r f ∧ r ∉ X := by
    push Not at hnotall
    exact hnotall
  have hqr : q ≠ r := by
    intro h
    exact hrX (h ▸ hqX)
  have hend : G.ends f = Sym2.mk q r :=
    (Sym2.mem_and_mem_iff hqr).mp ⟨hfdata.1, hrf⟩
  have hfb : f ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨q, hqX, r, hrX, hend⟩
  rcases hfdata.2 with hfa | hfc
  · have hfalpha : f ∈ BoundaryColorEdges G phi X alpha := by
      simp [BoundaryColorEdges, hfb, hfa]
    have hempty := halphaClosed alpha (by simp)
    rw [hempty] at hfalpha
    simp at hfalpha
  · have hfcolor : f ∈ BoundaryColorEdges G phi X c := by
      simp [BoundaryColorEdges, hfb, hfc]
    have hempty := hcClosed c (by simp)
    rw [hempty] at hfcolor
    simp at hfcolor

private theorem helper_pathEdgeOutside_590.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (alpha beta : Fin k),
    let X : Finset V := TreeSequenceVertexSet base.core;
    ∀ (u v : V) (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath base.core phi alpha beta u v P →
    ∀ (f : E), Sum.inr f ∈ P.support →
    ∃ (w : V), Sum.inl w ∈ P.support ∧ w ∉ X ∧ Incident G w f := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base alpha beta X u v P hExit f hfSupport
  rcases hExit with ⟨hPath, hLength, huX, hvX, hMissing, honly⟩
  obtain ⟨m, hm, hmle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hfSupport
  have hmpos : 0 < m := by
    by_contra h
    have hmzero : m = 0 := by omega
    rw [hmzero] at hm
    simp at hm
  have hmlt : m < P.length := by
    by_contra h
    have hmlast : m = P.length := by omega
    rw [hmlast] at hm
    simp at hm
  have hprev := P.adj_getVert_succ (i := m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega, hm] at hprev
  obtain ⟨w, hwPrev⟩ : ∃ w : V, P.getVert (m - 1) = Sum.inl w := by
    cases hnode : P.getVert (m - 1) with
    | inl w => exact ⟨w, rfl⟩
    | inr e =>
        rw [hnode] at hprev
        simp [TwoColorIncidenceGraph] at hprev
  have hnext := P.adj_getVert_succ (i := m) hmlt
  rw [hm] at hnext
  obtain ⟨z, hzNext⟩ : ∃ z : V, P.getVert (m + 1) = Sum.inl z := by
    cases hnode : P.getVert (m + 1) with
    | inl z => exact ⟨z, rfl⟩
    | inr e =>
        rw [hnode] at hnext
        simp [TwoColorIncidenceGraph] at hnext
  have hwIncident : Incident G w f := by
    rw [hwPrev] at hprev
    simpa [TwoColorIncidenceGraph] using hprev.1
  have hzIncident : Incident G z f := by
    rw [hzNext] at hnext
    simpa [TwoColorIncidenceGraph] using hnext.1
  have hwSupport : Sum.inl w ∈ P.support := by
    rw [← hwPrev]
    exact P.getVert_mem_support (m - 1)
  have hzSupport : Sum.inl z ∈ P.support := by
    rw [← hzNext]
    exact P.getVert_mem_support (m + 1)
  by_cases hwX : w ∈ X
  · by_cases hzX : z ∈ X
    · have hwv : w = v :=
        (honly w (by simpa [X] using hwX)).mp hwSupport
      have hzv : z = v :=
        (honly z (by simpa [X] using hzX)).mp hzSupport
      have hverts : P.getVert (m - 1) = P.getVert (m + 1) := by
        rw [hwPrev, hzNext, hwv, hzv]
      have hindices := hPath.getVert_injOn
        (show m - 1 ≤ P.length by omega)
        (show m + 1 ≤ P.length by omega) hverts
      omega
    · exact ⟨z, hzSupport, hzX, hzIncident⟩
  · exact ⟨w, hwSupport, hwX, hwIncident⟩

private theorem helper_transportExit_653.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (alpha beta : Fin k),
    let X : Finset V := TreeSequenceVertexSet base.core;
    ∀ (c : Fin k), ¬alpha = c →
    let roots : Finset (V ⊕ E) :=
        {z : V ⊕ E | match z with | Sum.inl u => u ∉ X | Sum.inr _ => False};
    let rho : PartialEdgeColoring E k := fun (f : E) ↦ if
    ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha c z then if phi f = some alpha then
        some c else if phi f = some c then some alpha else phi f else phi f;
    let selected : E → Prop := fun (f : E) ↦
    ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha c z; (
    ∀ (f : E), rho f = some beta ↔ phi f = some beta) → (
    ∀ u ∉ X,
    ∀ (f : E), Incident G u f → phi f = some alpha ∨ phi f = some c → selected f) → (
    ∀ (u v : V) (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath base.core phi alpha beta u v P →
    ∀ (f : E), Sum.inr f ∈ P.support →
    ∃ (w : V), Sum.inl w ∈ P.support ∧ w ∉ X ∧ Incident G w f) →
    ∀ (u v : V) (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath base.core phi alpha beta u v P →
    ∃ (Q : (TwoColorIncidenceGraph G rho c beta).Walk (Sum.inl u) (Sum.inl v)), TreeExitPath
        base.core rho c beta u v Q ∧ Q.support = P.support := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base alpha beta X c hac roots rho selected hbetaFixed
      selectedOfOutside pathEdgeOutside u v P hExit
  have selectedAlphaEdge : ∀ f : E, Sum.inr f ∈ P.support →
      phi f = some alpha → selected f := by
    intro f hfP hfa
    obtain ⟨w, hwP, hwX, hwf⟩ := pathEdgeOutside u v P hExit f hfP
    exact selectedOfOutside w hwX f hwf (Or.inl hfa)
  have adjacencyTransport :
    ∀ (z w : Sum V E), z ∈ P.support → w ∈ P.support → (TwoColorIncidenceGraph G phi alpha
        beta).Adj z w → (TwoColorIncidenceGraph G rho c beta).Adj z w := by
    intro z w hzP hwP hadj
    cases z with
    | inl z =>
        cases w with
        | inl w => exact False.elim hadj
        | inr f =>
            rcases hadj with ⟨hzf, hcolor⟩
            refine ⟨hzf, ?_⟩
            rcases hcolor with hfa | hfb
            · left
              have hsel := selectedAlphaEdge f hwP hfa
              change ∃ z ∈ roots,
                Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
              simp only [rho]
              rw [ite_eq_left hsel, ite_eq_left hfa]
            · right
              exact (hbetaFixed f).2 hfb
    | inr f =>
        cases w with
        | inl w =>
            rcases hadj with ⟨hwf, hcolor⟩
            refine ⟨hwf, ?_⟩
            rcases hcolor with hfa | hfb
            · left
              have hsel := selectedAlphaEdge f hzP hfa
              change ∃ z ∈ roots,
                Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
              simp only [rho]
              rw [ite_eq_left hsel, ite_eq_left hfa]
            · right
              exact (hbetaFixed f).2 hfb
        | inr e => exact False.elim hadj
  have rebuild : ∀ {s t : Sum V E}
      (R : (TwoColorIncidenceGraph G phi alpha beta).Walk s t),
      (∀ z, z ∈ R.support → z ∈ P.support) →
      ∃ Q : (TwoColorIncidenceGraph G rho c beta).Walk s t,
        Q.support = R.support ∧ Q.length = R.length := by
    intro s t R
    induction R with
    | nil =>
        intro hsub
        exact ⟨.nil, rfl, rfl⟩
    | @cons s w t hsw R ih =>
        intro hsub
        have hsP : s ∈ P.support := hsub s (by simp)
        have hwP : w ∈ P.support := hsub w (by simp)
        obtain ⟨Q, hQsupport, hQlength⟩ := ih (by
          intro z hz
          exact hsub z (by simp [hz]))
        have hsw' := adjacencyTransport s w hsP hwP hsw
        refine ⟨.cons hsw' Q, ?_, ?_⟩
        · simp [hQsupport]
        · simp [hQlength]
  obtain ⟨Q, hQsupport, hQlength⟩ := rebuild P (by
    intro z hz
    exact hz)
  have hQpath : Q.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [hQsupport]
    exact hExit.1.support_nodup
  have hmissing : c ∈ MissingColors G rho u ∨
      beta ∈ MissingColors G rho u := by
    rcases hExit.2.2.2.2.1 with halphaMissing | hbetaMissing
    · left
      have huX : u ∉ X := by simpa [X] using hExit.2.2.1
      have hnotAlpha : alpha ∉ PresentColors G phi u := by
        simpa [MissingColors] using halphaMissing
      have hnotC : c ∉ PresentColors G rho u := by
        intro hcPresent
        obtain ⟨f, huf, hrhof⟩ := by
          simpa [PresentColors] using hcPresent
        by_cases hsel : selected f
        · change ∃ z ∈ roots,
            Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
          by_cases hfa : phi f = some alpha
          · apply hnotAlpha
            simpa [PresentColors] using
              (show ∃ q, Incident G u q ∧ phi q = some alpha from
                ⟨f, huf, hfa⟩)
          · by_cases hfc : phi f = some c
            · have hrhoAlpha : rho f = some alpha := by
                simp only [rho]
                rw [ite_eq_left hsel, ite_eq_right hfa, ite_eq_left hfc]
              have : some alpha = some c := hrhoAlpha.symm.trans hrhof
              exact hac (Option.some.inj this)
            · have hrhoOld : rho f = phi f := by
                simp only [rho]
                rw [ite_eq_left hsel, ite_eq_right hfa, ite_eq_right hfc]
              exact hfc (hrhoOld.symm.trans hrhof)
        · change ¬ ∃ z ∈ roots,
            Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
          have hfc : phi f = some c := by
            have hrhoOld : rho f = phi f := by
              simp only [rho]
              rw [ite_eq_right hsel]
            exact hrhoOld.symm.trans hrhof
          have hchosen := selectedOfOutside u huX f huf (Or.inr hfc)
          exact hsel hchosen
      simpa [MissingColors] using hnotC
    · right
      have hnotBeta : beta ∉ PresentColors G phi u := by
        simpa [MissingColors] using hbetaMissing
      have hnotBetaRho : beta ∉ PresentColors G rho u := by
        intro hbPresent
        obtain ⟨f, huf, hrf⟩ := by
          simpa [PresentColors] using hbPresent
        apply hnotBeta
        simpa [PresentColors] using
          (show ∃ q, Incident G u q ∧ phi q = some beta from
            ⟨f, huf, (hbetaFixed f).1 hrf⟩)
      simpa [MissingColors] using hnotBetaRho
  refine ⟨Q, ?_, hQsupport⟩
  refine ⟨hQpath, ?_, hExit.2.2.1, hExit.2.2.2.1, hmissing, ?_⟩
  · rw [hQlength]
    exact hExit.2.1
  · intro w hw
    rw [hQsupport]
    exact hExit.2.2.2.2.2 w hw

private theorem helper_hcClosedRho_796.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (alpha : Fin k),
    let X : Finset V := TreeSequenceVertexSet base.core;
    ∀ (c : Fin k), TreeColorSetClosed G phi base.core { c } →
    let roots : Finset (V ⊕ E) :=
        {z : V ⊕ E | match z with | Sum.inl u => u ∉ X | Sum.inr _ => False};
    let rho : PartialEdgeColoring E k := fun (f : E) ↦ if
    ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha c z then if phi f = some alpha then
        some c else if phi f = some c then some alpha else phi f else phi f; (IsProperEdgeColoring
        G rho ∧ IsOneEdgeUncolored rho e0 ∧ StableColoring base.core ∅ phi rho ∧
        TreeColoringInvariant base.core phi rho ∧
    ∀ (f : E), TreeIncidentEdge base.core f → rho f = phi f) → TreeColorSetClosed G rho base.core
        { c } := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base alpha X c hcClosed roots rho hstableCore
  unfold TreeColorSetClosed
  intro d hd
  have hdc : d = c := Finset.mem_singleton.mp hd
  subst d
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  have hfBoundary : f ∈ BoundaryEdges G X ∧ rho f = some c := by
    simpa [BoundaryColorEdges] using hf
  have hfIncident : TreeIncidentEdge base.core f := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hfBoundary
    obtain ⟨u, huX, v, hvX, hends⟩ := hfBoundary.1
    exact ⟨u, by simpa [X] using huX, by
      unfold Incident
      rw [hends]
      exact Sym2.mem_mk_left _ _⟩
  have hfixed := hstableCore.2.2.2.2 f hfIncident
  have hfOld : f ∈ BoundaryColorEdges G phi X c := by
    have hcolor : phi f = some c := by
      rw [← hfixed]
      exact hfBoundary.2
    simp [BoundaryColorEdges, hfBoundary.1, hcolor]
  have hempty := hcClosed c (by simp)
  rw [hempty] at hfOld
  simp at hfOld

private theorem helper_branch_588.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 →
    ∀ (base : HierarchyBase ett phi) (_ : TashkinovHierarchy ett base) (alpha beta : Fin k), alpha
        ≠ beta →
    ∀ (a₁ b₁ a₂ b₂ : V) (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₁) (Sum.inl
        b₁)) (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₂) (Sum.inl b₂)),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let X : Finset V := TreeSequenceVertexSet base.core;
    let x : V := Tn.vertex base.supportPosition; x ∈ TreeSequenceVertexSet Tn → X =
        TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet base.closure → x ∈ X →
    ∀ c ∈ MissingColors G phi x, TreeColorSetClosed G phi base.core { c } → TreeColorSetClosed G
        phi base.core { alpha } → TreeExitPath base.core phi alpha beta a₁ b₁ P₁ → TreeExitPath
        base.core phi alpha beta a₂ b₂ P₂ → c ≠ beta → (
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → CombinedStableColoring Tn base.closure (TashkinovStoredColors ett.series.data n) phi
        sigma → c ∈ TreeMissingColors sigma base.core → TreeColorSetClosed G sigma base.core { c }
        →
    ∀ (Q₁ : (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₁) (Sum.inl b₁)) (Q₂ :
        (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₂) (Sum.inl b₂)), TreeExitPath
        base.core sigma c beta a₁ b₁ Q₁ → TreeExitPath base.core sigma c beta a₂ b₂ Q₂ → False) →
        ¬alpha = c → False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hproper hone base H alpha beta hne a₁ b₁ a₂ b₂ P₁ P₂ n
      Tn X x hxT hcoreVertices hxX c hcxMissing hcClosed halphaClosed hP1 hP2 hcNeBeta finish hac
  have componentOutside : ∀ (u : V), u ∉ X → ∀ (v : V),
      Sum.inl v ∈ TwoColorComponent G phi alpha c (Sum.inl u) →
        v ∉ X := by
    exact @helper_componentOutside_422 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T phi ett base alpha c hcClosed halphaClosed
  let roots : Finset (Sum V E) := Finset.univ.filter fun z =>
    match z with
    | Sum.inl u => u ∉ X
    | Sum.inr _ => False
  let rho : PartialEdgeColoring E k := fun f =>
    if ∃ z ∈ roots,
        Sum.inr f ∈ TwoColorComponent G phi alpha c z then
      if phi f = some alpha then some c
      else if phi f = some c then some alpha
      else phi f
    else phi f
  have hrecolorCore : OutsideKempeRecoloring base.core phi rho alpha c := by
    unfold OutsideKempeRecoloring
    refine ⟨hac, roots, ?_, ?_⟩
    · intro z hz v hvComponent
      simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      cases z with
      | inl u =>
          exact componentOutside u hz v hvComponent
      | inr f =>
          exact False.elim hz
    · intro f
      rfl
  have hTsubset : TreeSequenceVertexSet Tn ⊆ X := by
    rw [hcoreVertices]
    exact Finset.subset_union_left
  have hRsubset : TreeSequenceVertexSet base.closure ⊆ X := by
    rw [hcoreVertices]
    exact Finset.subset_union_right
  have restrictRecolor : ∀ (S : TreeSequence G e0),
      TreeSequenceVertexSet S ⊆ X →
      OutsideKempeRecoloring S phi rho alpha c := by
    intro S hsub
    rcases hrecolorCore with ⟨hneac, roots', hout, hformula⟩
    refine ⟨hneac, roots', ?_, hformula⟩
    intro z hz v hvComponent hvS
    exact hout z hz v hvComponent (hsub hvS)
  have hrecolorT := restrictRecolor Tn hTsubset
  have hrecolorR := restrictRecolor base.closure hRsubset
  have hstableCore := OutsideKempeRecoloringStable G e0 base.core ∅
    phi rho alpha c hproper hone hrecolorCore
  have hstableT := OutsideKempeRecoloringStable G e0 Tn
    (TashkinovStoredColors ett.series.data n)
    phi rho alpha c hproper hone hrecolorT
  have hstableR := OutsideKempeRecoloringStable G e0 base.closure ∅
    phi rho alpha c hproper hone hrecolorR
  have hrhoProper : IsProperEdgeColoring G rho := hstableCore.1
  have hrhoOne : IsOneEdgeUncolored rho e0 := hstableCore.2.1
  have hrhoCombined : CombinedStableColoring Tn base.closure
      (TashkinovStoredColors ett.series.data n) phi rho := by
    exact ⟨hstableT.2.2.1, hstableR.2.2.1⟩
  let selected : E → Prop := fun f => ∃ z ∈ roots,
    Sum.inr f ∈ TwoColorComponent G phi alpha c z
  have hbetaFixed : ∀ f : E,
      rho f = some beta ↔ phi f = some beta := by
    intro f
    by_cases hsel : selected f
    · change ∃ z ∈ roots,
        Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
      simp only [rho]
      rw [ite_eq_left hsel]
      by_cases hfa : phi f = some alpha
      · rw [ite_eq_left hfa, hfa]
        simp [hcNeBeta, hne]
      · rw [ite_eq_right hfa]
        by_cases hfc : phi f = some c
        · rw [ite_eq_left hfc, hfc]
          simp [hne, hcNeBeta]
        · rw [ite_eq_right hfc]
    · change ¬ ∃ z ∈ roots,
        Sum.inr f ∈ TwoColorComponent G phi alpha c z at hsel
      simp only [rho]
      rw [ite_eq_right hsel]
  have selectedOfOutside : ∀ (u : V), u ∉ X → ∀ (f : E),
      Incident G u f →
      (phi f = some alpha ∨ phi f = some c) → selected f := by
    intro u hu f huf hfcolor
    refine ⟨Sum.inl u, ?_, ?_⟩
    · simp [roots, hu]
    · change (TwoColorIncidenceGraph G phi alpha c).connectedComponentMk
          (Sum.inr f) =
        (TwoColorIncidenceGraph G phi alpha c).connectedComponentMk
          (Sum.inl u)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (TwoColorIncidenceGraph G phi alpha c).Adj
            (Sum.inl u) (Sum.inr f) from ⟨huf, hfcolor⟩)).symm
  have pathEdgeOutside :
    ∀ (u v : V) (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath base.core phi alpha beta u v P →
    ∀ f : E, Sum.inr f ∈ P.support →
    ∃ w : V, Sum.inl w ∈ P.support ∧ w ∉ X ∧ Incident G w f := by
    exact @helper_pathEdgeOutside_590 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 input T phi ett base alpha beta
  have transportExit :
    ∀ (u v : V) (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath base.core phi alpha beta u v P →
    ∃ Q : (TwoColorIncidenceGraph G rho c beta).Walk (Sum.inl u) (Sum.inl v), TreeExitPath
        base.core rho c beta u v Q ∧ Q.support = P.support := by
    exact @helper_transportExit_653 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base alpha beta c hac hbetaFixed selectedOfOutside pathEdgeOutside
  obtain ⟨Q₁, hQ₁, hQ₁Support⟩ := transportExit a₁ b₁ P₁ hP1
  obtain ⟨Q₂, hQ₂, hQ₂Support⟩ := transportExit a₂ b₂ P₂ hP2
  have hcMissingRho : c ∈ TreeMissingColors rho base.core := by
    unfold TreeMissingColors
    refine Finset.mem_biUnion.mpr ⟨x, by simpa [X] using hxX, ?_⟩
    rw [hstableT.2.2.1.2 x hxT]
    exact hcxMissing
  have hcClosedRho : TreeColorSetClosed G rho base.core {c} := by
    exact @helper_hcClosedRho_796 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base alpha c hcClosed hstableCore
  exact finish rho hrhoProper hrhoOne hrhoCombined hcMissingRho hcClosedRho
    Q₁ Q₂ hQ₁ hQ₂

private theorem helper_presentBound_921.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let x : V := Tn.vertex base.supportPosition; (PresentColors G phi x).card ≤ Degree G x := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base n Tn x
  have chooseEdge (d : {d : Fin k // d ∈ PresentColors G phi x}) :
      ∃ f, Incident G x f ∧ phi f = some d.1 := by
    simpa [PresentColors] using d.property
  let select : {d : Fin k // d ∈ PresentColors G phi x} →
      {f : E // Incident G x f} := fun d =>
    ⟨Classical.choose (chooseEdge d),
      (Classical.choose_spec (chooseEdge d)).1⟩
  have selectColor : ∀ d, phi (select d).1 = some d.1 := by
    intro d
    exact (Classical.choose_spec (chooseEdge d)).2
  have selectInjective : Function.Injective select := by
    intro d e hde
    apply Subtype.ext
    apply Option.some.inj
    calc
      some (d : Fin k) = phi (select d).1 := (selectColor d).symm
      _ = phi (select e).1 := by rw [hde]
      _ = some (e : Fin k) := selectColor e
  let : Fintype {d : Fin k // d ∈ PresentColors G phi x} :=
    Fintype.ofFinite _
  have hcard := Fintype.card_le_of_injective select selectInjective
  change (PresentColors G phi x).card ≤
    (Finset.univ.filter (fun f => Incident G x f)).card
  simpa [Fintype.card_subtype] using hcard

private theorem helper_hlowerElem_973.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi) (_ : TashkinovHierarchy ett base),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; ColoredVertexSetElementary G
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (TreeSequenceVertexSet Tn) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hMP hpositive hlower base H n Tn
  by_cases honeRound : ett.rounds = 1
  · have htech := TechnicalTheoremBase G k ett.rounds e0 input ett.series
    have hTn : Tn = ett.series.data.tree ⟨1, by omega⟩ := by
      apply congrArg (fun i : Fin (ett.rounds + 2) => ett.series.data.tree i)
      apply Fin.ext
      simp [n, honeRound]
    have hcol : (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) = 0 := by
      apply Fin.ext
      simp [honeRound]
    rw [hTn, hcol]
    exact htech.1
  · have hgt : 1 < ett.rounds := by omega
    obtain ⟨pred, hpredRound, hpredMP, htrees, hdata⟩ :=
      CertifiedETTPredecessor G k e0 input T phi ett hMP hgt
    have hpredElem := hlower pred (by omega) (by omega) hpredMP
    have hp : ColoredVertexSetElementary G
        (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
        (TreeSequenceVertexSet
          (ett.series.data.tree ⟨ett.rounds, by omega⟩)) := hpredElem.1
    have heq : (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
        (Fin.last ett.rounds).castSucc := by
      apply Fin.ext
      rfl
    rw [heq] at hp
    simpa [Tn, n] using hp

lemma Step1ZeroDividerAnchorPE {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (hdividerZero : H.dividerCount = 0)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (halpha : alpha ∈ TreeMissingColors phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)))
    (hclosed : TreeColorSetClosed G phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)) {alpha})
    (a₁ b₁ a₂ b₂ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (hP₁ : TreeExitPath
      (HierarchyStarredStage H (Fin.last H.dividerCount))
      phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath
      (HierarchyStarredStage H (Fin.last H.dividerCount))
      phi alpha beta a₂ b₂ P₂)
    (hpaths : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (ha : a₁ ≠ a₂)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE) :
    False := by
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  let X : Finset V := TreeSequenceVertexSet base.core
  have hphi : phi = ett.series.data.coloring n := by
    simpa [n] using ett.generatingColoring
  have hstar : HierarchyStarredStage H (Fin.last H.dividerCount) =
      base.core := by
    have hlast : Fin.last H.dividerCount =
        (0 : Fin (H.dividerCount + 1)) := by
      apply Fin.ext
      simp [hdividerZero]
    rw [hlast]
    rfl
  have hparallel := base.parallel hPE
  rcases hparallel with ⟨hsupport, hclosure, hunion⟩
  obtain ⟨unionCert⟩ := hunion
  let x : V := Tn.vertex base.supportPosition
  have hxT : x ∈ TreeSequenceVertexSet Tn := by
    simp [x, TreeSequenceVertexSet]
  have initialVertices : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hab y hy
    unfold TreeSequenceVertexSet at hy ⊢
    simp only [Finset.mem_image] at hy ⊢
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨hlen, hvertices, hedges⟩ := hab
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
    exact hvertices i
  have augmentationVertices : ∀ {A B : TreeSequence G e0},
      TashkinovAugmentationSequence phi A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hab
    unfold TashkinovAugmentationSequence at hab
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => exact Finset.Subset.rfl
    | @head A B hstep htail ih =>
        intro y hy
        apply ih
        exact initialVertices hstep.2.1 hy
  have hxPrefix : x ∈ TreeSequenceVertexSet
      (TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
        (Nat.le_of_lt_succ base.supportPosition.isLt)) := by
    unfold TreeSequenceVertexSet
    simp only [Finset.mem_image]
    let i : Fin (base.supportPosition.val + 1) :=
      ⟨base.supportPosition.val, Nat.lt_succ_self _⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simp [TreeSequencePrefix, i, x]
  have hxR : x ∈ TreeSequenceVertexSet base.closure := by
    exact augmentationVertices hclosure.1 hxPrefix
  have hcoreVertices : X =
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet base.closure := by
    simpa [X, Tn, n] using unionCert.vertexSet
  have hxX : x ∈ X := by
    rw [hcoreVertices]
    exact Finset.mem_union_left _ hxT
  have degreeBound : MaximumDegree G + 1 ≤ k := by
    have step := ett.series.certified 0
    cases step with
    | initial triple => exact triple.2.2.1
  have presentBound : (PresentColors G phi x).card ≤ Degree G x := by
    exact @helper_presentBound_921 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base
  have degreeAt : Degree G x ≤ MaximumDegree G := by
    unfold MaximumDegree
    exact Finset.le_max' _ _ (Finset.mem_insert.mpr (Or.inr
      (Finset.mem_image.mpr ⟨x, by simp⟩)))
  have missingAtX : (MissingColors G phi x).Nonempty := by
    by_contra hempty
    have hmissingEmpty : MissingColors G phi x = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hall : PresentColors G phi x = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro d
      by_contra hd
      have hm : d ∈ MissingColors G phi x := by
        simp [MissingColors, hd]
      rw [hmissingEmpty] at hm
      exact Finset.notMem_empty d hm
    have hk : k ≤ Degree G x := by
      have := presentBound
      simpa [hall] using this
    omega
  obtain ⟨c, hcxMissing⟩ := missingAtX
  have hcT : c ∈ TreeMissingColors phi Tn := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨x, hxT, hcxMissing⟩
  have hcR : c ∈ TreeMissingColors phi base.closure := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨x, hxR, hcxMissing⟩
  have hlowerElem : ColoredVertexSetElementary G
      (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
      (TreeSequenceVertexSet Tn) := by
    exact @helper_hlowerElem_973 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett hMP hpositive hlower base H
  have hcommon := ParallelCommonMissingClosed G k e0 input T phi phi ett
    hpositive base hphi hPE hlowerElem
  have hcClosed : TreeColorSetClosed G phi base.core {c} := by
    unfold TreeColorSetClosed at hcommon ⊢
    intro d hd
    have hdc : d = c := Finset.mem_singleton.mp hd
    subst d
    exact hcommon c (Finset.mem_inter.mpr ⟨hcT, hcR⟩)
  have halphaClosed : TreeColorSetClosed G phi base.core {alpha} := by
    simpa [hstar] using hclosed
  have hP1 : TreeExitPath base.core phi alpha beta a₁ b₁ P₁ := by
    simpa [hstar] using hP₁
  have hP2 : TreeExitPath base.core phi alpha beta a₂ b₂ P₂ := by
    simpa [hstar] using hP₂
  have exitBoundary :
    ∀ (u v : V) (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath base.core phi alpha beta u v P →
    ∃ f : E, f ∈ BoundaryColorEdges G phi X beta ∧ Incident G v f ∧ Sum.inr f ∈ P.support := by
    exact @helper_exitBoundary_285 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base alpha beta halphaClosed
  obtain ⟨f₁, hf₁Boundary, hf₁Incident, hf₁Support⟩ :=
    exitBoundary a₁ b₁ P₁ hP1
  obtain ⟨f₂, hf₂Boundary, hf₂Incident, hf₂Support⟩ :=
    exitBoundary a₂ b₂ P₂ hP2
  have hbetaPresent : beta ∈ PresentColors G phi x := by
    have hbetaNotMissing : beta ∉ MissingColors G phi x := by
      intro hbetaMissing
      have hbetaT : beta ∈ TreeMissingColors phi Tn := by
        unfold TreeMissingColors
        exact Finset.mem_biUnion.mpr ⟨x, hxT, hbetaMissing⟩
      have hbetaR : beta ∈ TreeMissingColors phi base.closure := by
        unfold TreeMissingColors
        exact Finset.mem_biUnion.mpr ⟨x, hxR, hbetaMissing⟩
      have hbetaClosed : TreeColorSetClosed G phi base.core {beta} := by
        unfold TreeColorSetClosed at hcommon ⊢
        intro d hd
        have hdb : d = beta := Finset.mem_singleton.mp hd
        subst d
        exact hcommon beta (Finset.mem_inter.mpr ⟨hbetaT, hbetaR⟩)
      have hempty := hbetaClosed beta (by simp)
      rw [hempty] at hf₁Boundary
      simp at hf₁Boundary
    simpa [MissingColors] using hbetaNotMissing
  have hcNeBeta : c ≠ beta := by
    intro hcb
    subst c
    have hnot : beta ∉ PresentColors G phi x := by
      simpa [MissingColors] using hcxMissing
    exact hnot hbetaPresent
  have finish :
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → CombinedStableColoring Tn base.closure (TashkinovStoredColors ett.series.data n) phi
        sigma → c ∈ TreeMissingColors sigma base.core → TreeColorSetClosed G sigma base.core {c} →
    ∀ (Q₁ : (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₁) (Sum.inl b₁)) (Q₂ :
        (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₂) (Sum.inl b₂)), TreeExitPath
        base.core sigma c beta a₁ b₁ Q₁ → TreeExitPath base.core sigma c beta a₂ b₂ Q₂ → False := by
    exact @helper_finish_411 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett hMP hpositive hlower base beta a₁ b₁ a₂ b₂ ha hPE hxT hxR hxX c
        hcxMissing hcNeBeta
  by_cases hac : alpha = c
  · subst alpha
    have stableRefl : ∀ (S : TreeSequence G e0) (C : Finset (Fin k)),
        StableColoring S C phi phi := by
      intro S C
      constructor
      · intro f hf hcolor
        rfl
      · intro v hv
        rfl
    have hcombined : CombinedStableColoring Tn base.closure
        (TashkinovStoredColors ett.series.data n) phi phi :=
      ⟨stableRefl Tn _, stableRefl base.closure ∅⟩
    have hcMissingCore : c ∈ TreeMissingColors phi base.core := by
      unfold TreeMissingColors
      exact Finset.mem_biUnion.mpr
        ⟨x, by simpa [X] using hxX, hcxMissing⟩
    exact finish phi hproper hone hcombined hcMissingCore hcClosed P₁ P₂ hP1 hP2
  · exact @helper_branch_588 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett hproper hone base H alpha beta hne a₁ b₁ a₂ b₂ P₁ P₂ hxT hcoreVertices hxX
      c hcxMissing hcClosed halphaClosed hP1 hP2 hcNeBeta finish hac
end GoldbergSeymour

end
