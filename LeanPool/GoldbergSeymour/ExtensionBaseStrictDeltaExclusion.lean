/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesTreeFacts

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.ExtensionBaseSupportOrder
public import LeanPool.GoldbergSeymour.SameColorSeriesPreserved
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Extension Base Strict Delta Exclusion

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hsClosed_282.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (_ s _ : Fin ett.rounds), (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.kind s.succ = some TashkinovExtensionKind.PE
    → ColoredVertexSetClosed G ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring s.castSucc) (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree s.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett q s t
  set series : TashkinovSeries G k ett.rounds e0 input := ett.series
  intro hsKind
  have step := series.certified s.succ
  generalize hz : s.succ = z at step
  cases step with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      have hv := congrArg Fin.val hz
      simp at hv
  | SE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hrs : r = s := by
        apply Fin.ext
        have hv := congrArg Fin.val hz
        simp at hv ⊢
        omega
      subst r
      rw [currentKind] at hsKind
      simp at hsKind
  | RE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hrs : r = s := by
        apply Fin.ext
        have hv := congrArg Fin.val hz
        simp at hv ⊢
        omega
      subst r
      rw [currentKind] at hsKind
      simp at hsKind
  | PE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
      have hrs : r = s := by
        apply Fin.ext
        have hv := congrArg Fin.val hz
        simp at hv ⊢
        omega
      subst r
      unfold ColoredVertexSetClosed
      intro f c v hf hv hfc hcm
      exact previousClosed hf hv hfc hcm

private theorem helper_colorCarry_371.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (_ s t : Fin ett.rounds) (deltaT : Fin
    k), (↑s : ℕ) < (↑t : ℕ) → ∀ u ∈ TreeSequenceVertexSet (ett.series.data.tree
    s.succ.castSucc), deltaT ∈ MissingColors G (ett.series.data.coloring s.castSucc) u →
    deltaT ∈ TreeMissingColors ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring t.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc) ∪ TashkinovStoredColors (ett.series : TashkinovSeries G
    k ett.rounds e0 input).data t.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett q s t deltaT hst
  set series : TashkinovSeries G k ett.rounds e0 input := ett.series
  intro u huS huMissing
  have start : deltaT ∈
      TreeMissingColors (series.data.coloring s.castSucc)
          (series.data.tree s.succ.castSucc) ∪
        TashkinovStoredColors series.data s.castSucc :=
    Finset.mem_union_left _ (by
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨u, huS, huMissing⟩)
  have claim :
    ∀ (n : ℕ), s.val ≤ n → n < ett.rounds →
    ∀ r : Fin ett.rounds, r.val = n → deltaT ∈ TreeMissingColors (series.data.coloring r.castSucc)
        (series.data.tree r.succ.castSucc) ∪ TashkinovStoredColors series.data r.castSucc := by
    intro n hsn
    induction n, hsn using Nat.le_induction with
    | base =>
        intro hn r hr
        have hrs : r = s := by apply Fin.ext; omega
        simpa [hrs] using start
    | succ n hn ih =>
        intro hrounds r hr
        let p : Fin ett.rounds := ⟨n, by omega⟩
        have hold := ih (by omega) p rfl
        have hfirst := (HkuMissingStoredMonotone G k ett.rounds e0 input
          series p).1 hold
        have hsecond := (HkuMissingStoredMonotone G k ett.rounds e0 input
          series p).2 hfirst
        have hcolor : p.succ = r.castSucc := by
          apply Fin.ext
          simp [p, hr]
        have htree : p.succ.succ = r.succ.castSucc := by
          apply Fin.ext
          simp [p, hr]
        simpa [hcolor, htree] using hsecond
  exact claim t.val (Nat.le_of_lt hst) t.isLt t rfl

private theorem helper_edgeAtRho_418.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input :
    PartialEdgeColoring E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (_ s t : Fin ett.rounds) (hst :
    (↑s : ℕ) < (↑t : ℕ)), ∀ u ∈ TreeSequenceVertexSet (ett.series.data.tree s.succ.castSucc),
    TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    s.succ.castSucc) ⊆ TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc) → ∀ (rho : PartialEdgeColoring E k) (choice :
    MaximumDefectiveChoice G e0 ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc) (TashkinovStoredColors (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data t.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring t.castSucc)), StableColoring ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree t.succ.castSucc) (insert choice.color
    (TashkinovStoredColors (ett.series : TashkinovSeries G k ett.rounds e0 input).data
    t.castSucc)) choice.selected rho → choice.color ∈ MissingColors G
    (ett.series.data.coloring s.castSucc) u → (∀ x ∈ TreeSequenceVertexSet ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree s.succ.castSucc), x ≠ u → ∃ (f : E),
    Incident G x f ∧ (ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring
    s.castSucc f = some choice.color ∧ f ∈ InternalEdges G (TreeSequenceVertexSet ((ett.series
    : TashkinovSeries G k ett.rounds e0 input).data.tree s.succ.castSucc))) → choice.color ∈
    TreeMissingColors ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring
    t.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    t.succ.castSucc) ∪ TashkinovStoredColors (ett.series : TashkinovSeries G k ett.rounds e0
    input).data t.castSucc → let beforeT : Fin ett.rounds := (⟨(↑t : ℕ) - (1 : ℕ),
    Decidable.byContradiction fun (a : ¬(↑t : ℕ) - (1 : ℕ) < ett.rounds) => by omega⟩ : Fin
    ett.rounds); beforeT.succ = t.castSucc → (↑s : ℕ) ≤ (↑beforeT : ℕ) → ∀ x ∈
    TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    s.succ.castSucc), x ≠ u → ∃ (f : E), Incident G x f ∧ f ∈ InternalEdges G
    (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    t.succ.castSucc)) ∧ rho f = some choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett q s t hst
  set series : TashkinovSeries G k ett.rounds e0 input := ett.series
  intro u huS hsSubset rho choice rhoStable huMissing witnessEdge colorCarry beforeT hbeforeSucc
      hsbefore x hxS hxu
  obtain ⟨f, hxf, hfOldColor, hfInternalS⟩ := witnessEdge x hxS hxu
  have hfTreeS : TreeIncidentEdge
      (series.data.tree s.succ.castSucc) f := ⟨x, hxS, hxf⟩
  have hfBefore := (SameColorSeriesPreserved G k ett.rounds e0 input
    series s beforeT hsbefore f choice.color hfTreeS hfOldColor
    (Finset.mem_union_left _ (by
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨u, huS, huMissing⟩))).2 hfInternalS
  have hfAtT : series.data.coloring t.castSucc f =
      some choice.color := by
    rw [hbeforeSucc] at hfBefore
    exact hfBefore.trans hfOldColor
  have hfInternalT : f ∈ InternalEdges G
      (TreeSequenceVertexSet (series.data.tree t.succ.castSucc)) := by
    simp only [InternalEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hfInternalS ⊢
    intro y hyf
    exact hsSubset (hfInternalS y hyf)
  have hxT := hsSubset hxS
  have hfTreeT : TreeIncidentEdge
      (series.data.tree t.succ.castSucc) f := ⟨x, hxT, hxf⟩
  have hfSelected : choice.selected f = some choice.color :=
    (choice.selectedStable.1 f hfTreeT
      ⟨choice.color, colorCarry, hfAtT⟩).trans hfAtT
  have hfRho : rho f = some choice.color :=
    (rhoStable.1 f hfTreeT
      ⟨choice.color, Finset.mem_union_right _
        (Finset.mem_insert_self _ _), hfSelected⟩).trans hfSelected
  exact ⟨f, hxf, hfInternalT, hfRho⟩

private theorem helper_noBoundaryOnOld_455.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (s t : Fin ett.rounds), ∀ (u : V) (rho :
    PartialEdgeColoring E k), IsProperEdgeColoring G rho → ∀ (choice : MaximumDefectiveChoice
    G e0 ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc)
    (TashkinovStoredColors (ett.series : TashkinovSeries G k ett.rounds e0 input).data
    t.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring
    t.castSucc)), (∀ x ∈ TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds
    e0 input).data.tree s.succ.castSucc), x ≠ u → ∃ (f : E), Incident G x f ∧ f ∈
    InternalEdges G (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc)) ∧ rho f = some choice.color) → ∀ x ∈
    TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    s.succ.castSucc), x ≠ u → ¬BoundaryColorVertex G rho (TreeSequenceVertexSet ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc)) choice.color x := by
  classical
  intro V E _ _ _ G k e0 input T generating ett s t
  set series : TashkinovSeries G k ett.rounds e0 input := ett.series
  intro u rho rhoProper choice edgeAtRho x hxS hxu hxBoundary
  obtain ⟨f, hxf, hfInternal, hfColor⟩ := edgeAtRho x hxS hxu
  obtain ⟨hxT, g, hgBoundaryColor, hxg⟩ := hxBoundary
  have hgBoundary : g ∈ BoundaryEdges G
      (TreeSequenceVertexSet (series.data.tree t.succ.castSucc)) :=
    (Finset.mem_filter.mp hgBoundaryColor).1
  have hgColor : rho g = some choice.color :=
    (Finset.mem_filter.mp hgBoundaryColor).2
  have hgf : g ≠ f := by
    intro hgf
    subst g
    have hfAll :
    ∀ y, Incident G y f → y ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc) := by
      simpa only [InternalEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hfInternal
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hgBoundary
    obtain ⟨a, ha, b, hb, hab⟩ := hgBoundary
    have hbf : Incident G b f := by simp [Incident, hab]
    exact hb (hfAll b hbf)
  exact (rhoProper hgf ⟨x, hxg, hxf⟩ hgColor) hfColor

private theorem helper_boundaryEq_516.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (t : Fin ett.rounds), ∀ (rho :
    PartialEdgeColoring E k), IsProperEdgeColoring G rho → IsOneEdgeUncolored rho e0 → ∀
    (choice : MaximumDefectiveChoice G e0 ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc) (TashkinovStoredColors (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data t.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring t.castSucc)), StableColoring ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree t.succ.castSucc) (insert choice.color
    (TashkinovStoredColors (ett.series : TashkinovSeries G k ett.rounds e0 input).data
    t.castSucc)) choice.selected rho → (∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc)) →
    TreeIncidentEdge ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    t.succ.castSucc) f) → BoundaryColorEdges G choice.selected (TreeSequenceVertexSet
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc))
    choice.color = BoundaryColorEdges G rho (TreeSequenceVertexSet ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc)) choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett t
  set series : TashkinovSeries G k ett.rounds e0 input := ett.series
  intro rho rhoProper rhoOne choice rhoStable boundaryIncident
  ext f
  simp only [BoundaryColorEdges, Finset.mem_filter]
  constructor
  · rintro ⟨hfBoundary, hfColor⟩
    refine ⟨hfBoundary, ?_⟩
    exact (rhoStable.1 f (boundaryIncident hfBoundary)
      ⟨choice.color, Finset.mem_union_right _
        (Finset.mem_insert_self _ _), hfColor⟩).trans hfColor
  · rintro ⟨hfBoundary, hfColor⟩
    refine ⟨hfBoundary, ?_⟩
    have hfixed := (sc1 G e0 (series.data.tree t.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors series.data t.castSucc))
      choice.selected rho choice.selectedProper
      choice.selectedOneUncolored rhoProper rhoOne).mp rhoStable f
        (boundaryIncident hfBoundary)
        (Or.inr ⟨choice.color,
          Finset.mem_union_right _ (Finset.mem_insert_self _ _),
          hfColor⟩)
    exact hfixed.symm.trans hfColor

private theorem helper_hvsStage_628.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (_ s t : Fin ett.rounds) (vs : V), (↑s :
    ℕ) < (↑t : ℕ) → ett.series.data.chosenVertex s.succ = some vs → (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.kind s.succ = some TashkinovExtensionKind.PE
    → ∀ (gamma : Fin k) (rho : PartialEdgeColoring E k), IsProperEdgeColoring G ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.coloring t.castSucc) → IsOneEdgeUncolored
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring t.castSucc) e0 →
    ColoredVertexSetClosed G ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring t.castSucc) (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree t.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring t.castSucc)
    (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    t.succ.castSucc)) → ¬Nonempty (RevisitingExtensionCertificate (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data t.castSucc) → ∀ (choice :
    MaximumDefectiveChoice G e0 ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc) (TashkinovStoredColors (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data t.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring t.castSucc)), (∃ (rho : PartialEdgeColoring E k),
    IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧ StableColoring ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc) (insert choice.color
    (TashkinovStoredColors (ett.series : TashkinovSeries G k ett.rounds e0 input).data
    t.castSucc)) choice.selected rho ∧ ¬Disjoint (MissingColors G rho choice.otherEndpoint)
    (TreeMissingColors rho ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    t.succ.castSucc))) → (ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring
    t.succ = TwoColorComponentSwap G rho gamma choice.color (Sum.inl choice.vertex) →
    (ett.series : TashkinovSeries G k ett.rounds e0 input).data.stored t.succ = {choice.color,
    gamma} → (ett.series : TashkinovSeries G k ett.rounds e0 input).data.connectingEdges
    t.succ = {choice.edge} → (ett.series : TashkinovSeries G k ett.rounds e0 input).data.kind
    t.succ = some TashkinovExtensionKind.PE → (ett.series : TashkinovSeries G k ett.rounds e0
    input).data.chosenVertex t.succ = some choice.vertex → (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.outsideVertex t.succ = some choice.otherEndpoint → (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.delta t.succ = some choice.color →
    (ett.series : TashkinovSeries G k ett.rounds e0 input).data.gamma t.succ = some gamma →
    TashkinovClosure ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring
    t.succ) ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc)
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.succ) →
    TreeSequenceInitialSegment ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.succ) → ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc).length < ((ett.series : TashkinovSeries G k ett.rounds
    e0 input).data.tree t.succ.succ).length → vs ∈ TreeSequenceVertexSet ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree s.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett q s t vs hst hsVertex
  set series : TashkinovSeries G k ett.rounds e0 input := ett.series
  intro hsKind gamma rho previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails currentColoring
      currentStored currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension
  have stepS := series.certified s.succ
  generalize hsZ : s.succ = z at stepS
  cases stepS with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      have hv := congrArg Fin.val hsZ
      simp at hv
  | SE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choiceS
      seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
      have hrs : r = s := by
        apply Fin.ext
        have hv := congrArg Fin.val hsZ
        simp at hv ⊢
        omega
      subst r
      rw [currentKind] at hsKind
      simp at hsKind
  | RE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring
      currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hrs : r = s := by
        apply Fin.ext
        have hv := congrArg Fin.val hsZ
        simp at hv ⊢
        omega
      subst r
      rw [currentKind] at hsKind
      simp at hsKind
  | PE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choiceS
      seriesAlternativeFails gammaS gammaRuleS secondStableS
      secondStableProperS secondStableOneUncoloredS
      secondStableRelationS exitWitnessS currentColoringS
      currentProperS currentOneUncoloredS currentStoredS
      currentEdgesS currentKindS currentVertexS currentOutsideS
      currentDeltaS currentGammaS closedExtensionS
      orderedExtensionS strictExtensionS =>
      have hrs : r = s := by
        apply Fin.ext
        have hv := congrArg Fin.val hsZ
        simp at hv ⊢
        omega
      subst r
      have hvs : choiceS.vertex = vs := by
        rw [currentVertexS] at hsVertex
        exact Option.some.inj hsVertex
      simpa [hvs] using choiceS.vertexDefective.1

private theorem helper_continuation_764.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
    terminalSupport ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds), (↑q : ℕ) + (1 : ℕ) =
    ett.rounds → ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
    ett.series.data.chosenVertex q.succ = some terminalSupport → (∀ (r a : Fin ett.rounds),
    (↑a : ℕ) < (↑r : ℕ) → ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 → StableColoring (ett.series.data.tree r.succ.castSucc)
    (TashkinovStoredColors ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)
    sigma → ∀ (delta : Fin k), DefectiveColor G sigma (TreeSequenceVertexSet
    (ett.series.data.tree r.succ.castSucc)) delta → ∀ (v : V), BoundaryColorVertex G sigma
    (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)) delta v → (∃ (w : V),
    BoundaryColorVertex G sigma (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc))
    delta w ∧ TreeVertexOrder (ett.series.data.tree r.succ.castSucc) w v) → ∀ (hvFinal : v ∈
    TreeSequenceVertexSet T), ETTFirstAppearanceIndex ett v hvFinal ≤ (↑a : ℕ) + (1 : ℕ) → ∀
    (va : V), ett.series.data.kind a.succ = some TashkinovExtensionKind.PE ∨
    ett.series.data.kind a.succ = some TashkinovExtensionKind.SE →
    ett.series.data.chosenVertex a.succ = some va → v = va ∨ TreeVertexOrder
    (ett.series.data.tree r.succ.castSucc) v va) → ∀ (s t : Fin ett.rounds), ∀ vs ∈
    TreeSequenceVertexSet T, s ∈ ExtensionBaseActiveIndices ett terminalSupport
    hterminalSupport → t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
    (↑s : ℕ) < (↑t : ℕ) → ett.series.data.chosenVertex s.succ = some vs → (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.kind s.succ = some TashkinovExtensionKind.PE
    → (∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → ∀ {x y : V},
    TreeVertexOrder A x y → TreeVertexOrder B x y) → (∀ {A : TreeSequence G e0} {x y z : V},
    TreeVertexOrder A x y → TreeVertexOrder A y z → TreeVertexOrder A x z) → (∀ {A B :
    TreeSequence G e0}, TreeSequenceInitialSegment A B → ∀ {x y : V}, y ∈
    TreeSequenceVertexSet A → TreeVertexOrder B x y → x ∈ TreeSequenceVertexSet A) → ∀ (u :
    V), TreeSequenceInitialSegment ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree s.succ.castSucc) T → TreeSequenceInitialSegment ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc) T → ∀ (gamma : Fin k)
    (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho → IsOneEdgeUncolored rho e0 →
    IsProperEdgeColoring G ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring t.castSucc) → IsOneEdgeUncolored ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.coloring t.castSucc) e0 → ColoredVertexSetClosed G ((ett.series
    : TashkinovSeries G k ett.rounds e0 input).data.coloring t.castSucc)
    (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    t.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.coloring t.castSucc) (TreeSequenceVertexSet ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc)) → ¬Nonempty
    (RevisitingExtensionCertificate (ett.series : TashkinovSeries G k ett.rounds e0
    input).data t.castSucc) → ∀ (choice : MaximumDefectiveChoice G e0 ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc) (TashkinovStoredColors
    (ett.series : TashkinovSeries G k ett.rounds e0 input).data t.castSucc) ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.coloring t.castSucc)), (∃ (rho :
    PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
    StableColoring ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    t.succ.castSucc) (insert choice.color (TashkinovStoredColors (ett.series : TashkinovSeries
    G k ett.rounds e0 input).data t.castSucc)) choice.selected rho ∧ ¬Disjoint (MissingColors
    G rho choice.otherEndpoint) (TreeMissingColors rho ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree t.succ.castSucc))) → (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.coloring t.succ = TwoColorComponentSwap G rho gamma choice.color
    (Sum.inl choice.vertex) → (ett.series : TashkinovSeries G k ett.rounds e0
    input).data.stored t.succ = {choice.color, gamma} → (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.connectingEdges t.succ = {choice.edge} → (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.kind t.succ = some TashkinovExtensionKind.PE
    → (ett.series : TashkinovSeries G k ett.rounds e0 input).data.chosenVertex t.succ = some
    choice.vertex → (ett.series : TashkinovSeries G k ett.rounds e0 input).data.outsideVertex
    t.succ = some choice.otherEndpoint → (ett.series : TashkinovSeries G k ett.rounds e0
    input).data.delta t.succ = some choice.color → (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.gamma t.succ = some gamma → TashkinovClosure ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.coloring t.succ) ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc) ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.succ) →
    TreeSequenceInitialSegment ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.succ) → ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc).length < ((ett.series : TashkinovSeries G k ett.rounds
    e0 input).data.tree t.succ.succ).length → choice.vertex ∈ TreeSequenceVertexSet T →
    ett.series.data.chosenVertex t.succ = some choice.vertex → (∀ x ∈ TreeSequenceVertexSet
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree s.succ.castSucc), x ≠ u
    → ¬BoundaryColorVertex G rho (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree t.succ.castSucc)) choice.color x) → StableColoring
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc)
    (TashkinovStoredColors (ett.series : TashkinovSeries G k ett.rounds e0 input).data
    t.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring
    t.castSucc) rho → BoundaryColorEdges G choice.selected (TreeSequenceVertexSet ((ett.series
    : TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc)) choice.color =
    BoundaryColorEdges G rho (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree t.succ.castSucc)) choice.color → choice.edge ∈
    BoundaryColorEdges G choice.selected (TreeSequenceVertexSet ((ett.series : TashkinovSeries
    G k ett.rounds e0 input).data.tree t.succ.castSucc)) choice.color → DefectiveColor G rho
    (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    t.succ.castSucc)) choice.color → False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport q hqTerminal
      hqKind hqVertex hLowerPartV s t vs hvsFinal hsActive htActive hst hsVertex
  set series : TashkinovSeries G k ett.rounds e0 input := ett.series
  intro hsKind orderTransfer orderTrans initialDownward u hsFinal htFinal gamma rho rhoProper
      rhoOne previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension hvtFinal htVertex noBoundaryOnOld rhoStableReference
      boundaryEq hchoiceBoundary hdefectiveRho
  have hchoiceBoundaryRho : choice.edge ∈ BoundaryColorEdges G rho
      (TreeSequenceVertexSet (series.data.tree t.succ.castSucc))
      choice.color := by
    rw [← boundaryEq]
    exact hchoiceBoundary
  obtain ⟨g, hgBoundary, hgne⟩ : ∃ g,
      g ∈ BoundaryColorEdges G rho
        (TreeSequenceVertexSet (series.data.tree t.succ.castSucc))
        choice.color ∧ g ≠ choice.edge := by
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Finset.one_lt_card.mp (show 1 <
        (BoundaryColorEdges G rho
          (TreeSequenceVertexSet
            (series.data.tree t.succ.castSucc)) choice.color).card by
          exact lt_of_lt_of_le Nat.one_lt_two hdefectiveRho)
    by_cases haChoice : a = choice.edge
    · exact ⟨b, hb, by
        intro hbChoice
        exact hab (haChoice.trans hbChoice.symm)⟩
    · exact ⟨a, ha, haChoice⟩
  have hgRaw : g ∈ BoundaryEdges G
      (TreeSequenceVertexSet (series.data.tree t.succ.castSucc)) :=
    (Finset.mem_filter.mp hgBoundary).1
  have hgColor : rho g = some choice.color :=
    (Finset.mem_filter.mp hgBoundary).2
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] at hgRaw
  obtain ⟨y, hyT, outside, houtside, hgEnds⟩ := hgRaw
  have hyg : Incident G y g := by simp [Incident, hgEnds]
  have hyBoundary : BoundaryColorVertex G rho
      (TreeSequenceVertexSet (series.data.tree t.succ.castSucc))
      choice.color y := ⟨hyT, g, hgBoundary, hyg⟩
  have hchoiceRhoColor : rho choice.edge = some choice.color :=
    (Finset.mem_filter.mp hchoiceBoundaryRho).2
  have hchoiceVertexT : choice.vertex ∈
      TreeSequenceVertexSet (series.data.tree t.succ.castSucc) :=
    choice.vertexDefective.1
  have hchoiceBoundaryVertex : BoundaryColorVertex G rho
      (TreeSequenceVertexSet (series.data.tree t.succ.castSucc))
      choice.color choice.vertex :=
    ⟨hchoiceVertexT, choice.edge, hchoiceBoundaryRho,
      choice.edgeIncident⟩
  have hyne : y ≠ choice.vertex := by
    intro hyEq
    subst y
    exact (rhoProper hgne
      ⟨choice.vertex, hyg, choice.edgeIncident⟩ hgColor)
        hchoiceRhoColor
  have hyDefective : DefectiveVertex G rho
      (TreeSequenceVertexSet (series.data.tree t.succ.castSucc)) y :=
    ⟨hyT, g, ⟨choice.color, hdefectiveRho, hgBoundary⟩, hyg⟩
  have hyOrder : TreeVertexOrder
      (series.data.tree t.succ.castSucc) y choice.vertex := by
    rcases choice.maximal rho y rhoProper rhoOne rhoStableReference
      hyDefective with heq | horder
    · exact (hyne heq).elim
    · exact horder
  have hsupport := (ExtensionBaseSupportOrder ett terminalSupport
    hterminalSupport q hqTerminal hqKind hqVertex hLowerPartV).1
    s t vs choice.vertex hvsFinal hvtFinal hsActive htActive hst
    hsVertex htVertex
  have hvsStage := @helper_hvsStage_628 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett q s t vs hst hsVertex hsKind gamma rho previousProper previousOneUncolored
      previousClosed previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      currentColoring currentStored currentEdges currentKind currentVertex currentOutside
      currentDelta currentGamma closedExtension orderedExtension strictExtension
  have hchoiceInS : choice.vertex ∈
      TreeSequenceVertexSet (series.data.tree s.succ.castSucc) := by
    rcases hsupport with heq | horder
    · simpa [heq] using hvsStage
    · exact initialDownward hsFinal hvsStage horder
  have hyFinalOrder : TreeVertexOrder T y choice.vertex :=
    orderTransfer htFinal hyOrder
  have hyOrderVs : TreeVertexOrder T y vs := by
    rcases hsupport with heq | horder
    · simpa [heq] using hyFinalOrder
    · exact orderTrans hyFinalOrder horder
  have hyInS := initialDownward hsFinal hvsStage hyOrderVs
  by_cases huChoice : u = choice.vertex
  · have hyu : y ≠ u := by simpa [huChoice] using hyne
    exact noBoundaryOnOld y hyInS hyu hyBoundary
  · exact noBoundaryOnOld choice.vertex hchoiceInS (Ne.symm huChoice)
      hchoiceBoundaryVertex

private theorem helper_continuation_1128.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
    terminalSupport ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds), (↑q : ℕ) + (1 : ℕ) =
    ett.rounds → ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
    ett.series.data.chosenVertex q.succ = some terminalSupport → (∀ (r a : Fin ett.rounds),
    (↑a : ℕ) < (↑r : ℕ) → ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 → StableColoring (ett.series.data.tree r.succ.castSucc)
    (TashkinovStoredColors ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)
    sigma → ∀ (delta : Fin k), DefectiveColor G sigma (TreeSequenceVertexSet
    (ett.series.data.tree r.succ.castSucc)) delta → ∀ (v : V), BoundaryColorVertex G sigma
    (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)) delta v → (∃ (w : V),
    BoundaryColorVertex G sigma (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc))
    delta w ∧ TreeVertexOrder (ett.series.data.tree r.succ.castSucc) w v) → ∀ (hvFinal : v ∈
    TreeSequenceVertexSet T), ETTFirstAppearanceIndex ett v hvFinal ≤ (↑a : ℕ) + (1 : ℕ) → ∀
    (va : V), ett.series.data.kind a.succ = some TashkinovExtensionKind.PE ∨
    ett.series.data.kind a.succ = some TashkinovExtensionKind.SE →
    ett.series.data.chosenVertex a.succ = some va → v = va ∨ TreeVertexOrder
    (ett.series.data.tree r.succ.castSucc) v va) → ∀ (s t : Fin ett.rounds), ∀ vs ∈
    TreeSequenceVertexSet T, s ∈ ExtensionBaseActiveIndices ett terminalSupport
    hterminalSupport → t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
    (↑s : ℕ) < (↑t : ℕ) → ett.series.data.chosenVertex s.succ = some vs → (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.kind s.succ = some TashkinovExtensionKind.PE
    → (∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → ∀ {x y : V},
    TreeVertexOrder A x y → TreeVertexOrder B x y) → (∀ {A : TreeSequence G e0} {x y z : V},
    TreeVertexOrder A x y → TreeVertexOrder A y z → TreeVertexOrder A x z) → (∀ {A B :
    TreeSequence G e0}, TreeSequenceInitialSegment A B → ∀ {x y : V}, y ∈
    TreeSequenceVertexSet A → TreeVertexOrder B x y → x ∈ TreeSequenceVertexSet A) → ∀ (u :
    V), TreeSequenceInitialSegment ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree s.succ.castSucc) T → TreeSequenceInitialSegment ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc) T → ∀ (gamma : Fin k)
    (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho → IsOneEdgeUncolored rho e0 →
    IsProperEdgeColoring G ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring t.castSucc) → IsOneEdgeUncolored ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.coloring t.castSucc) e0 → ColoredVertexSetClosed G ((ett.series
    : TashkinovSeries G k ett.rounds e0 input).data.coloring t.castSucc)
    (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    t.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.coloring t.castSucc) (TreeSequenceVertexSet ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc)) → ¬Nonempty
    (RevisitingExtensionCertificate (ett.series : TashkinovSeries G k ett.rounds e0
    input).data t.castSucc) → ∀ (choice : MaximumDefectiveChoice G e0 ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc) (TashkinovStoredColors
    (ett.series : TashkinovSeries G k ett.rounds e0 input).data t.castSucc) ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.coloring t.castSucc)), (∃ (rho :
    PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
    StableColoring ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    t.succ.castSucc) (insert choice.color (TashkinovStoredColors (ett.series : TashkinovSeries
    G k ett.rounds e0 input).data t.castSucc) : Finset (Fin k)) choice.selected rho ∧
    ¬Disjoint (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc))) → (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.coloring t.succ = TwoColorComponentSwap G
    rho gamma choice.color (Sum.inl choice.vertex) → (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.stored t.succ = (insert choice.color ({gamma} : Finset (Fin k))
    : Finset (Fin k)) → (ett.series : TashkinovSeries G k ett.rounds e0
    input).data.connectingEdges t.succ = ({choice.edge} : Finset E) → (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.kind t.succ = some TashkinovExtensionKind.PE
    → (ett.series : TashkinovSeries G k ett.rounds e0 input).data.chosenVertex t.succ = some
    choice.vertex → (ett.series : TashkinovSeries G k ett.rounds e0 input).data.outsideVertex
    t.succ = some choice.otherEndpoint → (ett.series : TashkinovSeries G k ett.rounds e0
    input).data.delta t.succ = some choice.color → (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.gamma t.succ = some gamma → TashkinovClosure ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.coloring t.succ) ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc) ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.succ) →
    TreeSequenceInitialSegment ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.succ) → ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc).length < ((ett.series : TashkinovSeries G k ett.rounds
    e0 input).data.tree t.succ.succ).length → choice.vertex ∈ TreeSequenceVertexSet T →
    ett.series.data.chosenVertex t.succ = some choice.vertex → (∀ x ∈ TreeSequenceVertexSet
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree s.succ.castSucc), x ≠ u
    → ¬BoundaryColorVertex G rho (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree t.succ.castSucc)) choice.color x) → StableColoring
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc)
    (TashkinovStoredColors (ett.series : TashkinovSeries G k ett.rounds e0 input).data
    t.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring
    t.castSucc) rho → BoundaryColorEdges G choice.selected (TreeSequenceVertexSet ((ett.series
    : TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc)) choice.color =
    BoundaryColorEdges G rho (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree t.succ.castSucc)) choice.color → choice.edge ∈
    BoundaryColorEdges G choice.selected (TreeSequenceVertexSet ((ett.series : TashkinovSeries
    G k ett.rounds e0 input).data.tree t.succ.castSucc)) choice.color → False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport q hqTerminal
      hqKind hqVertex hLowerPartV s t vs hvsFinal hsActive htActive hst hsVertex
  set series : TashkinovSeries G k ett.rounds e0 input := ett.series
  intro hsKind orderTransfer orderTrans initialDownward u hsFinal htFinal gamma rho rhoProper
      rhoOne previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension hvtFinal htVertex noBoundaryOnOld rhoStableReference
      boundaryEq hchoiceBoundary
  have hdefectiveSelected : DefectiveColor G choice.selected
      (TreeSequenceVertexSet (series.data.tree t.succ.castSucc))
      choice.color := by
    obtain ⟨c, hcDefective, hcBoundary⟩ := choice.edgeDefective
    have hcColor : choice.selected choice.edge = some c :=
      (Finset.mem_filter.mp hcBoundary).2
    have hc : c = choice.color :=
      Option.some.inj (hcColor.symm.trans choice.edgeColor)
    simpa [hc] using hcDefective
  have hdefectiveRho : DefectiveColor G rho
      (TreeSequenceVertexSet (series.data.tree t.succ.castSucc))
      choice.color := by
    unfold DefectiveColor at hdefectiveSelected ⊢
    rw [← boundaryEq]
    exact hdefectiveSelected
  exact @helper_continuation_764 V E inferInstance inferInstance inferInstance G k
      e0 input T generating ett terminalSupport hterminalSupport q hqTerminal hqKind hqVertex
      hLowerPartV s t vs hvsFinal hsActive htActive hst hsVertex hsKind orderTransfer orderTrans
      initialDownward u hsFinal htFinal gamma rho rhoProper rhoOne previousProper
      previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
      seriesAlternativeFails currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension strictExtension
      hvtFinal htVertex noBoundaryOnOld rhoStableReference boundaryEq hchoiceBoundary hdefectiveRho

private theorem helper_branch_447.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
    terminalSupport ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds), (↑q : ℕ) + (1 : ℕ) =
    ett.rounds → ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
    ett.series.data.chosenVertex q.succ = some terminalSupport → (∀ (r a : Fin ett.rounds),
    (↑a : ℕ) < (↑r : ℕ) → ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 → StableColoring (ett.series.data.tree r.succ.castSucc)
    (TashkinovStoredColors ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc)
    sigma → ∀ (delta : Fin k), DefectiveColor G sigma (TreeSequenceVertexSet
    (ett.series.data.tree r.succ.castSucc)) delta → ∀ (v : V), BoundaryColorVertex G sigma
    (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)) delta v → (∃ (w : V),
    BoundaryColorVertex G sigma (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc))
    delta w ∧ TreeVertexOrder (ett.series.data.tree r.succ.castSucc) w v) → ∀ (hvFinal : v ∈
    TreeSequenceVertexSet T), ETTFirstAppearanceIndex ett v hvFinal ≤ (↑a : ℕ) + (1 : ℕ) → ∀
    (va : V), ett.series.data.kind a.succ = some TashkinovExtensionKind.PE ∨
    ett.series.data.kind a.succ = some TashkinovExtensionKind.SE →
    ett.series.data.chosenVertex a.succ = some va → v = va ∨ TreeVertexOrder
    (ett.series.data.tree r.succ.castSucc) v va) → ∀ (s t : Fin ett.rounds) (vs vt : V), vs ∈
    TreeSequenceVertexSet T → vt ∈ TreeSequenceVertexSet T → ∀ (deltaT : Fin k), s ∈
    ExtensionBaseActiveIndices ett terminalSupport hterminalSupport → t ∈
    ExtensionBaseActiveIndices ett terminalSupport hterminalSupport → (↑s : ℕ) < (↑t : ℕ) →
    ett.series.data.chosenVertex s.succ = some vs → ett.series.data.chosenVertex t.succ = some
    vt → ett.series.data.delta t.succ = some deltaT → (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.kind s.succ = some TashkinovExtensionKind.PE → (∀ {A B :
    TreeSequence G e0}, TreeSequenceInitialSegment A B → ∀ {x y : V}, TreeVertexOrder A x y →
    TreeVertexOrder B x y) → (∀ {A : TreeSequence G e0} {x y z : V}, TreeVertexOrder A x y →
    TreeVertexOrder A y z → TreeVertexOrder A x z) → (∀ {A B : TreeSequence G e0},
    TreeSequenceInitialSegment A B → ∀ {x y : V}, y ∈ TreeSequenceVertexSet A →
    TreeVertexOrder B x y → x ∈ TreeSequenceVertexSet A) → ∀ u ∈ TreeSequenceVertexSet
    (ett.series.data.tree s.succ.castSucc), deltaT ∈ MissingColors G (ett.series.data.coloring
    s.castSucc) u → (∀ x ∈ TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds
    e0 input).data.tree s.succ.castSucc), x ≠ u → ∃ (f : E), Incident G x f ∧ (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.coloring s.castSucc f = some deltaT ∧ f ∈
    InternalEdges G (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree s.succ.castSucc))) → deltaT ∈ TreeMissingColors ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.coloring t.castSucc) ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree t.succ.castSucc) ∪
    TashkinovStoredColors (ett.series : TashkinovSeries G k ett.rounds e0 input).data
    t.castSucc → TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree s.succ.castSucc) ⊆ TreeSequenceVertexSet ((ett.series : TashkinovSeries G
    k ett.rounds e0 input).data.tree t.succ.castSucc) → TreeSequenceInitialSegment
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree s.succ.castSucc) T →
    TreeSequenceInitialSegment ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree t.succ.castSucc) T → ∀ (r : Fin ett.rounds), IsProperEdgeColoring G
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring r.castSucc) →
    IsOneEdgeUncolored ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring
    r.castSucc) e0 → ColoredVertexSetClosed G ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring r.castSucc) (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree r.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring r.castSucc)
    (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    r.succ.castSucc)) → ¬Nonempty (RevisitingExtensionCertificate (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data r.castSucc) → ∀ (choice :
    MaximumDefectiveChoice G e0 ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree r.succ.castSucc) (TashkinovStoredColors (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data r.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring r.castSucc)), (∃ (rho : PartialEdgeColoring E k),
    IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧ StableColoring ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree r.succ.castSucc) (insert choice.color
    (TashkinovStoredColors (ett.series : TashkinovSeries G k ett.rounds e0 input).data
    r.castSucc)) choice.selected rho ∧ ¬Disjoint (MissingColors G rho choice.otherEndpoint)
    (TreeMissingColors rho ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    r.succ.castSucc))) → ∀ (gamma : Fin k), ParallelExtensionColor (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data r.castSucc choice.selected choice.vertex
    gamma → ∀ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho → IsOneEdgeUncolored
    rho e0 → StableColoring ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    r.succ.castSucc) (insert choice.color (TashkinovStoredColors (ett.series : TashkinovSeries
    G k ett.rounds e0 input).data r.castSucc)) choice.selected rho → TreeExit ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree r.succ.castSucc) rho gamma choice.color
    choice.vertex → (ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring
    r.succ = TwoColorComponentSwap G rho gamma choice.color (Sum.inl choice.vertex) →
    IsProperEdgeColoring G ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring r.succ) → IsOneEdgeUncolored ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.coloring r.succ) e0 → (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.stored r.succ = {choice.color, gamma} → (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.connectingEdges r.succ = {choice.edge} →
    (ett.series : TashkinovSeries G k ett.rounds e0 input).data.kind r.succ = some
    TashkinovExtensionKind.PE → (ett.series : TashkinovSeries G k ett.rounds e0
    input).data.chosenVertex r.succ = some choice.vertex → (ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.outsideVertex r.succ = some choice.otherEndpoint → (ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.delta r.succ = some choice.color →
    (ett.series : TashkinovSeries G k ett.rounds e0 input).data.gamma r.succ = some gamma →
    TashkinovClosure ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.coloring
    r.succ) ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree r.succ.castSucc)
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree r.succ.succ) →
    TreeSequenceInitialSegment ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree r.succ.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree r.succ.succ) → ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree r.succ.castSucc).length < ((ett.series : TashkinovSeries G k ett.rounds
    e0 input).data.tree r.succ.succ).length → t.succ = r.succ → False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport q hqTerminal
      hqKind hqVertex hLowerPartV s t vs vt hvsFinal hvtFinal deltaT hsActive htActive hst
      hsVertex htVertex htDelta
  set series : TashkinovSeries G k ett.rounds e0 input := ett.series
  intro hsKind orderTransfer orderTrans initialDownward u huS huMissing witnessEdge colorCarry
      hsSubset hsFinal htFinal r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma gammaRule rho
      rhoProper rhoOne rhoStable exitWitness currentColoring currentProper currentOneUncolored
      currentStored currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension hz
  have hrt : r = t := by
    apply Fin.ext
    have hv := congrArg Fin.val hz
    simp at hv ⊢
    omega
  subst r
  have hchoiceVertex : choice.vertex = vt := by
    rw [currentVertex] at htVertex
    exact Option.some.inj htVertex
  have hchoiceColor : choice.color = deltaT := by
    rw [currentDelta] at htDelta
    exact Option.some.inj htDelta
  subst vt
  subst deltaT
  let beforeT : Fin ett.rounds := ⟨t.val - 1, by omega⟩
  have hbeforeSucc : beforeT.succ = t.castSucc := by
    apply Fin.ext
    simp [beforeT]
    omega
  have hsbefore : s.val ≤ beforeT.val := by
    simp [beforeT]
    omega
  have edgeAtRho := @helper_edgeAtRho_418 V E inferInstance inferInstance inferInstance G k e0 input
      T generating ett q s t hst u huS hsSubset rho choice rhoStable huMissing witnessEdge
      colorCarry hbeforeSucc hsbefore
  have noBoundaryOnOld := @helper_noBoundaryOnOld_455 V E inferInstance inferInstance inferInstance
      G k e0 input T generating ett s t u rho rhoProper choice edgeAtRho
  have rhoStableSmall : StableColoring
      (series.data.tree t.succ.castSucc)
      (TashkinovStoredColors series.data t.castSucc)
      choice.selected rho := by
    constructor
    · intro f hf hcontrol
      obtain ⟨c, hc, hfc⟩ := hcontrol
      apply rhoStable.1 f hf
      refine ⟨c, ?_, hfc⟩
      rcases Finset.mem_union.mp hc with hcMissing | hcStored
      · exact Finset.mem_union_left _ hcMissing
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hcStored)
    · exact rhoStable.2
  have rhoStableReference : StableColoring
      (series.data.tree t.succ.castSucc)
      (TashkinovStoredColors series.data t.castSucc)
      (series.data.coloring t.castSucc) rho := by
    exact (sc2 G e0 (series.data.tree t.succ.castSucc)
      (TashkinovStoredColors series.data t.castSucc)).trans
        (x := ⟨series.data.coloring t.castSucc,
          ⟨previousProper, previousOneUncolored⟩⟩)
        (y := ⟨choice.selected,
          ⟨choice.selectedProper, choice.selectedOneUncolored⟩⟩)
        (z := ⟨rho, ⟨rhoProper, rhoOne⟩⟩)
        choice.selectedStable rhoStableSmall
  have boundaryIncident : ∀ {f : E}, f ∈ BoundaryEdges G
      (TreeSequenceVertexSet (series.data.tree t.succ.castSucc)) →
      TreeIncidentEdge (series.data.tree t.succ.castSucc) f := by
    intro f hf
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hf
    obtain ⟨x, hx, y, hy, hends⟩ := hf
    exact ⟨x, hx, by simp [Incident, hends]⟩
  have boundaryEq := @helper_boundaryEq_516 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett t rho rhoProper rhoOne choice rhoStable boundaryIncident
  have hchoiceBoundary : choice.edge ∈ BoundaryColorEdges G
      choice.selected
      (TreeSequenceVertexSet (series.data.tree t.succ.castSucc))
      choice.color := by
    obtain ⟨c, hcDefective, hcBoundary⟩ := choice.edgeDefective
    have hcColor : choice.selected choice.edge = some c :=
      (Finset.mem_filter.mp hcBoundary).2
    have hc : c = choice.color :=
      Option.some.inj (hcColor.symm.trans choice.edgeColor)
    simpa [hc] using hcBoundary
  exact @helper_continuation_1128 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@hterminalSupport) (@q)
      (@hqTerminal) (@hqKind) (@hqVertex) (@hLowerPartV) (@s) (@t) (@vs) (@hvsFinal) (@hsActive)
      (@htActive) (@hst) (@hsVertex) (@hsKind) (@orderTransfer) (@orderTrans) (@initialDownward)
      (@u) (@hsFinal) (@htFinal) (@gamma) (@rho) (@rhoProper) (@rhoOne) (@previousProper)
      (@previousOneUncolored) (@previousClosed) (@previousNotStronglyClosed) (@noRevisiting)
      (@choice) (@seriesAlternativeFails) (@currentColoring) (@currentStored) (@currentEdges)
      (@currentKind) (@currentVertex) (@currentOutside) (@currentDelta) (@currentGamma)
      (@closedExtension) (@orderedExtension) (@strictExtension) (@hvtFinal) (@htVertex)
      (@noBoundaryOnOld) (@rhoStableReference) (@boundaryEq) (@hchoiceBoundary)
private theorem helper_stageSegment_802.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (_ _ _ : Fin ett.rounds), (∀ (i : Fin
    ett.rounds), TreeSequenceInitialSegment ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree i.succ.castSucc) ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.tree i.succ.succ)) → (∀ (A : TreeSequence G e0), TreeSequenceInitialSegment A
    A) → (∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B →
    TreeSequenceInitialSegment B C → TreeSequenceInitialSegment A C) → ∀ (a b : Fin
    ett.rounds), (↑a : ℕ) ≤ (↑b : ℕ) → TreeSequenceInitialSegment ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree a.succ.castSucc) ((ett.series :
    TashkinovSeries G k ett.rounds e0 input).data.tree b.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett q s t
  set series : TashkinovSeries G k ett.rounds e0 input := ett.series
  intro nextSegment segmentRefl segmentTrans a b hab
  have claim : ∀ (n : ℕ), a.val ≤ n → n < ett.rounds →
      ∀ r : Fin ett.rounds, r.val = n →
        TreeSequenceInitialSegment (series.data.tree a.succ.castSucc)
          (series.data.tree r.succ.castSucc) := by
    intro n han
    induction n, han using Nat.le_induction with
    | base =>
        intro hn r hr
        have hra : r = a := by apply Fin.ext; omega
        subst r
        exact segmentRefl _
    | succ n hn ih =>
        intro hrounds r hr
        let p : Fin ett.rounds := ⟨n, by omega⟩
        have hprev := ih (by omega) p rfl
        have hnext := nextSegment p
        have htree : p.succ.succ = r.succ.castSucc := by
          apply Fin.ext
          simp [p, hr]
        rw [htree] at hnext
        exact segmentTrans hprev hnext
  exact claim b.val hab b.isLt b rfl

private theorem helper_witnessEdge_892.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (s : Fin ett.rounds) (deltaT : Fin k),
    ColoredVertexSetElementary G ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring s.castSucc) (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree s.succ.castSucc)) → ∀ u ∈ TreeSequenceVertexSet
    (ett.series.data.tree s.succ.castSucc), deltaT ∈ MissingColors G (ett.series.data.coloring
    s.castSucc) u → ColoredVertexSetClosed G ((ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring s.castSucc) (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k
    ett.rounds e0 input).data.tree s.succ.castSucc)) → ∀ x ∈ TreeSequenceVertexSet
    ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree s.succ.castSucc), x ≠ u
    → ∃ (f : E), Incident G x f ∧ (ett.series : TashkinovSeries G k ett.rounds e0
    input).data.coloring s.castSucc f = some deltaT ∧ f ∈ InternalEdges G
    (TreeSequenceVertexSet ((ett.series : TashkinovSeries G k ett.rounds e0 input).data.tree
    s.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett s deltaT
  set series : TashkinovSeries G k ett.rounds e0 input := ett.series
  intro hsElementary u huS huMissing hsClosed x hxS hxu
  have hxNotMissing : deltaT ∉ MissingColors G
      (series.data.coloring s.castSucc) x := by
    intro hxMissing
    have hd := hsElementary huS hxS hxu.symm
    exact Finset.disjoint_left.mp hd huMissing hxMissing
  have hxPresent : deltaT ∈ PresentColors G
      (series.data.coloring s.castSucc) x := by
    simpa [MissingColors] using hxNotMissing
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hxPresent
  obtain ⟨f, hxf, hfColor⟩ := hxPresent
  have hfInternal : f ∈ InternalEdges G
      (TreeSequenceVertexSet (series.data.tree s.succ.castSucc)) := by
    simp only [InternalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    intro y hyf
    by_contra hyOut
    have hxy : x ≠ y := by
      intro hxy
      exact hyOut (hxy ▸ hxS)
    have hends : G.ends f = s(x, y) :=
      (Sym2.mem_and_mem_iff hxy).mp ⟨hxf, hyf⟩
    have hfBoundary : f ∈ BoundaryEdges G
        (TreeSequenceVertexSet (series.data.tree s.succ.castSucc)) := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨x, hxS, y, hyOut, hends⟩
    exact hsClosed hfBoundary huS hfColor huMissing
  exact ⟨f, hxf, hfColor, hfInternal⟩

theorem ExtensionBaseStrictDeltaExclusion {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (hLowerElementary : ∀ r : Fin ett.rounds, r.val < q.val →
      ColoredVertexSetElementary G (ett.series.data.coloring r.castSucc)
        (TreeSequenceVertexSet
          (ett.series.data.tree r.succ.castSucc)))
    (hLowerPartV : ∀ (r a : Fin ett.rounds), a.val < r.val →
      ∀ sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring (ett.series.data.tree r.succ.castSucc)
          (TashkinovStoredColors ett.series.data r.castSucc)
          (ett.series.data.coloring r.castSucc) sigma →
        ∀ delta : Fin k,
          DefectiveColor G sigma
            (TreeSequenceVertexSet
              (ett.series.data.tree r.succ.castSucc)) delta →
          ∀ v : V,
            BoundaryColorVertex G sigma
              (TreeSequenceVertexSet
                (ett.series.data.tree r.succ.castSucc)) delta v →
            (∃ w : V, BoundaryColorVertex G sigma
                (TreeSequenceVertexSet
                  (ett.series.data.tree r.succ.castSucc)) delta w ∧
              TreeVertexOrder (ett.series.data.tree r.succ.castSucc) w v) →
            ∀ hvFinal : v ∈ TreeSequenceVertexSet T,
              ETTFirstAppearanceIndex ett v hvFinal ≤ a.val + 1 →
              ∀ va : V,
                (ett.series.data.kind a.succ =
                    some TashkinovExtensionKind.PE ∨
                  ett.series.data.kind a.succ =
                    some TashkinovExtensionKind.SE) →
                ett.series.data.chosenVertex a.succ = some va →
                v = va ∨
                  TreeVertexOrder
                    (ett.series.data.tree r.succ.castSucc) v va)
    (s t : Fin ett.rounds) (vs vt : V)
    (hvsFinal : vs ∈ TreeSequenceVertexSet T)
    (hvtFinal : vt ∈ TreeSequenceVertexSet T)
    (deltaT : Fin k)
    (hsActive : s ∈ ExtensionBaseActiveIndices ett terminalSupport
      hterminalSupport)
    (htActive : t ∈ ExtensionBaseActiveIndices ett terminalSupport
      hterminalSupport)
    (hst : s.val < t.val)
    (hsVertex : ett.series.data.chosenVertex s.succ = some vs)
    (htVertex : ett.series.data.chosenVertex t.succ = some vt)
    (htDelta : ett.series.data.delta t.succ = some deltaT) :
    deltaT ∉ TreeMissingColors (ett.series.data.coloring s.castSucc)
      (ett.series.data.tree s.succ.castSucc) := by
  classical
  let series := ett.series
  have hsKind : series.data.kind s.succ =
      some TashkinovExtensionKind.PE := by
    have hh := hsActive
    simp [ExtensionBaseActiveIndices] at hh
    simpa [series] using hh.2.1
  have htKind : series.data.kind t.succ =
      some TashkinovExtensionKind.PE := by
    have hh := htActive
    simp [ExtensionBaseActiveIndices] at hh
    simpa [series] using hh.2.1
  have nextSegment (index : Fin ett.rounds) :
      TreeSequenceInitialSegment (ett.series.data.tree index.succ.castSucc)
        (ett.series.data.tree index.succ.succ) :=
    ett.series.positiveStepInitialSegment index.succ (Nat.zero_lt_succ _)
  have segmentRefl (A : TreeSequence G e0) :
      TreeSequenceInitialSegment A A :=
    ⟨le_rfl, by intro i; rfl, by intro i; rfl⟩
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    exact hAB.trans hBC
  have stageSegment := @helper_stageSegment_802 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett q s t nextSegment segmentRefl segmentTrans
  have stageFinal (a : Fin ett.rounds) :
      TreeSequenceInitialSegment (series.data.tree a.succ.castSucc) T := by
    have haq : a.val ≤ q.val := by
      have ha := a.isLt
      omega
    have haqSeg := stageSegment a q haq
    have htree : q.succ.castSucc = (⟨ett.rounds, by omega⟩ :
        Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp only [Fin.castSucc_succ, Fin.val_succ, Fin.val_castSucc]
      exact hqTerminal
    rw [htree] at haqSeg
    exact segmentTrans haqSeg ett.abovePenultimate
  have orderTransfer {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) {x y : V}
      (hxy : TreeVertexOrder A x y) : TreeVertexOrder B x y := by
    obtain ⟨hlen, hvertices, hedges⟩ := hAB
    obtain ⟨i, j, hix, hjy, hij⟩ := hxy
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i,
      Fin.castLE (Nat.succ_le_succ hlen) j,
      (hvertices i).trans hix, (hvertices j).trans hjy, hij⟩
  have orderTrans {A : TreeSequence G e0} {x y z : V}
      (hxy : TreeVertexOrder A x y) (hyz : TreeVertexOrder A y z) :
      TreeVertexOrder A x z := by
    obtain ⟨i, j, hix, hjy, hij⟩ := hxy
    obtain ⟨j', l, hjy', hlz, hjl⟩ := hyz
    have hj : j = j' := A.vertex_injective (hjy.trans hjy'.symm)
    subst j'
    exact ⟨i, l, hix, hlz, hij.trans hjl⟩
  have initialDownward {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) {x y : V}
      (hy : y ∈ TreeSequenceVertexSet A)
      (hxy : TreeVertexOrder B x y) : x ∈ TreeSequenceVertexSet A := by
    obtain ⟨hlen, hvertices, hedges⟩ := hAB
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hy ⊢
    obtain ⟨jA, hjA⟩ := hy
    obtain ⟨iB, jB, hiBx, hjBy, hij⟩ := hxy
    have hjEq : jB = Fin.castLE (Nat.succ_le_succ hlen) jA := by
      apply B.vertex_injective
      exact hjBy.trans ((hvertices jA).trans hjA).symm
    have hiBound : iB.val < A.length + 1 := by
      rw [hjEq] at hij
      exact lt_of_lt_of_le hij jA.isLt.le
    let iA : Fin (A.length + 1) := ⟨iB.val, hiBound⟩
    refine ⟨iA, ?_⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hlen) iA = iB := by
      apply Fin.ext
      rfl
    exact (hvertices iA).symm.trans (hcast ▸ hiBx)
  intro hmissing
  have hsltq : s.val < q.val := by
    have htlt := t.isLt
    omega
  have hsElementary : ColoredVertexSetElementary G
      (series.data.coloring s.castSucc)
      (TreeSequenceVertexSet (series.data.tree s.succ.castSucc)) := by
    exact hLowerElementary s hsltq
  simp only [TreeMissingColors, Finset.mem_biUnion] at hmissing
  obtain ⟨u, huS, huMissing⟩ := hmissing
  have hsClosed := @helper_hsClosed_282 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett q s t hsKind
  have witnessEdge := @helper_witnessEdge_892 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett s deltaT hsElementary u huS huMissing hsClosed
  have colorCarry := @helper_colorCarry_371 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett q s t deltaT hst u huS huMissing
  have hstSegment := stageSegment s t (Nat.le_of_lt hst)
  have hsSubset := TreeSequenceInitialSegmentVertexSetSubset hstSegment
  have hsFinal := stageFinal s
  have htFinal := stageFinal t
  have htStep := series.certified t.succ
  generalize hz : t.succ = z at htStep
  cases htStep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      have hv := congrArg Fin.val hz
      simp at hv
  | SE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hrt : r = t := by
        apply Fin.ext
        have hv := congrArg Fin.val hz
        simp at hv ⊢
        omega
      subst r
      rw [currentKind] at htKind
      simp at htKind
  | RE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hrt : r = t := by
        apply Fin.ext
        have hv := congrArg Fin.val hz
        simp at hv ⊢
        omega
      subst r
      rw [currentKind] at htKind
      simp at htKind
  | PE r previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule rho rhoProper rhoOne rhoStable exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_447 V E inferInstance inferInstance inferInstance G k e0 input T
              generating ett terminalSupport hterminalSupport q hqTerminal hqKind hqVertex
              hLowerPartV s t vs vt hvsFinal hvtFinal deltaT hsActive htActive hst hsVertex
              htVertex htDelta hsKind orderTransfer orderTrans initialDownward u huS huMissing
              witnessEdge colorCarry hsSubset hsFinal htFinal r previousProper
              previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
              seriesAlternativeFails gamma gammaRule rho rhoProper rhoOne rhoStable exitWitness
              currentColoring currentProper currentOneUncolored currentStored currentEdges
              currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
              orderedExtension strictExtension hz
end GoldbergSeymour

end
