/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColorDegreeBounds

public import LeanPool.GoldbergSeymour.InterchangeableExitPaths

public import LeanPool.GoldbergSeymour.TwoColorComponentClosedColors

public import LeanPool.GoldbergSeymour.TreeExitPathTransport

public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.ParallelInterchangeability
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Step1Zero Divider Anchor PE

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

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
    intro u outside v member
    exact halphaClosed.componentOutside hcClosed outside member
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
  have transportExit :
    ∀ (u v : V) (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath base.core phi alpha beta u v P →
    ∃ Q : (TwoColorIncidenceGraph G rho c beta).Walk (Sum.inl u) (Sum.inl v), TreeExitPath
        base.core rho c beta u v Q ∧ Q.support = P.support := by
    exact TreeExitPath.componentSwapTransport base.core phi alpha beta c hac
      hbetaFixed selectedOfOutside
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
  have presentBound := PresentColors.card_le_degree G phi x
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
    intro u v path exit
    exact ClosedColorExitPathBoundaryEdge G base.core phi alpha beta halphaClosed u v path exit
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
    intro sigma hsProper hsOne hsCombined hcMissingCore hcClosedCore Q₁ Q₂ hQ₁ hQ₂
    have hcxSigma : c ∈ MissingColors G sigma x := by
      rw [hsCombined.1.2 x hxT]
      exact hcxMissing
    have hinter := (interchange G k e0 input T phi sigma ett hMP hpositive
      hlower hPE base hsProper hsOne hsCombined c beta).2.2.1 hcMissingCore hcClosedCore
    exact ha (hinter.exitPath_start_eq hsProper hcNeBeta x
      (by simpa only [X] using hxX) (Or.inl hcxSigma) Q₁ Q₂ hQ₁ hQ₂)
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
