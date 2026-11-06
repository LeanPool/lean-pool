/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.InterchangeableExitPaths
public import LeanPool.GoldbergSeymour.TwoColorComponentClosedColors

public import LeanPool.GoldbergSeymour.TreeExitPathTransport

public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Step1Zero Divider Anchor Non PE

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hterminal_148.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (base : HierarchyBase ett phi) (_ :
        TashkinovHierarchy ett base), ett.series.data.kind (Fin.last ett.rounds) ≠ some
        TashkinovExtensionKind.PE →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let p : Fin (ett.rounds + (1 : ℕ)) := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a
        : ¬ett.rounds - (1 : ℕ) < ett.rounds + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dp : Finset (Fin k) := TashkinovStoredColors ett.series.data p; phi =
        ett.series.data.coloring n → IsProperEdgeColoring G (ett.series.data.coloring p) ∧
        IsOneEdgeUncolored (ett.series.data.coloring p) e0 ∧ ColoredVertexSetClosed G
        (ett.series.data.coloring p) (TreeSequenceVertexSet Tn) ∧ StableColoring Tn Dp
        (ett.series.data.coloring p) phi := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive base H hnonPE n p Tn Dp hphi
  as_aux_lemma =>
  have hstep := ett.series.certified n
  generalize targetEq : n = target at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hn : n ≠ 0 := by simp [n]; omega
    exact (hn targetEq).elim
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have hp : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by
      rw [targetEq]
      exact currentKind
    exact (hnonPE (by simpa [n] using hp)).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hi : i.succ = n := by
      apply Fin.ext
      have hv := congrArg Fin.val targetEq
      simp at hv
      omega
    have hip : i.castSucc = p := by
      apply Fin.ext
      simp only [Fin.val_castSucc, n, p] at hi ⊢
      have hv := congrArg Fin.val hi
      simp at hv
      omega
    have htree : ett.series.data.tree i.succ.castSucc = Tn := by
      simp [Tn, hi]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hip] using previousProper
    · simpa [hip] using previousOneUncolored
    · rw [← htree, ← hip]
      exact previousClosed
    · have hselected : choice.selected = phi :=
        currentColoring.symm.trans
          ((congrArg ett.series.data.coloring hi).trans hphi.symm)
      have hs : StableColoring Tn Dp
          (ett.series.data.coloring p) choice.selected := by
        simpa only [Dp, htree, hip] using choice.selectedStable
      exact Eq.mp
        (congrArg (fun q => StableColoring Tn Dp
          (ett.series.data.coloring p) q) hselected) hs
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hi : i.succ = n := by
      apply Fin.ext
      have hv := congrArg Fin.val targetEq
      simp at hv
      omega
    have hip : i.castSucc = p := by
      apply Fin.ext
      have hv := congrArg Fin.val hi
      simp [p, n] at hv ⊢
      omega
    have htree : ett.series.data.tree i.succ.castSucc = Tn := by
      simp [Tn, hi]
    have hcol : ett.series.data.coloring p = phi := by
      exact (congrArg ett.series.data.coloring hip.symm).trans
        (currentColoring.symm.trans
          ((congrArg ett.series.data.coloring hi).trans hphi.symm))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hip] using previousProper
    · simpa [hip] using previousOneUncolored
    · rw [← htree, ← hip]
      exact previousClosed
    · have hs : StableColoring Tn Dp
          (ett.series.data.coloring p) (ett.series.data.coloring p) :=
        (sc2 G e0 Tn Dp).refl
          ⟨ett.series.data.coloring p, by simpa [hip] using previousProper,
            by simpa [hip] using previousOneUncolored⟩
      exact Eq.mp
        (congrArg (fun q => StableColoring Tn Dp
          (ett.series.data.coloring p) q) hcol) hs

private theorem helper_finalInterchange_379.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi) (_ : TashkinovHierarchy ett base),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let p : Fin (ett.rounds + (1 : ℕ)) := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a
        : ¬ett.rounds - (1 : ℕ) < ett.rounds + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dp : Finset (Fin k) := TashkinovStoredColors ett.series.data p; IsProperEdgeColoring G
        (ett.series.data.coloring p) ∧ IsOneEdgeUncolored (ett.series.data.coloring p) e0 ∧
        ColoredVertexSetClosed G (ett.series.data.coloring p) (TreeSequenceVertexSet Tn) ∧
        StableColoring Tn Dp (ett.series.data.coloring p) phi → TreeMissingColors phi Tn =
        TreeMissingColors (ett.series.data.coloring p) Tn →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn Dp phi sigma →
    ∀ (a b : Fin k), a ∈ TreeMissingColors sigma Tn ∨ b ∈ TreeMissingColors sigma Tn →
        TreeInterchangeable G Tn sigma a b := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hMP hpositive hlower base H n p Tn Dp hterminal
      treeMissingEq sigma hsProper hsOne hsStable a b hmissing
  have hsComposed : StableColoring Tn Dp
      (ett.series.data.coloring p) sigma := by
    constructor
    · intro f hf hcolor
      obtain ⟨d, hd, hdf⟩ := hcolor
      have hdPhi : d ∈ TreeMissingColors phi Tn ∪ Dp := by
        rcases Finset.mem_union.mp hd with hdMissing | hdControl
        · exact Finset.mem_union_left _ (by
            rw [treeMissingEq]
            exact hdMissing)
        · exact Finset.mem_union_right _ hdControl
      have hphiFixed : phi f = ett.series.data.coloring p f := by
        exact hterminal.2.2.2.1 f hf ⟨d, hd, hdf⟩
      have hsigmaFixed : sigma f = phi f := by
        apply hsStable.1 f hf
        exact ⟨d, hdPhi, hphiFixed.trans hdf⟩
      exact hsigmaFixed.trans hphiFixed
    · intro v hv
      exact (hsStable.2 v hv).trans (hterminal.2.2.2.2 v hv)
  by_cases honeRound : ett.rounds = 1
  · have htech := TechnicalTheoremBase G k ett.rounds e0 input ett.series
    have hidx1 : (⟨1, by omega⟩ : Fin (ett.rounds + 2)) =
        n.castSucc := by
      apply Fin.ext
      simp [n, honeRound]
    have hT1 : ett.series.data.tree ⟨1, by omega⟩ = Tn := by
      rw [hidx1]
    have hs0 : StableColoring
        (ett.series.data.tree ⟨1, by omega⟩)
        (TashkinovStoredColors ett.series.data 0)
        (ett.series.data.coloring 0) sigma := by
      rw [hT1]
      simpa [p, Dp, honeRound] using hsComposed
    have hm0 : a ∈ TreeMissingColors sigma
          (ett.series.data.tree ⟨1, by omega⟩) ∨
        b ∈ TreeMissingColors sigma
          (ett.series.data.tree ⟨1, by omega⟩) := by
      rw [hT1]
      exact hmissing
    have hinter := htech.2 sigma hsProper hsOne hs0 a b hm0
    rw [hT1] at hinter
    exact hinter
  · have hgt : 1 < ett.rounds := by omega
    obtain ⟨pred, predRound, predMP, predTrees, predData⟩ :=
      CertifiedETTPredecessor G k e0 input T phi ett hMP hgt
    have low := (hlower pred (by omega) (by omega) predMP).2.1
    have hpredNext : pred.series.data.tree
        (Fin.last (pred.rounds + 1)) = Tn := by
      have hh := predTrees (Fin.last (pred.rounds + 1))
      have hidx : Fin.castLE (by omega) (Fin.last (pred.rounds + 1)) =
          n.castSucc := by
        apply Fin.ext
        simp [predRound, n]
        omega
      simpa [Tn] using hh.trans (congrArg ett.series.data.tree hidx)
    have hpredColor : pred.series.data.coloring (Fin.last pred.rounds) =
        ett.series.data.coloring p := by
      have hh := (predData (Fin.last pred.rounds)).1
      have hidx : Fin.castLE (by omega) (Fin.last pred.rounds) = p := by
        apply Fin.ext
        simp [predRound, p]
      rw [hidx] at hh
      exact hh
    have hpredStored : TashkinovStoredColors pred.series.data
        (Fin.last pred.rounds) = Dp := by
      have hh := (predData (Fin.last pred.rounds)).2.2.2.2.2.2.2.2.1
      have hidx : Fin.castLE (by omega) (Fin.last pred.rounds) = p := by
        apply Fin.ext
        simp [predRound, p]
      rw [hidx] at hh
      simpa [Dp] using hh
    have hsPred : StableColoring
        (pred.series.data.tree (Fin.last (pred.rounds + 1)))
        (TashkinovStoredColors pred.series.data (Fin.last pred.rounds))
        (pred.series.data.coloring (Fin.last pred.rounds)) sigma := by
      rw [hpredNext, hpredStored, hpredColor]
      exact hsComposed
    have hmPred : a ∈ TreeMissingColors sigma
          (pred.series.data.tree (Fin.last (pred.rounds + 1))) ∨
        b ∈ TreeMissingColors sigma
          (pred.series.data.tree (Fin.last (pred.rounds + 1))) := by
      rw [hpredNext]
      exact hmissing
    have hinter := low sigma hsProper hsOne hsPred a b hmPred
    rw [hpredNext] at hinter
    exact hinter

private theorem helper_branch_639.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds), IsProperEdgeColoring G phi →
        IsOneEdgeUncolored phi e0 →
    ∀ (base : HierarchyBase ett phi) (_ : TashkinovHierarchy ett base) (alpha beta : Fin k), alpha
        ≠ beta →
    ∀ (a₁ b₁ a₂ b₂ : V) (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₁) (Sum.inl
        b₁)) (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₂) (Sum.inl b₂)),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let p : Fin (ett.rounds + (1 : ℕ)) := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a
        : ¬ett.rounds - (1 : ℕ) < ett.rounds + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let _ : Finset V := TreeSequenceVertexSet Tn;
    let Dp : Finset (Fin k) := TashkinovStoredColors ett.series.data p; TreeExitPath Tn phi alpha
        beta a₁ b₁ P₁ → TreeExitPath Tn phi alpha beta a₂ b₂ P₂ → TreeColorSetClosed G phi Tn
        { alpha } →
    let x : V := Tn.vertex (0 : Fin (Tn.length + (1 : ℕ))); x ∈ TreeSequenceVertexSet Tn →
    ∀ c ∈ MissingColors G phi x, TreeColorSetClosed G phi Tn { c } → c ≠ beta → (
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring Tn Dp phi sigma → c ∈ TreeMissingColors sigma Tn →
    ∀ (Q₁ : (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₁) (Sum.inl b₁)) (Q₂ :
        (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₂) (Sum.inl b₂)), TreeExitPath Tn
        sigma c beta a₁ b₁ Q₁ → TreeExitPath Tn sigma c beta a₂ b₂ Q₂ → False) → ¬alpha = c →
        False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive hproper hone base H alpha beta hne a₁ b₁ a₂
      b₂ P₁ P₂ n p Tn X Dp hP1 hP2 halphaClosed x hxT c hcxMissing hcClosed hcNeBeta finish hac
  have componentOutside (u : V) (outside : u ∉ X) (v : V)
      (member : Sum.inl v ∈ TwoColorComponent G phi alpha c (Sum.inl u)) : v ∉ X :=
    halphaClosed.componentOutside hcClosed outside member
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
  have hrecolor : OutsideKempeRecoloring Tn phi rho alpha c := by
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
  have hstable := OutsideKempeRecoloringStable G e0 Tn Dp
    phi rho alpha c hproper hone hrecolor
  have hrhoProper : IsProperEdgeColoring G rho := hstable.1
  have hrhoOne : IsOneEdgeUncolored rho e0 := hstable.2.1
  have hrhoStable : StableColoring Tn Dp phi rho := hstable.2.2.1
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
  have transportExit := TreeExitPath.componentSwapTransport Tn phi alpha beta c hac
    hbetaFixed selectedOfOutside
  obtain ⟨Q₁, hQ₁, hQ₁Support⟩ := transportExit a₁ b₁ P₁ hP1
  obtain ⟨Q₂, hQ₂, hQ₂Support⟩ := transportExit a₂ b₂ P₂ hP2
  have hcMissingRho : c ∈ TreeMissingColors rho Tn := by
    unfold TreeMissingColors
    refine Finset.mem_biUnion.mpr ⟨x, hxT, ?_⟩
    rw [hrhoStable.2 x hxT]
    exact hcxMissing
  exact finish rho hrhoProper hrhoOne hrhoStable hcMissingRho
    Q₁ Q₂ hQ₁ hQ₂

private theorem helper_continuation_1146.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (_ :
        IsProperEdgeColoring G phi) (_ : IsOneEdgeUncolored phi e0) (_ :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (base : HierarchyBase ett phi) (H :
        TashkinovHierarchy ett base) (alpha beta : Fin k) (_ : alpha ≠ beta) (_ : alpha ∈
        TreeMissingColors phi (HierarchyStarredStage H (Fin.last H.dividerCount))) (_ :
        TreeColorSetClosed G phi (HierarchyStarredStage H (Fin.last H.dividerCount)) ({ alpha } :
        Finset (Fin k))) (a₁ b₁ a₂ b₂ : V) (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
        (Sum.inl a₁) (Sum.inl b₁)) (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl
        a₂) (Sum.inl b₂)) (_ : TreeExitPath (HierarchyStarredStage H (Fin.last H.dividerCount))
        phi alpha beta a₁ b₁ P₁) (_ : TreeExitPath (HierarchyStarredStage H (Fin.last
        H.dividerCount)) phi alpha beta a₂ b₂ P₂) (_ :
    ∀ x ∈ P₁.support, x ∉ P₂.support) (_ : a₁ ≠ a₂),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let p : Fin (ett.rounds + (1 : ℕ)) := (⟨ett.rounds - (1 : ℕ),
    by
          omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dp : Finset (Fin k) := TashkinovStoredColors ett.series.data p;
    ∀ (_ : IsProperEdgeColoring G (ett.series.data.coloring p) ∧ IsOneEdgeUncolored
        (ett.series.data.coloring p) e0 ∧ ColoredVertexSetClosed G (ett.series.data.coloring p)
        (TreeSequenceVertexSet Tn) ∧ StableColoring Tn Dp (ett.series.data.coloring p) phi) (_ :
    ∀ d ∈ TreeMissingColors phi Tn, BoundaryColorEdges G phi (TreeSequenceVertexSet Tn) d = ∅) (_
        : TreeExitPath Tn phi alpha beta a₁ b₁ P₁) (_ : TreeExitPath Tn phi alpha beta a₂ b₂ P₂)
        (_ : alpha ∈ TreeMissingColors phi Tn) (_ : TreeColorSetClosed G phi Tn ({ alpha } :
        Finset (Fin k))) (f₁ : E) (_ : Sum.inr f₁ ∈ P₁.support) (f₂ : E) (_ : Sum.inr f₂ ∈
        P₂.support) (_ : beta ∉ TreeMissingColors phi Tn),
    let x : V := Tn.vertex (0 : Fin (Tn.length + (1 : ℕ)));
    ∀ (_ : x ∈ TreeSequenceVertexSet Tn) (_ : MaximumDegree G + (1 : ℕ) ≤ k) (_ : (PresentColors G
        phi x).card ≤ Degree G x), False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hMP hpositive hproper hone hlower base H alpha beta
      hne halpha hclosed a₁ b₁ a₂ b₂ P₁ P₂ hP₁ hP₂ hpaths ha n p Tn Dp hterminal missingClosed
      hP1 hP2 halphaT halphaClosed f₁ hf₁Support f₂ hf₂Support hbetaNotMissing x hxT degreeBound
      presentBound
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
  have hcClosed : TreeColorSetClosed G phi Tn {c} := by
    unfold TreeColorSetClosed
    intro d hd
    have hdc : d = c := Finset.mem_singleton.mp hd
    subst d
    exact missingClosed c hcT
  have hbetaPresent : beta ∈ PresentColors G phi x := by
    by_contra hb
    apply hbetaNotMissing
    unfold TreeMissingColors
    refine Finset.mem_biUnion.mpr ⟨x, hxT, ?_⟩
    simpa [MissingColors] using hb
  have hcNeBeta : c ≠ beta := by
    intro hcb
    subst c
    have hnot : beta ∉ PresentColors G phi x := by
      simpa [MissingColors] using hcxMissing
    exact hnot hbetaPresent
  have treeMissingEq : TreeMissingColors phi Tn =
      TreeMissingColors (ett.series.data.coloring p) Tn := by
    ext d
    unfold TreeMissingColors
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨v, hv, hd⟩
      refine ⟨v, hv, ?_⟩
      rw [← hterminal.2.2.2.2 v hv]
      exact hd
    · rintro ⟨v, hv, hd⟩
      refine ⟨v, hv, ?_⟩
      rw [hterminal.2.2.2.2 v hv]
      exact hd
  have finalInterchange := @helper_finalInterchange_379 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 input T phi ett hMP hpositive hlower base H hterminal
      treeMissingEq
  have finish :
      ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma →
        IsOneEdgeUncolored sigma e0 → StableColoring Tn Dp phi sigma →
        c ∈ TreeMissingColors sigma Tn →
        ∀ (Q₁ : (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₁) (Sum.inl b₁))
          (Q₂ : (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₂) (Sum.inl b₂)),
        TreeExitPath Tn sigma c beta a₁ b₁ Q₁ →
          TreeExitPath Tn sigma c beta a₂ b₂ Q₂ → False := by
    intro sigma hsProper hsOne hsStable hcMissing Q₁ Q₂ hQ₁ hQ₂
    have hcxSigma : c ∈ MissingColors G sigma x := by
      rw [hsStable.2 x hxT]
      exact hcxMissing
    have hinter := finalInterchange sigma hsProper hsOne hsStable c beta (Or.inl hcMissing)
    exact ha (hinter.exitPath_start_eq hsProper hcNeBeta x hxT
      (Or.inl hcxSigma) Q₁ Q₂ hQ₁ hQ₂)
  by_cases hac : alpha = c
  · subst alpha
    have hsRefl : StableColoring Tn Dp phi phi := by
      constructor
      · intro f hf hcolor
        rfl
      · intro v hv
        rfl
    exact finish phi hproper hone hsRefl hcT P₁ P₂ hP1 hP2
  · exact @helper_branch_639 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett hpositive hproper hone base H alpha beta hne a₁ b₁ a₂ b₂ P₁ P₂ hP1 hP2
      halphaClosed hxT c hcxMissing hcClosed hcNeBeta finish hac

lemma Step1ZeroDividerAnchorNonPE {V E : Type*}
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
    (hnonPE : ett.series.data.kind (Fin.last ett.rounds) ≠
      some TashkinovExtensionKind.PE) : False := by
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let p : Fin (ett.rounds + 1) := ⟨ett.rounds - 1, by omega⟩
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  let X : Finset V := TreeSequenceVertexSet Tn
  let Dp : Finset (Fin k) := TashkinovStoredColors ett.series.data p
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
  have hcore : base.core = Tn := by
    simpa [n, Tn] using base.nonparallel hnonPE
  have hterminal := @helper_hterminal_148 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett hpositive base H hnonPE hphi
  have missingClosed : ∀ d : Fin k,
      d ∈ TreeMissingColors phi Tn →
        BoundaryColorEdges G phi (TreeSequenceVertexSet Tn) d = ∅ := by
    intro d hd
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hfData : f ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) ∧
        phi f = some d := by
      simpa [BoundaryColorEdges] using hf
    obtain ⟨y, hyT, hyd⟩ := Finset.mem_biUnion.mp hd
    have hfIncident : TreeIncidentEdge Tn f := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] at hfData
      obtain ⟨u, huT, v, hvT, huv⟩ := hfData.1
      refine ⟨u, huT, ?_⟩
      unfold Incident
      rw [huv]
      exact Sym2.mem_mk_left _ _
    have hydPrev : d ∈ MissingColors G (ett.series.data.coloring p) y := by
      rw [← hterminal.2.2.2.2 y hyT]
      exact hyd
    have hdPrev : d ∈ TreeMissingColors (ett.series.data.coloring p) Tn := by
      unfold TreeMissingColors
      exact Finset.mem_biUnion.mpr ⟨y, hyT, hydPrev⟩
    have hfFixed : phi f = ett.series.data.coloring p f := by
      apply (sc1 G e0 Tn Dp (ett.series.data.coloring p) phi
        hterminal.1 hterminal.2.1 hproper hone).mp
        hterminal.2.2.2 f hfIncident
      exact Or.inr ⟨d, Finset.mem_union_left _ hdPrev, hfData.2⟩
    exact (hterminal.2.2.1 hfData.1 hyT
      (hfFixed.symm.trans hfData.2)) hydPrev
  have hP1 : TreeExitPath Tn phi alpha beta a₁ b₁ P₁ := by
    simpa [hstar, hcore] using hP₁
  have hP2 : TreeExitPath Tn phi alpha beta a₂ b₂ P₂ := by
    simpa [hstar, hcore] using hP₂
  have halphaT : alpha ∈ TreeMissingColors phi Tn := by
    simpa [hstar, hcore] using halpha
  have halphaClosed : TreeColorSetClosed G phi Tn {alpha} := by
    simpa [hstar, hcore] using hclosed
  obtain ⟨f₁, hf₁Boundary, hf₁Incident, hf₁Support⟩ :=
    ClosedColorExitPathBoundaryEdge G Tn phi alpha beta halphaClosed
      a₁ b₁ P₁ hP1
  obtain ⟨f₂, hf₂Boundary, hf₂Incident, hf₂Support⟩ :=
    ClosedColorExitPathBoundaryEdge G Tn phi alpha beta halphaClosed
      a₂ b₂ P₂ hP2
  have hbetaNotMissing : beta ∉ TreeMissingColors phi Tn := by
    intro hbeta
    have hempty := missingClosed beta hbeta
    rw [hempty] at hf₁Boundary
    simp at hf₁Boundary
  let x : V := Tn.vertex 0
  have hxT : x ∈ TreeSequenceVertexSet Tn := by
    simp [x, TreeSequenceVertexSet]
  have degreeBound : MaximumDegree G + 1 ≤ k := by
    have step := ett.series.certified 0
    cases step with
    | initial triple => exact triple.2.2.1
  have presentBound : (PresentColors G phi x).card ≤ Degree G x := by
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
  exact @helper_continuation_1146 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hMP) (@hpositive) (@hproper)
      (@hone) (@hlower) (@base) (@H) (@alpha) (@beta) (@hne) (@halpha) (@hclosed) (@a₁) (@b₁)
      (@a₂) (@b₂) (@P₁) (@P₂) (@hP₁) (@hP₂) (@hpaths) (@ha) (@hterminal) (@missingClosed) (@hP1)
      (@hP2) (@halphaT) (@halphaClosed) (@f₁) (@hf₁Support) (@f₂) (@hf₂Support)
      (@hbetaNotMissing) (@hxT) (@degreeBound) (@presentBound)
end GoldbergSeymour

end
