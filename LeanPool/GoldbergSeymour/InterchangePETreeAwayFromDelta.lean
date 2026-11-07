/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor
public import LeanPool.GoldbergSeymour.CombinedStableClosurePreserved
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.ElementarySingleBoundaryInterchangeable
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.ParallelClosureUnionElementary
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Interchange PETree Away From Delta

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hproperGen_107.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : (0 : ℕ) < ett.rounds) (_ : ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.PE) (_ : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    ∀ (_ : generating = ett.series.data.coloring n), IsProperEdgeColoring G generating := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive hPE gamma n hgen
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
    have hi : i.succ = n := by
      apply Fin.ext
      have hv := congrArg Fin.val targetEq
      simp at hv
      omega
    simpa [hgen, hi] using currentProper
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hp : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hp
    contradiction
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hp : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hp
    contradiction

private theorem helper_honeGen_147.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : (0 : ℕ) < ett.rounds) (_ : ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.PE) (_ : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    ∀ (_ : generating = ett.series.data.coloring n), IsOneEdgeUncolored generating e0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive hPE gamma n hgen
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
    have hi : i.succ = n := by
      apply Fin.ext
      have hv := congrArg Fin.val targetEq
      simp at hv
      omega
    simpa [hgen, hi] using currentOneUncolored
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hp : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hp
    contradiction
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hp : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hp
    contradiction

private theorem helper_hlowerElem_240.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (_ :
        LowerRoundInductionHypothesis G k e0 ett.rounds),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : Fin ett.rounds), ColoredVertexSetElementary G (ett.series.data.coloring (⟨ett.rounds -
        (1 : ℕ), Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds + (1 : ℕ))
        ↦
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (TreeSequenceVertexSet Tn) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower n Tn i
  by_cases honeRound : ett.rounds = 1
  · have htech := TechnicalTheoremBase G k ett.rounds e0 input ett.series
    have hT : Tn = ett.series.data.tree ⟨1, by omega⟩ := by
      apply congrArg (fun j : Fin (ett.rounds + 2) => ett.series.data.tree j)
      apply Fin.ext
      simp [n, honeRound]
    have hc : (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) = 0 := by
      apply Fin.ext
      simp [honeRound]
    rw [hT, hc]
    exact htech.1
  · have hgt : 1 < ett.rounds := by omega
    obtain ⟨pred, hpredRound, hpredMP, htrees, hdata⟩ :=
      CertifiedETTPredecessor G k e0 input T generating ett hMP hgt
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
    exact hp

private theorem helper_hsigmaEmpty_384.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (generating sigma : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating),
    ∀ alpha ∈ TreeMissingColors sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    StableColoring Tn (TashkinovStoredColors ett.series.data n) sigma generating →
    BoundaryColorEdges G generating (TreeSequenceVertexSet Tn) alpha = ∅ →
    BoundaryColorEdges G sigma (TreeSequenceVertexSet Tn) alpha = ∅ := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett alpha halpha n Tn hstableRev hgenEmpty
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have hg' : g ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) ∧
      sigma g = some alpha := by
    simpa [BoundaryColorEdges] using hg
  have hinc : TreeIncidentEdge Tn g := by
    unfold TreeIncidentEdge
    obtain ⟨u, hu, v, hv, he⟩ := by
      simpa [BoundaryEdges] using hg'.1
    refine ⟨u, hu, ?_⟩
    change u ∈ G.ends g
    rw [he]
    simp
  have hctrl : ∃ c ∈ TreeMissingColors sigma Tn ∪
      TashkinovStoredColors ett.series.data n, sigma g = some c :=
    ⟨alpha, Finset.mem_union_left _ halpha, hg'.2⟩
  have heq : generating g = sigma g := hstableRev.1 g hinc hctrl
  have : g ∈ BoundaryColorEdges G generating (TreeSequenceVertexSet Tn) alpha := by
    simp [BoundaryColorEdges, hg'.1, heq, hg'.2]
  rw [hgenEmpty] at this
  simp at this

private theorem helper_hgammaSingleton_407.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : generating = ett.series.data.coloring n) (_ : StableColoring Tn (TashkinovStoredColors
        ett.series.data n) generating sigma) (i : Fin ett.rounds) (choice : MaximumDefectiveChoice
        G e0 (ett.series.data.tree i.succ.castSucc) (TashkinovStoredColors ett.series.data
        i.castSucc) (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k) (_ : i.succ =
        n) (_ : BoundaryColorEdges G (ett.series.data.coloring i.succ) (TreeSequenceVertexSet
        (ett.series.data.tree i.succ.castSucc)) terminalGamma = { choice.edge } ∧ (
    ∀ g ∈ BoundaryColorEdges G (ett.series.data.coloring i.succ) (TreeSequenceVertexSet
        (ett.series.data.tree i.succ.castSucc)) choice.color,
    ∃ (w : V), TreeVertexOrder (ett.series.data.tree i.succ.castSucc) w choice.vertex ∧ Incident G
        w g) ∧ (ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) →
    ∀ alpha ∈ TreeMissingColors (ett.series.data.coloring i.succ) (ett.series.data.tree
        i.succ.castSucc), alpha ≠ choice.color → BoundaryColorEdges G (ett.series.data.coloring
        i.succ) (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) alpha = ∅)) (_ :
        ett.series.data.coloring n choice.edge = some terminalGamma) (_ : terminalGamma ∈
        TashkinovStoredColors ett.series.data n) (_ : StableColoring Tn (TashkinovStoredColors
        ett.series.data n) sigma generating), BoundaryColorEdges G sigma (TreeSequenceVertexSet
        Tn) terminalGamma = { choice.edge } := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett n Tn hgen hstableTree i choice
      terminalGamma hi hbound hcurrentEdge hgammaStored hstableRev
  apply Finset.Subset.antisymm
  · intro g hg
    have hg' : g ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) ∧
        sigma g = some terminalGamma := by
      simpa [BoundaryColorEdges] using hg
    have hinc : TreeIncidentEdge Tn g := by
      unfold TreeIncidentEdge
      obtain ⟨u, hu, v, hv, he⟩ := by
        simpa [BoundaryEdges] using hg'.1
      refine ⟨u, hu, ?_⟩
      change u ∈ G.ends g
      rw [he]
      simp
    have hctrl : ∃ c ∈ TreeMissingColors sigma Tn ∪
        TashkinovStoredColors ett.series.data n, sigma g = some c :=
      ⟨terminalGamma, Finset.mem_union_right _ hgammaStored, hg'.2⟩
    have heq : generating g = sigma g := hstableRev.1 g hinc hctrl
    have : g ∈ BoundaryColorEdges G generating (TreeSequenceVertexSet Tn)
        terminalGamma := by
      simp [BoundaryColorEdges, hg'.1, heq, hg'.2]
    have ht : g ∈ BoundaryColorEdges G
        (ett.series.data.coloring i.succ)
        (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) terminalGamma := by
      simpa [hgen, Tn, hi] using this
    rw [hbound.1] at ht
    simpa using ht
  · intro g hg
    have : g = choice.edge := by simpa using hg
    subst g
    have hce : generating choice.edge = some terminalGamma := by
      simpa [hgen, Tn, hi] using hcurrentEdge
    have hb : choice.edge ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) := by
      obtain ⟨c, hc, hm⟩ := choice.edgeDefective
      have hm' := hm
      simp only [BoundaryColorEdges, Finset.mem_filter] at hm'
      simpa [Tn, hi] using hm'.1
    have hinc : TreeIncidentEdge Tn choice.edge := by
      unfold TreeIncidentEdge
      obtain ⟨u, hu, v, hv, he⟩ := by simpa [BoundaryEdges] using hb
      refine ⟨u, hu, ?_⟩
      change u ∈ G.ends choice.edge
      rw [he]
      simp
    have hs : sigma choice.edge = generating choice.edge :=
      hstableTree.1 choice.edge hinc
        ⟨terminalGamma, Finset.mem_union_right _ hgammaStored, hce⟩
    have hcs : sigma choice.edge = some terminalGamma := hs.trans hce
    simp [BoundaryColorEdges, hb, hcs]

private theorem helper_undoneOne_411.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : IsOneEdgeUncolored sigma e0) (i :
        Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k) (_ : terminalGamma ≠
        choice.color),
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex); IsOneEdgeUncolored undone e0 := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett hone i choice terminalGamma hnegc undone
  dsimp [undone]
  unfold IsOneEdgeUncolored
  have hone' := hone
  unfold IsOneEdgeUncolored at hone'
  constructor
  · simp [TwoColorComponentSwap, hone'.1]
  · intro e he
    obtain ⟨c, hc⟩ := hone'.2 e he
    by_cases hem : Sum.inr e ∈
        TwoColorComponent G sigma terminalGamma choice.color
          (Sum.inl choice.vertex)
    · by_cases hcg : c = terminalGamma
      · exact ⟨choice.color, by simp [TwoColorComponentSwap, hem, hc, hcg]⟩
      · by_cases hcd : c = choice.color
        · exact ⟨terminalGamma, by simp [TwoColorComponentSwap, hem, hc, hcd,
            hnegc.symm]⟩
        · exact ⟨c, by simp [TwoColorComponentSwap, hem, hc, hcg, hcd]⟩
    · exact ⟨c, by simp [TwoColorComponentSwap, hem, hc]⟩

private theorem helper_hreach_473.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (alpha beta : Fin k) (i : Fin ett.rounds)
        (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors ett.series.data i.castSucc) (ett.series.data.coloring i.castSucc))
        (terminalGamma : Fin k),
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex);
    ∀ (_ : (
    ∀ (x y : V ⊕ E), (TwoColorIncidenceGraph G undone alpha beta).Adj x y ↔
        (TwoColorIncidenceGraph G sigma alpha beta).Adj x y)) {x y : V ⊕ E},
        (TwoColorIncidenceGraph G undone alpha beta).Reachable x y ↔ (TwoColorIncidenceGraph G
        sigma alpha beta).Reachable x y := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett alpha beta i choice terminalGamma undone
      hadj x y
  constructor <;> intro hp
  · rcases hp with ⟨p⟩
    refine ⟨?_⟩
    induction p with
    | nil => exact .nil
    | cons ha p ih => exact .cons ((hadj _ _).mp ha) ih
  · rcases hp with ⟨p⟩
    refine ⟨?_⟩
    induction p with
    | nil => exact .nil
    | cons ha p ih => exact .cons ((hadj _ _).mpr ha) ih

private theorem helper_htransport_500.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (alpha beta : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k),
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex);
    ∀ (_ : (
    ∀ (x y : V ⊕ E), (TwoColorIncidenceGraph G undone alpha beta).Adj x y ↔
        (TwoColorIncidenceGraph G sigma alpha beta).Adj x y)) (_ : (
    ∀ (z : V ⊕ E), TwoColorComponent G undone alpha beta z = TwoColorComponent G sigma alpha beta
        z)) (_ : TreeInterchangeable G Tn undone alpha beta), TreeInterchangeable G Tn sigma alpha
        beta := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett alpha beta n Tn i choice terminalGamma
      undone hadj hcomponentEq hinter
  unfold TreeInterchangeable at hinter ⊢
  intro z w hz hw hzX hwX
  rw [← hcomponentEq z, ← hcomponentEq w]
  apply hinter z w
  · rcases hz with ⟨hn, x, hx, hs⟩
    refine ⟨hn, x, ?_, ?_⟩
    · rw [← hcomponentEq z] at hx
      exact hx
    · intro y hy z hz
      apply hs
      · exact (hadj x y).mp hy
      · exact (hadj x z).mp hz
  · rcases hw with ⟨hn, x, hx, hs⟩
    refine ⟨hn, x, ?_, ?_⟩
    · rw [← hcomponentEq w] at hx
      exact hx
    · intro y hy z hz
      apply hs
      · exact (hadj x y).mp hy
      · exact (hadj x z).mp hz
  · rcases hzX with ⟨v, hv, hx⟩
    exact ⟨v, hv, by rw [hcomponentEq z]; exact hx⟩
  · rcases hwX with ⟨v, hv, hx⟩
    exact ⟨v, hv, by rw [hcomponentEq w]; exact hx⟩

private theorem helper_branch_528.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : (0 : ℕ) < ett.rounds) (alpha beta :
        Fin k) (_ : alpha ∈ TreeMissingColors sigma (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k) (_ : i.succ = n) (_ :
        StableColoring (ett.series.data.tree i.castSucc.succ) (TashkinovStoredColors
        ett.series.data i.castSucc) (ett.series.data.coloring i.castSucc) (TwoColorComponentSwap G
        sigma terminalGamma choice.color (Sum.inl choice.vertex))),
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex);
    ∀ (_ : IsProperEdgeColoring G undone) (_ : IsOneEdgeUncolored undone e0) (_ : (
    ∀ (e : E), undone e = some alpha ↔ sigma e = some alpha)) (_ : (
    ∀ (_ : TreeInterchangeable G Tn undone alpha beta), TreeInterchangeable G Tn sigma alpha
        beta)) (_ : ett.rounds = (1 : ℕ)), TreeInterchangeable G (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) sigma alpha beta := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett hpositive alpha beta halpha n Tn i choice
      terminalGamma hi stablePreviousUndone undone undoneProper' undoneOne' hswapAlpha htransport
      honeRound
  have htech := TechnicalTheoremBase G k ett.rounds e0 input ett.series
  let undone := TwoColorComponentSwap G sigma terminalGamma choice.color
    (Sum.inl choice.vertex)
  have hi0 : i = (⟨0, by omega⟩ : Fin ett.rounds) := by
    apply Fin.ext
    have hv := congrArg Fin.val hi
    simp [n, honeRound] at hv ⊢
    omega
  have htree0 : ett.series.data.tree (⟨1, by omega⟩ : Fin (ett.rounds + 2)) = Tn := by
    apply congrArg ett.series.data.tree
    apply Fin.ext
    simp [n, honeRound]
  have htreeLast : ett.series.data.tree (Fin.last ett.rounds).castSucc =
      ett.series.data.tree (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
    apply congrArg ett.series.data.tree
    apply Fin.ext
    simp [honeRound]
  have hstable0 : StableColoring
      (ett.series.data.tree ⟨1, by omega⟩)
      (TashkinovStoredColors ett.series.data 0)
      (ett.series.data.coloring 0) undone := by
    have hci : i.castSucc = 0 := by
      apply Fin.ext
      simp [hi0, honeRound]
    have hti : i.castSucc.succ = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp [hi0, honeRound]
    convert stablePreviousUndone using 1 <;> simp [hci]
  have hmissing0 : alpha ∈ TreeMissingColors undone
      (ett.series.data.tree ⟨1, by omega⟩) := by
    unfold TreeMissingColors
    obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp halpha
    refine Finset.mem_biUnion.mpr ⟨v, ?_, ?_⟩
    · rw [htreeLast] at hv
      exact hv
    · have hnot : ∀ x, Incident G v x → ¬undone x = some alpha := by
        intro x hx hxa
        unfold MissingColors at hmv
        have hmv' : ∀ x, Incident G v x → ¬sigma x = some alpha := by
          simpa [PresentColors] using (Finset.mem_sdiff.mp hmv).2
        exact hmv' x hx ((hswapAlpha x).mp hxa)
      simpa [MissingColors, PresentColors] using hnot
  have hres := htech.2 undone undoneProper' undoneOne' hstable0 alpha beta
  have htemp := hres (Or.inl hmissing0)
  have htemp' : TreeInterchangeable G Tn undone alpha beta := by
    rw [← htree0]
    exact htemp
  simpa [Tn] using (htransport htemp')

private theorem helper_undoneOne_605.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : IsOneEdgeUncolored sigma e0) (i :
        Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k) (_ : terminalGamma ≠
        choice.color),
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma choice.color
        (Sum.inl choice.vertex);
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex); IsOneEdgeUncolored undone e0 := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett hone i choice terminalGamma hnegc undone
      undone
  dsimp [undone]
  unfold IsOneEdgeUncolored
  have hone' := hone
  unfold IsOneEdgeUncolored at hone'
  constructor
  · simp [TwoColorComponentSwap, hone'.1]
  · intro e he
    obtain ⟨c, hc⟩ := hone'.2 e he
    by_cases hem : Sum.inr e ∈
        TwoColorComponent G sigma terminalGamma choice.color
          (Sum.inl choice.vertex)
    · by_cases hcg : c = terminalGamma
      · exact ⟨choice.color, by simp [TwoColorComponentSwap, hem, hc, hcg]
        ⟩
      · by_cases hcd : c = choice.color
        · exact ⟨terminalGamma, by simp [TwoColorComponentSwap, hem, hc, hcd,
            hnegc.symm]⟩
        · exact ⟨c, by simp [TwoColorComponentSwap, hem, hc, hcg, hcd]⟩
    · exact ⟨c, by simp [TwoColorComponentSwap, hem, hc]⟩

private theorem helper_hstablePred_651.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k) (_ : i.succ = n) (_ :
        StableColoring (ett.series.data.tree i.castSucc.succ) (TashkinovStoredColors
        ett.series.data i.castSucc) (ett.series.data.coloring i.castSucc) (TwoColorComponentSwap G
        sigma terminalGamma choice.color (Sum.inl choice.vertex))),
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma choice.color
        (Sum.inl choice.vertex);
    ∀ (hgt : (1 : ℕ) < ett.rounds) (pred : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))),
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex);
    ∀ (_ : pred.series.data.tree (Fin.last (pred.rounds + (1 : ℕ))) = Tn) (_ :
        pred.series.data.coloring (Fin.last pred.rounds) = ett.series.data.coloring i.castSucc) (_
        : TashkinovStoredColors pred.series.data (Fin.last pred.rounds) = TashkinovStoredColors
        ett.series.data i.castSucc), StableColoring (pred.series.data.tree (Fin.last (pred.rounds
        + (1 : ℕ)))) (TashkinovStoredColors pred.series.data (Fin.last pred.rounds))
        (pred.series.data.coloring (Fin.last pred.rounds)) undone := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett n Tn i choice terminalGamma hi
      stablePreviousUndone undone hgt pred undone hpredNext hpredColor hpredStored
  rw [hpredStored, hpredColor]
  have htreeI : i.castSucc.succ = n.castSucc := by
    apply Fin.ext
    have hv := congrArg Fin.val hi
    simp [n] at hv ⊢
    omega
  rw [hpredNext]
  change StableColoring (ett.series.data.tree n.castSucc)
    (TashkinovStoredColors ett.series.data i.castSucc)
    (ett.series.data.coloring i.castSucc) undone
  rw [← htreeI]
  simpa [undone] using stablePreviousUndone

private theorem helper_hreach_710.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (alpha beta : Fin k) (i : Fin ett.rounds)
        (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors ett.series.data i.castSucc) (ett.series.data.coloring i.castSucc))
        (terminalGamma : Fin k),
    let undone_1 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex);
    ∀ (_ : (
    ∀ (x y : V ⊕ E), (TwoColorIncidenceGraph G undone_1 alpha beta).Adj x y ↔
        (TwoColorIncidenceGraph G sigma alpha beta).Adj x y)),
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex);
    ∀ (_ : (
    ∀ (x y : V ⊕ E), (TwoColorIncidenceGraph G undone alpha beta).Adj x y ↔
        (TwoColorIncidenceGraph G sigma alpha beta).Adj x y)) {x y : V ⊕ E},
        (TwoColorIncidenceGraph G undone alpha beta).Reachable x y ↔ (TwoColorIncidenceGraph G
        sigma alpha beta).Reachable x y := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett alpha beta i choice terminalGamma undone
      hadj undone hadj x y
  constructor <;> intro hp
  · rcases hp with ⟨p⟩
    refine ⟨?_⟩
    induction p with
    | nil => exact .nil
    | cons ha p ih => exact .cons ((hadj _ _).mp ha) ih
  · rcases hp with ⟨p⟩
    refine ⟨?_⟩
    induction p with
    | nil => exact .nil
    | cons ha p ih => exact .cons ((hadj _ _).mpr ha) ih

private theorem helper_htransport_737.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (alpha beta : Fin k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k),
    let undone_1 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex);
    ∀ (_ : (
    ∀ (x y : V ⊕ E), (TwoColorIncidenceGraph G undone_1 alpha beta).Adj x y ↔
        (TwoColorIncidenceGraph G sigma alpha beta).Adj x y)) (_ : (
    ∀ (z : V ⊕ E), TwoColorComponent G undone_1 alpha beta z = TwoColorComponent G sigma alpha
        beta z)),
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex);
    ∀ (_ : (
    ∀ (x y : V ⊕ E), (TwoColorIncidenceGraph G undone alpha beta).Adj x y ↔
        (TwoColorIncidenceGraph G sigma alpha beta).Adj x y)) (_ : (
    ∀ (z : V ⊕ E), TwoColorComponent G undone alpha beta z = TwoColorComponent G sigma alpha beta
        z)) (_ : TreeInterchangeable G Tn undone alpha beta), TreeInterchangeable G Tn sigma alpha
        beta := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett alpha beta n Tn i choice terminalGamma
      undone hadj hcomponentEq undone hadj hcomponentEq hinter
  unfold TreeInterchangeable at hinter ⊢
  intro z w hz hw hzX hwX
  rw [← hcomponentEq z, ← hcomponentEq w]
  apply hinter z w
  · rcases hz with ⟨hn, x, hx, hs⟩
    refine ⟨hn, x, ?_, ?_⟩
    · rw [← hcomponentEq z] at hx
      exact hx
    · intro y hy z hz
      apply hs
      · exact (hadj x y).mp hy
      · exact (hadj x z).mp hz
  · rcases hw with ⟨hn, x, hx, hs⟩
    refine ⟨hn, x, ?_, ?_⟩
    · rw [← hcomponentEq w] at hx
      exact hx
    · intro y hy z hz
      apply hs
      · exact (hadj x y).mp hy
      · exact (hadj x z).mp hz
  · rcases hzX with ⟨v, hv, hx⟩
    exact ⟨v, hv, by rw [hcomponentEq z]; exact hx⟩
  · rcases hwX with ⟨v, hv, hx⟩
    exact ⟨v, hv, by rw [hcomponentEq w]; exact hx⟩

private theorem helper_branch_576.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett) (_ : (0 : ℕ) <
        ett.rounds) (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (_ :
        IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (delta alpha beta : Fin k)
        (_ : ett.series.data.delta (Fin.last ett.rounds) = some delta) (_ : alpha ∈
        TreeMissingColors sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (_ : ¬alpha
        = delta) (_ : ¬beta = delta),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k) (_ : i.succ = n) (_ :
        ett.series.data.delta n = some choice.color) (_ : terminalGamma ≠ choice.color) (_ : alpha
        ≠ terminalGamma) (_ : ¬beta = terminalGamma) (_ : StableColoring (ett.series.data.tree
        i.castSucc.succ) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc) (TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex))),
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex);
    ∀ (_ : IsProperEdgeColoring G undone) (_ : IsOneEdgeUncolored undone e0) (_ : alpha ≠
        choice.color) (_ : beta ≠ terminalGamma) (_ : beta ≠ choice.color) (_ : (
    ∀ (e : E), undone e = some alpha ↔ sigma e = some alpha)) (_ : (
    ∀ (e : E), undone e = some beta ↔ sigma e = some beta)) (_ : (
    ∀ (x y : V ⊕ E), (TwoColorIncidenceGraph G undone alpha beta).Adj x y ↔
        (TwoColorIncidenceGraph G sigma alpha beta).Adj x y)) (_ : (
    ∀ {x y : V ⊕ E}, (TwoColorIncidenceGraph G undone alpha beta).Reachable x y ↔
        (TwoColorIncidenceGraph G sigma alpha beta).Reachable x y)) (_ : (
    ∀ (z : V ⊕ E), TwoColorComponent G undone alpha beta z = TwoColorComponent G sigma alpha beta
        z)) (_ : (
    ∀ (_ : TreeInterchangeable G Tn undone alpha beta), TreeInterchangeable G Tn sigma alpha
        beta)) (_ : ¬ett.rounds = (1 : ℕ)), TreeInterchangeable G (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) sigma alpha beta := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett hMP hpositive hlower hproper hone delta alpha
      beta hdelta halpha hne hbeta n Tn i choice terminalGamma hi hdelta' hnegc halphaGamma hbg
      stablePreviousUndone undone undoneProper' undoneOne' halphaDelta hbetaGamma hbetaDelta
      hswapAlpha hswapBeta hadj hreach hcomponentEq htransport honeRound
  have hgt : 1 < ett.rounds := by omega
  have hpred := CertifiedETTPredecessor G k e0 input T generating ett hMP hgt
  rcases hpred with ⟨pred, predRound, predMP, predTrees, predData⟩
  have hiVal : i.val + 1 = ett.rounds := by
    have hv := congrArg Fin.val hi
    simp [n] at hv
    omega
  have low := (hlower pred (by omega) (by omega) predMP).2.1
  let undone := TwoColorComponentSwap G sigma terminalGamma choice.color
    (Sum.inl choice.vertex)
  have undoneProper' : IsProperEdgeColoring G undone := by
    exact TwoColorComponentSwapProper G sigma terminalGamma choice.color
      hnegc hproper (Sum.inl choice.vertex)
  have undoneOne' : IsOneEdgeUncolored undone e0 := by
    exact @helper_undoneOne_605 V E inferInstance inferInstance inferInstance G k e0 input T
        generating sigma ett hone i choice terminalGamma hnegc
  have hpredNext : pred.series.data.tree
      (Fin.last (pred.rounds + 1)) = Tn := by
    have hh := predTrees (Fin.last (pred.rounds + 1))
    have hidx : (Fin.castLE (by omega) (Fin.last (pred.rounds + 1))) = n.castSucc := by
      apply Fin.ext
      simp [predRound, n]
      omega
    simpa [Tn] using hh.trans (congrArg ett.series.data.tree hidx)
  have hpredColor : pred.series.data.coloring (Fin.last pred.rounds) =
      ett.series.data.coloring i.castSucc := by
    have hh := (predData (Fin.last pred.rounds)).1
    have hidx : (Fin.castLE (by omega) (Fin.last pred.rounds)) = i.castSucc := by
      apply Fin.ext
      simp [predRound]
      omega
    rw [hidx] at hh
    exact hh
  have hpredStored : TashkinovStoredColors pred.series.data
      (Fin.last pred.rounds) = TashkinovStoredColors ett.series.data i.castSucc := by
    have hh := (predData (Fin.last pred.rounds)).2.2.2.2.2.2.2.2.1
    have hidx : (Fin.castLE (by omega) (Fin.last pred.rounds)) = i.castSucc := by
      apply Fin.ext
      simp [predRound]
      omega
    rw [hidx] at hh
    exact hh
  have hstablePred := @helper_hstablePred_651 V E inferInstance inferInstance inferInstance G k e0
      input T generating sigma ett i choice terminalGamma hi stablePreviousUndone hgt pred hpredNext
      hpredColor hpredStored
  have halphaDelta : alpha ≠ choice.color := by
    intro heq
    apply hne
    have hcd : choice.color = delta := by
      rw [← Option.some.injEq]
      rw [← hdelta', hdelta]
    exact heq.trans hcd
  have hbetaGamma : beta ≠ terminalGamma := hbg
  have hbetaDelta : beta ≠ choice.color := by
    intro heq
    apply hbeta
    have hcd : choice.color = delta := by
      rw [← Option.some.injEq]
      rw [← hdelta', hdelta]
    exact heq.trans hcd
  have hswapAlpha : ∀ e, undone e = some alpha ↔ sigma e = some alpha := by
    intro e
    by_cases he : Sum.inr e ∈
        TwoColorComponent G sigma terminalGamma choice.color
          (Sum.inl choice.vertex)
    · by_cases h1 : sigma e = some terminalGamma <;>
        by_cases h2 : sigma e = some choice.color <;>
        simp [undone, TwoColorComponentSwap, he, h1, h2,
          halphaGamma.symm, halphaDelta.symm,
          hnegc.symm]
    · simp [undone, TwoColorComponentSwap, he]
  have hswapBeta : ∀ e, undone e = some beta ↔ sigma e = some beta := by
    intro e
    by_cases he : Sum.inr e ∈
        TwoColorComponent G sigma terminalGamma choice.color
          (Sum.inl choice.vertex)
    · by_cases h1 : sigma e = some terminalGamma <;>
        by_cases h2 : sigma e = some choice.color <;>
        simp [undone, TwoColorComponentSwap, he, h1, h2,
          hbetaGamma.symm, hbetaDelta.symm,
          hnegc.symm]
    · simp [undone, TwoColorComponentSwap, he]
  have hadj : ∀ x y,
      (TwoColorIncidenceGraph G undone alpha beta).Adj x y ↔
        (TwoColorIncidenceGraph G sigma alpha beta).Adj x y := by
    intro x y
    cases x <;> cases y <;>
      simp [TwoColorIncidenceGraph, hswapAlpha, hswapBeta]
  have hreach := @helper_hreach_710 V E inferInstance inferInstance inferInstance G k e0 input T
      generating sigma ett alpha beta i choice terminalGamma hadj hadj
  have hcomponentEq :
    ∀ z, TwoColorComponent G undone alpha beta z = TwoColorComponent G sigma alpha beta z := by
    intro z
    apply Set.ext
    intro x
    change (TwoColorIncidenceGraph G undone alpha beta).connectedComponentMk x =
      (TwoColorIncidenceGraph G undone alpha beta).connectedComponentMk z ↔
      (TwoColorIncidenceGraph G sigma alpha beta).connectedComponentMk x =
      (TwoColorIncidenceGraph G sigma alpha beta).connectedComponentMk z
    rw [SimpleGraph.ConnectedComponent.eq, SimpleGraph.ConnectedComponent.eq]
    exact hreach
  have htransport := @helper_htransport_737 V E inferInstance inferInstance inferInstance G k e0
      input T generating sigma ett alpha beta i choice terminalGamma hadj hcomponentEq hadj
      hcomponentEq
  have hmissingPred : alpha ∈ TreeMissingColors undone
      (pred.series.data.tree (Fin.last (pred.rounds + 1))) := by
    rw [hpredNext]
    unfold TreeMissingColors
    obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp halpha
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    simpa [MissingColors, PresentColors, hswapAlpha] using hmv
  have hstablePredNext : StableColoring
      (pred.series.data.tree (Fin.last (pred.rounds + 1)))
      (TashkinovStoredColors pred.series.data (Fin.last pred.rounds))
      (pred.series.data.coloring (Fin.last pred.rounds)) undone := by
    exact hstablePred
  have hmissingPredNext : alpha ∈ TreeMissingColors undone
      (pred.series.data.tree (Fin.last (pred.rounds + 1))) := by
    exact hmissingPred
  apply htransport
  simpa [hpredNext] using
    (low undone undoneProper' undoneOne' hstablePredNext alpha beta
      (Or.inl hmissingPredNext))

private theorem helper_branch_563.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett) (_ : (0 : ℕ) <
        ett.rounds) (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (_ :
        IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (delta alpha beta : Fin k)
        (_ : ett.series.data.delta (Fin.last ett.rounds) = some delta) (_ : alpha ∈
        TreeMissingColors sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (_ : ¬alpha
        = delta) (_ : ¬beta = delta),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k) (_ : i.succ = n) (_ :
        ett.series.data.delta n = some choice.color) (_ : terminalGamma ≠ choice.color) (_ : alpha
        ≠ terminalGamma) (_ : (
    ∃ (selected : PartialEdgeColoring E k) (secondStable : PartialEdgeColoring E k),
        IsProperEdgeColoring G selected ∧ IsOneEdgeUncolored selected e0 ∧ StableColoring
        (ett.series.data.tree i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc) selected ∧ IsProperEdgeColoring G secondStable ∧
        IsOneEdgeUncolored secondStable e0 ∧ StableColoring (ett.series.data.tree i.succ.castSucc)
        (insert choice.color (TashkinovStoredColors ett.series.data i.castSucc)) selected
        secondStable ∧ ett.series.data.coloring i.succ = TwoColorComponentSwap G secondStable
        terminalGamma choice.color (Sum.inl choice.vertex) ∧
    have undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma terminalGamma
        choice.color (Sum.inl choice.vertex); StableColoring (ett.series.data.tree
        i.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data i.castSucc))
        secondStable undone ∧ StableColoring (ett.series.data.tree i.succ.castSucc) (insert
        choice.color (TashkinovStoredColors ett.series.data i.castSucc)) selected undone ∧
        StableColoring (ett.series.data.tree i.succ.castSucc) (TashkinovStoredColors
        ett.series.data i.castSucc) (ett.series.data.coloring i.castSucc) undone)) (_ : ¬beta =
        terminalGamma), TreeInterchangeable G (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) sigma alpha beta := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett hMP hpositive hlower hproper hone delta alpha
      beta hdelta halpha hne hbeta n Tn i choice terminalGamma hi hdelta' hnegc halphaGamma hundo
      hbg
  rcases hundo with ⟨selected, undoneStable, selectedProper, selectedOne,
    selectedStable, undoneProper, undoneOne, undoneRelation, currentSwap,
    finalStable⟩
  dsimp at finalStable
  rcases finalStable with ⟨stableSecondUndone, stableSelectedUndone,
    stablePreviousUndone⟩
  let undone := TwoColorComponentSwap G sigma terminalGamma choice.color
    (Sum.inl choice.vertex)
  have undoneProper' : IsProperEdgeColoring G undone := by
    exact TwoColorComponentSwapProper G sigma terminalGamma choice.color
      hnegc hproper (Sum.inl choice.vertex)
  have undoneOne' : IsOneEdgeUncolored undone e0 := by
    exact @helper_undoneOne_411 V E inferInstance inferInstance inferInstance G k e0 input T
        generating sigma ett hone i choice terminalGamma hnegc
  have halphaDelta : alpha ≠ choice.color := by
    intro heq
    apply hne
    have hcd : choice.color = delta := by
      rw [← Option.some.injEq]
      rw [← hdelta', hdelta]
    exact heq.trans hcd
  have hbetaGamma : beta ≠ terminalGamma := hbg
  have hbetaDelta : beta ≠ choice.color := by
    intro heq
    apply hbeta
    have hcd : choice.color = delta := by
      rw [← Option.some.injEq]
      rw [← hdelta', hdelta]
    exact heq.trans hcd
  have hswapAlpha : ∀ e, undone e = some alpha ↔ sigma e = some alpha := by
    intro e
    by_cases he : Sum.inr e ∈
        TwoColorComponent G sigma terminalGamma choice.color
          (Sum.inl choice.vertex)
    · by_cases h1 : sigma e = some terminalGamma <;>
        by_cases h2 : sigma e = some choice.color <;>
        simp [undone, TwoColorComponentSwap, he, h1, h2,
          halphaGamma.symm, halphaDelta.symm,
          hnegc.symm]
    · simp [undone, TwoColorComponentSwap, he]
  have hswapBeta : ∀ e, undone e = some beta ↔ sigma e = some beta := by
    intro e
    by_cases he : Sum.inr e ∈
        TwoColorComponent G sigma terminalGamma choice.color
          (Sum.inl choice.vertex)
    · by_cases h1 : sigma e = some terminalGamma <;>
        by_cases h2 : sigma e = some choice.color <;>
        simp [undone, TwoColorComponentSwap, he, h1, h2,
          hbetaGamma.symm, hbetaDelta.symm,
          hnegc.symm]
    · simp [undone, TwoColorComponentSwap, he]
  have hadj : ∀ x y,
      (TwoColorIncidenceGraph G undone alpha beta).Adj x y ↔
        (TwoColorIncidenceGraph G sigma alpha beta).Adj x y := by
    intro x y
    cases x <;> cases y <;>
      simp [TwoColorIncidenceGraph, hswapAlpha, hswapBeta]
  have hreach := @helper_hreach_473 V E inferInstance inferInstance inferInstance G k e0 input T
      generating sigma ett alpha beta i choice terminalGamma hadj
  have hcomponentEq :
    ∀ z, TwoColorComponent G undone alpha beta z = TwoColorComponent G sigma alpha beta z := by
    intro z
    apply Set.ext
    intro x
    change (TwoColorIncidenceGraph G undone alpha beta).connectedComponentMk x =
      (TwoColorIncidenceGraph G undone alpha beta).connectedComponentMk z ↔
      (TwoColorIncidenceGraph G sigma alpha beta).connectedComponentMk x =
      (TwoColorIncidenceGraph G sigma alpha beta).connectedComponentMk z
    rw [SimpleGraph.ConnectedComponent.eq, SimpleGraph.ConnectedComponent.eq]
    exact hreach
  have htransport := @helper_htransport_500 V E inferInstance inferInstance inferInstance G k e0
      input T generating sigma ett alpha beta i choice terminalGamma hadj hcomponentEq
  by_cases honeRound : ett.rounds = 1
  · exact @helper_branch_528 V E inferInstance inferInstance inferInstance G k e0 input T
      generating sigma ett hpositive alpha beta halpha i choice terminalGamma hi
      stablePreviousUndone undoneProper' undoneOne' hswapAlpha htransport honeRound
  · exact @helper_branch_576 V E inferInstance inferInstance  inferInstance G k e0
      input T generating sigma ett hMP hpositive hlower hproper hone delta alpha beta hdelta
      halpha hne hbeta i choice terminalGamma hi hdelta' hnegc halphaGamma hbg
      stablePreviousUndone undoneProper' undoneOne' halphaDelta hbetaGamma hbetaDelta hswapAlpha
      hswapBeta hadj hreach hcomponentEq htransport honeRound
private theorem helper_hpre_845.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (i : Fin ett.rounds) (terminalGamma : Fin k) (_ : i.succ = n) (_ : ett.series.data.gamma n =
        some terminalGamma) (_ : ColoredVertexSetElementary G (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) <
        ett.rounds + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (TreeSequenceVertexSet Tn)), ColoredVertexSetElementary G
        (ett.series.data.coloring i.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        i.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive n Tn i terminalGamma hi hcolor hlowerElem
  have hidx : i.castSucc = (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) := by
    apply Fin.ext
    have hv := congrArg Fin.val hi
    simp [n] at hv ⊢
    omega
  have htree : Tn = ett.series.data.tree i.succ.castSucc := by
    have hidx2 : n.castSucc = i.succ.castSucc := by
      apply Fin.ext
      have hv := congrArg Fin.val hi
      simp [n] at hv ⊢
      omega
    simpa [Tn] using congrArg (fun j => ett.series.data.tree j) hidx2
  have hcolor : ett.series.data.coloring i.castSucc =
      ett.series.data.coloring (⟨ett.rounds - 1, by omega⟩) :=
    congrArg ett.series.data.coloring hidx
  unfold ColoredVertexSetElementary at hlowerElem ⊢
  rw [hcolor, ← htree]
  exact fun {u} hu {v} hv huv => hlowerElem hu hv huv

private theorem helper_hgammaStored_906.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : (0 : ℕ) < ett.rounds),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : generating = ett.series.data.coloring n) (i : Fin ett.rounds) (choice :
        MaximumDefectiveChoice G e0 (ett.series.data.tree i.succ.castSucc) (TashkinovStoredColors
        ett.series.data i.castSucc) (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k)
        (_ : ett.series.data.stored i.succ = { choice.color, terminalGamma }) (_ : i.succ = n) (_
        : terminalGamma ∉ TreeMissingColors generating Tn), terminalGamma ∈ TashkinovStoredColors
        ett.series.data n := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive n Tn hgen i choice terminalGamma
      currentStored hi hgammaNotTree
  have hn : n.val ≠ 0 := by simp [n]; omega
  rw [TashkinovStoredColors]
  simp only [hn, ↓reduceIte]
  apply Finset.mem_sdiff.mpr
  constructor
  · simp only [Finset.mem_biUnion]
    refine ⟨n, Finset.mem_univ _, ?_⟩
    rw [← hi, currentStored]
    simp
  · intro hm
    apply hgammaNotTree
    simpa [hgen] using hm

private theorem helper_hstableRev_920.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (generating sigma : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : StableColoring Tn (TashkinovStoredColors ett.series.data n) generating sigma)
      (_ : IsProperEdgeColoring G generating) (_ : IsOneEdgeUncolored generating e0),
    StableColoring Tn (TashkinovStoredColors ett.series.data n) sigma generating := by
  classical
  intro V E _ _ _ G k e0 input T generating sigma ett hproper hone n Tn hstableTree hproperGen
      honeGen
  let left : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨generating, hproperGen, honeGen⟩
  let right : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨sigma, hproper, hone⟩
  have forward : StableColoring Tn
      (TashkinovStoredColors ett.series.data n) left.1 right.1 := by
    simpa [left, right] using hstableTree
  have reverse := (sc2 G e0 Tn
    (TashkinovStoredColors ett.series.data n)).symm forward
  simpa [left, right] using reverse

private theorem helper_continuation_1320.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett) (_ : (0 : ℕ) <
        ett.rounds) (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (_ :
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) (base :
        HierarchyBase ett generating) (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored
        sigma e0) (_ : CombinedStableColoring (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) base.closure (TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds)) generating sigma) (delta alpha beta : Fin k) (_ : ett.series.data.delta
        (Fin.last ett.rounds) = some delta) (_ : alpha ∈ TreeMissingColors sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (_ : ¬alpha = delta) (_ : ¬beta =
        delta),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : generating = ett.series.data.coloring n) (_ : StableColoring Tn (TashkinovStoredColors
        ett.series.data n) generating sigma) (_ : IsProperEdgeColoring G generating) (_ :
        IsOneEdgeUncolored generating e0) (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree i.succ.castSucc) (TashkinovStoredColors ett.series.data
        i.castSucc) (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k) (_ :
        ett.series.data.kind i.succ = some TashkinovExtensionKind.PE) (_ :
        ett.series.data.chosenVertex i.succ = some choice.vertex) (_ : ett.series.data.delta
        i.succ = some choice.color) (_ : ett.series.data.gamma i.succ = some terminalGamma) (_ :
        i.succ = n) (_ : ett.series.data.delta n = some choice.color) (_ : BoundaryColorEdges G
        (ett.series.data.coloring i.succ) (TreeSequenceVertexSet (ett.series.data.tree
        i.succ.castSucc)) terminalGamma = { choice.edge } ∧ (
    ∀ g ∈ BoundaryColorEdges G (ett.series.data.coloring i.succ) (TreeSequenceVertexSet
        (ett.series.data.tree i.succ.castSucc)) choice.color,
    ∃ (w : V), TreeVertexOrder (ett.series.data.tree i.succ.castSucc) w choice.vertex ∧ Incident G
        w g) ∧ (ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) →
    ∀ alpha ∈ TreeMissingColors (ett.series.data.coloring i.succ) (ett.series.data.tree
        i.succ.castSucc), alpha ≠ choice.color → BoundaryColorEdges G (ett.series.data.coloring
        i.succ) (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) alpha = ∅)) (_ :
        terminalGamma ≠ choice.color) (_ : ett.series.data.coloring n choice.edge = some
        terminalGamma) (_ : terminalGamma ∈ TashkinovStoredColors ett.series.data n) (_ :
        StableColoring Tn (TashkinovStoredColors ett.series.data n) sigma generating) (_ : alpha ≠
        terminalGamma) (_ : BoundaryColorEdges G sigma (TreeSequenceVertexSet Tn) alpha = ∅),
        TreeInterchangeable G (ett.series.data.tree (Fin.last ett.rounds).castSucc) sigma alpha
        beta := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hMP hpositive hlower hPE base hproper
      hone hstable delta alpha beta hdelta halpha hne hbeta n Tn hgen hstableTree hproperGen
      honeGen i choice terminalGamma currentKind currentVertex currentDelta terminalGammaValue hi
      hdelta' hbound hnegc hcurrentEdge hgammaStored hstableRev halphaGamma hsigmaEmpty
  have hgammaSingleton := @helper_hgammaSingleton_407 V E inferInstance inferInstance inferInstance
      G k e0 input T generating sigma ett hgen hstableTree i choice terminalGamma hi hbound
      hcurrentEdge hgammaStored hstableRev
  have hnonempty : choice.edge ∈ BoundaryColorEdges G sigma
      (TreeSequenceVertexSet Tn) terminalGamma := by
    rw [hgammaSingleton]
    simp
  have hnonemptyData : choice.edge ∈ BoundaryEdges G
      (TreeSequenceVertexSet Tn) ∧
      sigma choice.edge = some terminalGamma := by
    simpa [BoundaryColorEdges] using hnonempty
  have hmissEq : TreeMissingColors sigma Tn =
      TreeMissingColors generating Tn := by
    unfold TreeMissingColors
    apply Finset.ext
    intro c
    constructor <;> intro hc
    · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
      refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
      exact hstableTree.2 v hv ▸ hcv
    · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
      refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
      exact (hstableTree.2 v hv).symm ▸ hcv
  have hclosure := CombinedStableClosurePreserved G k e0 input T generating generating sigma ett
    hpositive base (by simpa [n] using hgen) hPE hproperGen honeGen hproper hone hstable
  let baseSigma : HierarchyBase ett sigma :=
    { core := base.core
      closure := base.closure
      supportPosition := base.supportPosition
      supportPositive := base.supportPositive
      terminalMissingColors := by
        simpa [hgen] using hmissEq
      parallel := by
        dsimp
        intro hp
        have hh := base.parallel hp
        exact ⟨hh.1, hclosure.2.2, hh.2.2⟩
      nonparallel := base.nonparallel }
  have hcoreElem : ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet base.core) := ParallelClosureUnionElementary G k e0 input T generating
    ett hMP hpositive hlower hPE sigma hproper hone hstableTree baseSigma
  have helemSigma : ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet Tn) := by
    intro u hu v hv huv
    have huCore : u ∈ TreeSequenceVertexSet base.core := by
      obtain ⟨ou⟩ := (base.parallel hPE).2.2
      rw [ou.vertexSet]
      exact Finset.mem_union_left _ hu
    have hvCore : v ∈ TreeSequenceVertexSet base.core := by
      obtain ⟨ou⟩ := (base.parallel hPE).2.2
      rw [ou.vertexSet]
      exact Finset.mem_union_left _ hv
    exact hcoreElem huCore hvCore huv
  have hext := ExtensionBase G k e0 input T generating ett hMP hpositive hlower
  dsimp at hext
  have hstableLast : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      (ett.series.data.coloring (Fin.last ett.rounds)) sigma := by
    simpa [Tn, n, hgen] using hstableTree
  have hstableI : StableColoring
      (ett.series.data.tree i.succ.castSucc)
      (TashkinovStoredColors ett.series.data i.succ)
      (ett.series.data.coloring i.succ) sigma := by
    simpa [Tn, n, hgen, hi] using hstableTree
  have hcomponent := hext choice.vertex terminalGamma choice.color
    (by simpa [n, hi] using currentKind) (by simpa [n, hi] using currentVertex)
    (by simpa [n, hi] using terminalGammaValue) (by simpa [n, hi] using currentDelta)
    sigma hproper hone hstableLast
  have hvchoice : choice.vertex ∈ TreeSequenceVertexSet Tn := by
    simpa [Tn, hi] using choice.vertexDefective.1
  have hvchoiceI : choice.vertex ∈
      TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc) := by
    simpa [Tn, hi] using hvchoice
  have hcomponentI : ∀ w, w ∈
      TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc) →
      (Sum.inl w ∈ TwoColorComponent G sigma terminalGamma choice.color
        (Sum.inl choice.vertex) ↔ w = choice.vertex) := by
    intro w hw
    apply hcomponent w
    simpa [Tn, hi] using hw
  have hundo := ParallelExtensionUndoStable G k ett.rounds e0 input ett.series i
    choice.vertex terminalGamma choice.color
    (by simpa using currentKind) (by simpa using currentVertex)
    (by simpa using terminalGammaValue) (by simpa using currentDelta)
    sigma hproper hone hstableI hvchoiceI hcomponentI
  by_cases hbg : beta = terminalGamma
  · subst beta
    apply ElementarySingleBoundaryInterchangeable G sigma Tn alpha terminalGamma hproper
    · exact helemSigma
    · exact hsigmaEmpty
    · rw [hgammaSingleton]
      simp
  · exact @helper_branch_563 V E inferInstance inferInstance  inferInstance G k e0
      input T generating sigma ett hMP hpositive hlower hproper hone delta alpha beta hdelta
      halpha hne hbeta i choice terminalGamma hi hdelta' hnegc halphaGamma hundo hbg

private theorem helper_branch_213.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett) (_ : (0 : ℕ) <
        ett.rounds) (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (_ :
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) (base :
        HierarchyBase ett generating) (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored
        sigma e0) (_ : CombinedStableColoring (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) base.closure (TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds)) generating sigma) (_ delta alpha beta : Fin k) (_ : ett.series.data.delta
        (Fin.last ett.rounds) = some delta) (_ : alpha ∈ TreeMissingColors sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (_ : ¬alpha = delta) (_ : ¬beta =
        delta),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : generating = ett.series.data.coloring n) (_ : StableColoring Tn (TashkinovStoredColors
        ett.series.data n) generating sigma) (_ : IsProperEdgeColoring G generating) (_ :
        IsOneEdgeUncolored generating e0) (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree i.succ.castSucc) (TashkinovStoredColors ett.series.data
        i.castSucc) (ett.series.data.coloring i.castSucc)) (terminalGamma : Fin k) (_ :
        ParallelExtensionColor ett.series.data i.castSucc choice.selected choice.vertex
        terminalGamma) (secondStable : PartialEdgeColoring E k) (_ : StableColoring
        (ett.series.data.tree i.succ.castSucc) (insert choice.color (TashkinovStoredColors
        ett.series.data i.castSucc)) choice.selected secondStable) (_ : ett.series.data.coloring
        i.succ = TwoColorComponentSwap G secondStable terminalGamma choice.color (Sum.inl
        choice.vertex)) (_ : ett.series.data.stored i.succ = { choice.color, terminalGamma }) (_ :
        ett.series.data.connectingEdges i.succ = { choice.edge }) (_ : ett.series.data.kind i.succ
        = some TashkinovExtensionKind.PE) (_ : ett.series.data.chosenVertex i.succ = some
        choice.vertex) (_ : ett.series.data.delta i.succ = some choice.color) (_ :
        ett.series.data.gamma i.succ = some terminalGamma) (_ : n = i.succ), TreeInterchangeable G
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) sigma alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hMP hpositive hlower hPE base hproper
      hone hstable gamma delta alpha beta hdelta halpha hne hbeta n Tn hgen hstableTree
      hproperGen honeGen i choice terminalGamma gammaRule secondStable secondStableRelation
      currentColoring currentStored currentEdges currentKind currentVertex currentDelta
      terminalGammaValue targetEq
  have hi : i.succ = n := by
    apply Fin.ext
    have hv := congrArg Fin.val targetEq
    simp at hv
    omega
  have hvertex : ett.series.data.chosenVertex n = some choice.vertex := by
    rw [← hi]
    exact currentVertex
  have hcolor : ett.series.data.gamma n = some terminalGamma := by
    rw [← hi]
    exact terminalGammaValue
  have hdelta' : ett.series.data.delta n = some choice.color := by
    rw [← hi]
    exact currentDelta
  have hlowerElem := @helper_hlowerElem_240 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett hMP hpositive hlower i
  have hbound := HkuParallelBoundaryStructure G k ett.rounds e0 input ett.series i
    choice.edge choice.color terminalGamma choice.vertex
    (by simpa using currentKind) (by simpa using currentEdges)
    (by simpa using currentDelta) (by simpa using terminalGammaValue)
    (by simpa using currentVertex)
  have hpre := @helper_hpre_845 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett hpositive i terminalGamma hi hcolor hlowerElem
  have hnegc : terminalGamma ≠ choice.color := by
    intro heq
    have hp : choice.color ∈ PresentColors G choice.selected choice.vertex := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨choice.edge, choice.edgeIncident, choice.edgeColor⟩
    have hm : terminalGamma ∉ PresentColors G choice.selected choice.vertex := by
      simpa [MissingColors] using gammaRule.1
    exact hm (heq ▸ hp)
  have hsecondEdge : secondStable choice.edge = some choice.color := by
    have hs := secondStableRelation.1 choice.edge
      ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
      ⟨choice.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _),
        choice.edgeColor⟩
    exact hs.trans choice.edgeColor
  have hcomponentEdge : Sum.inr choice.edge ∈
      TwoColorComponent G secondStable terminalGamma choice.color
        (Sum.inl choice.vertex) := by
    change (TwoColorIncidenceGraph G secondStable terminalGamma choice.color).connectedComponentMk
        (Sum.inr choice.edge) =
      (TwoColorIncidenceGraph G secondStable terminalGamma choice.color).connectedComponentMk
        (Sum.inl choice.vertex)
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, choice.edgeIncident, hsecondEdge]
  have hcurrentEdge : ett.series.data.coloring n choice.edge =
      some terminalGamma := by
    have hcur : ett.series.data.coloring n =
        TwoColorComponentSwap G secondStable terminalGamma choice.color
          (Sum.inl choice.vertex) := by
      simpa [hi] using currentColoring
    rw [hcur]
    simp [TwoColorComponentSwap, hcomponentEdge, hsecondEdge]
  have hgammaNotTree : terminalGamma ∉ TreeMissingColors generating Tn := by
    intro hm
    have hm' : terminalGamma ∈ TreeMissingColors
        (ett.series.data.coloring i.succ)
        (ett.series.data.tree i.succ.castSucc) := by
      simpa [hgen, Tn, hi] using hm
    have hx := hbound.2.2 hpre terminalGamma hm' hnegc
    rw [hbound.1] at hx
    simp at hx
  have hgammaStored := @helper_hgammaStored_906 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett hpositive hgen i choice terminalGamma currentStored hi hgammaNotTree
  have hstableRev := @helper_hstableRev_920 V E inferInstance inferInstance inferInstance G k e0
      input T generating sigma ett hproper hone hstableTree hproperGen honeGen
  have hgenMissing : alpha ∈ TreeMissingColors generating Tn := by
    unfold TreeMissingColors at halpha ⊢
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp halpha
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    rw [← hstableTree.2 v hv]
    exact hm
  have halphaGamma : alpha ≠ terminalGamma := by
    intro heq
    apply hgammaNotTree
    simpa [heq] using hgenMissing
  have hgenEmpty : BoundaryColorEdges G generating
      (TreeSequenceVertexSet Tn) alpha = {} := by
    have hx := hbound.2.2 hpre alpha
      (by simpa [hgen, Tn, hi] using hgenMissing)
      (by
        have hcd : choice.color = delta := by
          rw [← Option.some.injEq]
          rw [← hdelta', hdelta]
        intro ha
        apply hne
        exact ha.trans hcd)
    simpa [hgen, Tn, hi] using hx
  have hsigmaEmpty := @helper_hsigmaEmpty_384 V E inferInstance inferInstance inferInstance G k e0
      input T generating sigma ett alpha halpha hstableRev hgenEmpty
  exact @helper_continuation_1320 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating sigma ett hMP hpositive hlower hPE base hproper hone hstable delta
      alpha beta hdelta halpha hne hbeta hgen hstableTree hproperGen honeGen i choice
      terminalGamma currentKind currentVertex currentDelta terminalGammaValue hi hdelta' hbound
      hnegc hcurrentEdge hgammaStored hstableRev halphaGamma hsigmaEmpty
theorem InterchangePETreeAwayFromDelta {V E : Type*}
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
    (support : V) (gamma delta alpha beta : Fin k)
    (_ : ett.series.data.chosenVertex (Fin.last ett.rounds) =
      some support)
    (_ : ett.series.data.gamma (Fin.last ett.rounds) = some gamma)
    (hdelta : ett.series.data.delta (Fin.last ett.rounds) = some delta) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    alpha ∈ TreeMissingColors sigma Tn →
      alpha ≠ delta →
      beta ≠ delta →
      TreeInterchangeable G Tn sigma alpha beta := by
  classical
  dsimp
  intro halpha hne hbeta
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  have hgen : generating = ett.series.data.coloring n := by
    simpa [n] using ett.generatingColoring
  have hstableTree : StableColoring Tn
      (TashkinovStoredColors ett.series.data n) generating sigma := by
    simpa [Tn, hgen] using hstable.1
  have hproperGen := @helper_hproperGen_107 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett hpositive hPE gamma hgen
  have honeGen := @helper_honeGen_147 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett hpositive hPE gamma hgen
  have hstep := ett.series.certified n
  generalize targetEq : n = target at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hn : n ≠ 0 := by simp [n]; omega
    exact (hn targetEq).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hp : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hp
    contradiction
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hp : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hp
    contradiction
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      terminalGamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta terminalGammaValue closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_213 V E inferInstance inferInstance inferInstance inferInstance G
              k e0 input T generating sigma ett hMP hpositive hlower hPE base hproper hone
              hstable gamma delta alpha beta hdelta halpha hne hbeta hgen hstableTree hproperGen
              honeGen i choice terminalGamma gammaRule secondStable secondStableRelation
              currentColoring currentStored currentEdges currentKind currentVertex currentDelta
              terminalGammaValue targetEq
end GoldbergSeymour

end
