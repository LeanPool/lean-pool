/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ElementaryClosedMissingColorOdd

public import LeanPool.GoldbergSeymour.HierarchyBaseExists

public import LeanPool.GoldbergSeymour.ParallelClosureUnionElementary

public import LeanPool.GoldbergSeymour.TreeMissingColorsCardLowerBound
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetStrict

/-!
# Technical Current Ladder Missing Bound Large

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_stepFacts_59.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (i : Fin ett.rounds), IsProperEdgeColoring G
        (ett.series.data.coloring i.castSucc) ∧ IsOneEdgeUncolored (ett.series.data.coloring
        i.castSucc) e0 ∧ ColoredVertexSetClosed G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) ∧
        TreeSequenceInitialSegment (ett.series.data.tree i.succ.castSucc) (ett.series.data.tree
        i.succ.succ) ∧ (ett.series.data.tree i.succ.castSucc).length < (ett.series.data.tree
        i.succ.succ).length := by
  classical
  intro V E _ _ _ G k e0 input T generating ett r
  have fact := ett.series.certified r.succ
  generalize hi : r.succ = z at fact ⊢
  cases fact with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    simp_all []
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hsame : i = r := by
      apply Fin.ext
      simpa using (congrArg Fin.val hi).symm
    subst i
    simpa [hi] using ⟨previousProper, previousOneUncolored, previousClosed,
      orderedExtension, strictExtension⟩
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have hsame : i = r := by
      apply Fin.ext
      simpa using (congrArg Fin.val hi).symm
    subst i
    simpa [hi] using ⟨previousProper, previousOneUncolored, previousClosed,
      orderedExtension, strictExtension⟩
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hsame : i = r := by
      apply Fin.ext
      simpa using (congrArg Fin.val hi).symm
    subst i
    simpa [hi] using ⟨previousProper, previousOneUncolored, previousClosed,
      orderedExtension, strictExtension⟩

private theorem helper_elementaryAt_110.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett → TechnicalInductionContext G k e0 ett.rounds
        → (0 : ℕ) < ett.rounds →
    ∀ (r : Fin ett.rounds), ColoredVertexSetElementary G (ett.series.data.coloring r.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP ctx positive r
  by_cases hfirst : r.val = 0
  · have hr : r = (⟨0, positive⟩ : Fin ett.rounds) := by
      apply Fin.ext
      exact hfirst
    subst r
    exact (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
  · let q : ℕ := r.val
    have hrpos : 1 ≤ r.val := Nat.one_le_iff_ne_zero.mpr hfirst
    have hrlt := r.isLt
    have hqpos : 1 ≤ q := by dsimp [q]; exact hrpos
    have hqbefore : q < ett.rounds := by dsimp [q]; exact hrlt
    obtain ⟨restricted, hrq, hrestricted, htrees, hdata⟩ :=
      CertifiedETTRestriction G k e0 input T generating ett hMP q
        (by omega) hqbefore
    have he : ColoredVertexSetElementary G
        (ett.series.data.coloring ⟨q, by omega⟩)
        (TreeSequenceVertexSet (ett.series.data.tree ⟨q + 1, by omega⟩)) := by
      exact ctx.lowerOne (input := input)
        (T := ett.series.data.tree ⟨q + 1, by omega⟩)
        (generating := ett.series.data.coloring ⟨q, by omega⟩) restricted (by omega)
        (by simpa [hrq] using hqbefore) hrestricted
    have eqcolor : (⟨q, by omega⟩ : Fin (ett.rounds + 1)) = r.castSucc := by
      apply Fin.ext
      dsimp [q]
    have eqtree : (⟨q + 1, by omega⟩ : Fin (ett.rounds + 2)) = r.succ.castSucc := by
      apply Fin.ext
      dsimp [q]
    rw [eqcolor, eqtree] at he
    exact he

private theorem helper_oddAt_143.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumDegree G + (1 : ℕ) ≤ k → (
    ∀ (i : Fin ett.rounds), IsProperEdgeColoring G (ett.series.data.coloring i.castSucc) ∧
        IsOneEdgeUncolored (ett.series.data.coloring i.castSucc) e0 ∧ ColoredVertexSetClosed G
        (ett.series.data.coloring i.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        i.succ.castSucc)) ∧ TreeSequenceInitialSegment (ett.series.data.tree i.succ.castSucc)
        (ett.series.data.tree i.succ.succ) ∧ (ett.series.data.tree i.succ.castSucc).length <
        (ett.series.data.tree i.succ.succ).length) → (
    ∀ (r : Fin ett.rounds), ColoredVertexSetElementary G (ett.series.data.coloring r.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc))) →
    ∀ (r : Fin ett.rounds), Odd (TreeSequenceVertexSet (ett.series.data.tree
        r.succ.castSucc)).card := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hdegree stepFacts elementaryAt r
  have he : ColoredVertexSetElementary G (ett.series.data.coloring r.castSucc)
      (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)) :=
    elementaryAt r
  have sf := stepFacts r
  have hp : IsProperEdgeColoring G (ett.series.data.coloring r.castSucc) := sf.1
  have hc : ColoredVertexSetClosed G (ett.series.data.coloring r.castSucc)
      (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)) := sf.2.2.1
  obtain ⟨alpha, halpha⟩ := Finset.card_pos.mp (by
    have hh := TreeMissingColorsCardLowerBound G k e0
      (ett.series.data.coloring r.castSucc)
      (ett.series.data.tree r.succ.castSucc) (by simpa using sf.2.1.1)
      hdegree he
    have hnon : 0 ≤
        (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)).card :=
      Nat.zero_le _
    have hpos : 0 <
        (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)).card + 2 := by
      omega
    exact lt_of_lt_of_le hpos hh)
  have hclosed : TreeColorSetClosed G
      (ett.series.data.coloring r.castSucc)
      (ett.series.data.tree r.succ.castSucc) {alpha} := by
    intro beta hbeta
    have hba : beta = alpha := by simpa using hbeta
    rw [hba]
    ext f
    constructor
    · intro hf
      simp only [BoundaryColorEdges, Finset.mem_filter] at hf
      obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp halpha
      exact False.elim ((hc hf.1 hv hf.2) hmv)
    · intro hf
      simp at hf
  exact ElementaryClosedMissingColorOdd G k e0
    (ett.series.data.coloring r.castSucc)
    (ett.series.data.tree r.succ.castSucc) alpha hp he
    (by simpa using halpha) hclosed

private theorem helper_cardBound_183.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett → (11 : ℕ) ≤ TashkinovOrder G → (0 : ℕ) <
        ett.rounds → (
    ∀ (i : Fin ett.rounds), IsProperEdgeColoring G (ett.series.data.coloring i.castSucc) ∧
        IsOneEdgeUncolored (ett.series.data.coloring i.castSucc) e0 ∧ ColoredVertexSetClosed G
        (ett.series.data.coloring i.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        i.succ.castSucc)) ∧ TreeSequenceInitialSegment (ett.series.data.tree i.succ.castSucc)
        (ett.series.data.tree i.succ.succ) ∧ (ett.series.data.tree i.succ.castSucc).length <
        (ett.series.data.tree i.succ.succ).length) → (
    ∀ (r : Fin ett.rounds), Odd (TreeSequenceVertexSet (ett.series.data.tree
        r.succ.castSucc)).card) →
    ∀ (n : ℕ) (hn : n < ett.rounds), (2 : ℕ) * n + (11 : ℕ) ≤ (TreeSequenceVertexSet
        (ett.series.data.tree (⟨n, hn⟩ : Fin ett.rounds).succ.castSucc)).card := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hlarge positive stepFacts oddAt n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      have hbaseEq := hMP.1
      calc
        11 ≤ TashkinovOrder G := hlarge
        _ = (TreeSequenceVertexSet
            (ett.series.data.tree (⟨1, by omega⟩ : Fin (ett.rounds + 2)))).card := by
          simpa using hbaseEq.symm
    · let p : Fin ett.rounds := ⟨n - 1, by omega⟩
      have hp := ih (n - 1) (by omega) (by omega)
      have sf := stepFacts p
      have hseg := TreeSequenceInitialSegmentVertexSetStrict sf.2.2.2.1 sf.2.2.2.2
      have hsegCard := Finset.card_lt_card hseg
      have hp' : 2 * (n - 1) + 11 ≤
          (TreeSequenceVertexSet (ett.series.data.tree p.succ.castSucc)).card := by
        exact hp
      obtain ⟨a, ha⟩ := oddAt p
      let cur : Fin ett.rounds := ⟨n, by omega⟩
      obtain ⟨b, hb⟩ := oddAt cur
      have heq : cur.succ.castSucc = p.succ.succ := by
        apply Fin.ext
        dsimp [cur, p]
        omega
      have hb' : (TreeSequenceVertexSet
          (ett.series.data.tree p.succ.succ)).card = 2 * b + 1 := by
        rw [← heq]
        exact hb
      have hnext : 2 * n + 11 ≤
          (TreeSequenceVertexSet (ett.series.data.tree p.succ.succ)).card := by
        omega
      rw [← heq] at hnext
      exact hnext

private theorem helper_finalFacts_230.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett → TechnicalInductionContext G k e0 ett.rounds
        → (0 : ℕ) < ett.rounds → (
    ∀ (r : Fin ett.rounds), ColoredVertexSetElementary G (ett.series.data.coloring r.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc))) →
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let finalTree : TreeSequence G e0 := ett.series.data.tree terminal.castSucc;
        ColoredVertexSetElementary G generating (TreeSequenceVertexSet finalTree) ∧
        IsProperEdgeColoring G generating ∧ IsOneEdgeUncolored generating e0 := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP ctx positive elementaryAt terminal finalTree
  have cert := ett.series.certified terminal
  generalize ht : terminal = z at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    have : (0 : Fin (ett.rounds + 1)) = terminal := by simp [ht]
    have : False := by
      have hzero : terminal = 0 := by simp [ht]
      have hv := congrArg Fin.val hzero
      simp [terminal] at hv
      omega
    exact this.elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hi : i.succ = terminal := by simp [ht]
    have hprev : ColoredVertexSetElementary G
        (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet finalTree) := by
      have ee : ColoredVertexSetElementary G
          (ett.series.data.coloring i.castSucc)
          (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) :=
        elementaryAt i
      have htree : ett.series.data.tree i.succ.castSucc = finalTree := by
        simp [finalTree, hi]
      rw [htree] at ee
      unfold ColoredVertexSetElementary at ee ⊢
      intro u hu v hv huv
      exact ee hu hv huv
    have hgen : generating = choice.selected := by
      calc
        generating = ett.series.data.coloring terminal := ett.generatingColoring
        _ = choice.selected := by rw [← currentColoring]; simp [hi]
    rw [hgen]
    refine ⟨?_, choice.selectedProper,
      by simpa [hgen] using choice.selectedOneUncolored⟩
    intro u hu v hv huv
    have hui : u ∈ TreeSequenceVertexSet
        (ett.series.data.tree i.succ.castSucc) := by
      simpa [finalTree, hi] using hu
    have hvi : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree i.succ.castSucc) := by
      simpa [finalTree, hi] using hv
    rw [choice.selectedStable.2 u hui, choice.selectedStable.2 v hvi]
    exact hprev hu hv huv
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have hi : i.succ = terminal := by simp [ht]
    have hgen : generating = ett.series.data.coloring terminal := by
      exact ett.generatingColoring
    have base := Classical.choice (HierarchyBaseExists ett)
    have stable : StableColoring finalTree
        (TashkinovStoredColors ett.series.data terminal) generating generating := by
      unfold StableColoring
      exact ⟨by intro f hf h; rfl, by intro v hv; rfl⟩
    have coreElem : ColoredVertexSetElementary G generating
        (TreeSequenceVertexSet base.core) :=
      ParallelClosureUnionElementary G k e0 input
      T generating ett hMP positive
      (by
        intro input' T' generating' lowerE hp hb hm
        exact ⟨ctx.lowerOne lowerE hp hb hm,
          ctx.lowerTwo lowerE hp hb hm,
          ctx.lowerThree lowerE hp hb hm,
          ctx.lowerFour lowerE hp hb hm,
          ctx.lowerFive lowerE hp hb hm,
          ctx.lowerSix lowerE hp hb hm⟩)
      (by simpa [hi] using currentKind)
      generating (by
        rw [hgen]
        rw [← hi]
        exact currentProper)
        (by
          rw [hgen]
          rw [← hi]
          exact currentOneUncolored) stable base
    obtain ⟨closureFact, union, unionFact⟩ :=
      base.parallel (by simpa [hi] using currentKind)
    obtain ⟨unionFact⟩ := unionFact
    have subset := TreeSequenceInitialSegmentVertexSetSubset unionFact.leftSegment
    have cp : IsProperEdgeColoring G
        (ett.series.data.coloring terminal) := by
      rw [← hi]
      exact currentProper
    have co : IsOneEdgeUncolored
        (ett.series.data.coloring terminal) e0 := by
      rw [← hi]
      exact currentOneUncolored
    refine ⟨?_, by rw [hgen]; exact cp, by rw [hgen]; exact co⟩
    intro u hu v hv huv
    exact coreElem (subset hu) (subset hv) huv
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hi : i.succ = terminal := by simp [ht]
    have hprev : ColoredVertexSetElementary G
        (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet finalTree) := by
      have ee : ColoredVertexSetElementary G
          (ett.series.data.coloring i.castSucc)
          (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) :=
        elementaryAt i
      have htree : ett.series.data.tree i.succ.castSucc = finalTree := by
        simp [finalTree, hi]
      rw [htree] at ee
      unfold ColoredVertexSetElementary at ee ⊢
      intro u hu v hv huv
      exact ee hu hv huv
    have hgen : generating = ett.series.data.coloring i.castSucc := by
      calc
        generating = ett.series.data.coloring terminal := ett.generatingColoring
        _ = ett.series.data.coloring i.succ := by rw [hi]
        _ = ett.series.data.coloring i.castSucc := currentColoring
    refine ⟨?_, by simpa [hgen] using previousProper,
      by simpa [hgen] using previousOneUncolored⟩
    rw [hgen]
    exact hprev

theorem TechnicalCurrentLadderMissingBoundLarge
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 11 <= TashkinovOrder G) :
    let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree terminal.castSucc
    2 * ett.rounds + 11 <= (TreeMissingColors generating Tn).card := by
  classical
  dsimp
  have positive : 0 < ett.rounds := Nat.lt_of_lt_of_le Nat.zero_lt_one ett.roundsPositive
  have stepFacts := @helper_stepFacts_59 V E inferInstance inferInstance inferInstance G k e0 input
      T generating ett
  have elementaryAt := @helper_elementaryAt_110 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T generating ett hMP ctx positive
  have oddAt := @helper_oddAt_143 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett hdegree stepFacts elementaryAt
  have cardBound := @helper_cardBound_183 V E inferInstance inferInstance inferInstance G k e0 input
      T generating ett hMP hlarge positive stepFacts oddAt
  have hvertex : 2 * ett.rounds + 9 ≤
      (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card := by
    have hh := cardBound (ett.rounds - 1) (by omega)
    have heq : ett.rounds - 1 + 1 = ett.rounds := Nat.sub_add_cancel (by omega)
    convert hh using 1 <;> simp [Fin.last, heq]; omega
  let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let finalTree : TreeSequence G e0 := ett.series.data.tree terminal.castSucc
  have finalFacts := @helper_finalFacts_230 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T generating ett hMP ctx positive elementaryAt
  have hmissing := TreeMissingColorsCardLowerBound G k e0 generating finalTree
    (by simpa [finalTree] using finalFacts.2.2.1) hdegree finalFacts.1
  have hv : 2 * ett.rounds + 9 ≤
      (TreeSequenceVertexSet finalTree).card := by
    simpa [finalTree, terminal] using hvertex
  calc
    2 * ett.rounds + 11 ≤ (TreeSequenceVertexSet finalTree).card + 2 := by omega
    _ ≤ (TreeMissingColors generating finalTree).card := hmissing

end GoldbergSeymour

end
