/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HkuUnsupportedVertexColors
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ParallelExtensionColor
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.SupportingPEColorChain
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Supporting PEStored Intersection

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_pe_step_55.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (j : Fin (rounds + (1 : ℕ))) (i : Fin rounds), j =
        i.succ →
    ∀ (v : V) (gamma delta : Fin k), series.data.kind j = some TashkinovExtensionKind.PE →
        series.data.chosenVertex j = some v → series.data.delta j = some delta → series.data.gamma
        j = some gamma → v ∈ TreeSequenceVertexSet (series.data.tree i.succ.castSucc) →
        MissingColors G (series.data.coloring i.castSucc) v \ { gamma } = MissingColors G
        (series.data.coloring i.succ) v \ { delta } ∧ gamma ∉ MissingColors G
        (series.data.coloring i.succ) v ∧ delta ∈ MissingColors G (series.data.coloring i.succ) v
  := by
  classical
  intro V E _ _ _ G k rounds e0 input series j i hj v gamma delta hkind hvertex hdelta hgamma hv
  cases series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    rw [initialKind] at hkind
    simp at hkind
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    rw [currentKind] at hkind
    simp at hkind
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    rw [currentKind] at hkind
    simp at hkind
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      actualGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hci : ci = i := by
      apply Fin.ext
      have := congrArg Fin.val hj
      simp at this ⊢
      omega
    subst ci
    have hvchoice : choice.vertex = v := by
      have := hvertex
      rw [currentVertex] at this
      simpa using Option.some.inj this
    subst v
    have hdelta' : choice.color = delta := by
      rw [currentDelta] at hdelta
      simpa using Option.some.inj hdelta
    have hgamma' : actualGamma = gamma := by
      rw [currentGamma] at hgamma
      simpa using Option.some.inj hgamma
    subst delta
    subst gamma
    have hmiss : actualGamma ∈ MissingColors G secondStable choice.vertex := by
      exact (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸ gammaRule.1
    have hedge : secondStable choice.edge = some choice.color := by
      exact (secondStableRelation.1 choice.edge
        ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
        ⟨choice.color, And.intro (by simp) choice.edgeColor⟩).trans choice.edgeColor
    have hneq : actualGamma ≠ choice.color := by
      intro heq
      have hm' : actualGamma ∈ (Finset.univ : Finset (Fin k)) \ PresentColors G secondStable
          choice.vertex := hmiss
      apply (Finset.mem_sdiff.mp hm').2
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨choice.edge, choice.edgeIncident, by simpa [heq] using hedge⟩
    have component_edge : ∀ e, Incident G choice.vertex e →
        secondStable e = some actualGamma ∨ secondStable e = some choice.color →
        Sum.inr e ∈ TwoColorComponent G secondStable actualGamma choice.color
          (Sum.inl choice.vertex) := by
      intro e he hc
      change (TwoColorIncidenceGraph G secondStable actualGamma choice.color).connectedComponentMk
        (Sum.inr e) = _
      apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      simp [TwoColorIncidenceGraph, he, hc]
    have gamma_no : ∀ e, Incident G choice.vertex e →
        secondStable e ≠ some actualGamma := by
      intro e he hec
      have hm' : actualGamma ∈ (Finset.univ : Finset (Fin k)) \ PresentColors G secondStable
          choice.vertex := hmiss
      apply (Finset.mem_sdiff.mp hm').2
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, he, hec⟩
    have swap_gamma_no : actualGamma ∉ MissingColors G
        (TwoColorComponentSwap G secondStable actualGamma choice.color
          (Sum.inl choice.vertex)) choice.vertex := by
      intro hm
      have hm' : actualGamma ∈ (Finset.univ : Finset (Fin k)) \ PresentColors G
          (TwoColorComponentSwap G secondStable actualGamma choice.color
            (Sum.inl choice.vertex)) choice.vertex := hm
      apply (Finset.mem_sdiff.mp hm').2
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨choice.edge, choice.edgeIncident, ?_⟩
      rw [TwoColorComponentSwap]
      simp [component_edge choice.edge choice.edgeIncident (Or.inr hedge), hedge]
    have swap_delta_yes : choice.color ∈ MissingColors G
        (TwoColorComponentSwap G secondStable actualGamma choice.color
          (Sum.inl choice.vertex)) choice.vertex := by
      apply Finset.mem_sdiff.mpr
      refine ⟨by simp, ?_⟩
      intro hp
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨e, he, hec⟩ := hp
      rw [TwoColorComponentSwap] at hec
      by_cases hcomp : Sum.inr e ∈ TwoColorComponent G secondStable actualGamma
          choice.color (Sum.inl choice.vertex)
      · simp [hcomp] at hec
        by_cases hgc : secondStable e = some actualGamma
        · exact (gamma_no e he hgc).elim
        · by_cases hdc : secondStable e = some choice.color
          · simp [hdc, hneq] at hec
            exact hneq hec.symm
          · simp [hgc, hdc] at hec
      · simp only [Fin.castSucc_succ, hcomp, ↓reduceIte] at hec
        exact hcomp (component_edge e he (Or.inr hec))
    have present_other :
    ∀ c, c ≠ actualGamma → c ≠ choice.color → (c ∈ PresentColors G secondStable choice.vertex ↔ c
        ∈ PresentColors G (TwoColorComponentSwap G secondStable actualGamma choice.color (Sum.inl
        choice.vertex)) choice.vertex) := by
      intro c hcg hcd
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> rintro ⟨e, he, hec⟩ <;> refine ⟨e, he, ?_⟩
      · rw [TwoColorComponentSwap]
        by_cases hcomp : Sum.inr e ∈ TwoColorComponent G secondStable actualGamma
            choice.color (Sum.inl choice.vertex)
        · simp [hcomp, hec, hcg, hcd]
        · simp only [Fin.castSucc_succ, hcomp, ↓reduceIte]
          exact hec
      · rw [TwoColorComponentSwap] at hec
        by_cases hcomp : Sum.inr e ∈ TwoColorComponent G secondStable actualGamma
            choice.color (Sum.inl choice.vertex)
        · simp only [Fin.castSucc_succ, hcomp, ↓reduceIte] at hec
          by_cases ha : secondStable e = some actualGamma
          · simp [ha] at hec
            exact (hcd hec.symm).elim
          · by_cases hb : secondStable e = some choice.color
            · simp [hb, hneq.symm] at hec
              exact (hcg hec.symm).elim
            · simp only [ha, ↓reduceIte, hb] at hec
              exact hec
        · simp only [Fin.castSucc_succ, hcomp, ↓reduceIte] at hec
          exact hec
    have missing_other :
    ∀ c, c ≠ actualGamma → c ≠ choice.color → (c ∈ MissingColors G secondStable choice.vertex ↔ c
        ∈ MissingColors G (TwoColorComponentSwap G secondStable actualGamma choice.color (Sum.inl
        choice.vertex)) choice.vertex) := by
      intro c hcg hcd
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact not_congr (present_other c hcg hcd)
    refine ⟨?_, ?_, ?_⟩
    · ext c
      simp only [Finset.mem_sdiff]
      have hstable : MissingColors G (series.data.coloring i.castSucc) choice.vertex =
        MissingColors G secondStable choice.vertex :=
        (choice.selectedStable.2 choice.vertex hv).symm.trans
        (secondStableRelation.2 choice.vertex hv).symm
      rw [hstable, currentColoring]
      simp only [Finset.mem_singleton]
      by_cases hcg : c = actualGamma
      · subst c
        simp [hmiss, swap_gamma_no]
      by_cases hcd : c = choice.color
      · subst c
        have delta_no : choice.color ∉ MissingColors G secondStable choice.vertex := by
          intro hm
          have hm' : choice.color ∈ (Finset.univ : Finset (Fin k)) \ PresentColors G secondStable
              choice.vertex := hm
          apply (Finset.mem_sdiff.mp hm').2
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨choice.edge, choice.edgeIncident, hedge⟩
        simp [delta_no, swap_delta_yes]
      simpa [hcg, hcd] using (missing_other c hcg hcd)
    · rw [currentColoring]
      exact swap_gamma_no
    · rw [currentColoring]
      exact swap_delta_yes

private theorem helper_support_tree_236.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (u : V) (j : Fin (rounds + (1 : ℕ))),
        series.data.kind j = some TashkinovExtensionKind.PE → series.data.chosenVertex j = some u
        → u ∈ TreeSequenceVertexSet (series.data.tree j.castSucc) := by
  classical
  intro V E _ _ _ G k rounds e0 input series u j hk hvj
  cases series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    rw [initialKind] at hk
    simp at hk
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    rw [currentKind] at hk
    simp at hk
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    rw [currentKind] at hk
    simp at hk
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      actualGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    rw [currentKind] at hk
    have hv : choice.vertex = u := by
      rw [currentVertex] at hvj
      simpa using Option.some.inj hvj
    simpa [hv] using choice.vertexDefective.1

private theorem helper_hlocal_273.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds p : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (u : V) (indices : Fin (p
        + (1 : ℕ)) → Fin rounds), (
    ∀ (j : Fin rounds), (↑j : ℕ) ≤ (↑q : ℕ) ∧ series.data.kind j.succ = some
        TashkinovExtensionKind.PE ∧ series.data.chosenVertex j.succ = some u ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = j) → (
    ∀ (j : Fin (rounds + (1 : ℕ))) (i : Fin rounds), j = i.succ →
    ∀ (v : V) (gamma delta : Fin k), series.data.kind j = some TashkinovExtensionKind.PE →
        series.data.chosenVertex j = some v → series.data.delta j = some delta → series.data.gamma
        j = some gamma → v ∈ TreeSequenceVertexSet (series.data.tree i.succ.castSucc) →
        MissingColors G (series.data.coloring i.castSucc) v \ { gamma } = MissingColors G
        (series.data.coloring i.succ) v \ { delta } ∧ gamma ∉ MissingColors G
        (series.data.coloring i.succ) v ∧ delta ∈ MissingColors G (series.data.coloring i.succ) v)
        → (
    ∀ (j : Fin (rounds + (1 : ℕ))), series.data.kind j = some TashkinovExtensionKind.PE →
        series.data.chosenVertex j = some u → u ∈ TreeSequenceVertexSet (series.data.tree
        j.castSucc)) →
    ∀ (a : Fin (p + (1 : ℕ))),
    ∃ (gamma : Fin k), series.data.gamma (indices a).succ = some gamma ∧
    ∃ (delta : Fin k), series.data.delta (indices a).succ = some delta ∧ MissingColors G
        (series.data.coloring (indices a).castSucc) u \ { gamma } = MissingColors G
        (series.data.coloring (indices a).succ) u \ { delta } ∧ gamma ∉ MissingColors G
        (series.data.coloring (indices a).succ) u ∧ delta ∈ MissingColors G (series.data.coloring
        (indices a).succ) u ∧ series.data.stored (indices a).succ = { delta, gamma } := by
  classical
  intro V E _ _ _ G k rounds p e0 input series q u indices henumerates pe_step support_tree
  have pe_data : ∀ (j : Fin (rounds + 1)) (i : Fin rounds), j = i.succ →
      series.data.kind j = some TashkinovExtensionKind.PE →
      ∃ gamma delta, series.data.gamma j = some gamma ∧
        series.data.delta j = some delta ∧ series.data.stored j = {delta, gamma} := by
    intro j i hj hk
    cases series.certified j with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      rw [initialKind] at hk
      simp at hk
    | SE ci previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
      rw [currentKind] at hk
      simp at hk
    | RE ci previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        available currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
        orderedExtension strictExtension =>
      rw [currentKind] at hk
      simp at hk
    | PE ci previousProper previousOneUncolored previousClosed previousNotStronglyClosed
        noRevisiting choice seriesAlternativeFails actualGamma gammaRule secondStable
        secondStableProper secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
        orderedExtension strictExtension =>
      have hci : ci = i := by
        apply Fin.ext
        have hh := congrArg Fin.val hj
        simp at hh ⊢
        omega
      subst ci
      exact ⟨actualGamma, choice.color, currentGamma, currentDelta, currentStored⟩
  intro a
  have he := (henumerates (indices a)).mpr ⟨a, rfl⟩
  have ht := support_tree (indices a).succ he.2.1 he.2.2
  obtain ⟨gamma, delta, hg, hd, hstored⟩ := pe_data ((indices a).succ) (indices a) rfl he.2.1
  have hp := pe_step (indices a).succ (indices a) rfl u gamma delta
      he.2.1 he.2.2 hd hg ht
  refine ⟨gamma, hg, delta, hd, ?_, ?_, ?_, ?_⟩
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2
  · exact hstored

private theorem helper_next_segment_336.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (j : Fin (rounds + (1 : ℕ))) (i : Fin rounds), j =
        i.succ → TreeSequenceInitialSegment (series.data.tree i.succ.castSucc) (series.data.tree
        i.succ.succ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series j i hj
  cases series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero i) hj.symm |>.elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hvals := congrArg Fin.val hj
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hvals := congrArg Fin.val hj
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hvals := congrArg Fin.val hj
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension

private theorem helper_hgap_377.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds p : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (u : V) (indices : Fin (p
        + (1 : ℕ)) → Fin rounds), (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices a) : ℕ) < (↑(indices b) : ℕ)) →
        (
    ∀ (j : Fin rounds), (↑j : ℕ) ≤ (↑q : ℕ) ∧ series.data.kind j.succ = some
        TashkinovExtensionKind.PE ∧ series.data.chosenVertex j.succ = some u ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = j) → (
    ∀ (j : Fin (rounds + (1 : ℕ))), series.data.kind j = some TashkinovExtensionKind.PE →
        series.data.chosenVertex j = some u → u ∈ TreeSequenceVertexSet (series.data.tree
        j.castSucc)) → (
    ∀ (T T' : TreeSequence G e0), TreeSequenceInitialSegment T T' →
    ∀ x ∈ TreeSequenceVertexSet T, x ∈ TreeSequenceVertexSet T') → (
    ∀ (j : Fin (rounds + (1 : ℕ))) (i : Fin rounds), j = i.succ → TreeSequenceInitialSegment
        (series.data.tree i.succ.castSucc) (series.data.tree i.succ.succ)) →
    ∀ (a : Fin p), MissingColors G (series.data.coloring (indices a.castSucc).succ) u =
        MissingColors G (series.data.coloring (indices a.succ).castSucc) u := by
  classical
  intro V E _ _ _ G k rounds p e0 input series q u indices hincreasing henumerates support_tree
      transfer_tree next_segment a
  let pp : Fin rounds := ⟨(indices a.castSucc).val + 1, by
    have hinc := hincreasing a.castSucc a.succ (by simp)
    omega⟩
  let qq : Fin rounds := ⟨(indices a.succ).val - 1, by
    have := (indices a.succ).isLt
    omega⟩
  by_cases hcon : (indices a.succ).val = (indices a.castSucc).val + 1
  · have heq : qq = indices a.castSucc := by
      apply Fin.ext
      simp [qq]
      omega
    have hsame : (indices a.succ).castSucc = (indices a.castSucc).succ := by
      apply Fin.ext
      simp
      omega
    rw [hsame]
  have hlt : (indices a.castSucc).val + 1 ≤ (indices a.succ).val - 1 := by
    have hinc := hincreasing a.castSucc a.succ (by simp)
    omega
  have hs := (henumerates (indices a.castSucc)).mpr ⟨a.castSucc, rfl⟩
  have hn := (henumerates (indices a.succ)).mpr ⟨a.succ, rfl⟩
  have hnpos : 0 < (indices a.succ).val := by
    have := (indices a.succ).isLt
    omega
  have hpq : pp.val ≤ qq.val := by
    simp [pp, qq]
    omega
  have hh := HkuUnsupportedVertexColors G k rounds e0 input series qq pp u hpq
    (by
      have ht := support_tree (indices a.castSucc).succ hs.2.1 hs.2.2
      have hseg := next_segment (indices a.castSucc).succ
        (indices a.castSucc) rfl
      have heq : pp.succ.castSucc = (indices a.castSucc).succ.succ := by
        apply Fin.ext
        simp [pp]
      rw [heq]
      exact transfer_tree _ _ hseg u ht)
    (by
      intro j hj1 hj2 hj
      have hjq : j.val ≤ q.val := by
        have hnextq := hn.1
        simp [qq] at hj2
        omega
      obtain ⟨b, hb⟩ := (henumerates j).mp ⟨hjq, hj.1, hj.2⟩
      have hbv := congrArg Fin.val hb
      rw [← hbv] at hj1 hj2
      change (indices a.castSucc).val + 1 ≤ (indices b).val at hj1
      change (indices b).val ≤ (indices a.succ).val - 1 at hj2
      have hleft : (indices a.castSucc).val + 1 ≤ (indices b).val := hj1
      have hright : (indices b).val + 1 ≤ (indices a.succ).val := by
        omega
      have hcast : a.castSucc.val = a.val := rfl
      have hsucc : a.succ.val = a.val + 1 := rfl
      by_cases hba : b.val ≤ a.val
      · by_cases hltb : b.val < a.val
        · have hh := hincreasing b a.castSucc hltb
          have hprev : (indices a.castSucc).val < (indices b).val := by omega
          omega
        · have hbeqval : b.val = a.val := by omega
          have hbeq : b = a.castSucc := Fin.ext (by exact hbeqval)
          rw [hbeq] at hleft
          omega
      · have hbigval : a.val + 1 ≤ b.val := by omega
        have hstrict : a.val + 1 < b.val := by
          by_contra hnot
          have heq : b.val = a.val + 1 := by omega
          have hbnext : b = a.succ := Fin.ext heq
          rw [hbnext] at hright
          omega
        have hbig : a.succ.val ≤ b.val := by
          rw [hsucc]
          exact hstrict.le
        have hstrictFin : a.succ.val < b.val := by
          rw [hsucc]
          exact hstrict
        have hh := hincreasing a.succ b hstrictFin
        have hnext : (indices b).val < (indices a.succ).val := by omega
        omega)
  have hpp : pp.castSucc = (indices a.castSucc).succ := by
    apply Fin.ext
    simp [pp]
  have hqq : qq.succ = (indices a.succ).castSucc := by
    apply Fin.ext
    simp [qq]
    omega
  rw [hpp, hqq] at hh
  exact hh

private theorem helper_residual_transport_478.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds p : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds),
    ∀ u ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc),
    ∀ (indices : Fin (p + (1 : ℕ)) → Fin rounds), (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices a) : ℕ) < (↑(indices b) : ℕ)) →
        (
    ∀ (j : Fin rounds), (↑j : ℕ) ≤ (↑q : ℕ) ∧ series.data.kind j.succ = some
        TashkinovExtensionKind.PE ∧ series.data.chosenVertex j.succ = some u ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = j) →
    ∀ (deltaLast : Fin k), series.data.delta (indices (Fin.last p)).succ = some deltaLast → (
    ∀ (a : Fin (p + (1 : ℕ))),
    ∃ (gamma : Fin k), series.data.gamma (indices a).succ = some gamma ∧
    ∃ (delta : Fin k), series.data.delta (indices a).succ = some delta ∧ MissingColors G
        (series.data.coloring (indices a).castSucc) u \ { gamma } = MissingColors G
        (series.data.coloring (indices a).succ) u \ { delta } ∧ gamma ∉ MissingColors G
        (series.data.coloring (indices a).succ) u ∧ delta ∈ MissingColors G (series.data.coloring
        (indices a).succ) u ∧ series.data.stored (indices a).succ = { delta, gamma }) → (
    ∀ (a : Fin p), MissingColors G (series.data.coloring (indices a.castSucc).succ) u =
        MissingColors G (series.data.coloring (indices a.succ).castSucc) u) →
    ∀ (gammaLast : Fin k), series.data.gamma (indices (Fin.last p)).succ = some gammaLast →
    ∀ (a b : Fin (p + (1 : ℕ))) (ga da : Fin k), (↑a : ℕ) ≤ (↑b : ℕ) → (↑a : ℕ) < (↑b : ℕ) →
        series.data.gamma (indices a).succ = some ga → series.data.delta (indices a).succ = some
        da → MissingColors G (series.data.coloring (indices a).castSucc) u \ { ga } =
        MissingColors G (series.data.coloring (indices a).succ) u \ { da } → MissingColors G
        (series.data.coloring (indices b).castSucc) u \ { gammaLast } = MissingColors G
        (series.data.coloring (indices b).succ) u \ { deltaLast } → b = Fin.last p → MissingColors
        G (series.data.coloring (indices a).castSucc) u \ { ga } = MissingColors G
        (series.data.coloring (indices b).castSucc) u \ { gammaLast } := by
  classical
  intro V E _ _ _ G k rounds p e0 input series q u hu indices hincreasing henumerates deltaLast
      hdeltaLast hlocal hgap gammaLast hgammaLast a b
  induction hdist : b.val - a.val using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    intro ga da hab hstrict hga hda hleft hright hbLast
    by_cases heq : a.val = b.val
    · have hfalse : a.val < a.val := by omega
      exact (Nat.lt_irrefl _ hfalse).elim
    · have halt : a.val + 1 ≤ b.val := by omega
      let mid : Fin (p + 1) := ⟨a.val + 1, by omega⟩
      obtain ⟨gm, hgm, dm, hdm, hmid, _, _, _⟩ := hlocal mid
      have hstep : MissingColors G (series.data.coloring (indices a).castSucc) u \ {ga} =
          MissingColors G (series.data.coloring (indices mid).castSucc) u \ {gm} := by
        have hgap' := hgap ⟨a.val, by omega⟩
        have haeq : (⟨a.val, by omega⟩ : Fin p).castSucc = a := by rfl
        have hmeq : mid.castSucc = ⟨a.val + 1, by omega⟩ := by rfl
        have hgap'' : MissingColors G (series.data.coloring (indices a).succ) u =
            MissingColors G (series.data.coloring (indices mid).castSucc) u := by
          simpa [haeq, hmeq] using hgap'
        have hbridge := congrArg (fun s : Finset (Fin k) => s \ {gm}) hgap''
        have hchain := SupportingPEColorChain G k rounds p e0 input series q u
          hu indices hincreasing henumerates ⟨a.val, by omega⟩
        have hidx1 : (⟨a.val, by omega⟩ : Fin p).succ = mid := by
          apply Fin.ext
          rfl
        have hidx0 : (⟨a.val, by omega⟩ : Fin p).castSucc = a := by
          apply Fin.ext
          rfl
        rw [hidx1, hidx0] at hchain
        have heqdm : gm = da := by
          rw [hgm, hda] at hchain
          exact Option.some.inj hchain
        rw [← heqdm] at hleft
        exact hleft.trans hbridge
      have hmidval : mid.val = a.val + 1 := by rfl
      have hdistlt : b.val - mid.val < b.val - a.val := by
        dsimp [mid]
        omega
      have hmidle : mid.val ≤ b.val := by
        dsimp [mid]
        omega
      have hdistn : b.val - mid.val < n := by omega
      have habmid : mid.val ≤ b.val := hmidle
      have hrest : MissingColors G (series.data.coloring (indices mid).castSucc) u \ {gm} =
          MissingColors G (series.data.coloring (indices b).castSucc) u \ {gammaLast} := by
        by_cases hmb : mid.val = b.val
        · have hbe : mid = b := Fin.ext hmb
          have hml : mid = Fin.last p := hbe.trans hbLast
          have heqgm : gm = gammaLast := by
            rw [← hml] at hgammaLast
            exact Option.some.inj (hgm.symm.trans hgammaLast)
          have hdm' : dm = deltaLast := by
            rw [← hml] at hdeltaLast
            exact Option.some.inj (hdm.symm.trans hdeltaLast)
          rw [heqgm, hdm'] at hmid
          rw [← hbe] at hright
          rw [heqgm, ← hbe]
        · have hstrictmid' : mid.val < b.val := by omega
          have hrest' := ih (b.val - mid.val) hdistn mid b (by rfl)
            gm dm habmid hstrictmid' hgm hdm hmid hright hbLast
          exact hrest'
      exact hstep.trans hrest

private theorem helper_hfinal_571.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds p : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (u : V) (indices : Fin (p
        + (1 : ℕ)) → Fin rounds), (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices a) : ℕ) < (↑(indices b) : ℕ)) →
        (
    ∀ (j : Fin rounds), (↑j : ℕ) ≤ (↑q : ℕ) ∧ series.data.kind j.succ = some
        TashkinovExtensionKind.PE ∧ series.data.chosenVertex j.succ = some u ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = j) → (
    ∀ (j : Fin (rounds + (1 : ℕ))), series.data.kind j = some TashkinovExtensionKind.PE →
        series.data.chosenVertex j = some u → u ∈ TreeSequenceVertexSet (series.data.tree
        j.castSucc)) → (
    ∀ (T T' : TreeSequence G e0), TreeSequenceInitialSegment T T' →
    ∀ x ∈ TreeSequenceVertexSet T, x ∈ TreeSequenceVertexSet T') → (
    ∀ (j : Fin (rounds + (1 : ℕ))) (i : Fin rounds), j = i.succ → TreeSequenceInitialSegment
        (series.data.tree i.succ.castSucc) (series.data.tree i.succ.succ)) → MissingColors G
        (series.data.coloring q.succ) u = MissingColors G (series.data.coloring (indices (Fin.last
        p)).succ) u := by
  classical
  intro V E _ _ _ G k rounds p e0 input series q u indices hincreasing henumerates support_tree
      transfer_tree next_segment
  by_cases heq : (indices (Fin.last p)).val = q.val
  · have he : indices (Fin.last p) = q := Fin.ext heq
    rw [he]
  · have hlastq := (henumerates (indices (Fin.last p))).mpr
      ⟨Fin.last p, rfl⟩ |>.1
    have hlastlt : (indices (Fin.last p)).val < q.val := by
      omega
    have hpf_lt : (indices (Fin.last p)).val + 1 < rounds := by
      omega
    let pf : Fin rounds := ⟨(indices (Fin.last p)).val + 1, hpf_lt⟩
    have hpfq : pf.val ≤ q.val := by
      dsimp [pf]
      omega
    have hseg := next_segment (indices (Fin.last p)).succ
      (indices (Fin.last p)) rfl
    have htree : u ∈ TreeSequenceVertexSet
        (series.data.tree (pf.succ.castSucc)) := by
      have hlastData := (henumerates (indices (Fin.last p))).mpr
        ⟨Fin.last p, rfl⟩
      have ht := support_tree (indices (Fin.last p)).succ
        hlastData.2.1 hlastData.2.2
      have he : pf.succ.castSucc =
          (indices (Fin.last p)).succ.succ := by
        apply Fin.ext
        simp [pf]
      rw [he]
      exact transfer_tree _ _ hseg u ht
    have hno : ∀ j : Fin rounds, pf.val ≤ j.val → j.val ≤ q.val →
        ¬ (series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
          series.data.chosenVertex j.succ = some u) := by
      intro j hjp hjq hj
      obtain ⟨b, hb⟩ := (henumerates j).mp ⟨hjq, hj.1, hj.2⟩
      have hbv := congrArg Fin.val hb
      have hlastval : (Fin.last p).val = p := rfl
      have hba : b.val ≤ p := by
        by_contra hn
        have hbl : p + 1 ≤ b.val := by omega
        have hi := hincreasing (Fin.last p) b (by omega)
        omega
      have hidx : (indices b).val ≤ (indices (Fin.last p)).val := by
        by_cases he : b.val = p
        · have be : b = Fin.last p := Fin.ext (by omega)
          rw [be]
        · have hbl : b.val < p := by omega
          have hi := hincreasing b (Fin.last p) hbl
          omega
      have hlow : pf.val ≤ (indices b).val := by
        exact hjp.trans hbv.symm.le
      dsimp [pf] at hlow
      omega
    have hh := HkuUnsupportedVertexColors G k rounds e0 input series q pf u
      hpfq htree hno
    have he : pf.castSucc = (indices (Fin.last p)).succ := by
      apply Fin.ext
      simp [pf]
    rw [he] at hh
    exact hh.symm

private theorem helper_hsubset_630.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds p : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (u : V) (indices : Fin (p + (1 : ℕ)) → Fin
        rounds) (deltaLast : Fin k), series.data.delta (indices (Fin.last p)).succ = some
        deltaLast → (
    ∀ (a : Fin (p + (1 : ℕ))),
    ∃ (gamma : Fin k), series.data.gamma (indices a).succ = some gamma ∧
    ∃ (delta : Fin k), series.data.delta (indices a).succ = some delta ∧ MissingColors G
        (series.data.coloring (indices a).castSucc) u \ { gamma } = MissingColors G
        (series.data.coloring (indices a).succ) u \ { delta } ∧ gamma ∉ MissingColors G
        (series.data.coloring (indices a).succ) u ∧ delta ∈ MissingColors G (series.data.coloring
        (indices a).succ) u ∧ series.data.stored (indices a).succ = { delta, gamma }) →
    ∀ (gammaLast : Fin k), series.data.gamma (indices (Fin.last p)).succ = some gammaLast →
        gammaLast ∉ MissingColors G (series.data.coloring (indices (Fin.last p)).succ) u →
        MissingColors G (series.data.coloring (indices (Fin.last p)).castSucc) u \ { gammaLast } =
        MissingColors G (series.data.coloring (indices (Fin.last p)).succ) u \ { deltaLast } → (
    ∀ (a b : Fin (p + (1 : ℕ))) (ga da : Fin k), (↑a : ℕ) ≤ (↑b : ℕ) → (↑a : ℕ) < (↑b : ℕ) →
        series.data.gamma (indices a).succ = some ga → series.data.delta (indices a).succ = some
        da → MissingColors G (series.data.coloring (indices a).castSucc) u \ { ga } =
        MissingColors G (series.data.coloring (indices a).succ) u \ { da } → MissingColors G
        (series.data.coloring (indices b).castSucc) u \ { gammaLast } = MissingColors G
        (series.data.coloring (indices b).succ) u \ { deltaLast } → b = Fin.last p → MissingColors
        G (series.data.coloring (indices a).castSucc) u \ { ga } = MissingColors G
        (series.data.coloring (indices b).castSucc) u \ { gammaLast }) →
    ∀ (a : Fin (p + (1 : ℕ))),
    ∀ c ∈ series.data.stored (indices a).succ, c ∈ MissingColors G (series.data.coloring (indices
        (Fin.last p)).succ) u → c = deltaLast := by
  classical
  intro V E _ _ _ G k rounds p e0 input series u indices deltaLast hdeltaLast hlocal gammaLast
      hgammaLast hgnLast hresLast residual_transport a c hc hm
  obtain ⟨ga, hga, da, hda, hres, hgn, hdin, hstored⟩ := hlocal a
  have ha_lt := a.isLt
  have hp_last : (Fin.last p).val = p := rfl
  rw [hstored] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  have hcommon : MissingColors G
        (series.data.coloring (indices a).castSucc) u \ {ga} =
        MissingColors G
          (series.data.coloring (indices (Fin.last p)).castSucc) u \ {gammaLast} := by
    by_cases ha : a.val = p
    · have ha_lt := a.isLt
      have hae : a = Fin.last p := Fin.ext (by omega)
      subst a
      have ega : ga = gammaLast := Option.some.inj (hga.symm.trans hgammaLast)
      have eda : da = deltaLast := Option.some.inj (hda.symm.trans hdeltaLast)
      subst ga
      subst da
      exact hres.trans hresLast.symm
    · apply residual_transport a (Fin.last p) ga da
        (by omega) (by omega) hga hda hres hresLast rfl
  rcases hc with hdc | hgc
  · subst c
    by_cases heq : da = deltaLast
    · exact heq
    · by_cases hga' : da = gammaLast
      · have hn : da ∉ MissingColors G
            (series.data.coloring (indices (Fin.last p)).succ) u := by
          simpa [hga'] using hgnLast
        exact (hn hm).elim
      · have hlastmem : da ∈ MissingColors G
            (series.data.coloring (indices (Fin.last p)).castSucc) u \ {gammaLast} := by
          rw [hresLast]
          exact Finset.mem_sdiff.mpr ⟨hm, by simpa using heq⟩
        have hamem : da ∈ MissingColors G
            (series.data.coloring (indices a).castSucc) u \ {ga} := by
          rw [hcommon]
          exact hlastmem
        have hbmem : da ∈ MissingColors G
            (series.data.coloring (indices a).succ) u \ {da} := by
          rw [hres] at hamem
          exact hamem
        exact False.elim ((Finset.mem_sdiff.mp hbmem).2
          (Finset.mem_singleton.mpr rfl))
  · subst c
    by_cases heq : ga = deltaLast
    · exact heq
    · by_cases hga' : ga = gammaLast
      · have hn : ga ∉ MissingColors G
            (series.data.coloring (indices (Fin.last p)).succ) u := by
          simpa [hga'] using hgnLast
        exact (hn hm).elim
      · have hlastmem : ga ∈ MissingColors G
            (series.data.coloring (indices (Fin.last p)).castSucc) u \ {gammaLast} := by
          rw [hresLast]
          exact Finset.mem_sdiff.mpr ⟨hm, by simpa using heq⟩
        have hamem : ga ∈ MissingColors G
            (series.data.coloring (indices a).castSucc) u \ {ga} := by
          rw [hcommon]
          exact hlastmem
        exact False.elim ((Finset.mem_sdiff.mp hamem).2
          (Finset.mem_singleton.mpr rfl))

theorem SupportingPEStoredIntersection {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds p : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (u : V)
    (hu : u ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc))
    (indices : Fin (p + 1) → Fin rounds)
    (hincreasing : ∀ a b, a.val < b.val →
      (indices a).val < (indices b).val)
    (henumerates : ∀ j : Fin rounds,
      (j.val ≤ q.val ∧
        series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
        series.data.chosenVertex j.succ = some u) ↔
      ∃ a : Fin (p + 1), indices a = j)
    (deltaLast : Fin k)
    (hdeltaLast : series.data.delta (indices (Fin.last p)).succ = some deltaLast) :
    let storedPairs := Finset.univ.biUnion fun a : Fin (p + 1) =>
      series.data.stored (indices a).succ
    MissingColors G (series.data.coloring q.succ) u ∩ storedPairs = {deltaLast} ∧
      MissingColors G
          (series.data.coloring (indices (Fin.last p)).succ) u ∩ storedPairs =
        {deltaLast} := by
  classical
  dsimp
  have pe_step := @helper_pe_step_55 V E inferInstance inferInstance inferInstance G k rounds e0
      input series
  have support_tree := @helper_support_tree_236 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series u
  have hlocal := @helper_hlocal_273 V E inferInstance inferInstance inferInstance G k rounds p e0
      input series q u indices henumerates pe_step support_tree
  have transfer_tree : ∀ (T T' : TreeSequence G e0),
      TreeSequenceInitialSegment T T' → ∀ x, x ∈ TreeSequenceVertexSet T →
        x ∈ TreeSequenceVertexSet T' := by
    intro T T' h x hx
    unfold TreeSequenceVertexSet at hx ⊢
    simp only [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    rcases h with ⟨hlen, hvertex, hedge⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, by simpa using hvertex i⟩
  have next_segment := @helper_next_segment_336 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series
  have hgap := @helper_hgap_377 V E inferInstance inferInstance inferInstance G k rounds p e0 input
      series q u indices hincreasing henumerates support_tree transfer_tree next_segment
  have hlast : ∃ gamma : Fin k,
      series.data.gamma (indices (Fin.last p)).succ = some gamma := by
    obtain ⟨gamma, hg, delta, hd, hstep, hstored⟩ := hlocal (Fin.last p)
    exact ⟨gamma, hg⟩
  obtain ⟨gammaLast, hgammaLast, deltaLast', hdeltaLast', hresLast, hgnLast, hdLast,
      hstoredLast⟩ :=
    hlocal (Fin.last p)
  have hdeltaEq : deltaLast' = deltaLast := by
    exact Option.some.inj (hdeltaLast'.symm.trans hdeltaLast)
  subst deltaLast'
  have residual_transport := @helper_residual_transport_478 V E inferInstance inferInstance
      inferInstance G k rounds p e0 input series q u hu indices hincreasing henumerates deltaLast
      hdeltaLast hlocal hgap gammaLast hgammaLast
  have residual_last :
    ∀ a : Fin (p + 1),
    ∀ ga da : Fin k, series.data.gamma (indices a).succ = some ga → series.data.delta (indices
        a).succ = some da → MissingColors G (series.data.coloring (indices a).castSucc) u \ {ga} =
        MissingColors G (series.data.coloring (indices a).succ) u \ {da} → ga = gammaLast → da =
        deltaLast → MissingColors G (series.data.coloring (indices a).castSucc) u \ {ga} =
        MissingColors G (series.data.coloring (indices (Fin.last p)).castSucc) u \ {gammaLast}
             := by
    intro a ga da hga hda hdata ega eda
    subst ga
    subst da
    have ha_lt := a.isLt
    have hp_last : (Fin.last p).val = p := rfl
    by_cases ha : a.val = p
    · have hae : a = Fin.last p := Fin.ext (by omega)
      subst a
      exact hdata.trans hresLast.symm
    · apply residual_transport a (Fin.last p) gammaLast deltaLast
        (by omega) (by omega) hga hda hdata hresLast rfl
  have hfinal := @helper_hfinal_571 V E inferInstance inferInstance inferInstance G k rounds p e0
      input series q u indices hincreasing henumerates support_tree transfer_tree next_segment
  have hsubset := @helper_hsubset_630 V E inferInstance inferInstance inferInstance G k rounds p e0
      input series u indices deltaLast hdeltaLast hlocal gammaLast hgammaLast hgnLast hresLast
      residual_transport
  constructor
  · ext c
    constructor
    · intro hc
      rcases Finset.mem_inter.mp hc with ⟨hm, hc⟩
      have hm' : c ∈ MissingColors G
          (series.data.coloring (indices (Fin.last p)).succ) u := by
        rw [← hfinal]
        exact hm
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hc
      obtain ⟨a, ha⟩ := hc
      have heq := hsubset a c ha hm'
      simp [heq]
    · intro hc
      have heq : c = deltaLast := by simpa using hc
      subst c
      apply Finset.mem_inter.mpr
      refine ⟨?_, ?_⟩
      · rw [hfinal]
        exact hdLast
      apply Finset.mem_biUnion.mpr
      refine ⟨Fin.last p, by simp, ?_⟩
      rw [hstoredLast]
      simp
  · ext c
    constructor
    · intro hc
      rcases Finset.mem_inter.mp hc with ⟨hm, hc⟩
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hc
      obtain ⟨a, ha⟩ := hc
      have heq := hsubset a c ha hm
      simp [heq]
    · intro hc
      have heq : c = deltaLast := by simpa using hc
      subst c
      apply Finset.mem_inter.mpr
      refine ⟨hdLast, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨Fin.last p, by simp, ?_⟩
      rw [hstoredLast]
      simp

end GoldbergSeymour

end
