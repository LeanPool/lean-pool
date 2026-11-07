/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesTreeFacts

public import LeanPool.GoldbergSeymour.HkuUnsupportedVertexColors
public import LeanPool.GoldbergSeymour.SupportingPEColorChain
public import LeanPool.GoldbergSeymour.TashkinovSeries

/-!
# Supporting PEMissing Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_swap_step_57.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (v : V), IsProperEdgeColoring G phi →
        alpha ∈ MissingColors G phi v → beta ∉ MissingColors G phi v → MissingColors G
        (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v = MissingColors G phi v \ { alpha }
        ∪ { beta } ∧ MissingColors G phi v = MissingColors G (TwoColorComponentSwap G phi alpha
        beta (Sum.inl v)) v \ { beta } ∪ { alpha } := by
  classical
  intro V E _ _ G k phi alpha beta v hproper hamiss hbmiss
  let _ := Fintype.ofFinite V
  have hpres : beta ∈ PresentColors G phi v := by
    simpa [MissingColors] using hbmiss
  have hneq : alpha ≠ beta := by
    intro heq
    have hnot : alpha ∉ MissingColors G phi v := by
      simpa [heq] using hbmiss
    exact hnot hamiss
  have edge_mem : ∀ e, Incident G v e →
      (phi e = some alpha ∨ phi e = some beta) →
      Sum.inr e ∈ TwoColorComponent G phi alpha beta (Sum.inl v) := by
    intro e hev hec
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, hev, hec]
  have present_step : ∀ c, c ∈ PresentColors G
      (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v ↔
      c = alpha ∨ (c ≠ beta ∧ c ∈ PresentColors G phi v) := by
    intro c
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, hev, hec⟩
      by_cases hcomp : Sum.inr e ∈ TwoColorComponent G phi alpha beta (Sum.inl v)
      · by_cases hae : phi e = some alpha
        · exfalso
          have hnot : alpha ∉ MissingColors G phi v := by
            simpa [MissingColors, PresentColors] using (show alpha ∈ PresentColors G phi v from
              by simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                 exact ⟨e, hev, hae⟩)
          exact hnot hamiss
        · by_cases hbe : phi e = some beta
          · have value := hec
            simp [TwoColorComponentSwap, hcomp, hbe, hneq.symm] at value
            exact Or.inl value.symm
          · right
            have value := hec
            simp only [TwoColorComponentSwap, hcomp, ↓reduceIte, hae, hbe] at value
            refine ⟨?_, ⟨e, hev, value⟩⟩
            intro heq
            exact hbe (by simpa [heq] using value)
      · right
        have value := hec
        simp only [TwoColorComponentSwap, hcomp, ↓reduceIte] at value
        by_cases hbe : phi e = some beta
        · exact (hcomp (edge_mem e hev (Or.inr hbe))).elim
        · refine ⟨?_, ⟨e, hev, value⟩⟩
          intro heq
          apply hbe
          simpa [heq] using value
    · rintro (rfl | ⟨hcβ, ⟨e, hev, hec⟩⟩)
      · obtain ⟨e, hev, heβ⟩ := by
          simpa [PresentColors] using hpres
        refine ⟨e, hev, ?_⟩
        simp [TwoColorComponentSwap, edge_mem e hev (Or.inr heβ), heβ]
      · refine ⟨e, hev, ?_⟩
        by_cases hae : phi e = some alpha
        · have hnot : alpha ∉ MissingColors G phi v := by
            simpa [MissingColors, PresentColors] using (show alpha ∈ PresentColors G phi v from
              by simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                 exact ⟨e, hev, hae⟩)
          exact False.elim (hnot hamiss)
        · by_cases hbe : phi e = some beta
          · exact False.elim (hcβ (Option.some.inj (hec.symm.trans hbe)))
          · simp only [TwoColorComponentSwap, hae, ↓reduceIte, hbe, ite_self]
            exact hec
  have forward_step : MissingColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v =
      (MissingColors G phi v \ {alpha}) ∪ {beta} := by
    ext c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_univ, true_and]
    rw [present_step]
    by_cases hca : c = alpha <;> by_cases hcb : c = beta <;> simp [hca, hcb, hneq, hneq.symm]
  have reverse_step : MissingColors G phi v =
      (MissingColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v \ {beta}) ∪ {alpha}
         := by
    rw [forward_step]
    ext c
    by_cases hca : c = alpha <;> by_cases hcb : c = beta <;>
      simp [hca, hcb, hamiss, hbmiss, hneq, hneq.symm]
  exact ⟨forward_step, reverse_step⟩

private theorem helper_pe_step_143.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (u : V), (
    ∀ (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (v : V), IsProperEdgeColoring G phi →
        alpha ∈ MissingColors G phi v → beta ∉ MissingColors G phi v → MissingColors G
        (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v = MissingColors G phi v \ { alpha }
        ∪ { beta } ∧ MissingColors G phi v = MissingColors G (TwoColorComponentSwap G phi alpha
        beta (Sum.inl v)) v \ { beta } ∪ { alpha }) →
    ∀ (i : Fin rounds) (d g : Fin k), series.data.kind i.succ = some TashkinovExtensionKind.PE →
        series.data.chosenVertex i.succ = some u → series.data.delta i.succ = some d →
        series.data.gamma i.succ = some g → MissingColors G (series.data.coloring i.castSucc) u =
        MissingColors G (series.data.coloring i.succ) u \ { d } ∪ { g } ∧ MissingColors G
        (series.data.coloring i.succ) u = MissingColors G (series.data.coloring i.castSucc) u \
        { g } ∪ { d } := by
  classical
  intro V E _ _ _ G k rounds e0 input series u swap_step i d g hi hv hd hg
  generalize target_eq : i.succ = target
  have certificate := series.certified target
  cases certificate with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma =>
    exact (Fin.succ_ne_zero i target_eq).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hci : ci = i := by
      apply Fin.ext
      have value := congrArg Fin.val target_eq
      simp at value
      omega
    subst ci
    rw [currentKind] at hi
    simp at hi
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hci : ci = i := by
      apply Fin.ext
      have value := congrArg Fin.val target_eq
      simp at value
      omega
    subst ci
    rw [currentKind] at hi
    simp at hi
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hci : ci = i := by
      apply Fin.ext
      have := congrArg Fin.val target_eq
      simp at this
      omega
    subst ci
    have vertex_eq : choice.vertex = u := by
      apply Option.some.inj
      exact currentVertex.symm.trans hv
    have hs := secondStableRelation.2 choice.vertex choice.vertexDefective.1
    have hsel := choice.selectedStable.2 choice.vertex choice.vertexDefective.1
    have hgamma : gamma ∈ MissingColors G secondStable choice.vertex := by
      rw [hs]
      exact gammaRule.1
    have hdelta_present : choice.color ∉ MissingColors G secondStable choice.vertex := by
      have hedge : TreeIncidentEdge (series.data.tree i.succ.castSucc) choice.edge :=
        ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
      have hstable := secondStableRelation.1 choice.edge hedge
        ⟨choice.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _), choice.edgeColor⟩
      have hcol : secondStable choice.edge = some choice.color :=
        hstable.trans choice.edgeColor
      intro hm
      have hp : choice.color ∈ PresentColors G secondStable choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨choice.edge, choice.edgeIncident, hcol⟩
      have hnot : choice.color ∉ MissingColors G secondStable choice.vertex := by
        simpa [MissingColors] using hp
      exact hnot hm
    have hswap := swap_step secondStable gamma choice.color choice.vertex
      secondStableProper hgamma hdelta_present
    have hs_u : MissingColors G secondStable u =
        MissingColors G choice.selected u := by simpa [vertex_eq] using hs
    have hsel_u : MissingColors G choice.selected u =
        MissingColors G (series.data.coloring i.castSucc) u := by simpa [vertex_eq] using hsel
    have hswap_one : MissingColors G
        (TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex)) u =
        (MissingColors G secondStable u \ {gamma}) ∪ {choice.color} := by
      simpa [vertex_eq] using hswap.1
    have hswap_two : MissingColors G secondStable u =
        (MissingColors G
          (TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex)) u \
              {choice.color}) ∪ {gamma} := by
      simpa [vertex_eq] using hswap.2
    have hmain : MissingColors G (series.data.coloring i.castSucc) u =
        (MissingColors G (series.data.coloring i.succ) u \ {choice.color}) ∪ {gamma} := by
      calc
        MissingColors G (series.data.coloring i.castSucc) u =
            MissingColors G choice.selected u := hsel_u.symm
        _ = MissingColors G secondStable u := hs_u.symm
        _ = (MissingColors G
            (TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex)) u \
                {choice.color}) ∪ {gamma} := hswap_two
        _ = (MissingColors G (series.data.coloring i.succ) u \ {choice.color}) ∪ {gamma} := by rw
            [← currentColoring]
    have hrev : MissingColors G (series.data.coloring i.succ) u =
        (MissingColors G (series.data.coloring i.castSucc) u \ {gamma}) ∪ {choice.color} := by
      calc
        MissingColors G (series.data.coloring i.succ) u =
            MissingColors G
              (TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex)) u
                 := by rw [currentColoring]
        _ = (MissingColors G secondStable u \ {gamma}) ∪ {choice.color} := hswap_one
        _ = (MissingColors G choice.selected u \ {gamma}) ∪ {choice.color} := by rw [hs_u]
        _ = (MissingColors G (series.data.coloring i.castSucc) u \ {gamma}) ∪ {choice.color} :=
            by rw [hsel_u]
    have delta_eq : d = choice.color := Option.some.inj (hd.symm.trans currentDelta)
    have gamma_eq : g = gamma := Option.some.inj (hg.symm.trans currentGamma)
    exact ⟨by simpa [delta_eq, gamma_eq] using hmain,
      by simpa [delta_eq, gamma_eq] using hrev⟩

private theorem helper_support_tree_256.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (u : V) (i : Fin rounds), series.data.kind i.succ =
        some TashkinovExtensionKind.PE → series.data.chosenVertex i.succ = some u → u ∈
        TreeSequenceVertexSet (series.data.tree i.succ.castSucc) := by
  classical
  intro V E _ _ _ G k rounds e0 input series u i hi hv
  generalize target_eq : i.succ = target
  have certificate := series.certified target
  cases certificate with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    exact (Fin.succ_ne_zero i target_eq).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hci : ci = i := by
      apply Fin.ext
      have value := congrArg Fin.val target_eq
      simp at value
      omega
    subst ci
    rw [currentKind] at hi
    simp at hi
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hci : ci = i := by
      apply Fin.ext
      have value := congrArg Fin.val target_eq
      simp at value
      omega
    subst ci
    rw [currentKind] at hi
    simp at hi
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma
      closedExtension orderedExtension strictExtension =>
    have hci : ci = i := by
      apply Fin.ext
      have value := congrArg Fin.val target_eq
      simp at value
      omega
    subst ci
    have veq : choice.vertex = u := Option.some.inj (currentVertex.symm.trans hv)
    simpa [veq] using choice.vertexDefective.1

private theorem helper_bridge_357.{u_1, u_2} :
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
    ∀ (i : Fin rounds), series.data.kind i.succ = some TashkinovExtensionKind.PE →
        series.data.chosenVertex i.succ = some u → u ∈ TreeSequenceVertexSet (series.data.tree
        i.succ.castSucc)) → (
    ∀ (T T' : TreeSequence G e0), TreeSequenceInitialSegment T T' →
    ∀ x ∈ TreeSequenceVertexSet T, x ∈ TreeSequenceVertexSet T') → (
    ∀ (j : Fin (rounds + (1 : ℕ))) (i : Fin rounds), j = i.succ → TreeSequenceInitialSegment
        (series.data.tree i.succ.castSucc) (series.data.tree i.succ.succ)) →
    ∀ (a : Fin p), MissingColors G (series.data.coloring (indices a.castSucc).succ) u =
        MissingColors G (series.data.coloring (indices a.succ).castSucc) u := by
  classical
  intro V E _ _ _ G k rounds p e0 input series q u indices hincreasing henumerates support_tree
      vertex_transfer next_segment a
  have inc := hincreasing a.castSucc a.succ (by simp)
  let left : Fin rounds := ⟨(indices a.castSucc).val + 1, by omega⟩
  let right : Fin rounds := ⟨(indices a.succ).val - 1, by omega⟩
  have hleft := (henumerates (indices a.castSucc)).2 ⟨a.castSucc, rfl⟩
  have htree := support_tree (indices a.castSucc) hleft.2.1 hleft.2.2
  have hright := (henumerates (indices a.succ)).2 ⟨a.succ, rfl⟩
  have hno : ∀ j : Fin rounds, left.val ≤ j.val → j.val ≤ right.val →
      ¬ (series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
        series.data.chosenVertex j.succ = some u) := by
    intro j hj1 hj2 hpe
    have hr : right.val ≤ (indices a.succ).val := by simp [right]
    have jq : j.val ≤ q.val := by omega
    obtain ⟨b, hb⟩ := (henumerates j).1 ⟨jq, hpe⟩
    have hbval : (indices b).val = j.val := congrArg Fin.val hb
    have hj1' : (indices a.castSucc).val + 1 ≤ j.val := by
      simpa [left] using hj1
    have hj2' : j.val ≤ (indices a.succ).val - 1 := by
      simpa [right] using hj2
    have hba : a.val < b.val := by
      by_contra hn
      have ble : b.val ≤ a.val := Nat.le_of_not_gt hn
      have bne : b ≠ a.castSucc := by
        intro beq
        have := hbval
        subst b
        omega
      have bstr : b.val < a.castSucc.val := lt_of_le_of_ne ble (by
        intro heq
        apply bne
        apply Fin.ext
        exact heq)
      have hi := hincreasing b a.castSucc bstr
      omega
    have hbs : b.val < a.succ.val := by
      by_contra hn
      have ble : a.succ.val ≤ b.val := Nat.le_of_not_gt hn
      have bne : b ≠ a.succ := by
        intro beq
        have := hbval
        subst b
        omega
      have bstr : a.succ.val < b.val := lt_of_le_of_ne ble (by
        intro heq
        apply bne
        apply Fin.ext
        exact heq.symm)
      have hi := hincreasing a.succ b bstr
      omega
    have aval : a.succ.val = a.val + 1 := rfl
    have acval : a.castSucc.val = a.val := rfl
    omega
  have htree' : u ∈ TreeSequenceVertexSet (series.data.tree left.succ.castSucc) := by
    have transferred := vertex_transfer _ _
      (next_segment (indices a.castSucc).succ (indices a.castSucc) rfl) u htree
    have indexeq : left.succ.castSucc = (indices a.castSucc).succ.succ := by
      apply Fin.ext
      change left.val + 1 = (indices a.castSucc).val + 2
      have leftval : left.val = (indices a.castSucc).val + 1 := rfl
      rw [leftval]
    rw [indexeq]
    exact transferred
  by_cases hcon : (indices a.succ).val = (indices a.castSucc).val + 1
  · have indexeq : (indices a.castSucc).succ = (indices a.succ).castSucc := by
      apply Fin.ext
      simp
      omega
    rw [indexeq]
  · have hgap : left.val ≤ right.val := by
      have incval := inc
      simp [left, right] at hcon ⊢
      omega
    have hrq : right.val ≤ q.val := by
      have hq := hright.1
      simp [right] at hq ⊢
      omega
    have right_eq : right.succ = (indices a.succ).castSucc := by
      apply Fin.ext
      simp [right]
      omega
    have bridgeValue := HkuUnsupportedVertexColors G k rounds e0 input series right
      left u hgap htree' hno
    rw [right_eq] at bridgeValue
    have left_eq : left.castSucc = (indices a.castSucc).succ := by
      apply Fin.ext
      simp [left]
    rw [left_eq] at bridgeValue
    exact bridgeValue

private theorem helper_pe_data_480.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input)
      (i : Fin rounds),
    series.data.kind i.succ = some TashkinovExtensionKind.PE →
    ∃ (d : Fin k) (g : Fin k),
    series.data.delta i.succ = some d ∧ series.data.gamma i.succ = some g := by
  classical
  intro V E _ _ _ G k rounds e0 input series i hi
  generalize target_eq : i.succ = target
  have cert := series.certified target
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure => exact (Fin.succ_ne_zero i target_eq).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have value := congrArg Fin.val target_eq
    simp at value
    have ci_eq : ci = i := by apply Fin.ext; omega
    subst ci
    rw [currentKind] at hi
    simp at hi
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have value := congrArg Fin.val target_eq
    simp at value
    have ci_eq : ci = i := by apply Fin.ext; omega
    subst ci
    rw [currentKind] at hi
    simp at hi
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have value := congrArg Fin.val target_eq
    simp at value
    have ci_eq : ci = i := by apply Fin.ext; omega
    subst ci
    rw [currentDelta, currentGamma]
    exact ⟨choice.color, gamma, rfl, rfl⟩

theorem SupportingPEMissingTransport {V E : Type*}
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
    (gammaFirst deltaLast : Fin k)
    (hgammaFirst : series.data.gamma (indices 0).succ = some gammaFirst)
    (hdeltaLast : series.data.delta (indices (Fin.last p)).succ = some deltaLast) :
    MissingColors G (series.data.coloring (indices 0).castSucc) u =
        (MissingColors G (series.data.coloring (indices (Fin.last p)).succ) u \
            { deltaLast }) ∪
          { gammaFirst } ∧
      MissingColors G (series.data.coloring (indices (Fin.last p)).succ) u =
        (MissingColors G (series.data.coloring (indices 0).castSucc) u \ { gammaFirst }) ∪
          { deltaLast } := by
  classical
  have swap_step := @helper_swap_step_57 V E inferInstance inferInstance G k
  have pe_step := @helper_pe_step_143 V E inferInstance inferInstance inferInstance G k rounds e0
      input series u swap_step
  have support_tree := @helper_support_tree_256 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series u
  have vertex_transfer : ∀ (T T' : TreeSequence G e0),
      TreeSequenceInitialSegment T T' → ∀ x, x ∈ TreeSequenceVertexSet T →
      x ∈ TreeSequenceVertexSet T' := by
    intro T T' hseg x hx
    unfold TreeSequenceVertexSet at hx ⊢
    simp only [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    rcases hseg with ⟨hlen, hvertex, hedge⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, by simpa using hvertex i⟩
  have next_segment := TashkinovSeries.stepInitialSegment G k rounds e0 input series
  have bridge := @helper_bridge_357 V E inferInstance inferInstance inferInstance G k rounds p e0
      input series q u indices hincreasing henumerates support_tree vertex_transfer next_segment
  have set_transport : ∀ (x y : Finset (Fin k)) (g d : Fin k),
      x = (y \ {d}) ∪ {g} → y = (x \ {g}) ∪ {d} →
      x \ {g} = y \ {d} := by
    intro x y g d hxy hyx
    by_cases hgd : g = d
    · subst d
      ext c
      by_cases hcg : c = g <;> rw [hxy] <;> simp [hcg]
    have gy : g ∉ y := by
      intro hgy
      have hgx : g ∈ x := by rw [hxy]; simp [hgy]
      rw [hyx] at hgy
      have cases : g = d ∨ (g ∈ x ∧ g ≠ g) := by simpa using hgy
      cases cases with
      | inl h => exact hgd h
      | inr h => exact h.2 rfl
    have dx : d ∉ x := by
      intro hdx
      rw [hxy] at hdx
      have hdg : d = g := by simpa using hdx
      exact hgd hdg.symm
    ext c
    by_cases hcg : c = g
    · subst c
      rw [hxy]
      simp [hgd, gy]
    · by_cases hcd : c = d
      · subst c
        rw [hxy]
        simp []
      · rw [hxy]
        simp [hcg, hcd]
  have pe_data := @helper_pe_data_480 V E inferInstance inferInstance inferInstance G k rounds e0
      input series
  have residual : ∀ (a : Fin (p + 1)) (d g : Fin k),
      series.data.delta (indices a).succ = some d →
      series.data.gamma (indices a).succ = some g →
      MissingColors G (series.data.coloring (indices a).castSucc) u \ {g} =
        MissingColors G (series.data.coloring (indices 0).castSucc) u \ {gammaFirst} := by
    intro a
    induction a using Fin.induction with
    | zero =>
      intro d g hd hg
      have gd : g = gammaFirst := Option.some.inj (hg.symm.trans hgammaFirst)
      subst g
      rfl
    | succ a ih =>
      intro d g hd hg
      obtain ⟨d0, g0, hd0, hg0⟩ := pe_data (indices a.castSucc)
        ((henumerates (indices a.castSucc)).2 ⟨a.castSucc, rfl⟩).2.1
      have ih0 := ih d0 g0 hd0 hg0
      have rel := set_transport _ _ g0 d0
        (pe_step _ d0 g0 ((henumerates (indices a.castSucc)).2 ⟨a.castSucc, rfl⟩).2.1
          ((henumerates (indices a.castSucc)).2 ⟨a.castSucc, rfl⟩).2.2 hd0 hg0).1
        (pe_step _ d0 g0 ((henumerates (indices a.castSucc)).2 ⟨a.castSucc, rfl⟩).2.1
          ((henumerates (indices a.castSucc)).2 ⟨a.castSucc, rfl⟩).2.2 hd0 hg0).2
      have chain := SupportingPEColorChain G k rounds p e0 input series q u hu
        indices hincreasing henumerates a
      have br := bridge a
      rw [chain] at hg
      have hgg : g = d0 := Option.some.inj (hg.symm.trans hd0)
      rw [hgg, ← br, ← rel, ih0]
  obtain ⟨dlast, glast, hdl, hgl⟩ := pe_data (indices (Fin.last p))
    ((henumerates (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).2.1
  have hres := residual (Fin.last p) dlast glast hdl hgl
  have hdl' : dlast = deltaLast := Option.some.inj (hdl.symm.trans hdeltaLast)
  subst dlast
  have lastRel := set_transport _ _ glast deltaLast
    (pe_step _ deltaLast glast
      ((henumerates (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).2.1
      ((henumerates (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).2.2 hdeltaLast hgl).1
    (pe_step _ deltaLast glast
      ((henumerates (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).2.1
      ((henumerates (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).2.2 hdeltaLast hgl).2
  have core : MissingColors G (series.data.coloring (indices 0).castSucc) u \ {gammaFirst} =
      MissingColors G (series.data.coloring (indices (Fin.last p)).succ) u \ {deltaLast} :=
    hres.symm.trans lastRel
  obtain ⟨d0, g0, hd0, hg0⟩ := pe_data (indices 0)
    ((henumerates (indices 0)).2 ⟨0, rfl⟩).2.1
  have hg0' : g0 = gammaFirst := Option.some.inj (hg0.symm.trans hgammaFirst)
  subst g0
  have firstStep := pe_step (indices 0) d0 gammaFirst
    ((henumerates (indices 0)).2 ⟨0, rfl⟩).2.1
    ((henumerates (indices 0)).2 ⟨0, rfl⟩).2.2 hd0 hgammaFirst
  have firstMem : gammaFirst ∈
      MissingColors G (series.data.coloring (indices 0).castSucc) u := by
    rw [firstStep.1]
    simp
  have lastStep := pe_step (indices (Fin.last p)) deltaLast glast
    ((henumerates (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).2.1
    ((henumerates (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩).2.2 hdeltaLast hgl
  have lastMem : deltaLast ∈
      MissingColors G (series.data.coloring (indices (Fin.last p)).succ) u := by
    rw [lastStep.2]
    simp
  have firstDecomp : MissingColors G (series.data.coloring (indices 0).castSucc) u =
      (MissingColors G (series.data.coloring (indices 0).castSucc) u \ {gammaFirst}) ∪
        {gammaFirst} := by
    ext c
    simp [firstMem]
  have lastDecomp : MissingColors G (series.data.coloring (indices (Fin.last p)).succ) u =
      (MissingColors G (series.data.coloring (indices (Fin.last p)).succ) u \ {deltaLast}) ∪
        {deltaLast} := by
    ext c
    simp [lastMem]
  constructor
  · calc
      MissingColors G (series.data.coloring (indices 0).castSucc) u =
          (MissingColors G (series.data.coloring (indices 0).castSucc) u \ {gammaFirst}) ∪
            {gammaFirst} := firstDecomp
      _ = (MissingColors G (series.data.coloring (indices (Fin.last p)).succ) u \ {deltaLast}) ∪
            {gammaFirst} := by rw [core]
  · calc
      MissingColors G (series.data.coloring (indices (Fin.last p)).succ) u =
          (MissingColors G (series.data.coloring (indices (Fin.last p)).succ) u \ {deltaLast}) ∪
            {deltaLast} := lastDecomp
      _ = (MissingColors G (series.data.coloring (indices 0).castSucc) u \ {gammaFirst}) ∪
            {deltaLast} := by rw [core]

end GoldbergSeymour

end
