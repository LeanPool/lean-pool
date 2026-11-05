/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.Degree
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.TashTreeBadPair
public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair
public import LeanPool.GoldbergSeymour.TashTreeProperPrefixElementary
public import LeanPool.GoldbergSeymour.TreeFreeColors
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeUsedColors

/-!
# Tash Tree Four Unused Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_continuation_174.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (q : ℕ) (hq : (1 : ℕ) ≤
        q) (hqt : q < T.length),
    let P : TreeSequence G e0 := TreeSequencePrefix T q hq (Nat.le_of_lt hqt); P.length = q →
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet P) → MaximumDegree G + (1 : ℕ) ≤ k
        →
    ∀ (hkpos : (0 : ℕ) < k), (
    ∀ (v : V), Degree G v ≤ MaximumDegree G) → Incident G (T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ
        T.length⟩ : Fin (T.length + (1 : ℕ)))) e0 → Incident G (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))) e0 →
    let fallback : Fin k := (⟨(0 : ℕ), hkpos⟩ : Fin k);
    let _ : E → Fin k := fun (e : E) ↦ (phi e).getD fallback;
    let incidentEdges : V → Finset E := fun (v : V) ↦ ({e : E | Incident G v e} : Finset E); (
    ∀ (v : V), (incidentEdges v).card = Degree G v) → (
    ∀ (v : V), (MissingColors G phi v).card = k - (PresentColors G phi v).card) → (
    ∀ (v : V), (1 : ℕ) ≤ (MissingColors G phi v).card) → (
    ∀ (v : V), Incident G v e0 → (PresentColors G phi v).card ≤ Degree G v - (1 : ℕ)) → (4 : ℕ) ≤
        (TreeFreeColors phi (TreeSequencePrefix T q hq (Nat.le_of_lt hqt))).card := by
  classical
  intro V E _ _ G k e0 phi T q hq hqt P hP_length hElementary hk hkpos hDegreeMax he0Incident0
      he0Incident1 fallback colorOf incidentEdges hIncidentCard hMissingCard hMissingOne
      hEndpointPresent
  have hMissingTwo (v : V) (he0v : Incident G v e0) :
      2 ≤ (MissingColors G phi v).card := by
    rw [hMissingCard]
    have hp := hEndpointPresent v he0v
    have hd := hDegreeMax v
    have hdpos : 1 ≤ Degree G v := by
      rw [← hIncidentCard]
      exact Finset.card_pos.mpr ⟨e0, by simpa [incidentEdges] using he0v⟩
    omega
  have hMissingTwo0 :
      2 ≤ (MissingColors G phi (P.vertex ⟨0, Nat.zero_lt_succ _⟩)).card := by
    apply hMissingTwo
    convert he0Incident0 using 1; apply congrArg T.vertex; apply Fin.ext; rfl
  have hMissingTwo1 :
      2 ≤ (MissingColors G phi (P.vertex ⟨1, Nat.succ_lt_succ hq⟩)).card := by
    apply hMissingTwo
    convert he0Incident1 using 1; apply congrArg T.vertex; apply Fin.ext; rfl
  let i0 : Fin (P.length + 1) := ⟨0, Nat.zero_lt_succ _⟩
  let i1 : Fin (P.length + 1) := ⟨1, Nat.succ_lt_succ P.positive⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hMissingNonempty (i : Fin (P.length + 1)) :
      (MissingColors G phi (P.vertex i)).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one (hMissingOne (P.vertex i)))
  let missingChoice : Fin (P.length + 1) → Fin k := fun i =>
    Classical.choose (hMissingNonempty i)
  have hMissingChoice (i : Fin (P.length + 1)) :
      missingChoice i ∈ MissingColors G phi (P.vertex i) :=
    Classical.choose_spec (hMissingNonempty i)
  have hPVertexMem (i : Fin (P.length + 1)) :
      P.vertex i ∈ TreeSequenceVertexSet P := by
    simp [TreeSequenceVertexSet]
  have hMissingChoiceInjective : Function.Injective missingChoice := by
    intro i j hij
    by_contra hne
    have hvne : P.vertex i ≠ P.vertex j := by
      intro hv
      exact hne (P.vertex_injective hv)
    have hdisjoint := hElementary (hPVertexMem i) (hPVertexMem j) hvne
    apply Finset.disjoint_left.mp hdisjoint (hMissingChoice i)
    rw [hij]
    exact hMissingChoice j
  let chosen : Finset (Fin k) := Finset.univ.image missingChoice
  have hChosenCard : chosen.card = q + 1 := by
    rw [show chosen.card = Finset.univ.card by
      exact Finset.card_image_iff.mpr hMissingChoiceInjective.injOn]
    simp [hP_length]
  have hChosenSubset : chosen ⊆ TreeMissingColors phi P := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨i, -, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨P.vertex i, hPVertexMem i, hMissingChoice i⟩
  have hMissingTwoI0 :
      2 ≤ (MissingColors G phi (P.vertex i0)).card := by
    simpa [i0, P] using hMissingTwo0
  have hMissingTwoI1 :
      2 ≤ (MissingColors G phi (P.vertex i1)).card := by
    simpa [i1, P] using hMissingTwo1
  have hExtraNonempty (i : Fin (P.length + 1))
      (htwo : 2 ≤ (MissingColors G phi (P.vertex i)).card) :
      ((MissingColors G phi (P.vertex i)).erase (missingChoice i)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (hMissingChoice i)]
    omega
  let extra0 : Fin k := Classical.choose (hExtraNonempty i0 hMissingTwoI0)
  let extra1 : Fin k := Classical.choose (hExtraNonempty i1 hMissingTwoI1)
  have hExtra0Erase :
      extra0 ∈ (MissingColors G phi (P.vertex i0)).erase (missingChoice i0) :=
    Classical.choose_spec (hExtraNonempty i0 hMissingTwoI0)
  have hExtra1Erase :
      extra1 ∈ (MissingColors G phi (P.vertex i1)).erase (missingChoice i1) :=
    Classical.choose_spec (hExtraNonempty i1 hMissingTwoI1)
  have hExtra0Missing : extra0 ∈ MissingColors G phi (P.vertex i0) :=
    (Finset.mem_erase.mp hExtra0Erase).2
  have hExtra1Missing : extra1 ∈ MissingColors G phi (P.vertex i1) :=
    (Finset.mem_erase.mp hExtra1Erase).2
  have hExtra0ChoiceNe : extra0 ≠ missingChoice i0 :=
    (Finset.mem_erase.mp hExtra0Erase).1
  have hExtra1ChoiceNe : extra1 ≠ missingChoice i1 :=
    (Finset.mem_erase.mp hExtra1Erase).1
  have hExtra0NotChosen : extra0 ∉ chosen := by
    intro hextra
    rcases Finset.mem_image.mp hextra with ⟨j, -, hj⟩
    by_cases hj0 : j = i0
    · subst j
      exact hExtra0ChoiceNe hj.symm
    · have hvne : P.vertex i0 ≠ P.vertex j := by
        intro hv
        exact hj0 (P.vertex_injective hv).symm
      have hdisjoint := hElementary (hPVertexMem i0) (hPVertexMem j) hvne
      apply Finset.disjoint_left.mp hdisjoint hExtra0Missing
      rw [← hj]
      exact hMissingChoice j
  have hExtra1NotChosen : extra1 ∉ chosen := by
    intro hextra
    rcases Finset.mem_image.mp hextra with ⟨j, -, hj⟩
    by_cases hj1 : j = i1
    · subst j
      exact hExtra1ChoiceNe hj.symm
    · have hvne : P.vertex i1 ≠ P.vertex j := by
        intro hv
        exact hj1 (P.vertex_injective hv).symm
      have hdisjoint := hElementary (hPVertexMem i1) (hPVertexMem j) hvne
      apply Finset.disjoint_left.mp hdisjoint hExtra1Missing
      rw [← hj]
      exact hMissingChoice j
  have hExtrasNe : extra0 ≠ extra1 := by
    have hvne : P.vertex i0 ≠ P.vertex i1 := by
      intro hv
      exact hi01 (P.vertex_injective hv)
    have hdisjoint := hElementary (hPVertexMem i0) (hPVertexMem i1) hvne
    intro h
    apply Finset.disjoint_left.mp hdisjoint hExtra0Missing
    rw [h]
    exact hExtra1Missing
  let selected : Finset (Fin k) := insert extra0 (insert extra1 chosen)
  have hSelectedCard : selected.card = q + 3 := by
    rw [show selected.card = (insert extra1 chosen).card + 1 by
      exact Finset.card_insert_of_notMem (by
        simp [hExtra0NotChosen, hExtrasNe])]
    rw [Finset.card_insert_of_notMem hExtra1NotChosen, hChosenCard]
  have hSelectedSubset : selected ⊆ TreeMissingColors phi P := by
    intro c hc
    simp only [selected, Finset.mem_insert] at hc
    rcases hc with rfl | rfl | hc
    · exact Finset.mem_biUnion.mpr
        ⟨P.vertex i0, hPVertexMem i0, hExtra0Missing⟩
    · exact Finset.mem_biUnion.mpr
        ⟨P.vertex i1, hPVertexMem i1, hExtra1Missing⟩
    · exact hChosenSubset hc
  have hTreeMissingCard : q + 3 ≤ (TreeMissingColors phi P).card := by
    rw [← hSelectedCard]
    exact Finset.card_le_card hSelectedSubset
  let eligible : Finset (Fin P.length) :=
    Finset.univ.filter fun j => 1 ≤ j.val
  have hUsedSubset : TreeUsedColors phi P ⊆
      eligible.image (fun j => colorOf (P.edge j)) := by
    intro c hc
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with ⟨j, hj, hphi⟩
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, ?_⟩
    · simpa [eligible] using hj
    · simp [colorOf, hphi]
  have hEligibleCard : eligible.card = q - 1 := by
    have heligible :
        eligible = Finset.univ.erase (⟨0, P.positive⟩ : Fin P.length) := by
      ext j
      simp [eligible, Fin.ext_iff]
      omega
    rw [heligible, Finset.card_erase_of_mem (by simp), Finset.card_univ]
    simp [hP_length]
  have hTreeUsedCard : (TreeUsedColors phi P).card ≤ q - 1 := by
    refine (Finset.card_le_card hUsedSubset).trans ?_
    refine (Finset.card_image_le).trans_eq hEligibleCard
  change 4 ≤ (TreeFreeColors phi P).card
  unfold TreeFreeColors
  have hsdiff := Finset.le_card_sdiff
    (TreeUsedColors phi P) (TreeMissingColors phi P)
  by_cases hqOne : q = 1
  · omega
  · have hqTwo : 2 ≤ q := by omega
    omega

theorem TashTreeFourUnusedColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (q : ℕ) (hq : 1 ≤ q) (hqt : q < T.length) :
    4 ≤ (TreeFreeColors phi (TreeSequencePrefix T q hq (Nat.le_of_lt hqt))).card := by
  classical
  let P : TreeSequence G e0 :=
    TreeSequencePrefix T q hq (Nat.le_of_lt hqt)
  have hP_length : P.length = q := rfl
  have hprefix : TreeSequenceInitialSegment P T := by
    refine ⟨Nat.le_of_lt hqt, ?_, ?_⟩
    · intro i
      rfl
    · intro j
      rfl
  have hproperPrefix : P.length < T.length := by
    simpa [hP_length] using hqt
  have hElementary :
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet P) :=
    TashTreeProperPrefixElementary G k e0 phi T P hmin hprefix hproperPrefix
  rcases hmin.1.1 with ⟨_, _, hk, hProper, hOne⟩
  have hkpos : 0 < k := by omega
  have hDegreeMax (v : V) : Degree G v ≤ MaximumDegree G := by
    unfold MaximumDegree
    apply Finset.le_max'
    simp
  have hfirstEnds :
      G.ends e0 = Sym2.mk (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)
        (T.vertex ⟨0, Nat.zero_lt_succ _⟩) := by
    rcases T.attaches ⟨0, T.positive⟩ with ⟨i, hi⟩
    have hi0 : i = ⟨0, Nat.zero_lt_one⟩ := Fin.eq_zero i
    subst i
    rw [T.first_edge] at hi
    simpa only [Fin.succ, Fin.castLT] using hi
  have he0Incident0 :
      Incident G (T.vertex ⟨0, Nat.zero_lt_succ _⟩) e0 := by
    rw [Incident, hfirstEnds]
    simp
  have he0Incident1 :
      Incident G (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩) e0 := by
    rw [Incident, hfirstEnds]
    simp
  let fallback : Fin k := ⟨0, hkpos⟩
  let colorOf : E → Fin k := fun e => (phi e).getD fallback
  let coloredIncident : V → Finset E := fun v =>
    Finset.univ.filter fun e => Incident G v e ∧ ∃ c, phi e = some c
  let incidentEdges : V → Finset E := fun v =>
    Finset.univ.filter fun e => Incident G v e
  have hPresentImage (v : V) :
      PresentColors G phi v = (coloredIncident v).image colorOf := by
    ext c
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, coloredIncident]
    constructor
    · rintro ⟨e, hie, hphi⟩
      refine ⟨e, ?_, ?_⟩
      · exact ⟨hie, c, hphi⟩
      · simp [colorOf, hphi]
    · rintro ⟨e, ⟨hie, d, hphi⟩, heq⟩
      have hdc : d = c := by
        simpa [colorOf, hphi] using heq
      subst d
      exact ⟨e, hie, hphi⟩
  have hColorInjective (v : V) :
      Set.InjOn colorOf (coloredIncident v : Set E) := by
    intro e he f hf hcolors
    simp only [coloredIncident, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at he hf
    rcases he with ⟨hie, c, hce⟩
    rcases hf with ⟨hif, d, hdf⟩
    have hcd : c = d := by
      have hce' : colorOf e = c := by simp [colorOf, hce]
      have hdf' : colorOf f = d := by simp [colorOf, hdf]
      rw [hce', hdf'] at hcolors
      exact hcolors
    subst d
    by_contra hef
    exact (hProper hef ⟨v, hie, hif⟩ hce) hdf
  have hPresentCard (v : V) :
      (PresentColors G phi v).card = (coloredIncident v).card := by
    rw [hPresentImage]
    exact Finset.card_image_iff.mpr (hColorInjective v)
  have hColoredSubsetIncident (v : V) :
      coloredIncident v ⊆ incidentEdges v := by
    intro e he
    simp only [coloredIncident, incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at he ⊢
    exact he.1
  have hIncidentCard (v : V) : (incidentEdges v).card = Degree G v := by
    rfl
  have hPresentDegree (v : V) :
      (PresentColors G phi v).card ≤ Degree G v := by
    rw [hPresentCard, ← hIncidentCard]
    exact Finset.card_le_card (hColoredSubsetIncident v)
  have hMissingCard (v : V) :
      (MissingColors G phi v).card = k - (PresentColors G phi v).card := by
    unfold MissingColors
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  have hMissingOne (v : V) : 1 ≤ (MissingColors G phi v).card := by
    rw [hMissingCard]
    have hp := hPresentDegree v
    have hd := hDegreeMax v
    omega
  have hEndpointPresent (v : V) (he0v : Incident G v e0) :
      (PresentColors G phi v).card ≤ Degree G v - 1 := by
    rw [hPresentCard, ← hIncidentCard]
    have hsubset : coloredIncident v ⊆ (incidentEdges v).erase e0 := by
      intro e he
      simp only [Finset.mem_erase]
      have heparts : Incident G v e ∧ ∃ c, phi e = some c := by
        simpa [coloredIncident] using he
      refine ⟨?_, ?_⟩
      · intro heq
        subst e
        rcases heparts.2 with ⟨c, hc⟩
        simp [hOne.1] at hc
      · simpa [incidentEdges] using heparts.1
    refine (Finset.card_le_card hsubset).trans_eq ?_
    rw [Finset.card_erase_of_mem]
    simpa [incidentEdges] using he0v
  exact @helper_continuation_174 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi)
      (@T) (@q) (@hq) (@hqt) (@hP_length) (@hElementary) (@hk) (@hkpos) (@hDegreeMax)
      (@he0Incident0) (@he0Incident1) (@hIncidentCard) (@hMissingCard) (@hMissingOne)
      (@hEndpointPresent)
end GoldbergSeymour

end
