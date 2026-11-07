/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesTreeFacts

public import LeanPool.GoldbergSeymour.TashkinovSeries

/-!
# Hku Missing Stored Monotone

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem HkuMissingStoredMonotone_branch_237.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
    LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
    : TashkinovSeries G k rounds e0 input) (q : Fin rounds), (∀ {phi : PartialEdgeColoring E
    k} (alpha beta : Fin k) (z : V ⊕ E) {v : V} {c : Fin k}, c ∈ MissingColors G phi v → c ≠
    alpha → c ≠ beta → c ∈ MissingColors G (TwoColorComponentSwap G phi alpha beta z) v) → (∀
    {A : TreeSequence G e0} {C : Finset (Fin k)} {phi pi : PartialEdgeColoring E k},
    StableColoring A C phi pi → TreeMissingColors phi A = TreeMissingColors pi A) → (∀ c ∈
    series.data.stored q.succ, c ∉ TreeMissingColors (series.data.coloring q.succ)
    (series.data.tree q.succ.castSucc) → c ∈ TashkinovStoredColors series.data q.succ) → (∀ c
    ∈ TashkinovStoredColors series.data q.castSucc, c ∈ TreeMissingColors
    (series.data.coloring q.succ) (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors
    series.data q.succ) → TreeMissingColors (series.data.coloring q.castSucc)
    (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors series.data q.castSucc ⊆
    TreeMissingColors (series.data.coloring q.succ) (series.data.tree q.succ.castSucc) ∪
    TashkinovStoredColors series.data q.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input series q swapMissing stableMissing currentStoredTransfer
      storedTransfer c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · have cert := series.certified q.succ
    generalize hj : q.succ = j at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      exact (Fin.succ_ne_zero q) hj |>.elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hvals := congrArg Fin.val hj
      simp at hvals
      have hi : i = q := by apply Fin.ext; omega
      subst i
      have heq := stableMissing choice.selectedStable
      have hnew : c ∈ TreeMissingColors choice.selected
            (series.data.tree q.succ.castSucc) := by
        rw [← heq]
        exact hc
      exact Finset.mem_union.mpr (Or.inl (by simpa [currentColoring] using hnew))
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      have hvals := congrArg Fin.val hj
      simp at hvals
      have hi : i = q := by apply Fin.ext; omega
      subst i
      have hfirst := stableMissing choice.selectedStable
      have hsecond := stableMissing secondStableRelation
      have hsecondold : TreeMissingColors (series.data.coloring q.castSucc)
            (series.data.tree q.succ.castSucc) =
          TreeMissingColors secondStable (series.data.tree q.succ.castSucc) :=
        hfirst.trans hsecond
      have hsc : c ∈ TreeMissingColors secondStable
            (series.data.tree q.succ.castSucc) := by
        rw [← hsecondold]
        exact hc
      by_cases hcg : c = gamma
      · by_cases hn : c ∈ TreeMissingColors (series.data.coloring q.succ)
            (series.data.tree q.succ.castSucc)
        · exact Finset.mem_union.mpr (Or.inl hn)
        · apply Finset.mem_union.mpr
          right
          apply currentStoredTransfer c
          · rw [currentStored]
            simp [hcg]
          · exact hn
      · by_cases hcd : c = choice.color
        · by_cases hn : c ∈ TreeMissingColors (series.data.coloring q.succ)
              (series.data.tree q.succ.castSucc)
          · exact Finset.mem_union.mpr (Or.inl hn)
          · apply Finset.mem_union.mpr
            right
            apply currentStoredTransfer c
            · rw [currentStored]
              simp [hcd]
            · exact hn
        · simp only [TreeMissingColors, Fin.castSucc_succ, Finset.mem_biUnion] at hsc
          rcases hsc with ⟨v, hv, hvc⟩
          have htrans := swapMissing gamma choice.color
                (Sum.inl choice.vertex) hvc hcg hcd
          apply Finset.mem_union.mpr
          left
          rw [currentColoring]
          unfold TreeMissingColors
          simp only [Finset.mem_biUnion]
          exact ⟨v, hv, htrans⟩
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hvals := congrArg Fin.val hj
      simp at hvals
      have hi : i = q := by apply Fin.ext; omega
      subst i
      exact Finset.mem_union.mpr (Or.inl (by simpa [currentColoring] using hc))
  · exact storedTransfer c hc

theorem HkuMissingStoredMonotone {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) :
    TreeMissingColors (series.data.coloring q.castSucc)
          (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.castSucc ⊆
      TreeMissingColors (series.data.coloring q.succ)
          (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.succ ∧
    TreeMissingColors (series.data.coloring q.succ)
          (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.succ ⊆
      TreeMissingColors (series.data.coloring q.succ)
          (series.data.tree q.succ.succ) ∪
        TashkinovStoredColors series.data q.succ := by
  classical
  let : DecidableEq V := Classical.decEq V
  have vertexTransfer {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    rcases hv with ⟨i, hi⟩
    rcases hab with ⟨hlen, hvertices, hedges⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, ?_⟩
    exact (hvertices i).trans hi
  have augmentationTransfer {A B : TreeSequence G e0}
      {phi : PartialEdgeColoring E k}
      (hab : TashkinovAugmentation phi A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    rcases hab with ⟨hlen, hseg, hc⟩
    exact vertexTransfer hseg hv
  have closureTransfer {A B : TreeSequence G e0}
      {phi : PartialEdgeColoring E k}
      (hab : TashkinovAugmentationSequence phi A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    unfold TashkinovAugmentationSequence at hab
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => exact hv
    | head hstep htail ih =>
      exact ih (augmentationTransfer hstep hv)
  have segment : ∀ (j : Fin (rounds + 1)) (i : Fin rounds), j = i.succ →
      TreeSequenceInitialSegment (series.data.tree i.succ.castSucc)
        (series.data.tree i.succ.succ) := by
    exact @TashkinovSeries.stepInitialSegment V E inferInstance inferInstance inferInstance G k
        rounds e0 input series
  have missingTransfer {A B : TreeSequence G e0}
      (hab : ∀ v, v ∈ TreeSequenceVertexSet A →
        v ∈ TreeSequenceVertexSet B) (phi : PartialEdgeColoring E k) :
      TreeMissingColors phi A ⊆ TreeMissingColors phi B := by
    intro c hc
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    rcases hc with ⟨v, hv, hvc⟩
    exact ⟨v, hab v hv, hvc⟩
  have secondSegment := segment q.succ q (by rfl)
  have oldVertices : ∀ v, v ∈ TreeSequenceVertexSet (series.data.tree q.castSucc.castSucc) →
      v ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc) := by
    intro v hv
    by_cases hq : q.val = 0
    · have hzero : q = ⟨0, by omega⟩ := by apply Fin.ext; exact hq
      cases series.certified 0 with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure =>
        have hidx : q.castSucc.castSucc = (0 : Fin (rounds + 2)) := by
          apply Fin.ext
          simp [hq]
        have hv' : v ∈ TreeSequenceVertexSet (series.data.tree 0) := by
          rw [hidx] at hv
          exact hv
        have hres := closureTransfer initialClosure.1 hv'
        have hnext : q.succ.castSucc = (1 : Fin (rounds + 2)) := by
          apply Fin.ext
          simp [hq]
        rw [hnext]
        exact hres
    · let i : Fin rounds := ⟨q.val - 1, by omega⟩
      have hi : i.succ = q.castSucc := by apply Fin.ext; simp [i]; omega
      have hs := segment q.castSucc i hi.symm
      have hv' : v ∈ TreeSequenceVertexSet (series.data.tree i.succ.castSucc) := by
        simpa [hi] using hv
      have hres := vertexTransfer hs hv'
      simpa [hi] using hres
  have laterMissing := missingTransfer (fun v hv => vertexTransfer secondSegment hv)
      (series.data.coloring q.succ)
  have swapMissing {phi : PartialEdgeColoring E k} (alpha beta : Fin k)
      (z : Sum V E) {v : V} {c : Fin k}
      (hc : c ∈ MissingColors G phi v) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      c ∈ MissingColors G (TwoColorComponentSwap G phi alpha beta z) v := by
    unfold MissingColors at hc ⊢
    rw [Finset.mem_sdiff] at hc ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hp
    rw [PresentColors] at hp
    rcases Finset.mem_filter.mp hp with ⟨_, hp⟩
    rcases hp with ⟨e, he, hpe⟩
    apply hc.2
    rw [PresentColors]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    refine ⟨e, he, ?_⟩
    unfold TwoColorComponentSwap at hpe
    by_cases hh : Sum.inr e ∈ TwoColorComponent G phi alpha beta z
    · rw [ite_eq_left hh] at hpe
      by_cases ha : phi e = some alpha
      · rw [ite_eq_left ha] at hpe
        exact False.elim (hcb (Option.some.inj hpe).symm)
      · by_cases hb : phi e = some beta
        · rw [ite_eq_right ha, ite_eq_left hb] at hpe
          exact False.elim (hca (Option.some.inj hpe).symm)
        · rw [ite_eq_right ha, ite_eq_right hb] at hpe
          exact hpe
    · rw [ite_eq_right hh] at hpe
      exact hpe
  have stableMissing {A : TreeSequence G e0} {C : Finset (Fin k)}
      {phi pi : PartialEdgeColoring E k}
      (hstable : StableColoring A C phi pi) :
      TreeMissingColors phi A = TreeMissingColors pi A := by
    ext c
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor
    · rintro ⟨v, hv, hvc⟩
      have hcopy := hvc
      rw [← hstable.2 v hv] at hcopy
      exact ⟨v, hv, hcopy⟩
    · rintro ⟨v, hv, hvc⟩
      have hcopy := hvc
      rw [hstable.2 v hv] at hcopy
      exact ⟨v, hv, hcopy⟩
  have currentStoredTransfer :
    ∀ c : Fin k, c ∈ series.data.stored q.succ → c ∉ TreeMissingColors (series.data.coloring
        q.succ) (series.data.tree q.succ.castSucc) → c ∈ TashkinovStoredColors series.data q.succ
  := by
    intro c hs hn
    unfold TashkinovStoredColors
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Fin.castSucc_succ,
    Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨⟨q.succ, ?_⟩, ?_⟩
    · simpa using hs
    · simpa using hn
  have storedTransfer :
    ∀ c : Fin k, c ∈ TashkinovStoredColors series.data q.castSucc → c ∈ TreeMissingColors
        (series.data.coloring q.succ) (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors
        series.data q.succ := by
    intro c hc
    by_cases hn : c ∈ TreeMissingColors (series.data.coloring q.succ)
          (series.data.tree q.succ.castSucc)
    · exact Finset.mem_union.mpr (Or.inl hn)
    · exact Finset.mem_union.mpr (Or.inr (by
        by_cases hq : q.val = 0
        · simp [TashkinovStoredColors, hq] at hc
        · unfold TashkinovStoredColors at hc ⊢
          simp only [Fin.val_castSucc, hq, ↓reduceIte, Finset.mem_sdiff, Finset.mem_biUnion,
              Finset.mem_univ, true_and,
    Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_self, Fin.castSucc_succ] at hc ⊢
          have hcum := hc.1
          refine ⟨?_, hn⟩
          rcases hcum with ⟨i, hci⟩
          refine ⟨i, ?_⟩
          by_cases hi : i.val ≤ q.val
          · simp [hi] at hci
            have hnext : i.val ≤ q.val + 1 := by omega
            simpa [hnext] using hci
          · simp [hi] at hci
      ))
  refine ⟨?_, ?_⟩
  · exact @HkuMissingStoredMonotone_branch_237 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series q swapMissing stableMissing currentStoredTransfer storedTransfer
  intro c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · exact Finset.mem_union.mpr (Or.inl (laterMissing hc))
  · exact Finset.mem_union.mpr (Or.inr hc)

end GoldbergSeymour

end
