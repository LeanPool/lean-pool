/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HkuTreeColorsControlled

public import LeanPool.GoldbergSeymour.SameColorSeriesPreserved

/-!
# Extension Base Claim Tree Edge Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_segment_61.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
    LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (rounds : ℕ)
    (series : TashkinovSeries G k rounds e0 input) (j : Fin (rounds + (1 : ℕ))) (i : Fin
    rounds), j = i.succ → TreeSequenceInitialSegment (series.data.tree i.succ.castSucc)
    (series.data.tree i.succ.succ) := by
  classical
  intro V E _ _ _ G k e0 input rounds series j i hji
  cases series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero i) hji.symm |>.elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hvals := congrArg Fin.val hji
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
    have hvals := congrArg Fin.val hji
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hvals := congrArg Fin.val hji
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension

private theorem helper_setTransfer_118.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
    LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (rounds : ℕ)
    (series : TashkinovSeries G k rounds e0 input) (jSlot q : Fin rounds), (↑q : ℕ) + (1 : ℕ)
    = rounds → (∀ (j : Fin (rounds + (1 : ℕ))) (i : Fin rounds), j = i.succ →
    TreeSequenceInitialSegment (series.data.tree i.succ.castSucc) (series.data.tree
    i.succ.succ)) → (∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → ∀ {v : V},
    v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B) → ∀ (n : ℕ), (↑jSlot : ℕ) ≤ n →
    n ≤ (↑q : ℕ) → ∀ (r : Fin rounds), (↑r : ℕ) = n → TreeMissingColors (series.data.coloring
    jSlot.castSucc) (series.data.tree jSlot.succ.castSucc) ∪ TashkinovStoredColors series.data
    jSlot.castSucc ⊆ TreeMissingColors (series.data.coloring r.castSucc) (series.data.tree
    r.succ.castSucc) ∪ TashkinovStoredColors series.data r.castSucc := by
  classical
  intro V E _ _ _ G k e0 input rounds series jSlot q hqTerminal segment vertexTransfer n hjn
  induction n, hjn using Nat.le_induction with
  | base =>
      intro hnq r hr
      have heq : r = jSlot := by apply Fin.ext; omega
      subst r
      intro c hc
      exact hc
  | succ n hn ih =>
      intro hnq r hr c hc
      let prev : Fin rounds := ⟨n, by omega⟩
      have hold := ih (by omega) prev rfl hc
      have hseg := segment prev.succ prev rfl
      have hverts : ∀ v, v ∈ TreeSequenceVertexSet
          (series.data.tree prev.succ.castSucc) →
          v ∈ TreeSequenceVertexSet (series.data.tree prev.succ.succ) := by
        intro v hv
        exact vertexTransfer hseg hv
      have hmono := HkuMissingStoredMonotone G k rounds e0 input series prev
      have hnew : TreeMissingColors (series.data.coloring prev.castSucc)
          (series.data.tree prev.succ.castSucc) ∪
        TashkinovStoredColors series.data prev.castSucc ⊆
        TreeMissingColors (series.data.coloring prev.succ)
          (series.data.tree prev.succ.succ) ∪
        TashkinovStoredColors series.data prev.succ := by
        intro d hd
        rcases Finset.mem_union.mp hd with hd | hd
        · have step := hmono.2 (hmono.1
            (Finset.mem_union.mpr (Or.inl hd)))
          exact step
        · have step := hmono.2 (hmono.1
            (Finset.mem_union.mpr (Or.inr hd)))
          exact step
      have hnext : r = ⟨n + 1, by omega⟩ := by apply Fin.ext; omega
      rw [hnext]
      have hcolor : prev.succ = (⟨n + 1, by omega⟩ : Fin rounds).castSucc := by
        apply Fin.ext
        simp [prev]
      have htree : prev.succ.succ =
          (⟨n + 1, by omega⟩ : Fin rounds).succ.castSucc := by
        apply Fin.ext
        simp [prev]
      simpa [prev] using hnew hold

private theorem helper_internalClaim_170.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
    LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (rounds : ℕ)
    (series : TashkinovSeries G k rounds e0 input) (jSlot q : Fin rounds), (↑jSlot : ℕ) ≤ (↑q
    : ℕ) → (↑q : ℕ) + (1 : ℕ) = rounds → ∀ (sigma : PartialEdgeColoring E k), StableColoring
    (series.data.tree q.succ.castSucc) (TashkinovStoredColors series.data q.succ)
    (series.data.coloring q.succ) sigma → let _ : DecidableEq V := Classical.decEq V; (∀ (j :
    Fin (rounds + (1 : ℕ))) (i : Fin rounds), j = i.succ → TreeSequenceInitialSegment
    (series.data.tree i.succ.castSucc) (series.data.tree i.succ.succ)) → (∀ {A B :
    TreeSequence G e0}, TreeSequenceInitialSegment A B → ∀ {f : E}, TreeIncidentEdge A f →
    TreeIncidentEdge B f) → TreeMissingColors (series.data.coloring jSlot.castSucc)
    (series.data.tree jSlot.succ.castSucc) ∪ TashkinovStoredColors series.data jSlot.castSucc
    ⊆ TreeMissingColors (series.data.coloring q.castSucc) (series.data.tree q.succ.castSucc) ∪
    TashkinovStoredColors series.data q.castSucc → ∀ f ∈ InternalEdges G
    (TreeSequenceVertexSet (series.data.tree jSlot.succ.castSucc)), ∀ (c : Fin k),
    series.data.coloring jSlot.castSucc f = some c → c ∈ TreeMissingColors
    (series.data.coloring jSlot.castSucc) (series.data.tree jSlot.succ.castSucc) ∪
    TashkinovStoredColors series.data jSlot.castSucc → sigma f = series.data.coloring
    jSlot.castSucc f := by
  classical
  intro V E _ _ _ G k e0 input rounds series jSlot q hjle hqTerminal sigma hsigmaStable this
      segment incidentTransfer finalSets f hf c hfc hc
  have hinc : TreeIncidentEdge (series.data.tree jSlot.succ.castSucc) f := by
    have hforall := (Finset.mem_filter.mp hf).2
    change ∃ v, v ∈ TreeSequenceVertexSet
      (series.data.tree jSlot.succ.castSucc) ∧ v ∈ G.ends f
    induction hends : G.ends f using Sym2.inductionOn with
    | _ x y =>
          have hx : Incident G x f := by
            change x ∈ G.ends f
            rw [hends]
            exact Sym2.mem_mk_left x y
          refine ⟨x, hforall x hx, ?_⟩
          exact Sym2.mem_mk_left x y
  have preserved := SameColorSeriesPreserved G k rounds e0 input series
    jSlot q hjle f c hinc hfc hc
  have hqcolor := preserved.2 hf
  have incidentForward : TreeIncidentEdge
      (series.data.tree q.succ.castSucc) f := by
    have carry : ∀ (n : ℕ), jSlot.val ≤ n → n ≤ q.val →
        ∀ r : Fin rounds, r.val = n →
        TreeIncidentEdge (series.data.tree r.succ.castSucc) f := by
      intro n hjn
      induction n, hjn using Nat.le_induction with
      | base =>
          intro hnq r hr
          have heq : r = jSlot := by apply Fin.ext; omega
          rw [heq]
          exact hinc
      | succ n hn ih =>
          intro hnq r hr
          let prev : Fin rounds := ⟨n, by omega⟩
          have hold := ih (by omega) prev rfl
          have hnew := incidentTransfer (segment prev.succ prev rfl) hold
          have heq : r = ⟨n + 1, by omega⟩ := by apply Fin.ext; omega
          rw [heq]
          have htree : prev.succ.succ =
              (⟨n + 1, by omega⟩ : Fin rounds).succ.castSucc := by
            apply Fin.ext
            simp [prev]
          rw [htree] at hnew
          exact hnew
    exact carry q.val (by omega) le_rfl q rfl
  have hmem := (HkuMissingStoredMonotone G k rounds e0 input series q).1
    (finalSets hc)
  have hstable := hsigmaStable.1 f
    incidentForward
    (by exact ⟨c, hmem, by rw [hqcolor, hfc]⟩)
  exact hstable.trans hqcolor

theorem ExtensionBaseClaimTreeEdgeColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (rounds : ℕ) (series : TashkinovSeries G k rounds e0 input)
    (jSlot q : Fin rounds) (hjle : jSlot.val ≤ q.val)
    (hqTerminal : q.val + 1 = rounds)
    (sigma : PartialEdgeColoring E k)
    (_ : IsProperEdgeColoring G sigma)
    (hsigmaOne : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring
      (series.data.tree q.succ.castSucc)
      (TashkinovStoredColors series.data q.succ)
      (series.data.coloring q.succ) sigma) :
    (∀ f : E,
      f ∈ InternalEdges G
        (TreeSequenceVertexSet (series.data.tree jSlot.succ.castSucc)) →
      ∀ c : Fin k,
        series.data.coloring jSlot.castSucc f = some c →
        c ∈ TreeMissingColors (series.data.coloring jSlot.castSucc)
              (series.data.tree jSlot.succ.castSucc) ∪
            TashkinovStoredColors series.data jSlot.castSucc →
        sigma f = series.data.coloring jSlot.castSucc f) ∧
    ∀ a : Fin (series.data.tree jSlot.succ.castSucc).length,
      sigma ((series.data.tree jSlot.succ.castSucc).edge a) =
        series.data.coloring jSlot.castSucc
          ((series.data.tree jSlot.succ.castSucc).edge a) := by
  classical
  exact ((by
    classical
  let : DecidableEq V := Classical.decEq V
  have segment := @helper_segment_61 V E inferInstance inferInstance inferInstance G k e0 input
      rounds series
  have vertexTransfer {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨x, hx⟩
    rcases hab with ⟨hlen, hvertices, hedges⟩
    unfold TreeSequenceVertexSet
    apply Finset.mem_image.mpr
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) x, Finset.mem_univ _, ?_⟩
    exact (hvertices x).trans hx
  have incidentTransfer {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {f : E}
      (hf : TreeIncidentEdge A f) : TreeIncidentEdge B f := by
    rcases hf with ⟨v, hv, hve⟩
    exact ⟨v, vertexTransfer hab hv, hve⟩
  have setTransfer := @helper_setTransfer_118 V E inferInstance inferInstance inferInstance G k e0
      input rounds series jSlot q hqTerminal segment vertexTransfer
  have finalSets := setTransfer q.val (by omega) le_rfl q rfl
  have internalClaim := @helper_internalClaim_170 V E inferInstance inferInstance inferInstance G k
      e0 input rounds series jSlot q hjle hqTerminal sigma hsigmaStable segment incidentTransfer
      finalSets
  refine ⟨internalClaim, ?_⟩
  intro a
  have stageOne : IsOneEdgeUncolored
      (series.data.coloring jSlot.castSucc) e0 := by
    generalize hz : jSlot.castSucc = z
    cases series.certified z with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        simpa only [initialColoring] using triple.2.2.2.2
    | SE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        rw [currentColoring]
        exact choice.selectedOneUncolored
    | PE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
        exact currentOneUncolored
    | RE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
        rw [currentColoring]
        exact previousOneUncolored
  by_cases ha : a.val = 0
  · have hea : (series.data.tree jSlot.succ.castSucc).edge a = e0 := by
        have hz : a = ⟨0, (series.data.tree jSlot.succ.castSucc).positive⟩ := by
          apply Fin.ext
          omega
        rw [hz]
        exact (series.data.tree jSlot.succ.castSucc).first_edge
    rw [hea, hsigmaOne.1]
    exact stageOne.1.symm
  · have used : (series.data.tree jSlot.succ.castSucc).edge a ∈
          InternalEdges G (TreeSequenceVertexSet
            (series.data.tree jSlot.succ.castSucc)) := by
        have hforall : ∀ v, Incident G v
            ((series.data.tree jSlot.succ.castSucc).edge a) →
            v ∈ TreeSequenceVertexSet (series.data.tree jSlot.succ.castSucc) := by
          intro v hv
          have hatt := (series.data.tree jSlot.succ.castSucc).attaches a
          rcases hatt with ⟨i, hi⟩
          change v ∈ G.ends ((series.data.tree jSlot.succ.castSucc).edge a) at hv
          rw [hi] at hv
          simp only [Fin.castSucc_succ, Sym2.mem_iff] at hv
          rcases hv with hv | hv
          · apply Finset.mem_image.mpr
            exact ⟨a.succ, Finset.mem_univ _, by simpa using hv.symm⟩
          · apply Finset.mem_image.mpr
            exact ⟨Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ a.isLt)),
              Finset.mem_univ _, by simpa using hv.symm⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hforall⟩
    have hedge : (series.data.tree jSlot.succ.castSucc).edge a ≠ e0 := by
      intro he
      have hz := (series.data.tree jSlot.succ.castSucc).edge_injective
        (he.trans (series.data.tree jSlot.succ.castSucc).first_edge.symm)
      apply ha
      simpa using congrArg Fin.val hz
    obtain ⟨c, hfc⟩ := stageOne.2 _ hedge
    have colorMem := (HkuTreeColorsControlled G k rounds e0 input series jSlot).1
    have hused : ∃ c, series.data.coloring jSlot.castSucc
        ((series.data.tree jSlot.succ.castSucc).edge a) = some c ∧
        c ∈ TreeUsedColors (series.data.coloring jSlot.castSucc)
          (series.data.tree jSlot.succ.castSucc) := by
      unfold TreeUsedColors
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨c, hfc, ?_⟩
      exact ⟨a, by omega, hfc⟩
    rcases hused with ⟨c, hfc, hcused⟩
    exact internalClaim _ used c hfc (colorMem hcused)))

end GoldbergSeymour

end
