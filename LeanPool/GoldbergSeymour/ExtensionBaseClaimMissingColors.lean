/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesTreeFacts

public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClass

public import LeanPool.GoldbergSeymour.SupportingPEMissingTransport
public import LeanPool.GoldbergSeymour.SupportingPEStoredIntersection

/-!
# Extension Base Claim Missing Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hstart_177.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
    terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds), (↑jSlot : ℕ) ≤ (↑q
    : ℕ) → (↑q : ℕ) + (1 : ℕ) = ett.rounds → (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex
    ett terminalSupport hterminalSupport → ∀ (w : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) →
    Fin ett.rounds), (∀ (a b : Fin ett.rounds), (↑a : ℕ) ≤ (↑b : ℕ) → ∀ v ∈
    TreeSequenceVertexSet (ett.series.data.tree a.succ.castSucc), v ∈ TreeSequenceVertexSet
    (ett.series.data.tree b.succ.castSucc)) → (ETTFirstAppearanceIndex ett terminalSupport
    hterminalSupport ≤ (↑(indices (0 : Fin (p + (1 : ℕ)))) : ℕ) + (1 : ℕ) ∧
    ett.series.data.kind (indices (0 : Fin (p + (1 : ℕ)))).succ = some
    TashkinovExtensionKind.PE ∧ ∃ (v : V), ett.series.data.chosenVertex (indices (0 : Fin (p +
    (1 : ℕ)))).succ = some v ∧ ∃ (x : v ∈ TreeSequenceVertexSet T), ETTFirstAppearanceIndex
    ett v x ≤ ETTFirstAppearanceIndex ett terminalSupport hterminalSupport) ∧
    ett.series.data.chosenVertex (indices (0 : Fin (p + (1 : ℕ)))).succ = some w → ∀ v0 ∈
    TreeSequenceVertexSet T, ∀ (hvT0 : w ∈ TreeSequenceVertexSet T), ETTFirstAppearanceIndex
    ett w hvT0 ≤ (↑jSlot : ℕ) + (1 : ℕ) → w ∈ TreeSequenceVertexSet (ett.series.data.tree
    jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q hjle
      hqTerminal hjSlot w p indices stage_vertices hclass0 v0 hchosenV0 hvT0 hbound0
  unfold ETTFirstAppearanceIndex at hbound0
  dsimp at hbound0
  simp only [Nat.add_le_add_iff_right] at hbound0
  let candidates : Finset (Fin (ett.rounds + 1)) := Finset.univ.filter
    (fun i => w ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i))
  have hc : candidates.Nonempty := by
    refine ⟨Fin.last ett.rounds, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett (Fin.last ett.rounds) = T by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    exact hvT0
  have hmin := Finset.min'_mem candidates hc
  have min_independent : ∀ (s : Finset (Fin (ett.rounds + 1)))
      (h1 h2 : s.Nonempty), s.min' h1 = s.min' h2 := by
    intro s h1 h2
    apply le_antisymm
    · exact Finset.min'_le _ _ (Finset.min'_mem s h2)
    · exact Finset.min'_le _ _ (Finset.min'_mem s h1)
  have hbound : (Finset.min' candidates hc).val ≤ jSlot.val := by
      dsimp [candidates] at hc ⊢
      convert hbound0 using 1
  have hminle : (Finset.min' candidates hc).val ≤ jSlot.val := hbound
  have hminval : (Finset.min' candidates hc).val < ett.rounds + 1 :=
    (Finset.min' candidates hc).isLt
  let a : Fin ett.rounds := ⟨(Finset.min' candidates hc).val, by omega⟩
  have ha : w ∈ TreeSequenceVertexSet
      (ett.series.data.tree a.succ.castSucc) := by
    have hnotlast : (Finset.min' candidates hc) ≠ Fin.last ett.rounds := by
      intro he
      have : ett.rounds ≤ jSlot.val := by simpa [he] using hminle
      omega
    have htree : ExtendedTashkinovLadderStage ett (Finset.min' candidates hc) =
        ett.series.data.tree a.succ.castSucc := by
      have hidx : (Finset.min' candidates hc) = a.castSucc := by
        apply Fin.ext
        rfl
      rw [hidx]
      simp [ExtendedTashkinovLadderStage]
    rw [← htree]
    simpa [candidates] using hmin
  exact stage_vertices a jSlot (by simp [a]; omega) w ha

private theorem helper_hfirst_227.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
    terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds), (↑jSlot : ℕ) ≤ (↑q
    : ℕ) → (↑q : ℕ) + (1 : ℕ) = ett.rounds → (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex
    ett terminalSupport hterminalSupport → ∀ (w : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) →
    Fin ett.rounds), (∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices a) : ℕ) <
    (↑(indices b) : ℕ)) → (∀ (r : Fin ett.rounds), (↑r : ℕ) ≤ (↑q : ℕ) ∧ ett.series.data.kind
    r.succ = some TashkinovExtensionKind.PE ∧ ett.series.data.chosenVertex r.succ = some w ↔ ∃
    (a : Fin (p + (1 : ℕ))), indices a = r) → (∀ (v : V) (hvT : v ∈ TreeSequenceVertexSet T),
    v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) →
    ETTFirstAppearanceIndex ett v hvT ≤ (↑jSlot : ℕ) + (1 : ℕ)) → (ETTFirstAppearanceIndex ett
    terminalSupport hterminalSupport ≤ (↑(indices (0 : Fin (p + (1 : ℕ)))) : ℕ) + (1 : ℕ) ∧
    ett.series.data.kind (indices (0 : Fin (p + (1 : ℕ)))).succ = some
    TashkinovExtensionKind.PE ∧ ∃ (v : V), ett.series.data.chosenVertex (indices (0 : Fin (p +
    (1 : ℕ)))).succ = some v ∧ ∃ (x : v ∈ TreeSequenceVertexSet T), ETTFirstAppearanceIndex
    ett v x ≤ ETTFirstAppearanceIndex ett terminalSupport hterminalSupport) ∧
    ett.series.data.chosenVertex (indices (0 : Fin (p + (1 : ℕ)))).succ = some w →
    (ETTFirstAppearanceIndex ett terminalSupport hterminalSupport ≤ (↑(indices (0 : Fin (p +
    (1 : ℕ)))) : ℕ) + (1 : ℕ) ∧ ett.series.data.kind (indices (0 : Fin (p + (1 : ℕ)))).succ =
    some TashkinovExtensionKind.PE ∧ ∃ (v : V), ett.series.data.chosenVertex (indices (0 : Fin
    (p + (1 : ℕ)))).succ = some v ∧ ∃ (x : v ∈ TreeSequenceVertexSet T),
    ETTFirstAppearanceIndex ett v x ≤ ETTFirstAppearanceIndex ett terminalSupport
    hterminalSupport) → ∀ v0 ∈ TreeSequenceVertexSet T, ∀ (hvT0 : w ∈ TreeSequenceVertexSet
    T), ETTFirstAppearanceIndex ett w hvT0 ≤ (↑jSlot : ℕ) + (1 : ℕ) → w ∈
    TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) → MissingColors G
    (ett.series.data.coloring jSlot.castSucc) w = MissingColors G (ett.series.data.coloring
    (indices (0 : Fin (p + (1 : ℕ)))).castSucc) w := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q hjle
      hqTerminal hjSlot w p indices hincreasing henumerates first_bound hclass0 hactive0' v0
      hchosenV0 hvT0 hbound0 hstart
  by_cases heq : jSlot = indices 0
  · subst heq
    rfl
  · have hlt : jSlot.val < (indices 0).val := by
      have hh := hactive0'.1
      omega
    let z : Fin ett.rounds := ⟨(indices 0).val - 1, by omega⟩
    have hzle : jSlot.val ≤ z.val := by simp [z]; omega
    have hno : ∀ r : Fin ett.rounds, jSlot.val ≤ r.val → r.val ≤ z.val →
        ¬ (ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ∧
          ett.series.data.chosenVertex r.succ = some w) := by
      intro r hr1 hr2 hpe
      obtain ⟨a, ha⟩ := (henumerates r).1 ⟨by omega, hpe.1, hpe.2⟩
      have hia : (indices 0).val ≤ (indices a).val := by
        by_cases ha0 : a = 0
        · simp [ha0]
        · have haPos : 0 < a.val := by
            apply Nat.pos_of_ne_zero
            intro haVal
            apply ha0
            apply Fin.ext
            exact haVal
          have : (0 : Fin (p + 1)).val < a.val := by simpa using haPos
          exact Nat.le_of_lt (hincreasing 0 a this)
      have : (indices 0).val ≤ r.val := by
        apply Fin.le_iff_val_le_val.mpr
        simpa [ha] using hia
      simp [z] at hr2
      omega
    have hz := HkuUnsupportedVertexColors G k ett.rounds e0 input ett.series
      z jSlot w (by omega) hstart hno
    have hzeq : z.succ = (indices 0).castSucc := by
      apply Fin.ext
      have hzpos : 1 ≤ (indices 0).val := by omega
      simp [z, Nat.sub_add_cancel hzpos]
    rw [hzeq] at hz
    exact hz

private theorem helper_hlastmem_268.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
    terminalSupport ∈ TreeSequenceVertexSet T) (_ q : Fin ett.rounds) (w : V) (p : ℕ) (indices
    : Fin (p + (1 : ℕ)) → Fin ett.rounds), (ETTFirstAppearanceIndex ett terminalSupport
    hterminalSupport ≤ (↑(indices (0 : Fin (p + (1 : ℕ)))) : ℕ) + (1 : ℕ) ∧
    ett.series.data.kind (indices (0 : Fin (p + (1 : ℕ)))).succ = some
    TashkinovExtensionKind.PE ∧ ∃ (v : V), ett.series.data.chosenVertex (indices (0 : Fin (p +
    (1 : ℕ)))).succ = some v ∧ ∃ (x : v ∈ TreeSequenceVertexSet T), ETTFirstAppearanceIndex
    ett v x ≤ ETTFirstAppearanceIndex ett terminalSupport hterminalSupport) ∧
    ett.series.data.chosenVertex (indices (0 : Fin (p + (1 : ℕ)))).succ = some w → ∀ v0 ∈
    TreeSequenceVertexSet T, w ∈ TreeSequenceVertexSet T → (↑(indices (Fin.last p)) : ℕ) ≤ (↑q
    : ℕ) ∧ ett.series.data.kind (indices (Fin.last p)).succ = some TashkinovExtensionKind.PE ∧
    ett.series.data.chosenVertex (indices (Fin.last p)).succ = some w → w ∈
    TreeSequenceVertexSet (ett.series.data.tree (indices (Fin.last p)).succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q w p
      indices hclass0 v0 hchosenV0 hvT0 hlastinfo
  have hcert := ett.series.certified (indices (Fin.last p)).succ
  generalize targetEq : (indices (Fin.last p)).succ = target at hcert
  cases hcert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    have hv := congrArg Fin.val targetEq
    simp at hv
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hci : ci = indices (Fin.last p) := by
      apply Fin.ext
      have hv := congrArg Fin.val targetEq
      simp at hv ⊢
      omega
    subst ci
    rw [currentKind] at hlastinfo
    simp at hlastinfo
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hci : ci = indices (Fin.last p) := by
      apply Fin.ext
      have hv := congrArg Fin.val targetEq
      simp at hv ⊢
      omega
    subst ci
    rw [currentKind] at hlastinfo
    simp at hlastinfo
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have hci : ci = indices (Fin.last p) := by
      apply Fin.ext
      have hv := congrArg Fin.val targetEq
      simp at hv ⊢
      omega
    subst ci
    have hvchoice : choice.vertex = w := by
      apply Option.some.inj
      exact currentVertex.symm.trans hlastinfo.2.2
    rw [← hvchoice]
    exact choice.vertexDefective.1

private theorem helper_hlate_321.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
    terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds), (↑jSlot : ℕ) ≤ (↑q
    : ℕ) → (↑q : ℕ) + (1 : ℕ) = ett.rounds → ett.series.data.kind q.succ = some
    TashkinovExtensionKind.PE → ett.series.data.chosenVertex q.succ = some terminalSupport → ∀
    w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), ∀ (p : ℕ) (indices : Fin
    (p + (1 : ℕ)) → Fin ett.rounds), (∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) →
    (↑(indices a) : ℕ) < (↑(indices b) : ℕ)) → (∀ (r : Fin ett.rounds), (↑r : ℕ) ≤ (↑q : ℕ) ∧
    ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ∧
    ett.series.data.chosenVertex r.succ = some w ↔ ∃ (a : Fin (p + (1 : ℕ))), indices a = r) →
    ∀ (deltaLast : Fin k) (sigma : PartialEdgeColoring E k), StableColoring
    (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.succ)
    (ett.series.data.coloring q.succ) sigma → (∀ (A B : TreeSequence G e0),
    TreeSequenceInitialSegment A B → ∀ v ∈ TreeSequenceVertexSet A, v ∈ TreeSequenceVertexSet
    B) → (∀ (j : Fin (ett.rounds + (1 : ℕ))) (i : Fin ett.rounds), j = i.succ →
    TreeSequenceInitialSegment (ett.series.data.tree i.succ.castSucc) (ett.series.data.tree
    i.succ.succ)) → (∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), v ∈
    TreeSequenceVertexSet T) → (∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree
    q.succ.castSucc), MissingColors G sigma v = MissingColors G (ett.series.data.coloring
    q.succ) v) → (have storedPairs : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p +
    (1 : ℕ))) => ett.series.data.stored (indices a).succ; MissingColors G
    (ett.series.data.coloring q.succ) w ∩ storedPairs = {deltaLast} ∧ MissingColors G
    (ett.series.data.coloring (indices (Fin.last p)).succ) w ∩ storedPairs = {deltaLast}) →
    (ETTFirstAppearanceIndex ett terminalSupport hterminalSupport ≤ (↑(indices (0 : Fin (p +
    (1 : ℕ)))) : ℕ) + (1 : ℕ) ∧ ett.series.data.kind (indices (0 : Fin (p + (1 : ℕ)))).succ =
    some TashkinovExtensionKind.PE ∧ ∃ (v : V), ett.series.data.chosenVertex (indices (0 : Fin
    (p + (1 : ℕ)))).succ = some v ∧ ∃ (x : v ∈ TreeSequenceVertexSet T),
    ETTFirstAppearanceIndex ett v x ≤ ETTFirstAppearanceIndex ett terminalSupport
    hterminalSupport) ∧ ett.series.data.chosenVertex (indices (0 : Fin (p + (1 : ℕ)))).succ =
    some w → ∀ v0 ∈ TreeSequenceVertexSet T, w ∈ TreeSequenceVertexSet T → (↑(indices
    (Fin.last p)) : ℕ) ≤ (↑q : ℕ) ∧ ett.series.data.kind (indices (Fin.last p)).succ = some
    TashkinovExtensionKind.PE ∧ ett.series.data.chosenVertex (indices (Fin.last p)).succ =
    some w → w ∈ TreeSequenceVertexSet (ett.series.data.tree (indices (Fin.last
    p)).succ.castSucc) → MissingColors G (ett.series.data.coloring (indices (Fin.last
    p)).succ) w = MissingColors G (ett.series.data.coloring q.succ) w := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q hjle
      hqTerminal hqKind hqVertex w hw p indices hincreasing henumerates deltaLast sigma
      hsigmaStable vertex_transfer next_segment final_transfer stable_vertex hinter hclass0 v0
      hchosenV0 hvT0 hlastinfo hlastmem
  by_cases hfinal : indices (Fin.last p) = q
  · subst hfinal
    rfl
  · have hltq : (indices (Fin.last p)).val < q.val := by omega
    let s : Fin ett.rounds := ⟨(indices (Fin.last p)).val + 1, by omega⟩
    have hsle : s.val ≤ q.val := by simp [s]; omega
    have hs_mem : w ∈ TreeSequenceVertexSet
        (ett.series.data.tree s.succ.castSucc) := by
      have hseg := next_segment (indices (Fin.last p)).succ
        (indices (Fin.last p)) rfl
      have ht := vertex_transfer _ _ hseg w hlastmem
      have htree : s.succ.castSucc =
          (indices (Fin.last p)).succ.succ := by
        apply Fin.ext
        simp [s]
      rw [htree]
      exact ht
    have hno : ∀ r : Fin ett.rounds, s.val ≤ r.val → r.val ≤ q.val →
        ¬ (ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ∧
          ett.series.data.chosenVertex r.succ = some w) := by
      intro r hr1 hr2 hpe
      obtain ⟨a, ha⟩ := (henumerates r).1 ⟨by omega, hpe.1, hpe.2⟩
      have hale : a.val ≤ (Fin.last p).val := by
        have hpval : (Fin.last p).val = p := by simp
        exact Fin.le_iff_val_le_val.mp (Fin.le_last a)
      by_cases hae : a = Fin.last p
      · have : r.val = (indices (Fin.last p)).val := by
          simpa [hae] using congrArg Fin.val ha.symm
        have hsval : s.val = (indices (Fin.last p)).val + 1 := by simp [s]
        omega
      · have hlt : a.val < (Fin.last p).val := by omega
        have hi := hincreasing a (Fin.last p) hlt
        have hridx : s.val ≤ (indices a).val := by
          simpa [ha] using hr1
        have hsval : s.val = (indices (Fin.last p)).val + 1 := by simp [s]
        omega
    have hs := HkuUnsupportedVertexColors G k ett.rounds e0 input ett.series
      q s w hsle hs_mem hno
    have hseq : s.castSucc = (indices (Fin.last p)).succ := by
      apply Fin.ext
      simp [s]
    rw [hseq] at hs
    exact hs

private theorem helper_branch_144.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds), (↑jSlot : ℕ) ≤ (↑q
        : ℕ) → (↑q : ℕ) + (1 : ℕ) = ett.rounds → ett.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → ett.series.data.chosenVertex q.succ = some terminalSupport →
        (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett terminalSupport hterminalSupport →
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc),
    ∀ (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds), (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices a) : ℕ) < (↑(indices b) : ℕ)) →
        (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r) → (
    ∀ (r : Fin ett.rounds), (↑r : ℕ) ≤ (↑q : ℕ) ∧ ett.series.data.kind r.succ = some
        TashkinovExtensionKind.PE ∧ ett.series.data.chosenVertex r.succ = some w ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r) →
    ∀ (gammaFirst deltaLast : Fin k), ett.series.data.gamma (indices (0 : Fin (p + (1 : ℕ)))).succ
        = some gammaFirst → ett.series.data.delta (indices (Fin.last p)).succ = some deltaLast →
    ∀ (sigma : PartialEdgeColoring E k), StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma → (
    ∀ (A B : TreeSequence G e0), TreeSequenceInitialSegment A B →
    ∀ v ∈ TreeSequenceVertexSet A, v ∈ TreeSequenceVertexSet B) → (
    ∀ (j : Fin (ett.rounds + (1 : ℕ))) (i : Fin ett.rounds), j = i.succ →
        TreeSequenceInitialSegment (ett.series.data.tree i.succ.castSucc) (ett.series.data.tree
        i.succ.succ)) → (
    ∀ (a b : Fin ett.rounds), (↑a : ℕ) ≤ (↑b : ℕ) →
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree a.succ.castSucc), v ∈ TreeSequenceVertexSet
        (ett.series.data.tree b.succ.castSucc)) → (
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), v ∈ TreeSequenceVertexSet
        T) → (
    ∀ (v : V) (hvT : v ∈ TreeSequenceVertexSet T), v ∈ TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc) → ETTFirstAppearanceIndex ett v hvT ≤ (↑jSlot : ℕ) + (1 : ℕ)) → (
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), MissingColors G sigma v =
        MissingColors G (ett.series.data.coloring q.succ) v) → (
    have storedPairs : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p + (1 : ℕ))) =>
        ett.series.data.stored (indices a).succ; MissingColors G (ett.series.data.coloring q.succ)
        w ∩ storedPairs = {deltaLast} ∧ MissingColors G (ett.series.data.coloring (indices
        (Fin.last p)).succ) w ∩ storedPairs = {deltaLast}) → MissingColors G
        (ett.series.data.coloring jSlot.castSucc) w = MissingColors G sigma w \ {deltaLast} ∪
        {gammaFirst} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q hjle
      hqTerminal hqKind hqVertex hjSlot w hw p indices hincreasing hclass henumerates gammaFirst
      deltaLast hgammaFirst hdeltaLast sigma hsigmaStable vertex_transfer next_segment
      stage_vertices final_transfer first_bound stable_vertex hinter
  have hclass0 := (hclass (indices 0)).2 ⟨0, rfl⟩
  simp only [ExtensionBaseSupportClass, ExtensionBaseActiveIndices, exists_and_left,
      Finset.mem_filter,
    Finset.mem_univ, true_and] at hclass0
  have hactive0 : indices 0 ∈ ExtensionBaseActiveIndices ett
      terminalSupport hterminalSupport := by
    unfold ExtensionBaseActiveIndices
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hclass0.1 with ⟨hlo, hkind, v0, hch, hv0, hfv⟩
    exact ⟨hlo, hkind, v0, hv0, hch, hfv⟩
  have hactive0' := hactive0
  simp only [ExtensionBaseActiveIndices, exists_and_left, Finset.mem_filter, Finset.mem_univ,
    true_and] at hactive0'
  have hchosen0 : ett.series.data.chosenVertex (indices 0).succ = some w :=
    hclass0.2
  obtain ⟨v0, hv0, hchosenV0, hfirstV0⟩ := hactive0'.2.2
  have hvT0 : w ∈ TreeSequenceVertexSet T := by
    have hvEq : v0 = w := by
      apply Option.some.inj
      exact hv0.symm.trans hchosen0
    simpa [hvEq] using hchosenV0
  have hfirstW : ETTFirstAppearanceIndex ett w hvT0 ≤
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport := by
    have hvEq : v0 = w := by
      apply Option.some.inj
      exact hv0.symm.trans hchosen0
    simpa [hvEq] using hfirstV0
  have hbound0 : ETTFirstAppearanceIndex ett w
      (by
        exact hvT0) ≤ jSlot.val + 1 := by
    have hb := hactive0'.1
    have heq := hjSlot
    have hle : ETTFirstAppearanceIndex ett w
        (by
          exact hvT0) ≤ (indices 0).val + 1 := by
        exact hfirstW.trans (by omega)
    omega
  have hstart := @helper_hstart_177 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett terminalSupport hterminalSupport jSlot q hjle hqTerminal hjSlot w p indices
      stage_vertices hclass0 v0 hchosenV0 hvT0 hbound0
  have hfirst := @helper_hfirst_227 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett terminalSupport hterminalSupport jSlot q hjle hqTerminal hjSlot w p indices
      hincreasing henumerates first_bound hclass0 hactive0' v0 hchosenV0 hvT0 hbound0 hstart
  have hlastinfo := (henumerates (indices (Fin.last p))).2 ⟨Fin.last p, rfl⟩
  have hlastmem := @helper_hlastmem_268 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett terminalSupport hterminalSupport jSlot q w p indices hclass0 v0 hchosenV0 hvT0
      hlastinfo
  have hlate := @helper_hlate_321 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett terminalSupport hterminalSupport jSlot q hjle hqTerminal hqKind hqVertex w hw p
      indices hincreasing henumerates deltaLast sigma hsigmaStable vertex_transfer next_segment
      final_transfer stable_vertex hinter hclass0 v0 hchosenV0 hvT0 hlastinfo hlastmem
  have htransport := SupportingPEMissingTransport G k ett.rounds p e0 input
      ett.series q w hw indices hincreasing henumerates gammaFirst deltaLast
      hgammaFirst hdeltaLast
  rw [hfirst]
  rw [hlate, ← stable_vertex w hw] at htransport
  exact htransport.1

private theorem helper_branch_230.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds), (↑jSlot : ℕ) ≤ (↑q
        : ℕ) → (↑q : ℕ) + (1 : ℕ) = ett.rounds → ett.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → ett.series.data.chosenVertex q.succ = some terminalSupport →
        (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett terminalSupport hterminalSupport →
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc),
    ∀ (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds), (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices a) : ℕ) < (↑(indices b) : ℕ)) →
        (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r) → (
    ∀ (r : Fin ett.rounds), (↑r : ℕ) ≤ (↑q : ℕ) ∧ ett.series.data.kind r.succ = some
        TashkinovExtensionKind.PE ∧ ett.series.data.chosenVertex r.succ = some w ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r) →
    ∀ (gammaFirst deltaLast : Fin k), ett.series.data.gamma (indices (0 : Fin (p + (1 : ℕ)))).succ
        = some gammaFirst → ett.series.data.delta (indices (Fin.last p)).succ = some deltaLast →
    ∀ (sigma : PartialEdgeColoring E k), StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma → (
    ∀ (A B : TreeSequence G e0), TreeSequenceInitialSegment A B →
    ∀ v ∈ TreeSequenceVertexSet A, v ∈ TreeSequenceVertexSet B) → (
    ∀ (j : Fin (ett.rounds + (1 : ℕ))) (i : Fin ett.rounds), j = i.succ →
        TreeSequenceInitialSegment (ett.series.data.tree i.succ.castSucc) (ett.series.data.tree
        i.succ.succ)) → (
    ∀ (a b : Fin ett.rounds), (↑a : ℕ) ≤ (↑b : ℕ) →
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree a.succ.castSucc), v ∈ TreeSequenceVertexSet
        (ett.series.data.tree b.succ.castSucc)) → (
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), v ∈ TreeSequenceVertexSet
        T) → (
    ∀ (v : V) (hvT : v ∈ TreeSequenceVertexSet T), v ∈ TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc) → ETTFirstAppearanceIndex ett v hvT ≤ (↑jSlot : ℕ) + (1 : ℕ)) → (
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), MissingColors G sigma v =
        MissingColors G (ett.series.data.coloring q.succ) v) →
    let storedPairs : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p + (1 : ℕ))) =>
        ett.series.data.stored (indices a).succ; MissingColors G sigma w ∩ storedPairs =
        {deltaLast} ∧ MissingColors G (ett.series.data.coloring jSlot.castSucc) w = MissingColors
        G sigma w \ {deltaLast} ∪ {gammaFirst} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q hjle
      hqTerminal hqKind hqVertex hjSlot w hw p indices hincreasing hclass henumerates gammaFirst
      deltaLast hgammaFirst hdeltaLast sigma hsigmaStable vertex_transfer next_segment
      stage_vertices final_transfer first_bound stable_vertex
  dsimp
  have hinter := SupportingPEStoredIntersection G k ett.rounds p e0 input
    ett.series q w hw indices hincreasing henumerates deltaLast hdeltaLast
  constructor
  · rw [stable_vertex w hw]
    exact hinter.1
  · exact @helper_branch_144 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett terminalSupport hterminalSupport jSlot q hjle hqTerminal hqKind
      hqVertex hjSlot w hw p indices hincreasing hclass henumerates gammaFirst deltaLast
      hgammaFirst hdeltaLast sigma hsigmaStable vertex_transfer next_segment stage_vertices
      final_transfer first_bound stable_vertex hinter
theorem ExtensionBaseClaimMissingColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (hjle : jSlot.val ≤ q.val)
    (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (hjSlot : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (w : V)
    (hw : w ∈ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc))
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (hincreasing : ∀ a b, a.val < b.val →
      (indices a).val < (indices b).val)
    (hclass : ∀ r : Fin ett.rounds,
      r ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ↔
        ∃ a : Fin (p + 1), indices a = r)
    (henumerates : ∀ r : Fin ett.rounds,
      (r.val ≤ q.val ∧
        ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ∧
        ett.series.data.chosenVertex r.succ = some w) ↔
      ∃ a : Fin (p + 1), indices a = r)
    (gammaFirst deltaLast : Fin k)
    (hgammaFirst : ett.series.data.gamma (indices 0).succ = some gammaFirst)
    (hdeltaLast : ett.series.data.delta
      (indices (Fin.last p)).succ = some deltaLast)
    (sigma : PartialEdgeColoring E k)
    (_ : IsProperEdgeColoring G sigma)
    (_ : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigma) :
    (∀ v : V,
      v ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      (∀ r : Fin ett.rounds,
        r ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
        ett.series.data.chosenVertex r.succ ≠ some v) →
      MissingColors G sigma v =
        MissingColors G (ett.series.data.coloring jSlot.castSucc) v) ∧
    (let storedPairs := Finset.univ.biUnion fun a : Fin (p + 1) =>
      ett.series.data.stored (indices a).succ
     MissingColors G sigma w ∩ storedPairs = {deltaLast} ∧
       MissingColors G (ett.series.data.coloring jSlot.castSucc) w =
         (MissingColors G sigma w \ {deltaLast}) ∪ {gammaFirst}) := by
  classical
  have vertex_transfer : ∀ (A B : TreeSequence G e0),
      TreeSequenceInitialSegment A B → ∀ v, v ∈ TreeSequenceVertexSet A →
      v ∈ TreeSequenceVertexSet B := by
    intro A B hseg v hv
    unfold TreeSequenceVertexSet at hv ⊢
    simp only [Finset.mem_image] at hv ⊢
    obtain ⟨i, hi, rfl⟩ := hv
    rcases hseg with ⟨hlen, hvertex, hedge⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, by simpa using hvertex i⟩
  have next_segment := TashkinovSeries.stepInitialSegment G k ett.rounds e0 input ett.series
  have stage_vertices : ∀ a b : Fin ett.rounds, a.val ≤ b.val → ∀ v,
      v ∈ TreeSequenceVertexSet (ett.series.data.tree a.succ.castSucc) →
      v ∈ TreeSequenceVertexSet (ett.series.data.tree b.succ.castSucc) := by
    have stage_aux : ∀ n : ℕ, ∀ a b : Fin ett.rounds,
        b.val - a.val = n → a.val ≤ b.val → ∀ v,
        v ∈ TreeSequenceVertexSet (ett.series.data.tree a.succ.castSucc) →
        v ∈ TreeSequenceVertexSet (ett.series.data.tree b.succ.castSucc) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro a b hgap hab v hv
        by_cases heq : a.val = b.val
        · have heq' : a = b := Fin.ext heq
          simpa [heq'] using hv
        · have alt : a.val < b.val := by omega
          let c : Fin ett.rounds := ⟨a.val + 1, by omega⟩
          have hcv0 := vertex_transfer _ _ (next_segment a.succ a rfl) v hv
          have hcv : v ∈ TreeSequenceVertexSet
              (ett.series.data.tree c.succ.castSucc) := by
            have hidx : c.succ.castSucc = a.succ.succ := by
              apply Fin.ext
              simp [c]
            rw [hidx]
            exact hcv0
          have cval : c.val = a.val + 1 := rfl
          have hlt : b.val - c.val < n := by omega
          have hcb : c.val ≤ b.val := by omega
          have hgap' : b.val - c.val = b.val - c.val := rfl
          exact ih (b.val - c.val) hlt c b hgap' hcb v hcv
    intro a b hab v hv
    exact stage_aux (b.val - a.val) a b rfl hab v hv
  have final_transfer : ∀ v, v ∈ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc) →
      v ∈ TreeSequenceVertexSet T := by
    intro v hv
    have hidx : q.succ.castSucc =
        (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp
      omega
    rw [hidx] at hv
    exact vertex_transfer _ _ ett.abovePenultimate v hv
  have first_bound : ∀ (v : V) (hvT : v ∈ TreeSequenceVertexSet T)
      (hv : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)),
      ETTFirstAppearanceIndex ett v hvT ≤ jSlot.val + 1 := by
    intro v hvT hv
    unfold ETTFirstAppearanceIndex
    dsimp
    have hmem : jSlot.castSucc ∈
        Finset.univ.filter (fun i =>
          v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc] using hv
    have hle := Finset.min'_le
      (Finset.univ.filter (fun i : Fin (ett.rounds + 1) =>
        v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)))
      jSlot.castSucc hmem
    have hnat := Fin.le_iff_val_le_val.mp hle
    rw [Fin.val_castSucc] at hnat
    convert Nat.succ_le_succ hnat using 1
  have stable_vertex :
    ∀ v, v ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) → MissingColors G sigma
        v = MissingColors G (ett.series.data.coloring q.succ) v := by
    intro v hv
    exact hsigmaStable.2 v hv
  refine ⟨?_, ?_⟩
  · intro v hv hno
    have unused : ∀ r : Fin ett.rounds, jSlot.val ≤ r.val → r.val ≤ q.val →
        ¬ (ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ∧
          ett.series.data.chosenVertex r.succ = some v) := by
      intro r hrj hrq hpe
      have hactive : r ∈ ExtensionBaseActiveIndices ett terminalSupport
          hterminalSupport := by
        unfold ExtensionBaseActiveIndices
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, hpe.1, ?_⟩
        · omega
        · have hvT := final_transfer v (stage_vertices jSlot q hjle v hv)
          refine ⟨v, hvT, ?_⟩
          exact ⟨hpe.2, by
            simpa [hjSlot] using
              (first_bound v (final_transfer v (stage_vertices jSlot q hjle v hv)) hv)⟩
      exact (hno r hactive) hpe.2
    have hu := HkuUnsupportedVertexColors G k ett.rounds e0 input ett.series
      q jSlot v hjle hv unused
    exact (stable_vertex v (stage_vertices jSlot q hjle v hv)).trans hu.symm
  · exact @helper_branch_230 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett terminalSupport hterminalSupport jSlot q hjle hqTerminal hqKind
      hqVertex hjSlot w hw p indices hincreasing hclass henumerates gammaFirst deltaLast
      hgammaFirst hdeltaLast sigma hsigmaStable vertex_transfer next_segment stage_vertices
      final_transfer first_bound stable_vertex
end GoldbergSeymour

end
