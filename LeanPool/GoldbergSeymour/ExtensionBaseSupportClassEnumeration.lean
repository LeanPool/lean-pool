/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClass

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# Extension Base Support Class Enumeration

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem ExtensionBaseSupportClassEnumeration_peVertex_63.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] {G :
    LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k} {T :
    TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k
    e0 input T generating) (_ : Fin ett.rounds) (w : V) (r : Fin ett.rounds),
    ett.series.data.kind r.succ = some TashkinovExtensionKind.PE →
    ett.series.data.chosenVertex r.succ = some w → w ∈ TreeSequenceVertexSet
    (ett.series.data.tree r.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett q w r hkind hvertex
  generalize targetEq : r.succ = target
  cases ett.series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero r targetEq).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have values := congrArg Fin.val targetEq
    simp at values
    have hi : i = r := by apply Fin.ext; omega
    subst i
    rw [currentKind] at hkind
    simp at hkind
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have values := congrArg Fin.val targetEq
    simp at values
    have hi : i = r := by apply Fin.ext; omega
    subst i
    rw [currentKind] at hkind
    simp at hkind
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have values := congrArg Fin.val targetEq
    simp at values
    have hi : i = r := by apply Fin.ext; omega
    subst i
    have vertexEq : choice.vertex = w :=
      Option.some.inj (currentVertex.symm.trans hvertex)
    simpa [vertexEq] using choice.vertexDefective.1

private theorem ExtensionBaseSupportClassEnumeration_nextSegment_239.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] {G :
    LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k} {T :
    TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k
    e0 input T generating), ∀ terminalSupport ∈ TreeSequenceVertexSet T, ∀ (_ : Fin
    ett.rounds) (w : V) (_ : Fin ett.rounds), ∀ v0 ∈ TreeSequenceVertexSet T, w ∈
    TreeSequenceVertexSet T → ∀ (r : Fin ett.rounds), TreeSequenceInitialSegment
    (ett.series.data.tree r.succ.castSucc) (ett.series.data.tree r.succ.succ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport q w r0 v0
      hv0Final hwFinal r
  generalize targetEq : r.succ = target
  cases ett.series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero r targetEq).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have values := congrArg Fin.val targetEq
    simp at values
    have hi : i = r := by apply Fin.ext; omega
    simpa [hi] using orderedExtension
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have values := congrArg Fin.val targetEq
    simp at values
    have hi : i = r := by apply Fin.ext; omega
    simpa [hi] using orderedExtension
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have values := congrArg Fin.val targetEq
    simp at values
    have hi : i = r := by apply Fin.ext; omega
    simpa [hi] using orderedExtension

theorem ExtensionBaseSupportClassEnumeration {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (hqTerminal : q.val + 1 = ett.rounds)
    (w : V)
    (hcommon : ∀ (s : Fin ett.rounds) (v : V)
      (hvFinal : v ∈ TreeSequenceVertexSet T),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      ett.series.data.chosenVertex s.succ = some v →
      ETTFirstAppearanceIndex ett v hvFinal =
        ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (hclassNonempty :
      (ExtensionBaseSupportClass ett terminalSupport hterminalSupport w).Nonempty) :
    ∃ (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds),
      w ∈ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc) ∧
      (∀ a b, a.val < b.val →
        (indices a).val < (indices b).val) ∧
      (∀ r : Fin ett.rounds,
        r ∈ ExtensionBaseSupportClass ett terminalSupport
              hterminalSupport w ↔
          ∃ a : Fin (p + 1), indices a = r) ∧
      ∀ r : Fin ett.rounds,
        (r.val ≤ q.val ∧
          ett.series.data.kind r.succ =
            some TashkinovExtensionKind.PE ∧
          ett.series.data.chosenVertex r.succ = some w) ↔
        ∃ a : Fin (p + 1), indices a = r := by
  classical
  have peVertex :
    ∀ (r : Fin ett.rounds), ett.series.data.kind r.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex r.succ = some w → w ∈ TreeSequenceVertexSet
        (ett.series.data.tree r.succ.castSucc) := by
    exact @ExtensionBaseSupportClassEnumeration_peVertex_63 V E inferInstance inferInstance
        inferInstance G k e0 input T generating ett q w
  have firstBound :
    ∀ (r : Fin ett.rounds) (hwFinal : w ∈ TreeSequenceVertexSet T), w ∈ TreeSequenceVertexSet
        (ett.series.data.tree r.succ.castSucc) → ETTFirstAppearanceIndex ett w hwFinal ≤ r.val + 1
  := by
    intro r hwFinal hw
    unfold ETTFirstAppearanceIndex
    dsimp
    have hmem : r.castSucc ∈
        Finset.univ.filter (fun i : Fin (ett.rounds + 1) =>
          w ∈ TreeSequenceVertexSet
            (ExtendedTashkinovLadderStage ett i)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc] using hw
    have hle := Finset.min'_le
      (Finset.univ.filter (fun i : Fin (ett.rounds + 1) =>
        w ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)))
      r.castSucc hmem
    have hnat := Fin.le_iff_val_le_val.mp hle
    rw [Fin.val_castSucc] at hnat
    convert Nat.succ_le_succ hnat using 1
  obtain ⟨r0, hr0Class⟩ := hclassNonempty
  have hr0Filter := hr0Class
  simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hr0Filter
  have hr0Active := hr0Filter.1
  have hr0Data := hr0Active
  simp only [ExtensionBaseActiveIndices, exists_and_left, Finset.mem_filter, Finset.mem_univ,
    true_and] at hr0Data
  obtain ⟨hr0Lower, hr0Kind, v0, hr0VertexV0, hv0Final, hv0First⟩ :=
    hr0Data
  have hv0Eq : v0 = w :=
    Option.some.inj (hr0VertexV0.symm.trans hr0Filter.2)
  have hwFinal : w ∈ TreeSequenceVertexSet T := by
    simpa [hv0Eq] using hv0Final
  have hfirstEq : ETTFirstAppearanceIndex ett w hwFinal =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport :=
    hcommon r0 w hwFinal hr0Active hr0Filter.2
  have classIff :
    ∀ r : Fin ett.rounds, r ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ↔
        r.val ≤ q.val ∧ ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ∧
        ett.series.data.chosenVertex r.succ = some w := by
    intro r
    constructor
    · intro hrClass
      have hrFilter := hrClass
      simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hrFilter
      have hrData := hrFilter.1
      simp only [ExtensionBaseActiveIndices, exists_and_left, Finset.mem_filter, Finset.mem_univ,
    true_and] at hrData
      exact ⟨by omega, hrData.2.1, hrFilter.2⟩
    · rintro ⟨hrq, hrKind, hrVertex⟩
      have hwStage := peVertex r hrKind hrVertex
      have hwFirst : ETTFirstAppearanceIndex ett w hwFinal ≤ r.val + 1 :=
        firstBound r hwFinal hwStage
      have hrActive : r ∈ ExtensionBaseActiveIndices ett terminalSupport
          hterminalSupport := by
        simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
          Finset.mem_univ, true_and]
        refine ⟨?_, hrKind, w, hwFinal, hrVertex, ?_⟩
        · rw [← hfirstEq]
          exact hwFirst
        · exact hfirstEq.le
      simp only [ExtensionBaseSupportClass, Finset.mem_filter]
      exact ⟨hrActive, hrVertex⟩
  let supportClass :=
    ExtensionBaseSupportClass ett terminalSupport hterminalSupport w
  let p := supportClass.card - 1
  have supportCard : supportClass.card = p + 1 := by
    have hpositive : 0 < supportClass.card :=
      Finset.card_pos.mpr ⟨r0, by simpa [supportClass] using hr0Class⟩
    dsimp [p]
    omega
  let sorted := supportClass.toList.insertionSort (· ≤ ·)
  have sortedLength : sorted.length = p + 1 := by
    simp [sorted, List.length_insertionSort, Finset.length_toList,
      supportCard]
  let indices : Fin (p + 1) → Fin ett.rounds := fun a =>
    sorted.get (Fin.cast sortedLength.symm a)
  have sortedPairwise : sorted.Pairwise (· ≤ ·) := by
    exact List.pairwise_insertionSort (· ≤ ·) supportClass.toList
  have sortedNodup : sorted.Nodup := by
    have hperm := List.perm_insertionSort (· ≤ ·) supportClass.toList
    exact hperm.nodup_iff.mpr supportClass.nodup_toList
  have indicesIncreasing : ∀ a b, a.val < b.val →
      (indices a).val < (indices b).val := by
    intro a b hab
    let aa : Fin sorted.length := Fin.cast sortedLength.symm a
    let bb : Fin sorted.length := Fin.cast sortedLength.symm b
    have hab' : aa < bb := by
      change a.val < b.val
      exact hab
    have hle : sorted.get aa ≤ sorted.get bb :=
      sortedPairwise.rel_get_of_lt hab'
    have hne : sorted.get aa ≠ sorted.get bb := by
      intro heq
      have habEq : aa = bb := sortedNodup.get_inj_iff.mp heq
      have : a = b := by
        apply Fin.ext
        simpa [aa, bb] using congrArg Fin.val habEq
      subst b
      omega
    have hlt : sorted.get aa < sorted.get bb := lt_of_le_of_ne hle hne
    simpa [indices, aa, bb] using hlt
  have indicesEnumerate : ∀ r : Fin ett.rounds,
      r ∈ supportClass ↔ ∃ a : Fin (p + 1), indices a = r := by
    intro r
    constructor
    · intro hr
      have hrList : r ∈ supportClass.toList :=
        Finset.mem_toList.mpr hr
      have hrSorted : r ∈ sorted := by
        have hperm :=
          List.perm_insertionSort (· ≤ ·) supportClass.toList
        exact hperm.mem_iff.mpr hrList
      obtain ⟨a, ha⟩ := List.get_of_mem hrSorted
      refine ⟨Fin.cast sortedLength a, ?_⟩
      simpa [indices] using ha
    · rintro ⟨a, rfl⟩
      have hiSorted : indices a ∈ sorted := by
        exact List.get_mem sorted (Fin.cast sortedLength.symm a)
      have hiList : indices a ∈ supportClass.toList := by
        have hperm :=
          List.perm_insertionSort (· ≤ ·) supportClass.toList
        exact hperm.mem_iff.mp hiSorted
      exact Finset.mem_toList.mp hiList
  have nextSegment :
    ∀ r : Fin ett.rounds, TreeSequenceInitialSegment (ett.series.data.tree r.succ.castSucc)
        (ett.series.data.tree r.succ.succ) := by
    exact @ExtensionBaseSupportClassEnumeration_nextSegment_239 V E inferInstance inferInstance
        inferInstance G k e0 input T generating ett terminalSupport hterminalSupport q w r0 v0
        hv0Final hwFinal
  have seriesVertexLater :
    ∀ (a b : Fin ett.rounds), a.val ≤ b.val →
    ∀ x, x ∈ TreeSequenceVertexSet (ett.series.data.tree a.succ.castSucc) → x ∈
        TreeSequenceVertexSet (ett.series.data.tree b.succ.castSucc) := by
    intro a b hab x hxa
    induction distance : b.val - a.val using Nat.strong_induction_on
        generalizing a b with
    | h n ih =>
      by_cases equal : a.val = b.val
      · have : a = b := Fin.ext equal
        simpa [this] using hxa
      · have stepLe : a.val + 1 ≤ b.val := by omega
        let mid : Fin ett.rounds := ⟨a.val + 1, by omega⟩
        have midVal : mid.val = a.val + 1 := rfl
        have hxm : x ∈ TreeSequenceVertexSet
            (ett.series.data.tree mid.succ.castSucc) := by
          have treeEq : mid.succ.castSucc = a.succ.succ := by
            apply Fin.ext
            simp [mid]
          rw [treeEq]
          exact TreeSequenceInitialSegmentVertexSetSubset
            (nextSegment a) hxa
        have hrest := ih (b.val - mid.val) (by omega) mid b (by omega) hxm
          (by simp)
        exact hrest
  have hr0Terminal := (classIff r0).mp hr0Class
  have hwCurrent : w ∈ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc) :=
    seriesVertexLater r0 q hr0Terminal.1 w
      (peVertex r0 hr0Terminal.2.1 hr0Terminal.2.2)
  refine ⟨p, indices, hwCurrent, indicesIncreasing, ?_, ?_⟩
  · intro r
    simpa [supportClass] using indicesEnumerate r
  · intro r
    have hclassRange :
        r ∈ ExtensionBaseSupportClass ett terminalSupport
              hterminalSupport w ↔
          ∃ a : Fin (p + 1), indices a = r := by
      simpa [supportClass] using indicesEnumerate r
    exact (classIff r).symm.trans hclassRange

end GoldbergSeymour

end
