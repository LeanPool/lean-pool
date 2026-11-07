/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesTreeFacts

public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.ExtensionRulesPEFirstAppearanceBound
public import LeanPool.GoldbergSeymour.StableColoringBeforeVertex
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# Extension Rules Earlier Indices

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_supportInFollowingTree_188.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (q : Fin ett.rounds) (v : V), ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v → v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.succ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett this q v hkind hvertex
  generalize hslot : q.succ = slot
  cases ett.series.certified slot with
  | initial => exact (Fin.succ_ne_zero q hslot).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hbad : some TashkinovExtensionKind.SE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [hslot] using hkind)
    cases hbad
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hbad : some TashkinovExtensionKind.RE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [hslot] using hkind)
    cases hbad
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hi : i = q := by
      apply Fin.ext
      simpa using (congrArg Fin.val hslot).symm
    subst i
    have hvchoice : choice.vertex = v :=
      Option.some.inj (currentVertex.symm.trans (by simpa [hslot] using hvertex))
    apply TreeSequenceInitialSegmentVertexSetSubset orderedExtension
    simpa [hvchoice] using choice.vertexDefective.1

private theorem helper_ladderStageEq_229.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) {T' : TreeSequence G e0}
    {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input T'
    generating') (s : ℕ) (hs : lower.rounds = s) (hsn : s < ett.rounds), T' =
    ett.series.data.tree (⟨s + (1 : ℕ), Decidable.byContradiction fun (a : ¬s + (1 : ℕ) <
    ett.rounds + (2 : ℕ)) => by omega⟩ : Fin (ett.rounds + (2 : ℕ))) → (∀ (i : Fin
    (lower.rounds + (2 : ℕ))), lower.series.data.tree i = ett.series.data.tree (Fin.castLE
    (Decidable.byContradiction fun (a : ¬lower.rounds + (2 : ℕ) ≤ ett.rounds + (2 : ℕ)) => by
    omega) i)) → ∀ (i : Fin (lower.rounds + (1 : ℕ))), ExtendedTashkinovLadderStage lower i =
    ExtendedTashkinovLadderStage ett (⟨(↑i : ℕ), Decidable.byContradiction fun (a : ¬(↑i : ℕ)
    < ett.rounds + (1 : ℕ)) => by omega⟩ : Fin (ett.rounds + (1 : ℕ))) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett T' generating' lower s hs hsn hdisplay htree i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · have hdisplay' : T' = ett.series.data.tree
        ⟨lower.rounds + 1, by omega⟩ := by
      simpa [hs] using hdisplay
    rw [show ExtendedTashkinovLadderStage lower (Fin.last lower.rounds) = T' by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    have hidx : (⟨(Fin.last lower.rounds).val, by omega⟩ :
        Fin (ett.rounds + 1)) =
        (⟨lower.rounds, by omega⟩ : Fin ett.rounds).castSucc := by
      apply Fin.ext
      simp
    rw [hidx]
    rw [show ExtendedTashkinovLadderStage ett
        (⟨lower.rounds, by omega⟩ : Fin ett.rounds).castSucc =
        ett.series.data.tree
          (⟨lower.rounds, by omega⟩ : Fin ett.rounds).succ.castSucc by
      unfold ExtendedTashkinovLadderStage
      exact @Fin.lastCases_castSucc ett.rounds
        (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) T
        (fun j => ett.series.data.tree j.succ.castSucc)
        (⟨lower.rounds, by omega⟩ : Fin ett.rounds)]
    exact hdisplay'.trans (congrArg ett.series.data.tree (by
      apply Fin.ext
      simp))
  · rw [show ExtendedTashkinovLadderStage lower a.castSucc =
        lower.series.data.tree a.succ.castSucc by
      unfold ExtendedTashkinovLadderStage
      exact @Fin.lastCases_castSucc lower.rounds
        (fun _ : Fin (lower.rounds + 1) => TreeSequence G e0) T'
        (fun j => lower.series.data.tree j.succ.castSucc) a]
    have hidx : (⟨(a.castSucc).val, by omega⟩ : Fin (ett.rounds + 1)) =
        (⟨a.val, by omega⟩ : Fin ett.rounds).castSucc := by
      apply Fin.ext
      rfl
    rw [hidx]
    rw [show ExtendedTashkinovLadderStage ett
        (⟨a.val, by omega⟩ : Fin ett.rounds).castSucc =
        ett.series.data.tree
          (⟨a.val, by omega⟩ : Fin ett.rounds).succ.castSucc by
      unfold ExtendedTashkinovLadderStage
      exact @Fin.lastCases_castSucc ett.rounds
        (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) T
        (fun j => ett.series.data.tree j.succ.castSucc)
        (⟨a.val, by omega⟩ : Fin ett.rounds)]
    exact (htree a.succ.castSucc).trans (congrArg ett.series.data.tree (by
      apply Fin.ext
      rfl))

private theorem helper_firstAppearanceEq_290.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), (0 : ℕ) < ett.rounds →
    let _ : DecidableEq V := Classical.decEq V; (
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating') (s : ℕ) (hs : lower.rounds = s) (hsn :
        s < ett.rounds), T' = ett.series.data.tree (⟨s + (1 : ℕ), Decidable.byContradiction fun (a
        : ¬s + (1 : ℕ) < ett.rounds + (2 : ℕ)) =>
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) → (
    ∀ (i : Fin (lower.rounds + (2 : ℕ))), lower.series.data.tree i = ett.series.data.tree
        (Fin.castLE (Decidable.byContradiction fun (a : ¬lower.rounds + (2 : ℕ) ≤ ett.rounds + (2
        : ℕ)) =>
    by omega
    ) i)) →
    ∀ (i : Fin (lower.rounds + (1 : ℕ))), ExtendedTashkinovLadderStage lower i =
        ExtendedTashkinovLadderStage ett (⟨(↑i : ℕ), Decidable.byContradiction fun (a : ¬(↑i : ℕ)
        < ett.rounds + (1 : ℕ)) =>
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) →
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating') (s : ℕ) (hs : lower.rounds = s) (hsn :
        s < ett.rounds), T' = ett.series.data.tree (⟨s + (1 : ℕ), Decidable.byContradiction fun (a
        : ¬s + (1 : ℕ) < ett.rounds + (2 : ℕ)) =>
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) → (
    ∀ (i : Fin (lower.rounds + (2 : ℕ))), lower.series.data.tree i = ett.series.data.tree
        (Fin.castLE (Decidable.byContradiction fun (a : ¬lower.rounds + (2 : ℕ) ≤ ett.rounds + (2
        : ℕ)) =>
    by omega
    ) i)) →
    ∀ (v : V) (hvLower : v ∈ TreeSequenceVertexSet T') (hvFinal : v ∈ TreeSequenceVertexSet T),
        ETTFirstAppearanceIndex ett v hvFinal ≤ s → ETTFirstAppearanceIndex lower v hvLower =
        ETTFirstAppearanceIndex ett v hvFinal := by
  classical
  intro V E _ _ _ G k e0 input T generating ett _ this ladderStageEq T' generating' lower s hs
      hsn hdisplay htree v hvLower hvFinal hbound
  have hladders := ladderStageEq lower s hs hsn hdisplay htree
  unfold ETTFirstAppearanceIndex at hbound ⊢
  dsimp at hbound ⊢
  let lowerCandidates : Finset (Fin (lower.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage lower i)
  let fullCandidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hlowerNonempty : lowerCandidates.Nonempty := by
    refine ⟨Fin.last lower.rounds, ?_⟩
    simp only [lowerCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage lower (Fin.last lower.rounds) = T' by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    exact hvLower
  have hfullNonempty : fullCandidates.Nonempty := by
    refine ⟨Fin.last ett.rounds, ?_⟩
    simp only [fullCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett (Fin.last ett.rounds) = T by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    exact hvFinal
  let ml := lowerCandidates.min' hlowerNonempty
  let mf := fullCandidates.min' hfullNonempty
  have hmfBound : mf.val < lower.rounds + 1 := by
    have hb : mf.val + 1 ≤ s := by
      dsimp [mf]
      convert hbound using 1
    omega
  let mfLower : Fin (lower.rounds + 1) := ⟨mf.val, hmfBound⟩
  have hmfMem : mfLower ∈ lowerCandidates := by
    simp only [lowerCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hladders mfLower]
    have hmem := Finset.min'_mem fullCandidates hfullNonempty
    simpa [fullCandidates, mfLower] using hmem
  have hmlMemFull : (⟨ml.val, by omega⟩ : Fin (ett.rounds + 1)) ∈
      fullCandidates := by
    simp only [fullCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hladders ml]
    exact (Finset.mem_filter.mp (Finset.min'_mem lowerCandidates
      hlowerNonempty)).2
  have hleOne := Finset.min'_le lowerCandidates mfLower hmfMem
  have hleTwo := Finset.min'_le fullCandidates
    (⟨ml.val, by omega⟩ : Fin (ett.rounds + 1)) hmlMemFull
  have hvals : ml.val = mf.val := by
    apply le_antisymm
    · exact Fin.le_iff_val_le_val.mp hleOne
    · exact Fin.le_iff_val_le_val.mp hleTwo
  change (lowerCandidates.min' _).val + 1 =
    (fullCandidates.min' _).val + 1
  simpa [ml, mf] using congrArg (fun x : ℕ => x + 1) hvals

private theorem helper_beforeEqOfSegment_356.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (_ : ExtendedTashkinovTree G k
        e0 input T generating),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B →
    ∀ (v : V) (hvA : v ∈ TreeSequenceVertexSet A) (hvB : v ∈ TreeSequenceVertexSet B),
        TreeVerticesBefore A v hvA = TreeVerticesBefore B v hvB := by
  classical
  intro V E _ _ _ G k e0 input T generating ett this A B hAB v hvA hvB
  rcases hAB with ⟨hlen, hvertices, hedges⟩
  apply Finset.ext
  intro w
  constructor
  · intro hw
    rcases Finset.mem_filter.mp hw with ⟨hwA, iw, iv, hiw, hiv, hlt⟩
    apply Finset.mem_filter.mpr
    refine ⟨TreeSequenceInitialSegmentVertexSetSubset
      ⟨hlen, hvertices, hedges⟩ hwA, ?_⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) iw,
      Fin.castLE (Nat.succ_le_succ hlen) iv,
      (hvertices iw).trans hiw, (hvertices iv).trans hiv, hlt⟩
  · intro hw
    rcases Finset.mem_filter.mp hw with ⟨hwB, iw, iv, hiw, hiv, hlt⟩
    rcases Finset.mem_image.mp hvA with ⟨av, havU, hav⟩
    let avB := Fin.castLE (Nat.succ_le_succ hlen) av
    have hivav : iv = avB := by
      apply B.vertex_injective
      exact hiv.trans ((hvertices av).trans hav).symm
    have hiBound : iw.val < A.length + 1 := by
      rw [hivav] at hlt
      simp [avB] at hlt
      omega
    let iwA : Fin (A.length + 1) := ⟨iw.val, hiBound⟩
    have hiwCast : Fin.castLE (Nat.succ_le_succ hlen) iwA = iw := by
      apply Fin.ext
      rfl
    have hwA : w ∈ TreeSequenceVertexSet A := by
      apply Finset.mem_image.mpr
      refine ⟨iwA, Finset.mem_univ _, ?_⟩
      exact (hvertices iwA).symm.trans (by simpa [hiwCast] using hiw)
    apply Finset.mem_filter.mpr
    refine ⟨hwA, iwA, av, ?_, hav, ?_⟩
    · exact (hvertices iwA).symm.trans (by simpa [hiwCast] using hiw)
    · rw [hivav] at hlt
      simpa [iwA, avB] using hlt

private theorem helper_branch_399.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett → (
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating'), (0 : ℕ) < lower.rounds → lower.rounds
        < ett.rounds → MaximumProperty lower → (
    ∀ (q : Fin lower.rounds) (v : V), lower.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → lower.series.data.chosenVertex q.succ = some v →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (j : Fin (lower.rounds + (1 : ℕ))),
        ETTFirstAppearanceIndex lower v hvFinal = (↑j : ℕ) + (1 : ℕ) →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (lower.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        lower.series.data q.succ) (lower.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T' v hvFinal (TashkinovStoredColors lower.series.data j)
        (lower.series.data.coloring j) sigma ∧ ((0 : ℕ) < (↑j : ℕ) → StableColoring
        (lower.series.data.tree j.castSucc) (TashkinovStoredColors lower.series.data j)
        (lower.series.data.coloring j) sigma)) ∧
    ∀ (q r : Fin lower.rounds) (vq vr : V), q ≠ r → vq ≠ vr → lower.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → lower.series.data.kind r.succ = some TashkinovExtensionKind.PE
        → lower.series.data.chosenVertex q.succ = some vq → lower.series.data.chosenVertex r.succ
        = some vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T') (hvr : vr ∈ TreeSequenceVertexSet T'),
        ETTFirstAppearanceIndex lower vq hvq = ETTFirstAppearanceIndex lower vr hvr → Disjoint
        (lower.series.data.stored q.succ) (lower.series.data.stored r.succ)) →
    let _ : DecidableEq V := Classical.decEq V; (
    ∀ (a : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hround : a ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
        Decidable.byContradiction fun (a_1 : ¬a < ett.rounds + (2 : ℕ)) =>
    by
                          omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) T) → (
    ∀ (q : Fin ett.rounds) (v : V), ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v → v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.succ)) → (
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating') (s : ℕ) (hs : lower.rounds = s) (hsn :
        s < ett.rounds), T' = ett.series.data.tree (⟨s + (1 : ℕ), Decidable.byContradiction fun (a
        : ¬s + (1 : ℕ) < ett.rounds + (2 : ℕ)) =>
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) → (
    ∀ (i : Fin (lower.rounds + (2 : ℕ))), lower.series.data.tree i = ett.series.data.tree
        (Fin.castLE (Decidable.byContradiction fun (a : ¬lower.rounds + (2 : ℕ) ≤ ett.rounds + (2
        : ℕ)) =>
    by
                                omega
    ) i)) →
    ∀ (v : V) (hvLower : v ∈ TreeSequenceVertexSet T') (hvFinal : v ∈ TreeSequenceVertexSet T),
        ETTFirstAppearanceIndex ett v hvFinal ≤ s → ETTFirstAppearanceIndex lower v hvLower =
        ETTFirstAppearanceIndex ett v hvFinal) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B →
    ∀ (v : V) (hvA : v ∈ TreeSequenceVertexSet A) (hvB : v ∈ TreeSequenceVertexSet B),
        TreeVerticesBefore A v hvA = TreeVerticesBefore B v hvB) →
    ∀ (q : Fin ett.rounds) (v : V), q.succ ≠ Fin.last ett.rounds → ett.series.data.kind q.succ =
        some TashkinovExtensionKind.PE → ett.series.data.chosenVertex q.succ = some v →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (j : Fin (ett.rounds + (1 : ℕ))),
        ETTFirstAppearanceIndex ett v hvFinal = (↑j : ℕ) + (1 : ℕ) →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T v hvFinal (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma ∧ ((0 : ℕ) < (↑j : ℕ) → StableColoring
        (ett.series.data.tree j.castSucc) (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hLowerThree this stageToT
      supportInFollowingTree firstAppearanceEq beforeEqOfSegment q v hqNotLast hkind hvertex
      hvFinal j hfirst sigma hproper hone hstable
  let s := q.val + 1
  have hsPositive : 1 ≤ s := by simp [s]
  have hsBefore : s < ett.rounds := by
    have hle : s ≤ ett.rounds := by omega
    have hne : s ≠ ett.rounds := by
      intro heq
      apply hqNotLast
      apply Fin.ext
      simpa [s] using heq
    omega
  obtain ⟨lower, hr, hmax, htree, hdata⟩ :=
    CertifiedETTRestriction G k e0 input T generating ett hMP s
      hsPositive hsBefore
  have hsupportFull := supportInFollowingTree q v hkind hvertex
  have hvLower : v ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨s + 1, by omega⟩) := by
    have hidx : q.succ.succ =
        (⟨s + 1, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp [s]
    simpa [hidx] using hsupportFull
  have hbound := ExtensionRulesPEFirstAppearanceBound G k e0 input T
    generating ett q v hkind hvertex hvFinal
  have hfirstEq := firstAppearanceEq lower s hr hsBefore rfl htree v
    hvLower hvFinal hbound
  let qLower : Fin lower.rounds := ⟨q.val, by omega⟩
  let jLower : Fin (lower.rounds + 1) := ⟨j.val, by omega⟩
  have hqSlot : Fin.castLE (by omega) qLower.succ = q.succ := by
    apply Fin.ext
    rfl
  have hjSlot : Fin.castLE (by omega) jLower = j := by
    apply Fin.ext
    rfl
  have hkindLower : lower.series.data.kind qLower.succ =
      some TashkinovExtensionKind.PE := by
    rw [(hdata qLower.succ).2.2.2.1, hqSlot]
    exact hkind
  have hvertexLower : lower.series.data.chosenVertex qLower.succ = some v := by
    rw [(hdata qLower.succ).2.2.2.2.1, hqSlot]
    exact hvertex
  have hfirstLower : ETTFirstAppearanceIndex lower v hvLower =
      jLower.val + 1 := by
    rw [hfirstEq, hfirst]
  have hstableLower : StableColoring
      (lower.series.data.tree qLower.succ.castSucc)
      (TashkinovStoredColors lower.series.data qLower.succ)
      (lower.series.data.coloring qLower.succ) sigma := by
    have htreeSlot := htree qLower.succ.castSucc
    have htreeIndex : Fin.castLE (by omega) qLower.succ.castSucc =
        q.succ.castSucc := by
      apply Fin.ext
      rfl
    have hcolor := (hdata qLower.succ).1
    have hstored := (hdata qLower.succ).2.2.2.2.2.2.2.2.1
    rw [htreeSlot, htreeIndex, hcolor, hstored, hqSlot]
    exact hstable
  have hlower := hLowerThree lower (by omega) (by omega) hmax
  have hresult := hlower.1 qLower v hkindLower hvertexLower hvLower
    jLower hfirstLower sigma hproper hone hstableLower
  have hdisplayToT : TreeSequenceInitialSegment
      (ett.series.data.tree ⟨s + 1, by omega⟩) T :=
    stageToT (s + 1) (by omega) (by omega)
  have hbefore := beforeEqOfSegment hdisplayToT v hvLower hvFinal
  have hjColor := (hdata jLower).1
  have hjStored := (hdata jLower).2.2.2.2.2.2.2.2.1
  have hbeforeFinal : StableColoringBeforeVertex T v hvFinal
      (TashkinovStoredColors ett.series.data j)
      (ett.series.data.coloring j) sigma := by
    rw [← hjSlot, ← hjColor, ← hjStored]
    unfold StableColoringBeforeVertex at hresult ⊢
    simpa [hbefore] using hresult.1
  refine ⟨hbeforeFinal, ?_⟩
  intro hjPositive
  have hjTree := htree jLower.castSucc
  have hjTreeSlot : Fin.castLE (by omega) jLower.castSucc = j.castSucc := by
    apply Fin.ext
    rfl
  have hjResult := hresult.2 (by simpa [jLower] using hjPositive)
  rw [hjTree, hjTreeSlot, hjColor, hjStored, hjSlot] at hjResult
  exact hjResult

private theorem helper_branch_480.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett → (
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating'), (0 : ℕ) < lower.rounds → lower.rounds
        < ett.rounds → MaximumProperty lower → (
    ∀ (q : Fin lower.rounds) (v : V), lower.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → lower.series.data.chosenVertex q.succ = some v →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (j : Fin (lower.rounds + (1 : ℕ))),
        ETTFirstAppearanceIndex lower v hvFinal = (↑j : ℕ) + (1 : ℕ) →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (lower.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        lower.series.data q.succ) (lower.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T' v hvFinal (TashkinovStoredColors lower.series.data j)
        (lower.series.data.coloring j) sigma ∧ ((0 : ℕ) < (↑j : ℕ) → StableColoring
        (lower.series.data.tree j.castSucc) (TashkinovStoredColors lower.series.data j)
        (lower.series.data.coloring j) sigma)) ∧
    ∀ (q r : Fin lower.rounds) (vq vr : V), q ≠ r → vq ≠ vr → lower.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → lower.series.data.kind r.succ = some TashkinovExtensionKind.PE
        → lower.series.data.chosenVertex q.succ = some vq → lower.series.data.chosenVertex r.succ
        = some vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T') (hvr : vr ∈ TreeSequenceVertexSet T'),
        ETTFirstAppearanceIndex lower vq hvq = ETTFirstAppearanceIndex lower vr hvr → Disjoint
        (lower.series.data.stored q.succ) (lower.series.data.stored r.succ)) →
    let _ : DecidableEq V := Classical.decEq V; (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
        Decidable.byContradiction fun (a_1 : ¬a < ett.rounds + (2 : ℕ)) =>
    by
                          omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b, Decidable.byContradiction fun (a_1
        : ¬b < ett.rounds + (2 : ℕ)) =>
    by
                          omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) → (
    ∀ (q : Fin ett.rounds) (v : V), ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v → v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.succ)) → (
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating') (s : ℕ) (hs : lower.rounds = s) (hsn :
        s < ett.rounds), T' = ett.series.data.tree (⟨s + (1 : ℕ), Decidable.byContradiction fun (a
        : ¬s + (1 : ℕ) < ett.rounds + (2 : ℕ)) =>
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) → (
    ∀ (i : Fin (lower.rounds + (2 : ℕ))), lower.series.data.tree i = ett.series.data.tree
        (Fin.castLE (Decidable.byContradiction fun (a : ¬lower.rounds + (2 : ℕ) ≤ ett.rounds + (2
        : ℕ)) =>
    by
                                omega
    ) i)) →
    ∀ (v : V) (hvLower : v ∈ TreeSequenceVertexSet T') (hvFinal : v ∈ TreeSequenceVertexSet T),
        ETTFirstAppearanceIndex ett v hvFinal ≤ s → ETTFirstAppearanceIndex lower v hvLower =
        ETTFirstAppearanceIndex ett v hvFinal) →
    ∀ (q r : Fin ett.rounds) (vq vr : V), q.succ ≠ Fin.last ett.rounds → r.succ ≠ Fin.last
        ett.rounds → q ≠ r → vq ≠ vr → ett.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → ett.series.data.kind r.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some vq → ett.series.data.chosenVertex r.succ = some
        vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T) (hvr : vr ∈ TreeSequenceVertexSet T),
        ETTFirstAppearanceIndex ett vq hvq = ETTFirstAppearanceIndex ett vr hvr → Disjoint
        (ett.series.data.stored q.succ) (ett.series.data.stored r.succ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hLowerThree this stageToStage
      supportInFollowingTree firstAppearanceEq q r vq vr hqNotLast hrNotLast hqr hvqr hqKind
      hrKind hqVertex hrVertex hvq hvr hfirst
  let s := max (q.val + 1) (r.val + 1)
  have hsPositive : 1 ≤ s := by simp [s]
  have hqBefore : q.val + 1 < ett.rounds := by
    have hle : q.val + 1 ≤ ett.rounds := by omega
    have hne : q.val + 1 ≠ ett.rounds := by
      intro heq
      apply hqNotLast
      apply Fin.ext
      simpa using heq
    omega
  have hrBefore : r.val + 1 < ett.rounds := by
    have hle : r.val + 1 ≤ ett.rounds := by omega
    have hne : r.val + 1 ≠ ett.rounds := by
      intro heq
      apply hrNotLast
      apply Fin.ext
      simpa using heq
    omega
  have hsBefore : s < ett.rounds := by simp [s]; omega
  obtain ⟨lower, hround, hmax, htree, hdata⟩ :=
    CertifiedETTRestriction G k e0 input T generating ett hMP s
      hsPositive hsBefore
  have hvqFull : vq ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨s + 1, by omega⟩) := by
    have hv0 := supportInFollowingTree q vq hqKind hqVertex
    have hseg : TreeSequenceInitialSegment
        (ett.series.data.tree ⟨q.val + 2, by omega⟩)
        (ett.series.data.tree ⟨s + 1, by omega⟩) := by
      exact stageToStage (q.val + 2) (s + 1) (by omega) (by
        simp [s]) (by omega)
    apply TreeSequenceInitialSegmentVertexSetSubset hseg
    have hidx : q.succ.succ =
        (⟨q.val + 2, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      rfl
    simpa [hidx] using hv0
  have hvrFull : vr ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨s + 1, by omega⟩) := by
    have hv0 := supportInFollowingTree r vr hrKind hrVertex
    have hseg : TreeSequenceInitialSegment
        (ett.series.data.tree ⟨r.val + 2, by omega⟩)
        (ett.series.data.tree ⟨s + 1, by omega⟩) := by
      exact stageToStage (r.val + 2) (s + 1) (by omega) (by
        simp [s]) (by omega)
    apply TreeSequenceInitialSegmentVertexSetSubset hseg
    have hidx : r.succ.succ =
        (⟨r.val + 2, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      rfl
    simpa [hidx] using hv0
  have hqBound := ExtensionRulesPEFirstAppearanceBound G k e0 input T
    generating ett q vq hqKind hqVertex hvq
  have hrBound := ExtensionRulesPEFirstAppearanceBound G k e0 input T
    generating ett r vr hrKind hrVertex hvr
  have hqFirst := firstAppearanceEq lower s hround hsBefore rfl htree vq
    hvqFull hvq (hqBound.trans (by simp [s]))
  have hrFirst := firstAppearanceEq lower s hround hsBefore rfl htree vr
    hvrFull hvr (hrBound.trans (by simp [s]))
  let qLower : Fin lower.rounds := ⟨q.val, by omega⟩
  let rLower : Fin lower.rounds := ⟨r.val, by omega⟩
  have hqSlot : Fin.castLE (by omega) qLower.succ = q.succ := by
    apply Fin.ext
    rfl
  have hrSlot : Fin.castLE (by omega) rLower.succ = r.succ := by
    apply Fin.ext
    rfl
  have hqKindLower : lower.series.data.kind qLower.succ =
      some TashkinovExtensionKind.PE := by
    rw [(hdata qLower.succ).2.2.2.1, hqSlot]
    exact hqKind
  have hrKindLower : lower.series.data.kind rLower.succ =
      some TashkinovExtensionKind.PE := by
    rw [(hdata rLower.succ).2.2.2.1, hrSlot]
    exact hrKind
  have hqVertexLower : lower.series.data.chosenVertex qLower.succ = some vq := by
    rw [(hdata qLower.succ).2.2.2.2.1, hqSlot]
    exact hqVertex
  have hrVertexLower : lower.series.data.chosenVertex rLower.succ = some vr := by
    rw [(hdata rLower.succ).2.2.2.2.1, hrSlot]
    exact hrVertex
  have hqrLower : qLower ≠ rLower := by
    intro heq
    apply hqr
    apply Fin.ext
    have hval : qLower.val = rLower.val := congrArg Fin.val heq
    simpa [qLower, rLower] using hval
  have hfirstLower : ETTFirstAppearanceIndex lower vq hvqFull =
      ETTFirstAppearanceIndex lower vr hvrFull := by
    rw [hqFirst, hrFirst]
    exact hfirst
  have hlower := hLowerThree lower (by omega) (by omega) hmax
  have hdisjoint := hlower.2 qLower rLower vq vr hqrLower hvqr
    hqKindLower hrKindLower hqVertexLower hrVertexLower hvqFull hvrFull
    hfirstLower
  have hqStored := (hdata qLower.succ).2.1
  have hrStored := (hdata rLower.succ).2.1
  rw [hqStored, hrStored, hqSlot, hrSlot] at hdisjoint
  exact hdisjoint

theorem ExtensionRulesEarlierIndices {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (_ : 0 < ett.rounds)
    (hLowerThree : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      ((∀ (q : Fin lower.rounds) (v : V),
          lower.series.data.kind q.succ =
              some TashkinovExtensionKind.PE →
          lower.series.data.chosenVertex q.succ = some v →
          ∀ hvFinal : v ∈ TreeSequenceVertexSet T',
          ∀ j : Fin (lower.rounds + 1),
            ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 →
            ∀ sigma : PartialEdgeColoring E k,
              IsProperEdgeColoring G sigma →
              IsOneEdgeUncolored sigma e0 →
              StableColoring
                (lower.series.data.tree q.succ.castSucc)
                (TashkinovStoredColors lower.series.data q.succ)
                (lower.series.data.coloring q.succ) sigma →
              StableColoringBeforeVertex T' v hvFinal
                  (TashkinovStoredColors lower.series.data j)
                  (lower.series.data.coloring j) sigma ∧
                (0 < j.val →
                  StableColoring (lower.series.data.tree j.castSucc)
                    (TashkinovStoredColors lower.series.data j)
                    (lower.series.data.coloring j) sigma)) ∧
        ∀ (q r : Fin lower.rounds) (vq vr : V),
          q ≠ r → vq ≠ vr →
          lower.series.data.kind q.succ =
              some TashkinovExtensionKind.PE →
          lower.series.data.kind r.succ =
              some TashkinovExtensionKind.PE →
          lower.series.data.chosenVertex q.succ = some vq →
          lower.series.data.chosenVertex r.succ = some vr →
          ∀ (hvq : vq ∈ TreeSequenceVertexSet T')
            (hvr : vr ∈ TreeSequenceVertexSet T'),
            ETTFirstAppearanceIndex lower vq hvq =
                ETTFirstAppearanceIndex lower vr hvr →
            Disjoint (lower.series.data.stored q.succ)
              (lower.series.data.stored r.succ))) :
    ((∀ (q : Fin ett.rounds) (v : V),
        q.succ ≠ Fin.last ett.rounds →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v →
        ∀ hvFinal : v ∈ TreeSequenceVertexSet T,
        ∀ j : Fin (ett.rounds + 1),
          ETTFirstAppearanceIndex ett v hvFinal = j.val + 1 →
          ∀ sigma : PartialEdgeColoring E k,
            IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
            StableColoring (ett.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors ett.series.data q.succ)
              (ett.series.data.coloring q.succ) sigma →
            StableColoringBeforeVertex T v hvFinal
                (TashkinovStoredColors ett.series.data j)
                (ett.series.data.coloring j) sigma ∧
              (0 < j.val →
                StableColoring (ett.series.data.tree j.castSucc)
                  (TashkinovStoredColors ett.series.data j)
                  (ett.series.data.coloring j) sigma)) ∧
      ∀ (q r : Fin ett.rounds) (vq vr : V),
        q.succ ≠ Fin.last ett.rounds →
        r.succ ≠ Fin.last ett.rounds →
        q ≠ r → vq ≠ vr →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.kind r.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some vq →
        ett.series.data.chosenVertex r.succ = some vr →
        ∀ (hvq : vq ∈ TreeSequenceVertexSet T)
          (hvr : vr ∈ TreeSequenceVertexSet T),
          ETTFirstAppearanceIndex ett vq hvq =
              ETTFirstAppearanceIndex ett vr hvr →
          Disjoint (ett.series.data.stored q.succ)
            (ett.series.data.stored r.succ)) := by
  classical
  let : DecidableEq V := Classical.decEq V
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    rcases hAB with ⟨hab, hvab, heab⟩
    rcases hBC with ⟨hbc, hvbc, hebc⟩
    refine ⟨hab.trans hbc, ?_, ?_⟩
    · intro i
      have hmid := hvbc (Fin.castLE (Nat.succ_le_succ hab) i)
      exact (by simpa using hmid.trans (hvab i))
    · intro i
      have hmid := hebc (Fin.castLE hab i)
      exact (by simpa using hmid.trans (heab i))
  have stageToStage (first last : ℕ) (positive : 1 ≤ first)
      (ordered : first ≤ last) (bounded : last ≤ ett.rounds) :
      TreeSequenceInitialSegment
        (ett.series.data.tree
          ⟨first, lt_of_le_of_lt ordered (Nat.lt_succ_of_le (Nat.le_succ_of_le bounded))⟩)
        (ett.series.data.tree ⟨last, Nat.lt_succ_of_le (Nat.le_succ_of_le bounded)⟩) :=
    ett.series.stageInitialSegmentOfLE _ _
      (Nat.lt_of_lt_of_le Nat.zero_lt_one positive) ordered
  have stageToT : ∀ (a : ℕ) (_ha : 1 ≤ a) (_hround : a ≤ ett.rounds),
      TreeSequenceInitialSegment
        (ett.series.data.tree ⟨a, by omega⟩) T := by
    intro a ha hround
    have hchain := stageToStage a ett.rounds ha hround le_rfl
    exact segmentTrans hchain ett.abovePenultimate
  have supportInFollowingTree := @helper_supportInFollowingTree_188 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett
  have ladderStageEq := @helper_ladderStageEq_229 V E inferInstance inferInstance inferInstance G k
      e0 input T generating ett
  have firstAppearanceEq :
    ∀ {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 input T' generating') (s : ℕ) (hs : lower.rounds = s) (hsn :
        s < ett.rounds) (hdisplay : T' = ett.series.data.tree ⟨s + 1,
    by omega
    ⟩) (htree :
    ∀ i : Fin (lower.rounds + 2), lower.series.data.tree i = ett.series.data.tree (Fin.castLE (
    by omega
    ) i)) (v : V) (hvLower : v ∈ TreeSequenceVertexSet T') (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hbound : ETTFirstAppearanceIndex ett v hvFinal ≤ s), ETTFirstAppearanceIndex lower v
        hvLower = ETTFirstAppearanceIndex ett v hvFinal := by
    exact @helper_firstAppearanceEq_290 V E inferInstance inferInstance inferInstance G k e0
        input T generating ett (by assumption) ladderStageEq
  have beforeEqOfSegment := @helper_beforeEqOfSegment_356 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett
  constructor
  · exact @helper_branch_399 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett hMP hLowerThree stageToT supportInFollowingTree firstAppearanceEq
      beforeEqOfSegment
  · exact @helper_branch_480 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett hMP hLowerThree stageToStage supportInFollowingTree firstAppearanceEq
end GoldbergSeymour

end
