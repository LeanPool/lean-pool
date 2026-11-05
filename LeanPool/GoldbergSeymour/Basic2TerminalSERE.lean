/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis
public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.HkuMissingStoredMonotone
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.StableColoringEquivalence

/-!
# Basic2Terminal SERE

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hpreviousStable_168.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : ett.series.data.kind
        (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨ ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.RE),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (sigma : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored
        sigma e0) (_ : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring
        (Fin.last ett.rounds)) sigma) (v : V) (_ : v ∈ TreeSequenceVertexSet T) (_ : Fin
        ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : previous.succ = terminal), StableColoring (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc) (ett.series.data.coloring
        previous.castSucc) sigma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive hterminalKind this sigma hproper hone
      hstable v hvFinal q terminal previous hpreviousSucc
  have cert := ett.series.certified terminal
  generalize hslot : terminal = slot at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hz := congrArg Fin.val hslot
    simp [terminal] at hz
    omega
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hterm := hterminalKind
    change ett.series.data.kind terminal =
        some TashkinovExtensionKind.SE ∨
      ett.series.data.kind terminal =
        some TashkinovExtensionKind.RE at hterm
    rw [hslot] at hterm
    rw [currentKind] at hterm
    have hbad : some TashkinovExtensionKind.PE =
        some TashkinovExtensionKind.SE ∨
      some TashkinovExtensionKind.PE =
        some TashkinovExtensionKind.RE := hterm
    simp at hbad
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hci : ci = previous := by
      apply Fin.ext
      have hs := congrArg Fin.val hslot
      simp [terminal, previous] at hs ⊢
      omega
    subst ci
    have hmonotone :=
      (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series previous).1
    have hterminalColor : ett.series.data.coloring terminal = choice.selected := by
      rw [hslot]
      exact currentColoring
    have hcurrentStable : StableColoring
        (ett.series.data.tree previous.succ.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc)
        choice.selected sigma := by
      constructor
      · intro f hf hcontrol
        rcases hcontrol with ⟨c, hc, hcf⟩
        have holdControl : c ∈
            TreeMissingColors (ett.series.data.coloring previous.castSucc)
                (ett.series.data.tree previous.succ.castSucc) ∪
              TashkinovStoredColors ett.series.data previous.castSucc := by
          rcases Finset.mem_union.mp hc with hc | hc
          · apply Finset.mem_union.mpr
            left
            simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
            rcases hc with ⟨x, hx, hxc⟩
            refine ⟨x, hx, ?_⟩
            rw [← choice.selectedStable.2 x hx]
            exact hxc
          · exact Finset.mem_union.mpr (Or.inr hc)
        have hnewControl := hmonotone holdControl
        have hnewControl' : c ∈
            TreeMissingColors (ett.series.data.coloring terminal)
                (ett.series.data.tree terminal.castSucc) ∪
              TashkinovStoredColors ett.series.data terminal := by
          simpa [hslot] using hnewControl
        have hf' : TreeIncidentEdge
            (ett.series.data.tree terminal.castSucc) f := by
          simpa [hslot] using hf
        have hcf' : ett.series.data.coloring terminal f = some c := by
          rw [hterminalColor]
          exact hcf
        have hs := hstable.1 f hf' ⟨c, hnewControl', hcf'⟩
        rw [hterminalColor] at hs
        exact hs
      · intro x hx
        have hs := hstable.2 x (by simpa [hpreviousSucc] using hx)
        rw [hterminalColor] at hs
        exact hs
    have hresult := (sc2 G e0
      (ett.series.data.tree previous.succ.castSucc)
      (TashkinovStoredColors ett.series.data previous.castSucc)).trans
        (x := ⟨ett.series.data.coloring previous.castSucc,
          ⟨previousProper, previousOneUncolored⟩⟩)
        (y := ⟨choice.selected,
          ⟨choice.selectedProper, choice.selectedOneUncolored⟩⟩)
        (z := ⟨sigma, ⟨hproper, hone⟩⟩)
        choice.selectedStable hcurrentStable
    simpa [hpreviousSucc] using hresult
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hci : ci = previous := by
      apply Fin.ext
      have hs := congrArg Fin.val hslot
      simp [terminal, previous] at hs ⊢
      omega
    subst ci
    have hmonotone :=
      (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series previous).1
    have hterminalColor : ett.series.data.coloring terminal =
        ett.series.data.coloring previous.castSucc := by
      rw [hslot]
      exact currentColoring
    constructor
    · intro f hf hcontrol
      rcases hcontrol with ⟨c, hc, hcf⟩
      have hnewControl := hmonotone hc
      have hnewControl' : c ∈
          TreeMissingColors (ett.series.data.coloring terminal)
              (ett.series.data.tree terminal.castSucc) ∪
            TashkinovStoredColors ett.series.data terminal := by
        simpa [hslot] using hnewControl
      have hf' : TreeIncidentEdge
          (ett.series.data.tree terminal.castSucc) f := by
        simpa [hslot] using hf
      have hcf' : ett.series.data.coloring terminal f = some c := by
        rw [hterminalColor]
        exact hcf
      have hs := hstable.1 f hf' ⟨c, hnewControl', hcf'⟩
      rw [hterminalColor] at hs
      exact hs
    · intro x hx
      have hs := hstable.2 x (by simpa [hpreviousSucc] using hx)
      rw [hterminalColor] at hs
      exact hs

private theorem helper_branch_305.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : ett.series.data.kind
        (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨ ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.RE),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (u w : V) (_ :
        TreeVertexOrder A u w), TreeVertexOrder B u w)) (sigma : PartialEdgeColoring E k) (_ :
        IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (delta : Fin k) (_ :
        DefectiveColor G sigma (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) delta) (v : V) (_ : v ∈ TreeSequenceVertexSet T) (q : Fin
        ett.rounds) (vi : V) (_ : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨
        ett.series.data.kind q.succ = some TashkinovExtensionKind.SE) (_ :
        ett.series.data.chosenVertex q.succ = some vi) (_ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    ∀ a ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) delta, Incident G v a →
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); previous.succ = terminal → ett.series.data.tree terminal.castSucc =
        ett.series.data.tree (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) → StableColoring (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc) (ett.series.data.coloring
        previous.castSucc) sigma → q.succ = terminal → v = vi ∨ TreeVertexOrder T v vi := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive hterminalKind this orderTransfer sigma
      hproper hone delta hdefective v hvFinal q vi hkind hchosen hvN a haColor hva terminal
      previous hpreviousSucc htreeTerminal hpreviousStable hqTerminal
  have cert := ett.series.certified terminal
  generalize hslot : terminal = slot at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hz := congrArg Fin.val hslot
    simp [terminal] at hz
    omega
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hterm := hterminalKind
    change ett.series.data.kind terminal =
        some TashkinovExtensionKind.SE ∨
      ett.series.data.kind terminal =
        some TashkinovExtensionKind.RE at hterm
    rw [hslot] at hterm
    rw [currentKind] at hterm
    have hbad : some TashkinovExtensionKind.PE =
        some TashkinovExtensionKind.SE ∨
      some TashkinovExtensionKind.PE =
        some TashkinovExtensionKind.RE := hterm
    simp at hbad
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hbad : some TashkinovExtensionKind.RE =
        some TashkinovExtensionKind.PE ∨
      some TashkinovExtensionKind.RE =
        some TashkinovExtensionKind.SE := by
      rw [← currentKind]
      simpa [hslot, hqTerminal] using hkind
    simp at hbad
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hci : ci = previous := by
      apply Fin.ext
      have hs := congrArg Fin.val hslot
      simp [terminal, previous] at hs ⊢
      omega
    subst ci
    have hchoice : choice.vertex = vi := by
      apply Option.some.inj
      exact currentVertex.symm.trans (by simpa [hslot, hqTerminal] using hchosen)
    have hvDefective : DefectiveVertex G sigma
        (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc)) v :=
      ⟨hvN, a, ⟨delta, hdefective, haColor⟩, hva⟩
    have hmaximal := choice.maximal sigma v hproper hone (by
      simpa only [hpreviousSucc] using hpreviousStable) (by
      simpa [hslot] using hvDefective)
    rcases hmaximal with heq | horder
    · exact Or.inl (heq.trans hchoice)
    · apply Or.inr
      have hsegment : TreeSequenceInitialSegment
          (ett.series.data.tree terminal.castSucc) T := by
        rw [htreeTerminal]
        exact ett.abovePenultimate
      exact orderTransfer hsegment v vi (by simpa [hslot, hchoice] using horder)

private theorem helper_appearanceInStage_400.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (_ : (
    ∀ (a b : ℕ) (_ : (1 : ℕ) ≤ a) (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
        TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))))) (v : V) (_ : v ∈ TreeSequenceVertexSet T) (_ : Fin
        ett.rounds) (x : V) (hxFinal : x ∈ TreeSequenceVertexSet T) (s : ℕ) (_ : (1 : ℕ) ≤ s)
        (_hsRound : s ≤ ett.rounds) (_ : ETTFirstAppearanceIndex ett x hxFinal ≤ s), x ∈
        TreeSequenceVertexSet (ett.series.data.tree (⟨s,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett this stageToStage v hvFinal q x hxFinal s
      hsPositive hsRound hbound
  unfold ETTFirstAppearanceIndex at hbound
  dsimp at hbound
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      x ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hnonempty : candidates.Nonempty := by
    refine ⟨Fin.last ett.rounds, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett
        (Fin.last ett.rounds) = T by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    exact hxFinal
  let m := candidates.min' hnonempty
  have hmBound : m.val + 1 ≤ s := by
    dsimp [m, candidates]
    convert hbound using 1
  have hmRounds : m.val < ett.rounds := by omega
  let mi : Fin ett.rounds := ⟨m.val, hmRounds⟩
  have hmEq : m = mi.castSucc := by
    apply Fin.ext
    rfl
  have hmem := Finset.min'_mem candidates hnonempty
  change m ∈ candidates at hmem
  have hxStart : x ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨m.val + 1, by omega⟩) := by
    rw [hmEq] at hmem
    have hstage : ExtendedTashkinovLadderStage ett mi.castSucc =
        ett.series.data.tree mi.succ.castSucc := by
      unfold ExtendedTashkinovLadderStage
      exact @Fin.lastCases_castSucc ett.rounds
        (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) T
        (fun j => ett.series.data.tree j.succ.castSucc) mi
    have hxMi : x ∈ TreeSequenceVertexSet
        (ett.series.data.tree mi.succ.castSucc) := by
      simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and,
        hstage] using hmem
    convert hxMi using 1
    apply congrArg TreeSequenceVertexSet
    apply congrArg ett.series.data.tree
    apply Fin.ext
    simp [mi]
  exact TreeSequenceInitialSegmentVertexSetSubset
    (stageToStage (m.val + 1) s (by omega) hmBound hsRound) hxStart

private theorem helper_earlierInPrefix_473.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T generating),
        ∀ v ∈ TreeSequenceVertexSet T,
          ∀ (_ : Fin ett.rounds) {A B : TreeSequence G e0} (x y : V),
            TreeSequenceInitialSegment A B →
              y ∈ TreeSequenceVertexSet A →
                TreeVertexOrder B x y → x ∈ TreeSequenceVertexSet A ∧ TreeVertexOrder A x y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal q A B x y hAB hyA hxy
  rcases hAB with ⟨hlen, hvertices, _⟩
  rcases Finset.mem_image.mp hyA with ⟨iyA, _, hiyA⟩
  rcases hxy with ⟨ixB, iyB, hixB, hiyB, hlt⟩
  let iyCast := Fin.castLE (Nat.succ_le_succ hlen) iyA
  have hiyEq : iyB = iyCast := by
    apply B.vertex_injective
    exact hiyB.trans ((hvertices iyA).trans hiyA).symm
  have hixBound : ixB.val < A.length + 1 := by
    rw [hiyEq] at hlt
    simp [iyCast] at hlt
    omega
  let ixA : Fin (A.length + 1) := ⟨ixB.val, hixBound⟩
  have hixCast : Fin.castLE (Nat.succ_le_succ hlen) ixA = ixB := by
    apply Fin.ext
    rfl
  have hixA : A.vertex ixA = x := by
    exact (hvertices ixA).symm.trans (by simpa [hixCast] using hixB)
  constructor
  · apply Finset.mem_image.mpr
    exact ⟨ixA, Finset.mem_univ _, hixA⟩
  · refine ⟨ixA, iyA, hixA, hiyA, ?_⟩
    rw [hiyEq] at hlt
    simpa [ixA, iyCast] using hlt

private theorem helper_hfirstLower_662.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (v : V) (_ : v ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds) (hqBefore : (↑q : ℕ) + (1 :
        ℕ) < ett.rounds),
    let r : ℕ := ett.rounds - (1 : ℕ);
    ∀ (hrBefore : r < ett.rounds) (_ : v ∈ TreeSequenceVertexSet (ett.series.data.tree (⟨(↑q : ℕ)
        + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) (lower : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (⟨r + (1 : ℕ), (
    by omega
    )⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨r, (
    by omega
    )⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : lower.rounds = r) (_ : (
    ∀ (i : Fin (lower.rounds + (2 : ℕ))), lower.series.data.tree i = ett.series.data.tree
        (Fin.castLE ((
    by omega
    )) i))) (hvLower : v ∈ TreeSequenceVertexSet (ett.series.data.tree (⟨r + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))),
    let qLower : Fin lower.rounds := (⟨(↑q : ℕ),
    by omega
    ⟩ : Fin lower.rounds); ETTFirstAppearanceIndex lower v hvLower ≤ (↑qLower : ℕ) + (1 : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive this v hvFinal q hqBefore r hrBefore
      hvAtQ lower hr htree hvLower qLower
  unfold ETTFirstAppearanceIndex
  dsimp
  have hqTreeCast : Fin.castLE (by omega) qLower.succ.castSucc =
      (⟨q.val + 1, by omega⟩ : Fin (ett.rounds + 2)) := by
    apply Fin.ext
    rfl
  have hmem : qLower.castSucc ∈
      Finset.univ.filter
        (fun i : Fin (lower.rounds + 1) =>
          v ∈ TreeSequenceVertexSet
            (ExtendedTashkinovLadderStage lower i)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage lower qLower.castSucc =
        lower.series.data.tree qLower.succ.castSucc by
      unfold ExtendedTashkinovLadderStage
      exact @Fin.lastCases_castSucc lower.rounds
        (fun _ : Fin (lower.rounds + 1) => TreeSequence G e0)
        (ett.series.data.tree ⟨r + 1, by omega⟩)
        (fun j => lower.series.data.tree j.succ.castSucc) qLower]
    rw [htree qLower.succ.castSucc, hqTreeCast]
    exact hvAtQ
  have hle := Finset.min'_le
    (Finset.univ.filter
      (fun i : Fin (lower.rounds + 1) =>
        v ∈ TreeSequenceVertexSet
          (ExtendedTashkinovLadderStage lower i))) qLower.castSucc hmem
  have hnat := Fin.le_iff_val_le_val.mp hle
  simpa [qLower] using Nat.succ_le_succ hnat

private theorem helper_boundaryEndpoint_620.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (sigma : PartialEdgeColoring E k) (delta : Fin k),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc),
    ∀ f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet (ett.series.data.tree
        terminal.castSucc)) delta, Incident G x f →
    ∃ z ∉ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), G.ends f = s(x, z) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett sigma delta terminal x hx f hf hxf
  have hfBoundary := (Finset.mem_filter.mp hf).1
  rcases (by
    simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using hfBoundary) with ⟨u, hu, z, hz, hends⟩
  have hxEnds : x = u ∨ x = z := by
    change x ∈ G.ends f at hxf
    rw [hends] at hxf
    simpa using hxf
  rcases hxEnds with hxu | hxz
  · exact ⟨z, hz, by simpa [hxu] using hends⟩
  · exact (hz (hxz ▸ hx)).elim

private theorem helper_hstableR_735.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (sigma : PartialEdgeColoring E k) (v : V) (_ : v ∈ TreeSequenceVertexSet T) (_ : Fin
        ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : StableColoring (ett.series.data.tree terminal.castSucc) (TashkinovStoredColors
        ett.series.data previous.castSucc) (ett.series.data.coloring previous.castSucc) sigma),
    let r : ℕ := ett.rounds - (1 : ℕ);
    ∀ (hrBefore : r < ett.rounds) (_ : TreeSequenceInitialSegment (ett.series.data.tree (⟨r,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree terminal.castSucc)) (lower :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (⟨r + (1 : ℕ), (
    by omega
    )⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨r, (
    by omega
    )⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : lower.rounds = r), StableColoring
        (ett.series.data.tree (⟨r,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc) sigma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive this sigma v hvFinal q terminal
      previous hpreviousStable r hrBefore hRTerminal lower hr
  constructor
  · intro f hf hcontrol
    apply hpreviousStable.1 f
    · rcases hf with ⟨x, hx, hxf⟩
      exact ⟨x, TreeSequenceInitialSegmentVertexSetSubset hRTerminal hx,
        hxf⟩
    · rcases hcontrol with ⟨c, hc, hcf⟩
      refine ⟨c, ?_, hcf⟩
      rcases Finset.mem_union.mp hc with hc | hc
      · apply Finset.mem_union.mpr
        left
        simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
        rcases hc with ⟨x, hx, hxc⟩
        exact ⟨x, TreeSequenceInitialSegmentVertexSetSubset hRTerminal hx,
          hxc⟩
      · exact Finset.mem_union.mpr (Or.inr hc)
  · intro x hx
    exact hpreviousStable.2 x
      (TreeSequenceInitialSegmentVertexSetSubset hRTerminal hx)

private theorem helper_continuation_767.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (_ :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (u w : V) (_ :
        TreeVertexOrder A u w), TreeVertexOrder B u w)) (sigma : PartialEdgeColoring E k) (_ :
        IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (delta : Fin k) (v : V) (_
        : v ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds) (vi : V) (_ : ett.series.data.kind
        q.succ = some TashkinovExtensionKind.PE ∨ ett.series.data.kind q.succ = some
        TashkinovExtensionKind.SE) (_ : ett.series.data.chosenVertex q.succ = some vi) (_ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (a : E) (_ :
        Incident G v a) (w : V) (b : E) (_ : Incident G w b) (_ : ett.series.data.tree (Fin.last
        ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc = ett.series.data.tree (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (_ : StableColoring (ett.series.data.tree (Fin.last
        ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc) (TashkinovStoredColors ett.series.data
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) (ett.series.data.coloring ((⟨ett.rounds - (1 :
        ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) sigma) (hqBefore : (↑q : ℕ) + (1 : ℕ) <
        ett.rounds) (_ : (1 : ℕ) ≤ (ett.rounds - (1 : ℕ) : ℕ)) (hrBefore : (ett.rounds - (1 : ℕ) :
        ℕ) < ett.rounds) (_ : v ∈ TreeSequenceVertexSet (ett.series.data.tree (⟨(ett.rounds - (1 :
        ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) (_ : v ∈ TreeSequenceVertexSet (ett.series.data.tree (⟨(↑q :
        ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) (_ : TreeSequenceInitialSegment (ett.series.data.tree
        (⟨(ett.rounds - (1 : ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds
        + (1 : ℕ))).castSucc)) (_ : w ∈ TreeSequenceVertexSet (ett.series.data.tree (⟨(ett.rounds
        - (1 : ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) (_ : TreeVertexOrder (ett.series.data.tree (⟨(ett.rounds -
        (1 : ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) w v) (_ : a ∈ BoundaryColorEdges G sigma
        (TreeSequenceVertexSet (ett.series.data.tree (⟨(ett.rounds - (1 : ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) delta) (_ : b ∈ BoundaryColorEdges G sigma
        (TreeSequenceVertexSet (ett.series.data.tree (⟨(ett.rounds - (1 : ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) delta) (_ : DefectiveColor G sigma (TreeSequenceVertexSet
        (ett.series.data.tree (⟨(ett.rounds - (1 : ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) delta), v = vi ∨ TreeVertexOrder T v vi := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower orderTransfer sigma hproper
      hone delta v hvFinal q vi hkind hchosen hvN a hva w b hwb
  set terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last
                                        ett.rounds
  set previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ :
                                        Fin ett.rounds)
  intro htreeTerminal hpreviousStable hqBefore
  set r : ℕ := ett.rounds - (1 : ℕ)
  intro hrPositive hrBefore hvR hvAtQ hRTerminal hwR hwvR haR hbR hdefectiveR
  have hvBoundaryR : BoundaryColorVertex G sigma
      (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
      delta v := ⟨hvR, a, haR, hva⟩
  have hwBoundaryR : BoundaryColorVertex G sigma
      (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
      delta w := ⟨hwR, b, hbR, hwb⟩
  obtain ⟨lower, hr, hmaxLower, htree, hdata⟩ :=
    CertifiedETTRestriction G k e0 input T generating ett hMP r
      hrPositive hrBefore
  let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
  have hnCast : Fin.castLE (by omega) nLower = previous.castSucc := by
    apply Fin.ext
    simp [nLower, hr, previous, r]
  have hnTreeCast : Fin.castLE (by omega) nLower.castSucc =
      previous.castSucc.castSucc := by
    apply Fin.ext
    simp [nLower, hr, previous, r]
  have hrTree : ett.series.data.tree ⟨r, by omega⟩ =
      ett.series.data.tree previous.castSucc.castSucc := by
    apply congrArg ett.series.data.tree
    apply Fin.ext
    simp [previous, r]
  have hdisplay : ett.series.data.tree ⟨r + 1, by omega⟩ =
      ett.series.data.tree terminal.castSucc := by
    congr 1
    apply Fin.ext
    simp [r, terminal]
    omega
  have hvLower : v ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨r + 1, by omega⟩) := by
    rw [hdisplay]
    exact hvN
  rcases hdata nLower with
    ⟨hnColor, hnRawStored, hnEdges, hnKind, hnVertex, hnOutside,
      hnDelta, hnGamma, hnStored, hnCert⟩
  have hnColor' : lower.series.data.coloring nLower =
      ett.series.data.coloring previous.castSucc := by
    rw [hnColor, hnCast]
  have hnStored' : TashkinovStoredColors lower.series.data nLower =
      TashkinovStoredColors ett.series.data previous.castSucc := by
    rw [hnStored, hnCast]
  have hnTree' : lower.series.data.tree nLower.castSucc =
      ett.series.data.tree ⟨r, by omega⟩ := by
    rw [htree nLower.castSucc, hnTreeCast, ← hrTree]
  have hstableR :=
    @helper_hstableR_735 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett hpositive sigma v hvFinal q hpreviousStable hrBefore hRTerminal lower hr
  have hstableLower : StableColoring
      (lower.series.data.tree nLower.castSucc)
      (TashkinovStoredColors lower.series.data nLower)
      (lower.series.data.coloring nLower) sigma := by
    rw [hnTree', hnStored', hnColor']
    exact hstableR
  let qLower : Fin lower.rounds := ⟨q.val, by omega⟩
  have hqCast : Fin.castLE (by omega) qLower.succ = q.succ := by
    apply Fin.ext
    rfl
  rcases hdata qLower.succ with
    ⟨_, _, _, hqKind, hqVertex, _, _, _, _, _⟩
  have hkindLower : lower.series.data.kind qLower.succ =
        some TashkinovExtensionKind.PE ∨
      lower.series.data.kind qLower.succ =
        some TashkinovExtensionKind.SE := by
    rw [hqKind, hqCast]
    exact hkind
  have hchosenLower : lower.series.data.chosenVertex qLower.succ = some vi := by
    rw [hqVertex, hqCast]
    exact hchosen
  have hfirstLower :=
    @helper_hfirstLower_662 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett hpositive v hvFinal q hqBefore hrBefore hvAtQ lower hr htree hvLower
  have hdefectiveLower : DefectiveColor G sigma
      (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
      delta := by
    rw [hnTree']
    exact hdefectiveR
  have hvBoundaryLower : BoundaryColorVertex G sigma
      (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
      delta v := by
    rw [hnTree']
    exact hvBoundaryR
  have hwBoundaryLower : BoundaryColorVertex G sigma
      (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
      delta w := by
    rw [hnTree']
    exact hwBoundaryR
  have hwvLower : TreeVertexOrder
      (lower.series.data.tree nLower.castSucc) w v := by
    rw [hnTree']
    exact hwvR
  have hlowerFive :=
    (hlower lower (by omega) (by omega) hmaxLower).2.2.2.2.1
  have hresult := hlowerFive sigma hproper hone hstableLower delta
    hdefectiveLower v hvBoundaryLower ⟨w, hwBoundaryLower, hwvLower⟩
    hvLower qLower vi hkindLower hchosenLower hfirstLower
  rcases hresult with heq | horder
  · exact Or.inl heq
  · apply Or.inr
    have hdisplayToT : TreeSequenceInitialSegment
        (ett.series.data.tree ⟨r + 1, by omega⟩) T := by
      rw [hdisplay]
      rw [htreeTerminal]
      exact ett.abovePenultimate
    exact orderTransfer hdisplayToT v vi horder

private theorem helper_branch_373.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (_ :
        LowerRoundInductionHypothesis G k e0 ett.rounds),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (_ : (
    ∀ (a b : ℕ) (_ : (1 : ℕ) ≤ a) (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
        TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))))) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (u w : V) (_ :
        TreeVertexOrder A u w), TreeVertexOrder B u w)) (sigma : PartialEdgeColoring E k) (_ :
        IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (delta : Fin k) (v : V)
        (hvFinal : v ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds) (vi : V) (_ :
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨ ett.series.data.kind q.succ
        = some TashkinovExtensionKind.SE) (_ : ett.series.data.chosenVertex q.succ = some vi) (_ :
        ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (_ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    ∀ a ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) delta, Incident G v a →
    ∀ (w : V), TreeVertexOrder (ett.series.data.tree (Fin.last ett.rounds).castSucc) w v → w ∈
        TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc) →
    ∀ b ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) delta, Incident G w b →
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); ett.series.data.tree terminal.castSucc = ett.series.data.tree
        (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) → StableColoring (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc) (ett.series.data.coloring
        previous.castSucc) sigma → ¬q.succ = terminal → v = vi ∨ TreeVertexOrder T v vi := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower this stageToStage orderTransfer
      sigma hproper hone delta v hvFinal q vi hkind hchosen hfirstBound hvN a haColor hva w hwv hwN
      b hbColor hwb terminal previous htreeTerminal hpreviousStable hqTerminal
  have hqBefore : q.val + 1 < ett.rounds := by
    have hle : q.val + 1 ≤ ett.rounds := by omega
    have hne : q.val + 1 ≠ ett.rounds := by
      intro heq
      apply hqTerminal
      apply Fin.ext
      simpa [terminal] using heq
    omega
  have appearanceInStage :=
    @helper_appearanceInStage_400 V E inferInstance inferInstance inferInstance G k e0
        input T generating ett stageToStage v hvFinal q
  let r := ett.rounds - 1
  have hrPositive : 1 ≤ r := by
    dsimp [r]
    omega
  have hrBefore : r < ett.rounds := by
    dsimp [r]
    omega
  have hfirstToR : ETTFirstAppearanceIndex ett v hvFinal ≤ r := by
    dsimp [r]
    omega
  have hvR : v ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨r, by omega⟩) :=
    appearanceInStage v hvFinal r hrPositive (by dsimp [r]; omega) hfirstToR
  have hvAtQ : v ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨q.val + 1, by omega⟩) :=
    appearanceInStage v hvFinal (q.val + 1) (by omega) (by omega)
      hfirstBound
  have hRTerminal : TreeSequenceInitialSegment
      (ett.series.data.tree ⟨r, by omega⟩)
      (ett.series.data.tree terminal.castSucc) := by
    rw [htreeTerminal]
    exact stageToStage r ett.rounds hrPositive (by dsimp [r]; omega) le_rfl
  have earlierInPrefix :=
    @helper_earlierInPrefix_473 V E inferInstance inferInstance inferInstance G k e0 input
        T generating ett v hvFinal q
  obtain ⟨hwR, hwvR⟩ := earlierInPrefix w v hRTerminal hvR hwv
  have boundaryEndpoint :=
    @helper_boundaryEndpoint_620 V E inferInstance inferInstance inferInstance G k e0 input
        T generating ett sigma delta
  obtain ⟨za, hzaOutside, haEnds⟩ :=
    boundaryEndpoint v hvN a haColor hva
  obtain ⟨zb, hzbOutside, hbEnds⟩ :=
    boundaryEndpoint w hwN b hbColor hwb
  have hzaR : za ∉ TreeSequenceVertexSet
      (ett.series.data.tree ⟨r, by omega⟩) := by
    intro hza
    exact hzaOutside (TreeSequenceInitialSegmentVertexSetSubset hRTerminal hza)
  have hzbR : zb ∉ TreeSequenceVertexSet
      (ett.series.data.tree ⟨r, by omega⟩) := by
    intro hzb
    exact hzbOutside (TreeSequenceInitialSegmentVertexSetSubset hRTerminal hzb)
  have haR : a ∈ BoundaryColorEdges G sigma
      (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
      delta := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    refine ⟨?_, (Finset.mem_filter.mp haColor).2⟩
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hvR, za, hzaR, haEnds⟩
  have hbR : b ∈ BoundaryColorEdges G sigma
      (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
      delta := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    refine ⟨?_, (Finset.mem_filter.mp hbColor).2⟩
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hwR, zb, hzbR, hbEnds⟩
  have hwne : w ≠ v := by
    intro hwvEq
    rcases hwv with ⟨iw, iv, hiw, hiv, hlt⟩
    have hieq : iw = iv := by
      apply (ett.series.data.tree terminal.castSucc).vertex_injective
      exact hiw.trans (hiv.trans hwvEq.symm).symm
    omega
  have hab : a ≠ b := by
    intro habEq
    subst b
    have hwEnds : w = v ∨ w = za := by
      change w ∈ G.ends a at hwb
      rw [haEnds] at hwb
      simpa using hwb
    rcases hwEnds with hwvEq | hwza
    · exact hwne hwvEq
    · exact hzaOutside (hwza ▸ hwN)
  have hdefectiveR : DefectiveColor G sigma
      (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
      delta := by
    unfold DefectiveColor
    have hc : 1 < (BoundaryColorEdges G sigma
        (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
        delta).card := Finset.one_lt_card.mpr
          ⟨a, haR, b, hbR, hab⟩
    omega
  exact @helper_continuation_767 V E inferInstance inferInstance  inferInstance G k
      e0 input T generating ett hMP hpositive hlower orderTransfer sigma hproper hone delta v
      hvFinal q vi hkind hchosen hvN a hva w b hwb htreeTerminal hpreviousStable hqBefore
      hrPositive hrBefore hvR hvAtQ hRTerminal hwR hwvR haR hbR hdefectiveR
theorem Basic2TerminalSERE {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hterminalKind :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.RE) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tn
        (TashkinovStoredColors ett.series.data n)
        (ett.series.data.coloring n) sigma →
      ∀ (delta : Fin k),
        DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
        ∀ (v : V),
          BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v →
          (∃ w, BoundaryColorVertex G sigma
              (TreeSequenceVertexSet Tn) delta w ∧
            TreeVertexOrder Tn w v) →
          ∀ (hvFinal : v ∈ TreeSequenceVertexSet T)
            (q : Fin ett.rounds) (vi : V),
            (ett.series.data.kind q.succ =
                 some TashkinovExtensionKind.PE ∨
               ett.series.data.kind q.succ =
                 some TashkinovExtensionKind.SE) →
            ett.series.data.chosenVertex q.succ = some vi →
            ETTFirstAppearanceIndex ett v hvFinal ≤ q.val + 1 →
            v = vi ∨ TreeVertexOrder T v vi := by
  classical
  let : DecidableEq V := Classical.decEq V
  have segmentRefl (A : TreeSequence G e0) :
      TreeSequenceInitialSegment A A :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
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
  have stepSegment : ∀ i : Fin (ett.rounds + 1), 0 < i.val →
      TreeSequenceInitialSegment (ett.series.data.tree i.castSucc)
        (ett.series.data.tree i.succ) := by
    intro i hi
    have cert := ett.series.certified i
    cases cert with
    | initial => exact (by simp at hi)
    | SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
    | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
    | RE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
  have stageToStage : ∀ (a b : ℕ) (_ha : 1 ≤ a) (_hab : a ≤ b)
      (_hb : b ≤ ett.rounds),
      TreeSequenceInitialSegment
        (ett.series.data.tree ⟨a, by omega⟩)
        (ett.series.data.tree ⟨b, by omega⟩) := by
    intro a b ha hab hb
    have chain : ∀ (d : ℕ) (_hd : a + d ≤ b),
        TreeSequenceInitialSegment
          (ett.series.data.tree ⟨a, by omega⟩)
          (ett.series.data.tree ⟨a + d, by omega⟩) := by
      intro d hd
      induction d with
      | zero => simpa using segmentRefl (ett.series.data.tree ⟨a, by omega⟩)
      | succ d ih =>
          have hprev := ih (by omega)
          let idx : Fin (ett.rounds + 1) := ⟨a + d, by omega⟩
          have hone := stepSegment idx (by dsimp [idx]; omega)
          have hone' : TreeSequenceInitialSegment
              (ett.series.data.tree ⟨a + d, by omega⟩)
              (ett.series.data.tree ⟨a + (d + 1), by omega⟩) := by
            simpa [idx, Nat.add_assoc] using hone
          exact segmentTrans hprev hone'
    have hchain := chain (b - a) (by omega)
    convert hchain using 1; apply congrArg ett.series.data.tree;
      apply Fin.ext; simp; omega
  have orderTransfer : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B → ∀ u w,
        TreeVertexOrder A u w → TreeVertexOrder B u w := by
    intro A B hAB u w huw
    rcases hAB with ⟨hlen, hvertices, _⟩
    rcases huw with ⟨iu, iw, hu, hw, hi⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) iu,
      Fin.castLE (Nat.succ_le_succ hlen) iw,
      (hvertices iu).trans hu, (hvertices iw).trans hw, hi⟩
  dsimp only
  intro sigma hproper hone hstable delta hdefective v hvBoundary
    hvNonminimum hvFinal q vi hkind hchosen hfirstBound
  rcases hvBoundary with ⟨hvN, a, haColor, hva⟩
  rcases hvNonminimum with
    ⟨w, ⟨hwN, b, hbColor, hwb⟩, hwv⟩
  let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let previous : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hpreviousSucc : previous.succ = terminal := by
    apply Fin.ext
    simp [previous, terminal]
    omega
  have htreeTerminal :
      ett.series.data.tree terminal.castSucc =
        ett.series.data.tree ⟨ett.rounds, by omega⟩ := by
    congr 1
  have hpreviousStable :=
    @helper_hpreviousStable_168 V E inferInstance inferInstance inferInstance G k e0 input
        T generating ett hpositive hterminalKind sigma hproper hone hstable v hvFinal q
        hpreviousSucc
  by_cases hqTerminal : q.succ = terminal
  · exact @helper_branch_305 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett hpositive hterminalKind orderTransfer sigma hproper hone delta hdefective v
      hvFinal q vi hkind hchosen hvN a haColor hva hpreviousSucc htreeTerminal hpreviousStable
      hqTerminal
  · exact @helper_branch_373 V E inferInstance inferInstance  inferInstance G k e0
      input T generating ett hMP hpositive hlower stageToStage orderTransfer sigma hproper hone
      delta v hvFinal q vi hkind hchosen hfirstBound hvN a haColor hva w hwv hwN b hbColor hwb
      htreeTerminal hpreviousStable hqTerminal
end GoldbergSeymour

end
