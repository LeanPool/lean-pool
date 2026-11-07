/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TerminalPrefixReconstruction
public import LeanPool.GoldbergSeymour.StableColoringFullCertificate
public import LeanPool.GoldbergSeymour.TerminalHierarchyRestore
public import LeanPool.GoldbergSeymour.MinimumContextTransport
public import LeanPool.GoldbergSeymour.NormalizedDatum

/-!
# Hierarchy Situation Two Outside Penultimate Reconstruction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchySituationTwoOutsidePenultimateReconstruction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeData
      G k e0 input T phi ett base C ctx)
    (beta : Fin k)
    (hbetaMissingTwoBefore :
      beta ∈ TreeMissingColors phi
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)))
    (hbetaUnusedOnFullTail :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta)
    (hbetaAlternative :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Dn := TashkinovStoredColors ett.series.data n
      let Dnq := HierarchyStoredColorsAt H q
      let Gamma := Dnq.biUnion (C.good.gamma q)
      let A := HierarchyStarredStage H q
      let tailUsed := (Finset.univ : Finset (Fin k)).filter fun c =>
        ∃ t : Fin T.length, A.length ≤ t.val ∧
          phi (T.edge t) = some c
      (0 < H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma) ∨
        (H.dividerCount = 0 ∧ beta ∉ Dn ∧ beta ∉ Gamma) ∨
        (beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed))
    (hbetaPresentTerminal :
      beta ∉ MissingColors G phi (T.vertex D.terminalVertexIndex))
    (houtsidePenultimate :
      let Bplus := HierarchyFullTailPrefix C
        (HierarchyFullTailLength C - 1)
      let yp := T.vertex D.terminalVertexIndex
      ∀ v : V,
        Sum.inl v ∈ TwoColorComponent G phi D.alpha beta (Sum.inl yp) →
          v ∉ TreeSequenceVertexSet Bplus) :
    let _ := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
    let yp := T.vertex D.terminalVertexIndex
    let Q := TwoColorComponent G phi D.alpha beta (Sum.inl yp)
    let sigma := TwoColorComponentSwap G phi D.alpha beta (Sum.inl yp)
    Sum.inl yp ∈ Q ∧
      (∃ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ Q) ∧
      ∃ P : HierarchyReplacementPresentation
          G k e0 input T phi ett base C ctx,
        P.coloring = sigma ∧
          ∃ N : HierarchySituationTwoCaseThreeNormalizedData
              G k e0 P.corresponding.replacementInput T P.coloring
                P.corresponding.replacementETT P.replacementBase
                P.counterexample P.minimumContext,
            N.alpha = beta := by
  classical
  dsimp only
  let sigma := TwoColorComponentSwap G phi D.alpha beta
    (Sum.inl (T.vertex D.terminalVertexIndex))
  let Bplus := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  obtain ⟨hroot, hmeet, hfixed, hstable, hterminal, ⟨F⟩⟩ :=
    P2752_T2_PrefixReconstruction G k e0 input T phi ett base C ctx D beta
      hbetaUnusedOnFullTail hbetaPresentTerminal houtsidePenultimate
  obtain ⟨corr, hMP⟩ := P2752_T2_FullCertificate G k e0 input T phi sigma
    ett base C ctx Bplus F hfixed hstable
  obtain ⟨newBase, K, good, hsame⟩ :=
    P2752_T2_TerminalHierarchyRestore G k e0 input T phi sigma ett base C ctx D
      beta hbetaMissingTwoBefore hbetaPresentTerminal rfl F hfixed corr
  let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, (fun _ => rfl), (fun _ => rfl)⟩
  have hlenB : B.length = T.length - 2 := by
    let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
    have hp : 2 ≤ T.length - A.length := D.tailAtLeastTwo
    change min (A.length + (T.length - A.length - 2)) T.length = T.length - 2
    omega
  have hBplus : TreeSequenceInitialSegment B Bplus := by
    have hle : B.length ≤ Bplus.length := by
      have hp : T.length = Bplus.length + 1 := F.penultimateLength
      omega
    refine ⟨hle, ?_, ?_⟩
    · intro i
      rw [← F.belowFull.2.1 (Fin.castLE (Nat.succ_le_succ hle) i)]
      convert hBT.2.1 i using 1
      congr 1
    · intro i
      rw [← F.belowFull.2.2 (Fin.castLE hle i)]
      convert hBT.2.2 i using 1
      congr 1
  have hnotElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) := by
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hbetaMissingTwoBefore
    have hvplus := TreeSequenceInitialSegmentVertexSetSubset hBplus hv
    have hmissing : beta ∈ MissingColors G sigma v := by
      rw [F.invariant.2 v hvplus]
      exact hm
    have hne : v ≠ T.vertex D.terminalVertexIndex := by
      intro heq
      exact houtsidePenultimate (T.vertex D.terminalVertexIndex) hroot (heq ▸ hvplus)
    intro helementary
    have hd := helementary (TreeSequenceInitialSegmentVertexSetSubset hBT hv)
      (by simp [TreeSequenceVertexSet]) hne
    exact Finset.disjoint_left.mp hd hmissing hterminal
  let Cnew : HierarchyCounterexample newBase := {
    positive := by rw [corr.rungAgreement]; exact C.positive
    hierarchy := K
    good := good
    maximum := hMP
    notElementary := hnotElementary }
  obtain ⟨newContext⟩ := P2752_T2_MinimumContextTransport G k e0 input T phi sigma
    ett base C ctx corr newBase Cnew hsame
  let P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := {
    coloring := sigma
    corresponding := corr
    maximum := hMP
    replacementBase := newBase
    counterexample := Cnew
    sameGood := hsame
    minimumContext := newContext }
  obtain ⟨N, hN⟩ := P2752_T2_NormalizedDatum G k e0 input T phi ett base C ctx D
    beta hbetaMissingTwoBefore hbetaUnusedOnFullTail hbetaAlternative P
    hfixed F.invariant hterminal
  exact ⟨hroot, hmeet, P, rfl, N, hN⟩

end GoldbergSeymour

end
