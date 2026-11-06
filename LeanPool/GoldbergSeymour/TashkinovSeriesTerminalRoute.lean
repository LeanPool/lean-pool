/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict

/-!
# The last certified extension on a terminal prefix

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A nontrivial terminal prefix retains the last certified extension route. -/
theorem TashkinovSeries.terminalRoute {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (positive : 0 < rounds) (phi : PartialEdgeColoring E k)
    (coloringEqual : phi = series.data.coloring (Fin.last rounds))
    (B : TreeSequence G e0)
    (TnToB : TreeSequenceInitialSegment (series.data.tree (Fin.last rounds).castSucc) B)
    (TnStrictB : (series.data.tree (Fin.last rounds).castSucc).length < B.length)
    (BToFinal : TreeSequenceInitialSegment B
      (series.data.tree (Fin.last (rounds + 1)))) :
    let n := Fin.last rounds
    let Tn := series.data.tree n.castSucc
    (series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence phi Tn B) ∨
    ((series.data.kind n = some TashkinovExtensionKind.SE ∨
      series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0),
        series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
        TashkinovAugmentationSequence phi seed B) := by
  classical
  let n := Fin.last rounds
  let Tn := series.data.tree n.castSucc
  change Tn.length < B.length at TnStrictB
  have step := series.certified n
  generalize hi : n = i at step
  cases step with
  | initial => have hv := congrArg Fin.val hi; simp [n] at hv; have := positive; omega
  | SE j _ _ _ _ _ choice _ coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hroute : TashkinovAugmentationSequence phi seed
        (series.data.tree (Fin.last (rounds + 1))) := by
      simpa [hj, hlast, ← coloringEqual, n] using closure.1
    have hseedB : TreeSequenceInitialSegment seed B :=
      TreeSequenceInitialSegment.of_common_extension BToFinal
        (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute) (by
            have hl := adjoin.1
            rw [hj] at hl
            change seed.length = Tn.length + 1 at hl
            omega)
    exact Or.inr ⟨Or.inl (by simpa [hj] using kind), choice.edge, seed,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
      TashkinovAugmentationSequenceRestrict phi seed B _ hroute hseedB BToFinal⟩
  | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
      edges kind vertex outside delta gammaEq closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    refine Or.inl ⟨by simpa [hj] using kind, ?_⟩
    apply TashkinovAugmentationSequenceRestrict phi Tn B _ _ TnToB BToFinal
    simpa [Tn, hj, hlast, ← coloringEqual, n] using closure.1
  | RE j _ _ _ _ available coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hroute : TashkinovAugmentationSequence phi seed
        (series.data.tree (Fin.last (rounds + 1))) := by
      simpa [hj, hlast, ← coloringEqual, n] using closure.1
    have hseedB : TreeSequenceInitialSegment seed B :=
      TreeSequenceInitialSegment.of_common_extension BToFinal
        (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute) (by
            have hl := adjoin.1
            rw [hj] at hl
            change seed.length = Tn.length + 1 at hl
            omega)
    exact Or.inr ⟨Or.inr (by simpa [hj] using kind), available.edge, seed,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
      TashkinovAugmentationSequenceRestrict phi seed B _ hroute hseedB BToFinal⟩

end GoldbergSeymour

end
