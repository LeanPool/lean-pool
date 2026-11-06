/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySplitter

/-!
# Stable replacement of a hierarchy inside a region

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A stable coloring replacement preserves the hierarchy stages inside its controlled region. -/
theorem TashkinovHierarchy.stableReplacement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input phi : PartialEdgeColoring E k} {B : TreeSequence G e0}
    {ett : ExtendedTashkinovTree G k e0 input B phi} {base : HierarchyBase ett phi}
    (HB : TashkinovHierarchy ett base) (maximum : MaximumProperty ett)
    (lower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (region : TreeSequence G e0) (coreToRegion : TreeSequenceInitialSegment base.core region)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G phi) (hone : IsOneEdgeUncolored phi e0)
    (sigmaProper : IsProperEdgeColoring G sigma) (sigmaOne : IsOneEdgeUncolored sigma e0)
    (stableRegion : ∀ S : TreeSequence G e0,
      TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet region →
        ∀ D : Finset (Fin k), StableColoring S D phi sigma)
    (stableTn : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma)
    (terminalRoute :
      let n := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi Tn B) ∨
      (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0),
        ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence phi seed B)
    (routeTransport : ∀ S : TreeSequence G e0,
      TashkinovAugmentationSequence phi S B → TashkinovAugmentationSequence sigma S B) :
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma B,
      MaximumProperty corr.replacementETT ∧
      ∃ (baseS : HierarchyBase corr.replacementETT sigma)
        (HS : TashkinovHierarchy corr.replacementETT baseS), SameHierarchyStages HB HS := by
  classical
  let n := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  have TnToB : TreeSequenceInitialSegment Tn B := ett.abovePenultimate
  have TnStrictB : Tn.length < B.length := ett.strictAbovePenultimate
  by_cases hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · have closureSubset : TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet region := by
      obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hPE
      intro v hv
      apply TreeSequenceInitialSegmentVertexSetSubset coreToRegion
      rw [u.vertexSet]
      exact Finset.mem_union_right _ hv
    have hcombined : CombinedStableColoring Tn base.closure Dn phi sigma :=
      ⟨stableTn, stableRegion base.closure closureSubset ∅⟩
    have hseq : TashkinovAugmentationSequence sigma Tn B := by
      rcases terminalRoute with ⟨_, hs⟩ | ⟨hk, _⟩
      · exact routeTransport Tn hs
      · rcases hk with hk | hk <;> rw [hPE] at hk <;> cases hk
    exact HierarchySplitter G k e0 input B phi sigma ett maximum ett.roundsPositive
      lower base HB hPE hproper hone sigmaProper sigmaOne hcombined hseq
  · have hmod : ModColoring ett sigma :=
      Td G k e0 input B phi ett maximum ett.roundsPositive lower sigma sigmaProper sigmaOne
        (by simpa only [← ett.generatingColoring, n, Tn, Dn] using stableTn)
    have hroute :
        ((ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn B) ∨
        ((ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed B)) := by
      rcases terminalRoute with ⟨hp, _⟩ | ⟨hk, f, seed, hedges, hadjoin, hs⟩
      · exact (hPE hp).elim
      · exact Or.inr ⟨hk, f, seed, hedges, hadjoin, routeTransport seed hs⟩
    obtain ⟨corr⟩ := hmod.2.2 B TnToB TnStrictB hroute
    have hMP := MaximumPropertyTransport G k e0 ett sigma hmod B corr maximum
    refine ⟨corr, hMP, ?_⟩
    rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
      hedges, hkinds, hproperSeries, honeSeries, hstableSeries⟩
    rcases newETT with ⟨r, rp, series, above, strict, below, gen⟩
    cases hr
    have heq : series = newSeries := eq_of_heq hs
    cases heq
    let rep : ExtendedTashkinovTree G k e0 newInput B sigma :=
      ⟨ett.rounds, rp, newSeries, above, strict, below, gen⟩
    let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
    have hj : j.succ = n := Fin.ext (by simp [j, n]; have := ett.roundsPositive; omega)
    have htree : newSeries.data.tree n.castSucc = Tn := by simpa [hj, Tn] using htrees j
    have hkind := hkinds n
    let pos : Fin ((newSeries.data.tree n.castSucc).length + 1) :=
      Fin.cast (congrArg (fun S : TreeSequence G e0 => S.length + 1) htree.symm)
        base.supportPosition
    let baseS : HierarchyBase rep sigma :=
      { core := base.core
        closure := base.closure
        supportPosition := pos
        supportPositive := by simpa [pos] using base.supportPositive
        terminalMissingColors := rfl
        parallel := by
          dsimp only [rep]
          intro hp
          exact (hPE (hkind.symm.trans hp)).elim
        nonparallel := by
          dsimp only [rep]
          intro hp
          exact (base.nonparallel hPE).trans htree.symm }
    let HS : TashkinovHierarchy rep baseS :=
      { dividerCount := HB.dividerCount
        stage := HB.stage
        baseStage := HB.baseStage.trans htree.symm
        terminalStage := HB.terminalStage
        nested := HB.nested
        strict := HB.strict
        dividerPosition := HB.dividerPosition
        dividerPositive := HB.dividerPositive
        dividerIncreasing := HB.dividerIncreasing
        dividerStage := HB.dividerStage
        coreInsideFirst := HB.coreInsideFirst }
    refine ⟨baseS, HS, ?_⟩
    refine ⟨rfl, rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
    · exact ⟨fun hp => (hPE hp).elim, fun hp => (hPE (hkind.symm.trans hp)).elim⟩
    · intro hp; exact (hPE hp).elim


end GoldbergSeymour

end
