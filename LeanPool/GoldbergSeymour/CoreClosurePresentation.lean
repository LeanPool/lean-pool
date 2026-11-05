/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingTerminalClosureEq

public import LeanPool.GoldbergSeymour.HierarchyBaseCorrespondingTransport
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment

public import LeanPool.GoldbergSeymour.TashkinovClosureExists

/-!
# P2634_T1_Core Closure Presentation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2634_T1_CoreClosurePresentation
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hmod : ModColoring ett phi)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett phi)
    (hroute : TashkinovAugmentationSequence phi
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) base.core)
    (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
      base.core.length) :
    exists (Z : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi Z),
      MaximumProperty corr.replacementETT /\
        TashkinovClosure phi base.core Z /\
        corr.replacementETT.series.data.tree
            (Fin.last (corr.replacementETT.rounds + 1)) = Z /\
        corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc /\
        corr.replacementETT.series.data.kind
            (Fin.last corr.replacementETT.rounds) =
          some TashkinovExtensionKind.PE /\
        exists baseZ : HierarchyBase corr.replacementETT phi,
          baseZ.core = base.core /\ baseZ.closure = base.closure /\
            baseZ.supportPosition.val = base.supportPosition.val := by
  obtain ⟨Z, hclosure⟩ := TashkinovClosureExists phi base.core
  have hsequence : TashkinovAugmentationSequence phi
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) Z :=
    hroute.trans hclosure.1
  have hsegment := TashkinovAugmentationSequenceInitialSegment phi
    (ett.series.data.tree (Fin.last ett.rounds).castSucc) Z hsequence
  have hcoreSegment := TashkinovAugmentationSequenceInitialSegment phi
    base.core Z hclosure.1
  obtain ⟨corr⟩ := hmod.2.2 Z hsegment (lt_of_lt_of_le hstrict hcoreSegment.1)
    (Or.inl ⟨hPE, hsequence⟩)
  have hfinal := CorrespondingTerminalClosureEq G k e0 input T phi ett phi Z
    (ett.series.data.tree (Fin.last ett.rounds).castSucc) corr
    (Or.inl ⟨hPE, rfl⟩) ⟨hsequence, hclosure.2⟩
  have hmax := MaximumPropertyTransport G k e0 ett phi hmod Z corr hMP
  obtain ⟨baseZ, hcore, hcl, hsupport⟩ :=
    HierarchyBaseCorrespondingTransport G k e0 input T Z phi ett corr base
  have hindices :
      corr.replacementETT.series.data.tree
          (Fin.last (corr.replacementETT.rounds + 1)) = Z /\
      corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc /\
      corr.replacementETT.series.data.kind
          (Fin.last corr.replacementETT.rounds) =
        some TashkinovExtensionKind.PE := by
    rcases corr with ⟨inputZ, seriesZ, ettZ, hr, hs, hc, ht, hd, he, hk,
      hp, ho, hstable⟩
    cases ettZ with
    | mk rounds positive series above strict below generating =>
      cases hr
      have hseries : series = seriesZ := eq_of_heq hs
      cases hseries
      have hn : 0 < ett.rounds := by have := ett.roundsPositive; omega
      let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
      have hq : q.succ = Fin.last ett.rounds := by
        apply Fin.ext
        simp [q]
        omega
      refine ⟨hfinal, ?_, (hk (Fin.last ett.rounds)).trans hPE⟩
      simpa only [hq] using ht q
  exact ⟨Z, corr, hmax, hclosure, hindices.1, hindices.2.1,
    hindices.2.2, baseZ, hcore, hcl, hsupport⟩

end GoldbergSeymour

end
