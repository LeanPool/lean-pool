/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary

public import LeanPool.GoldbergSeymour.MaximumPropertyTransport

public import LeanPool.GoldbergSeymour.TashkinovClosureExists

/-!
# Extension Base Closure

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseClosure {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (base : ExtendedTashkinovTree G k e0 input T generating)
    (rho1 : PartialEdgeColoring E k) (seed : TreeSequence G e0)
    (terminalSupport : V) (supportColors : Finset (Fin k))
    (hseedSegment : TreeSequenceInitialSegment
      (base.series.data.tree (Fin.last base.rounds).castSucc) seed)
    (hseedStrict :
      (base.series.data.tree (Fin.last base.rounds).castSucc).length <
        seed.length)
    (hseedEligible :
      (base.series.data.kind (Fin.last base.rounds) =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho1
          (base.series.data.tree (Fin.last base.rounds).castSucc) seed) ∨
      ((base.series.data.kind (Fin.last base.rounds) =
            some TashkinovExtensionKind.SE ∨
          base.series.data.kind (Fin.last base.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          base.series.data.connectingEdges (Fin.last base.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (base.series.data.tree (Fin.last base.rounds).castSucc)
              f adjoinSeed ∧
            TashkinovAugmentationSequence rho1 adjoinSeed seed))
    (hmod : ModColoring base rho1) (hMP : MaximumProperty base)
    (hLowerElementary : ∀ (Tstar : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 base rho1 Tstar),
      MaximumProperty corr.replacementETT →
      ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet Tstar)) :
    ∃ (TjPrime : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 base rho1 TjPrime),
      TashkinovClosure rho1 seed TjPrime ∧
        MaximumProperty corr.replacementETT ∧
        ColoredVertexSetElementary G rho1
          (TreeSequenceVertexSet TjPrime) ∧
        (let awayMissing :=
          ((TreeSequenceVertexSet TjPrime).erase terminalSupport).biUnion
            fun v => MissingColors G rho1 v
         (awayMissing ∩ supportColors).Nonempty ∨
           awayMissing ∩ supportColors = ∅) := by
  classical
  let terminalTree : TreeSequence G e0 :=
    base.series.data.tree (Fin.last base.rounds).castSucc
  have segmentTrans :
    ∀ (A B C : TreeSequence G e0), TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C := by
    intro A B C hab hbc
    rcases hab with ⟨ab, hvab, heab⟩
    rcases hbc with ⟨bc, hvbc, hebc⟩
    have abc : A.length ≤ C.length := by omega
    refine ⟨abc, ?_, ?_⟩
    · intro i
      have hfirst := hvbc (Fin.castLE (Nat.succ_le_succ ab) i)
      have hsecond := hvab i
      have indexMatch :
          Fin.castLE (Nat.succ_le_succ abc) i =
            Fin.castLE (Nat.succ_le_succ bc)
              (Fin.castLE (Nat.succ_le_succ ab) i) := by
        apply Fin.ext
        rfl
      rw [indexMatch]
      exact hfirst.trans hsecond
    · intro j
      have hfirst := hebc (Fin.castLE ab j)
      have hsecond := heab j
      have indexMatch :
          Fin.castLE abc j = Fin.castLE bc (Fin.castLE ab j) := by
        apply Fin.ext
        rfl
      rw [indexMatch]
      exact hfirst.trans hsecond
  have sequenceSegment : ∀ (A B : TreeSequence G e0),
      TashkinovAugmentationSequence rho1 A B →
      TreeSequenceInitialSegment A B := by
    intro A B hseq
    unfold TashkinovAugmentationSequence at hseq
    induction hseq with
    | refl =>
        exact ⟨Nat.le_refl _, by intro i; rfl, by intro j; rfl⟩
    | @tail B C hseq hstep ih =>
        rcases hstep with ⟨hlen, hsegment, color⟩
        exact segmentTrans A B C ih hsegment
  obtain ⟨TjPrime, hclosure⟩ := TashkinovClosureExists rho1 seed
  have seedSegment : TreeSequenceInitialSegment seed TjPrime :=
    sequenceSegment seed TjPrime hclosure.1
  have hprimeSegment : TreeSequenceInitialSegment terminalTree TjPrime := by
    apply segmentTrans terminalTree seed TjPrime
    · simpa [terminalTree] using hseedSegment
    · exact seedSegment
  have hprimeStrict : terminalTree.length < TjPrime.length := by
    rcases seedSegment with ⟨hbound, hv, he⟩
    have hseedle : seed.length ≤ TjPrime.length := hbound
    exact lt_of_lt_of_le (by simpa [terminalTree] using hseedStrict) hseedle
  have eligiblePrime :
      ((base.series.data.kind (Fin.last base.rounds) =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho1 terminalTree TjPrime) ∨
      ((base.series.data.kind (Fin.last base.rounds) =
            some TashkinovExtensionKind.SE ∨
          base.series.data.kind (Fin.last base.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          base.series.data.connectingEdges (Fin.last base.rounds) = {f} ∧
            TreeSequenceAdjoinEdge terminalTree f adjoinSeed ∧
            TashkinovAugmentationSequence rho1 adjoinSeed TjPrime)) := by
    rcases hseedEligible with hpe | hse
    · left
      exact ⟨hpe.1, Relation.ReflTransGen.trans hpe.2 hclosure.1⟩
    · right
      rcases hse with ⟨hkind, f, adjoinSeed, hf, hadjoin, hseq⟩
      exact ⟨hkind, f, adjoinSeed, hf, hadjoin,
        Relation.ReflTransGen.trans hseq hclosure.1⟩
  have correspondence :
      Nonempty (CorrespondingExtendedTashkinovTree G k e0 base rho1 TjPrime) := by
    unfold ModColoring at hmod
    exact hmod.2.2 TjPrime (by simpa [terminalTree] using hprimeSegment)
      (by simpa [terminalTree] using hprimeStrict) (by simpa [terminalTree] using eligiblePrime)
  obtain ⟨corr⟩ := correspondence
  have transported : MaximumProperty corr.replacementETT :=
    MaximumPropertyTransport G k e0 base rho1 hmod TjPrime corr hMP
  have elementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime) := hLowerElementary TjPrime corr transported
  refine ⟨TjPrime, corr, hclosure, transported, elementary, ?_⟩
  let awayMissing :=
    ((TreeSequenceVertexSet TjPrime).erase terminalSupport).biUnion
      (fun v => MissingColors G rho1 v)
  by_cases hnonempty : (awayMissing ∩ supportColors).Nonempty
  · exact Or.inl hnonempty
  · exact Or.inr (Finset.not_nonempty_iff_eq_empty.mp hnonempty)

end GoldbergSeymour

end
