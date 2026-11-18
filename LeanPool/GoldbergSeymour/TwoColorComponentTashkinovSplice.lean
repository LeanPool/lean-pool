/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.TashkinovAlternatingSegmentAppend
public import LeanPool.GoldbergSeymour.TwoColorComponentNearestSegment

/-!
# Two Color Component Tashkinov Splice

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem TwoColorComponentTashkinovSplice
    {V E : Type*}
    [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (S : TreeSequence G e0)
    (alpha beta : Fin k) (y : V)
    (hproper : IsProperEdgeColoring G phi)
    (hne : alpha ≠ beta)
    (halpha : alpha ∈ TreeMissingColors phi S)
    (hbeta : beta ∈ TreeMissingColors phi S)
    (hy : y ∉ TreeSequenceVertexSet S)
    (hmeets : ∃ u ∈ TreeSequenceVertexSet S,
      Sum.inl u ∈ TwoColorComponent G phi alpha beta (Sum.inl y)) :
    ∃ (u : V) (S' : TreeSequence G e0),
      u ∈ TreeSequenceVertexSet S /\
        Sum.inl u ∈
          TwoColorComponent G phi alpha beta (Sum.inl y) /\
        TreeSequenceInitialSegment S S' /\
        S.length < S'.length /\
        TashkinovAugmentationSequence phi S S' /\
        S'.vertex (Fin.last S'.length) = y /\
        ∀ r : Fin S'.length, S.length ≤ r.val →
          S'.vertex r.succ ∉ TreeSequenceVertexSet S /\
            Sum.inr (S'.edge r) ∈
              TwoColorComponent G phi alpha beta (Sum.inl y) /\
            Sum.inl (S'.vertex r.succ) ∈
              TwoColorComponent G phi alpha beta (Sum.inl y) /\
            (phi (S'.edge r) = some alpha ∨
              phi (S'.edge r) = some beta) /\
            G.ends (S'.edge r) =
              if r.val = S.length then
                s(u, S'.vertex r.succ)
              else
                s(S'.vertex r.castSucc, S'.vertex r.succ) := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨m, hm, pathVertex, pathEdge, hvertexInjective,
      hedgeInjective, hstart, hlast, houtside, hvertexComponent,
      hedgeComponent, hcolors, hends, hedgeFresh⟩ :=
    TwoColorComponentNearestSegment G phi S alpha beta y hproper hne hy hmeets
  obtain ⟨S', hSS', _hlengthEq, _hsegmentEntries, hlength, haugment,
      hlastVertex, hnew⟩ :=
    TashkinovAlternatingSegmentAppend G phi S alpha beta y m hm
      pathVertex pathEdge hvertexInjective hedgeInjective hstart houtside
      hvertexComponent hedgeComponent hcolors hends hedgeFresh halpha hbeta
  refine ⟨pathVertex 0, S', hstart, hvertexComponent 0, hSS', hlength,
    haugment, ?_, hnew⟩
  rw [hlastVertex, hlast]

end GoldbergSeymour

end
