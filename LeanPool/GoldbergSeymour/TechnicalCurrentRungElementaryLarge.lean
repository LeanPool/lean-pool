/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CurrentElementaryOrGoodHierarchyConstructionLarge

/-!
# Technical Current Rung Elementary Large

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TechnicalCurrentRungElementaryLarge
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 11 <= TashkinovOrder G) :
    ColoredVertexSetElementary G generating
      (TreeSequenceVertexSet T) := by
  rcases CurrentElementaryOrGoodHierarchyConstructionLarge
      G k e0 input T generating ett hMP ctx hdegree hlarge with
    hElementary | ⟨U, corrU, hMPU, baseU, H, good, _, hvertices⟩
  · exact hElementary
  · have hlower : forall {input' : PartialEdgeColoring E k}
        {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
        0 < lower.rounds ->
        lower.rounds < corrU.replacementETT.rounds ->
        MaximumProperty lower ->
        ColoredVertexSetElementary G generating'
            (TreeSequenceVertexSet T') /\
          (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
           let Tnext : TreeSequence G e0 :=
             lower.series.data.tree (Fin.last (lower.rounds + 1))
           forall sigma : PartialEdgeColoring E k,
             IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
             StableColoring Tnext
               (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma ->
             forall alpha beta : Fin k,
               (alpha ∈ TreeMissingColors sigma Tnext \/
                 beta ∈ TreeMissingColors sigma Tnext) ->
               TreeInterchangeable G Tnext sigma alpha beta) /\
          ((forall (q : Fin lower.rounds) (v : V),
            lower.series.data.kind q.succ =
                some TashkinovExtensionKind.PE ->
            lower.series.data.chosenVertex q.succ = some v ->
            forall hvFinal : v ∈ TreeSequenceVertexSet T',
            forall j : Fin (lower.rounds + 1),
              ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 ->
              forall sigma : PartialEdgeColoring E k,
                IsProperEdgeColoring G sigma ->
                IsOneEdgeUncolored sigma e0 ->
                StableColoring
                  (lower.series.data.tree q.succ.castSucc)
                  (TashkinovStoredColors lower.series.data q.succ)
                  (lower.series.data.coloring q.succ) sigma ->
                StableColoringBeforeVertex T' v hvFinal
                    (TashkinovStoredColors lower.series.data j)
                    (lower.series.data.coloring j) sigma /\
                  (0 < j.val ->
                    StableColoring (lower.series.data.tree j.castSucc)
                      (TashkinovStoredColors lower.series.data j)
                      (lower.series.data.coloring j) sigma)) /\
            forall (q r : Fin lower.rounds) (vq vr : V),
              q ≠ r -> vq ≠ vr ->
              lower.series.data.kind q.succ =
                  some TashkinovExtensionKind.PE ->
              lower.series.data.kind r.succ =
                  some TashkinovExtensionKind.PE ->
              lower.series.data.chosenVertex q.succ = some vq ->
              lower.series.data.chosenVertex r.succ = some vr ->
              forall (hvq : vq ∈ TreeSequenceVertexSet T')
                (hvr : vr ∈ TreeSequenceVertexSet T'),
                ETTFirstAppearanceIndex lower vq hvq =
                    ETTFirstAppearanceIndex lower vr hvr ->
                Disjoint (lower.series.data.stored q.succ)
                  (lower.series.data.stored r.succ)) /\
          (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
           let Tn : TreeSequence G e0 :=
             lower.series.data.tree n.castSucc
           forall (v : V) (gamma delta : Fin k),
             lower.series.data.kind n = some TashkinovExtensionKind.PE ->
             lower.series.data.chosenVertex n = some v ->
             lower.series.data.gamma n = some gamma ->
             lower.series.data.delta n = some delta ->
             forall sigma : PartialEdgeColoring E k,
               IsProperEdgeColoring G sigma ->
               IsOneEdgeUncolored sigma e0 ->
               StableColoring Tn
                 (TashkinovStoredColors lower.series.data n)
                 (lower.series.data.coloring n) sigma ->
               forall w, w ∈ TreeSequenceVertexSet Tn ->
                 (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                     (Sum.inl v) <-> w = v)) /\
          (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
           let Tn : TreeSequence G e0 :=
             lower.series.data.tree n.castSucc
           forall sigma : PartialEdgeColoring E k,
             IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
             StableColoring Tn
               (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma ->
             forall (delta : Fin k),
               DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta ->
               forall (v : V),
                 BoundaryColorVertex G sigma
                     (TreeSequenceVertexSet Tn) delta v ->
                 (exists w, BoundaryColorVertex G sigma
                     (TreeSequenceVertexSet Tn) delta w /\
                   TreeVertexOrder Tn w v) ->
                 forall (hvFinal : v ∈ TreeSequenceVertexSet T')
                   (q : Fin lower.rounds) (vi : V),
                   (lower.series.data.kind q.succ =
                        some TashkinovExtensionKind.PE \/
                      lower.series.data.kind q.succ =
                        some TashkinovExtensionKind.SE) ->
                   lower.series.data.chosenVertex q.succ = some vi ->
                   ETTFirstAppearanceIndex lower v hvFinal <= q.val + 1 ->
                   v = vi \/ TreeVertexOrder T' v vi) /\
          (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
           let Tn : TreeSequence G e0 :=
             lower.series.data.tree n.castSucc
           forall sigma : PartialEdgeColoring E k,
             IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
             StableColoring Tn
               (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma ->
             ModColoring lower sigma) := by
      intro input' T' generating' lower hpositive hround hmaximum
      have hround' : lower.rounds < ett.rounds := by
        simpa [corrU.rungAgreement] using hround
      exact ⟨ctx.lowerOne lower hpositive hround' hmaximum,
        ctx.lowerTwo lower hpositive hround' hmaximum,
        ctx.lowerThree lower hpositive hround' hmaximum,
        ctx.lowerFour lower hpositive hround' hmaximum,
        ctx.lowerFive lower hpositive hround' hmaximum,
        ctx.lowerSix lower hpositive hround' hmaximum⟩
    have hcurrent := fun {input' : PartialEdgeColoring E k}
        {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (current : ExtendedTashkinovTree G k e0 input' T' generating')
        (hround : current.rounds = corrU.replacementETT.rounds)
        (hmaximum : MaximumProperty current) =>
      And.intro
        (ctx.currentThree current (hround.trans corrU.rungAgreement) hmaximum)
        (And.intro
          (ctx.currentFour current (hround.trans corrU.rungAgreement) hmaximum)
          (And.intro
            (ctx.currentFive current (hround.trans corrU.rungAgreement) hmaximum)
            (ctx.currentSix current (hround.trans corrU.rungAgreement)
              hmaximum)))
    have hbound := fun {input' : PartialEdgeColoring E k}
        {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (current : ExtendedTashkinovTree G k e0 input' T' generating')
        (hround : current.rounds = corrU.replacementETT.rounds)
        (hmaximum : MaximumProperty current)
        (_ : HierarchyBase current generating')
        (_ : TashkinovHierarchy current ‹HierarchyBase current generating'›)
        (_ : GoodHierarchy ‹TashkinovHierarchy current
          ‹HierarchyBase current generating'››) => by
      have hround' : current.rounds = ett.rounds :=
        hround.trans corrU.rungAgreement
      let currentCtx : TechnicalInductionContext G k e0 current.rounds :=
        hround'.symm ▸ ctx
      exact TechnicalCurrentLadderMissingBoundLarge
        G k e0 input' T' generating' current hmaximum currentCtx
          hdegree hlarge
    have hUElementary : ColoredVertexSetElementary G generating
        (TreeSequenceVertexSet U) := by
      exact GoodHierarchyElementaryLarge
        G k e0 corrU.replacementInput U generating corrU.replacementETT
          hMPU baseU H good hlower hcurrent hlarge hbound
    have hsubsetFinal :=
      TreeSequenceInitialSegmentVertexSetSubset ett.belowFinal
    have hsubsetU : TreeSequenceVertexSet T ⊆ TreeSequenceVertexSet U := by
      simpa [hvertices] using hsubsetFinal
    intro u hu v hv huv
    exact hUElementary (hsubsetU hu) (hsubsetU hv) huv

end GoldbergSeymour

end
