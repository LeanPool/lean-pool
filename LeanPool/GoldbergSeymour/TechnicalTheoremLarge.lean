/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Basic2
public import LeanPool.GoldbergSeymour.ExtensionBase
public import LeanPool.GoldbergSeymour.ExtensionRules
public import LeanPool.GoldbergSeymour.RutgersCurrentRungInterchangeability
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.TechnicalCurrentRungElementaryLarge

/-!
# Technical Theorem Large

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_buildContext_130.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating),
    MaximumProperty ett →
    MaximumDegree G + (1 : ℕ) ≤ k →
    (11 : ℕ) ≤ TashkinovOrder G →
    ∀ (n : ℕ),
    TechnicalInductionContext G k e0 n := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hdegree hlarge n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have completeLower : forall {input : PartialEdgeColoring E k}
          {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
          (ett : ExtendedTashkinovTree G k e0 input T generating),
          0 < ett.rounds -> ett.rounds < n -> MaximumProperty ett ->
          ColoredVertexSetElementary G generating (TreeSequenceVertexSet T) /\
            (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
             let Tnext : TreeSequence G e0 :=
               ett.series.data.tree (Fin.last (ett.rounds + 1))
             forall sigma : PartialEdgeColoring E k,
               IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
               StableColoring Tnext
                 (TashkinovStoredColors ett.series.data terminal)
                 (ett.series.data.coloring terminal) sigma ->
               forall alpha beta : Fin k,
                 (alpha ∈ TreeMissingColors sigma Tnext ∨
                   beta ∈ TreeMissingColors sigma Tnext) ->
                 TreeInterchangeable G Tnext sigma alpha beta) /\
            ((forall (q : Fin ett.rounds) (v : V),
                ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ->
                ett.series.data.chosenVertex q.succ = some v ->
                forall hvFinal : v ∈ TreeSequenceVertexSet T,
                forall j : Fin (ett.rounds + 1),
                  ETTFirstAppearanceIndex ett v hvFinal = j.val + 1 ->
                  forall sigma : PartialEdgeColoring E k,
                    IsProperEdgeColoring G sigma ->
                    IsOneEdgeUncolored sigma e0 ->
                    StableColoring (ett.series.data.tree q.succ.castSucc)
                      (TashkinovStoredColors ett.series.data q.succ)
                      (ett.series.data.coloring q.succ) sigma ->
                    StableColoringBeforeVertex T v hvFinal
                        (TashkinovStoredColors ett.series.data j)
                        (ett.series.data.coloring j) sigma /\
                      (0 < j.val ->
                        StableColoring (ett.series.data.tree j.castSucc)
                          (TashkinovStoredColors ett.series.data j)
                          (ett.series.data.coloring j) sigma)) /\
              forall (q r : Fin ett.rounds) (vq vr : V),
                q ≠ r -> vq ≠ vr ->
                ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ->
                ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ->
                ett.series.data.chosenVertex q.succ = some vq ->
                ett.series.data.chosenVertex r.succ = some vr ->
                forall (hvq : vq ∈ TreeSequenceVertexSet T)
                  (hvr : vr ∈ TreeSequenceVertexSet T),
                  ETTFirstAppearanceIndex ett vq hvq =
                      ETTFirstAppearanceIndex ett vr hvr ->
                  Disjoint (ett.series.data.stored q.succ)
                    (ett.series.data.stored r.succ)) /\
            (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
             let Tterminal : TreeSequence G e0 :=
               ett.series.data.tree terminal.castSucc
             forall (v : V) (gamma delta : Fin k),
               ett.series.data.kind terminal = some TashkinovExtensionKind.PE ->
               ett.series.data.chosenVertex terminal = some v ->
               ett.series.data.gamma terminal = some gamma ->
               ett.series.data.delta terminal = some delta ->
               forall sigma : PartialEdgeColoring E k,
                 IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
                 StableColoring Tterminal
                   (TashkinovStoredColors ett.series.data terminal)
                   (ett.series.data.coloring terminal) sigma ->
                 forall w, w ∈ TreeSequenceVertexSet Tterminal ->
                   (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                       (Sum.inl v) <-> w = v)) /\
            (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
             let Tterminal : TreeSequence G e0 :=
               ett.series.data.tree terminal.castSucc
             forall sigma : PartialEdgeColoring E k,
               IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
               StableColoring Tterminal
                 (TashkinovStoredColors ett.series.data terminal)
                 (ett.series.data.coloring terminal) sigma ->
               forall delta : Fin k,
                 DefectiveColor G sigma (TreeSequenceVertexSet Tterminal) delta ->
                 forall v : V,
                   BoundaryColorVertex G sigma
                       (TreeSequenceVertexSet Tterminal) delta v ->
                   (exists w, BoundaryColorVertex G sigma
                       (TreeSequenceVertexSet Tterminal) delta w /\
                     TreeVertexOrder Tterminal w v) ->
                   forall (hvFinal : v ∈ TreeSequenceVertexSet T)
                     (q : Fin ett.rounds) (vi : V),
                     (ett.series.data.kind q.succ =
                          some TashkinovExtensionKind.PE ∨
                        ett.series.data.kind q.succ =
                          some TashkinovExtensionKind.SE) ->
                     ett.series.data.chosenVertex q.succ = some vi ->
                     ETTFirstAppearanceIndex ett v hvFinal <= q.val + 1 ->
                     v = vi ∨ TreeVertexOrder T v vi) /\
            (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
             let Tterminal : TreeSequence G e0 :=
               ett.series.data.tree terminal.castSucc
             forall sigma : PartialEdgeColoring E k,
               IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
               StableColoring Tterminal
                 (TashkinovStoredColors ett.series.data terminal)
                 (ett.series.data.coloring terminal) sigma ->
               ModColoring ett sigma) := by
        intro input T generating ett hpositive hround hMP
        have ctx : TechnicalInductionContext G k e0 ett.rounds :=
          ih ett.rounds hround
        exact And.intro
          (TechnicalCurrentRungElementaryLarge G k e0 input T generating
            ett hMP ctx hdegree hlarge)
          (And.intro
            (by
              apply RutgersCurrentRungInterchangeability
                G k e0 ett hMP hdegree
              · intro input' T' generating' current hround' hmaximum
                let currentCtx : TechnicalInductionContext
                    G k e0 current.rounds := hround'.symm ▸ ctx
                intro u hu v hv huv
                exact TechnicalCurrentRungElementaryLarge
                  G k e0 input' T' generating' current hmaximum currentCtx
                    hdegree hlarge hu hv huv
              · intro input' T' generating' current hround' hmaximum
                exact ctx.currentFour current hround' hmaximum
              · intro input' T' generating' current hround' hmaximum
                exact ctx.currentSix current hround' hmaximum
              · intro input' T' generating' lower hp hlt hmaximum
                exact ctx.lowerTwo lower hp hlt hmaximum)
            (And.intro (ctx.currentThree ett rfl hMP)
              (And.intro (ctx.currentFour ett rfl hMP)
                (And.intro (ctx.currentFive ett rfl hMP)
                  (ctx.currentSix ett rfl hMP)))))
      refine {
        lowerOne := ?_
        lowerTwo := ?_
        lowerThree := ?_
        lowerFour := ?_
        lowerFive := ?_
        lowerSix := ?_
        currentThree := ?_
        currentFour := ?_
        currentFive := ?_
        currentSix := ?_ }
      · intro input T generating ett hpositive hround hMP
        exact (completeLower ett hpositive hround hMP).1
      · intro input T generating ett hpositive hround hMP
        exact (completeLower ett hpositive hround hMP).2.1
      · intro input T generating ett hpositive hround hMP
        exact (completeLower ett hpositive hround hMP).2.2.1
      · intro input T generating ett hpositive hround hMP
        exact (completeLower ett hpositive hround hMP).2.2.2.1
      · intro input T generating ett hpositive hround hMP
        exact (completeLower ett hpositive hround hMP).2.2.2.2.1
      · intro input T generating ett hpositive hround hMP
        exact (completeLower ett hpositive hround hMP).2.2.2.2.2
      · intro input T generating ett hround hMP
        have hpositive : 0 < ett.rounds := ett.roundsPositive
        apply ExtensionRules G k e0 input T generating ett hMP hpositive
        intro T' generating' lower hp hlt hmax
        exact completeLower lower hp (by omega) hmax
      · intro input T generating ett hround hMP
        have hpositive : 0 < ett.rounds := ett.roundsPositive
        apply ExtensionBase G k e0 input T generating ett hMP hpositive
        intro input' T' generating' lower hp hlt hmax
        exact completeLower lower hp (by omega) hmax
      · intro input T generating ett hround hMP
        have hpositive : 0 < ett.rounds := ett.roundsPositive
        apply Basic2 G k e0 input T generating ett hMP hpositive
        intro input' T' generating' lower hp hlt hmax
        exact completeLower lower hp (by omega) hmax
      · intro input T generating ett hround hMP
        have hpositive : 0 < ett.rounds := ett.roundsPositive
        apply Td G k e0 input T generating ett hMP hpositive
        intro input' T' generating' lower hp hlt hmax
        exact completeLower lower hp (by omega) hmax

theorem TechnicalTheoremLarge
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 11 <= TashkinovOrder G) :
    ColoredVertexSetElementary G generating (TreeSequenceVertexSet T) /\
      (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
       let Tnext : TreeSequence G e0 :=
         ett.series.data.tree (Fin.last (ett.rounds + 1))
       forall sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
         StableColoring Tnext
           (TashkinovStoredColors ett.series.data terminal)
           (ett.series.data.coloring terminal) sigma ->
         forall alpha beta : Fin k,
           (alpha ∈ TreeMissingColors sigma Tnext ∨
             beta ∈ TreeMissingColors sigma Tnext) ->
           TreeInterchangeable G Tnext sigma alpha beta) /\
      ((forall (q : Fin ett.rounds) (v : V),
          ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ->
          ett.series.data.chosenVertex q.succ = some v ->
          forall hvFinal : v ∈ TreeSequenceVertexSet T,
          forall j : Fin (ett.rounds + 1),
            ETTFirstAppearanceIndex ett v hvFinal = j.val + 1 ->
            forall sigma : PartialEdgeColoring E k,
              IsProperEdgeColoring G sigma ->
              IsOneEdgeUncolored sigma e0 ->
              StableColoring (ett.series.data.tree q.succ.castSucc)
                (TashkinovStoredColors ett.series.data q.succ)
                (ett.series.data.coloring q.succ) sigma ->
              StableColoringBeforeVertex T v hvFinal
                  (TashkinovStoredColors ett.series.data j)
                  (ett.series.data.coloring j) sigma /\
                (0 < j.val ->
                  StableColoring (ett.series.data.tree j.castSucc)
                    (TashkinovStoredColors ett.series.data j)
                    (ett.series.data.coloring j) sigma)) /\
        forall (q r : Fin ett.rounds) (vq vr : V),
          q ≠ r -> vq ≠ vr ->
          ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ->
          ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ->
          ett.series.data.chosenVertex q.succ = some vq ->
          ett.series.data.chosenVertex r.succ = some vr ->
          forall (hvq : vq ∈ TreeSequenceVertexSet T)
            (hvr : vr ∈ TreeSequenceVertexSet T),
            ETTFirstAppearanceIndex ett vq hvq =
                ETTFirstAppearanceIndex ett vr hvr ->
            Disjoint (ett.series.data.stored q.succ)
              (ett.series.data.stored r.succ)) /\
      (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
       let Tterminal : TreeSequence G e0 :=
         ett.series.data.tree terminal.castSucc
       forall (v : V) (gamma delta : Fin k),
         ett.series.data.kind terminal = some TashkinovExtensionKind.PE ->
         ett.series.data.chosenVertex terminal = some v ->
         ett.series.data.gamma terminal = some gamma ->
         ett.series.data.delta terminal = some delta ->
         forall sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
           StableColoring Tterminal
             (TashkinovStoredColors ett.series.data terminal)
             (ett.series.data.coloring terminal) sigma ->
           forall w, w ∈ TreeSequenceVertexSet Tterminal ->
             (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                 (Sum.inl v) <-> w = v)) /\
      (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
       let Tterminal : TreeSequence G e0 :=
         ett.series.data.tree terminal.castSucc
       forall sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
         StableColoring Tterminal
           (TashkinovStoredColors ett.series.data terminal)
           (ett.series.data.coloring terminal) sigma ->
         forall delta : Fin k,
           DefectiveColor G sigma (TreeSequenceVertexSet Tterminal) delta ->
           forall v : V,
             BoundaryColorVertex G sigma
                 (TreeSequenceVertexSet Tterminal) delta v ->
             (exists w, BoundaryColorVertex G sigma
                 (TreeSequenceVertexSet Tterminal) delta w /\
               TreeVertexOrder Tterminal w v) ->
             forall (hvFinal : v ∈ TreeSequenceVertexSet T)
               (q : Fin ett.rounds) (vi : V),
               (ett.series.data.kind q.succ =
                    some TashkinovExtensionKind.PE ∨
                  ett.series.data.kind q.succ =
                    some TashkinovExtensionKind.SE) ->
               ett.series.data.chosenVertex q.succ = some vi ->
               ETTFirstAppearanceIndex ett v hvFinal <= q.val + 1 ->
               v = vi ∨ TreeVertexOrder T v vi) /\
      (let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
       let Tterminal : TreeSequence G e0 :=
         ett.series.data.tree terminal.castSucc
       forall sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
         StableColoring Tterminal
           (TashkinovStoredColors ett.series.data terminal)
           (ett.series.data.coloring terminal) sigma ->
         ModColoring ett sigma) := by
  classical
  have buildContext := @helper_buildContext_130 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T generating ett hMP hdegree hlarge
  have ctx : TechnicalInductionContext G k e0 (ett.rounds + 1) :=
    buildContext (ett.rounds + 1)
  have hround : ett.rounds < ett.rounds + 1 := by omega
  exact And.intro
    (ctx.lowerOne ett ett.roundsPositive hround hMP)
    (And.intro
      (ctx.lowerTwo ett ett.roundsPositive hround hMP)
      (And.intro
        (ctx.lowerThree ett ett.roundsPositive hround hMP)
        (And.intro
          (ctx.lowerFour ett ett.roundsPositive hround hMP)
          (And.intro
            (ctx.lowerFive ett ett.roundsPositive hround hMP)
            (ctx.lowerSix ett ett.roundsPositive hround hMP)))))

end GoldbergSeymour

end
