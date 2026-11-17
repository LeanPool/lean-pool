/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.RutgersCurrentRungInterchangeability
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
      have completeLower : LowerRoundInductionHypothesis G k e0 n := by
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
    LowerRoundProperties ett := by
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
