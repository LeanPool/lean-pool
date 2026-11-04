/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Algebra.Order.Floor.Ring
public import LeanPool.LongTails.Template

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

namespace LongTails.Setups.SmoothAndConvex

universe u

open LongTails.OracleTemplate

/-- Problem information available to the method, excluding its target accuracy. -/
structure Public where
  /-- Real Hilbert space in which optimization takes place. -/
  E : Type u
  /-- Normed additive structure of the optimization space. -/
  [normedE : NormedAddCommGroup E]
  /-- Real inner product defining gradients. -/
  [linearE : InnerProductSpace ℝ E]
  /-- Completeness of the optimization space. -/
  [completeE : CompleteSpace E]
  /-- Global Lipschitz bound for the gradient. -/
  L : ℝ
  /-- Initial point of the algorithm. -/
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.completeE

/-- Public problem information together with the parameters of the accuracy guarantee. -/
structure Params extends Public where
  /-- Bound on the initial distance to a minimizer. -/
  R : ℝ
  /-- Positive target objective-gap accuracy. -/
  ε : ℝ

/-- Convex optimization with exact gradients and the displayed regularity assumptions. -/
abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid q := 0 < q.L ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q f oracle :=
    ConvexOn ℝ Set.univ f ∧
    (∀ k seed x, HasGradientAt f (oracle.answer k (0, x) seed) x) ∧
    (∀ k seed x y, ‖oracle.answer k (0, x) seed - oracle.answer k (0, y) seed‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R)
  successful q f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ q.ε

end LongTails.Setups.SmoothAndConvex
