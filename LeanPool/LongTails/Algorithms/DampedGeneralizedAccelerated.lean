/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import LeanPool.LongTails.Setups.GeneralizedSmoothAndConvex
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

namespace LongTails.OracleTemplate.GeneralizedAccelerated

open LongTails.Setups.GeneralizedSmoothAndConvex

/-- The reported point, auxiliary center, accumulated weight and curvature guess. -/
structure Iterate (E : Type*) where
  /-- Accumulated accelerated weight. -/
  A : ℝ
  /-- Point reported after the step. -/
  x : E
  /-- Auxiliary center in the energy potential. -/
  z : E
  /-- Current estimate of the local curvature. -/
  guess : ℝ

/-- A first gradient query and the state needed to consume the second query. -/
structure Pending (E : Type*) where
  /-- Iterate before the current pair of queries. -/
  previous : Iterate E
  /-- Tentative accelerated weight. -/
  weight : ℝ
  /-- Interpolation point used for the first query. -/
  y : E
  /-- Curvature computed from the first gradient. -/
  curvature : ℝ
  /-- Local step at which the second gradient is queried. -/
  point : E

/-- The initialization, first-query and second-query phases of the accelerated algorithm. -/
inductive State (E : Type*) where
  | start (A : ℝ) (x : E)
  | ready (s : Iterate E)
  | pending (p : Pending E)

/-- The positive root of the accelerated weight equation for a curvature guess. -/
noncomputable def tentativeWeight {E : Type*} (s : Iterate E) : ℝ :=
  (1 + Real.sqrt (1 + 4 * s.guess * s.A)) / (2 * s.guess)

/-- The weighted interpolation of the reported point and auxiliary center. -/
noncomputable def coupling {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Iterate E) : E :=
  let a := tentativeWeight s
  (s.A / (s.A + a)) • s.x + (a / (s.A + a)) • s.z

/-- A gradient-dependent curvature bound used to choose a safe local step. -/
noncomputable def localCurvature {E : Type*} [NormedAddCommGroup E]
    (L0 L1 : ℝ) (g : E) : ℝ :=
  4 * (L0 + L1 * ‖g‖)

/-- Form a local gradient step and retain its data for the second gradient query. -/
noncomputable def prepare {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L0 L1 : ℝ) (s : Iterate E) (y g : E) : Pending E :=
  let M := localCurvature L0 L1 g
  ⟨s, tentativeWeight s, y, M, y - (1 / M) • g⟩

/-- Consume the second gradient, damping the update when the curvature guess is too small. -/
noncomputable def finish {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Pending E) (g : E) : Iterate E := by
  classical
  exact
    if p.curvature ≤ p.previous.guess then
      ⟨p.previous.A + p.weight, p.point, p.previous.z - p.weight • g,
        p.previous.guess / 16⟩
    else
      let γ := p.previous.guess / p.curvature
      let a := γ * p.weight
      let A := p.previous.A + a
      ⟨A, ((1 - γ) * p.previous.A / A) • p.previous.x +
          (γ * (p.previous.A + p.weight) / A) • p.point,
        p.previous.z - a • g, 16 * p.previous.guess⟩

/-- One accelerated step, using gradients at the interpolation point and the local step. -/
noncomputable def step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L0 L1 : ℝ) (g : E → E) (s : Iterate E) : Iterate E :=
  let p := prepare L0 L1 s (coupling s) (g (coupling s))
  finish p (g p.point)

/-- Initialize the energy weight from the radius and objective-gap bounds. -/
noncomputable def initialIterate {E : Type*} [NormedAddCommGroup E]
    (L0 L1 R Δ : ℝ) (x0 : E) (g : E → E) : Iterate E :=
  ⟨R ^ 2 / (2 * Δ), x0, x0, localCurvature L0 L1 (g x0)⟩

/-- The accelerated iterate after a fixed number of two-gradient steps. -/
noncomputable def run {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L0 L1 : ℝ) (g : E → E) (s : Iterate E) : ℕ → Iterate E
  | 0 => s
  | n + 1 => step L0 L1 g (run L0 L1 g s n)

/-- The oracle state machine implementing damped acceleration without objective queries. -/
noncomputable def algorithm (p : Public) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := .start (p.R ^ 2 / (2 * p.Δ)) p.x0
  query := fun state => (0, match state with
    | .start _ x => x
    | .ready s => coupling s
    | .pending s => s.point)
  update
    | .start A x, g =>
      let s : Iterate p.E := ⟨A, x, x, localCurvature p.L0 p.L1 g⟩
      .pending (prepare p.L0 p.L1 s x g)
    | .ready s, g => .pending (prepare p.L0 p.L1 s (coupling s) g)
    | .pending s, g => .ready (finish s g)
  output
    | .start _ x => x
    | .ready s => s.x
    | .pending s => s.previous.x

end LongTails.OracleTemplate.GeneralizedAccelerated
