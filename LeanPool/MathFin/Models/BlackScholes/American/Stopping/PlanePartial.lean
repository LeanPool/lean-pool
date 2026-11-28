/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Directional derivatives of plane functions

The directional derivative `planePartial G v z = fderiv ℝ G z v` of a function on the `(t, x)`
plane, with its smoothness and its reading as the ordinary time and space derivatives. Shared by
the heat-boundary equation (`HeatBoundaryEquation`) and Itô's formula for plane functions
(`PlaneIto`).

## Main definitions

* `planePartial`: the directional derivative `fderiv ℝ G z v` of a plane function `G` at `z` along
  `v`.

## Main results

* `planePartial_contDiff`: if `G` is `C^(n+1)`, each directional derivative `planePartial G v`
  is `C^n`.
* `planePartial_smoothAt`: if `G` is `C^∞` at `z`, so is `planePartial G v`.
* `planePartial_hasDeriv_time`, `planePartial_hasDeriv_space`: if `G` is differentiable at
  `(t,w)`, its partial in the direction `(1,0)` (resp. `(0,1)`) is the ordinary derivative of
  `s ↦ G (s,w)` (resp. `y ↦ G (t,y)`).

## Tags

directional derivative, partial derivatives, plane function, space-time derivative,
Fréchet derivative, MSC 35R35, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open scoped ContDiff

/-- The directional derivative `fderiv ℝ G z v` of a plane function `G` at `z` along `v`. -/
noncomputable def planePartial (G : ℝ × ℝ → ℝ) (v : ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ G z v

theorem planePartial_contDiff {G : ℝ × ℝ → ℝ} {n : ℕ} (hG : ContDiff ℝ (n + 1) G)
    (v : ℝ × ℝ) : ContDiff ℝ n (planePartial G v) :=
  (hG.fderiv_right (m := n) (by norm_cast)).clm_apply contDiff_const

theorem planePartial_smoothAt {G : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hG : ContDiffAt ℝ ∞ G z) (v : ℝ × ℝ) :
    ContDiffAt ℝ ∞ (planePartial G v) z :=
  (hG.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem planePartial_hasDeriv_time {G : ℝ × ℝ → ℝ} {t w : ℝ}
    (hG : DifferentiableAt ℝ G (t, w)) :
    HasDerivAt (fun s => G (s,w)) (planePartial G (1,0) (t,w)) t := by
  simpa only [Function.comp_def,id_eq,planePartial] using hG.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t w))

theorem planePartial_hasDeriv_space {G : ℝ × ℝ → ℝ} {t w : ℝ}
    (hG : DifferentiableAt ℝ G (t, w)) :
    HasDerivAt (fun y => G (t,y)) (planePartial G (0,1) (t,w)) w := by
  simpa only [Function.comp_def,id_eq,planePartial] using hG.hasFDerivAt.comp_hasDerivAt w
    ((hasDerivAt_const w t).prodMk (hasDerivAt_id w))

end MathFin.BlackScholes.AmericanPut.Stopping
