/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.Reduction
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # The derivatives of raw SVI variance

Part of the SVI polynomial-sign certificate (#174).

For `σ > 0`, `slope` and `curvature` are the first and second derivatives of `variance` in
log-strike.

## Main results

* `variance_hasDerivAt`: for `σ > 0`, `slope p k` is the derivative of `variance p` at `k`.
* `slope_hasDerivAt`: for `σ > 0`, `curvature p k` is the derivative of `slope p` at `k`.
* `deriv_variance`, `deriv_slope`: the same statements as `deriv (variance p) = slope p` and
  `deriv (slope p) = curvature p`.

## Tags

raw SVI, variance slope, variance curvature, log-strike derivative, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

theorem variance_hasDerivAt (p : Params) (hs : 0 < p.sigma) (k : ℝ) :
    HasDerivAt (variance p) (slope p k) k := by
  have hpos : 0 < (k - p.m)^2 + p.sigma^2 := by positivity
  have hx := (hasDerivAt_id k).sub_const p.m
  have hr := ((hx.pow 2).add_const (p.sigma^2)).sqrt (ne_of_gt hpos)
  have h := ((hx.const_mul p.rho).add hr).const_mul p.b |>.const_add p.a
  convert h using 1 <;> first | rfl | (dsimp [slope]; ring)

theorem slope_hasDerivAt (p : Params) (hs : 0 < p.sigma) (k : ℝ) :
    HasDerivAt (slope p) (curvature p k) k := by
  have hpos : 0 < (k - p.m)^2 + p.sigma^2 := by positivity
  have hroot : Real.sqrt ((k - p.m)^2 + p.sigma^2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hx := (hasDerivAt_id k).sub_const p.m
  have hr := ((hx.pow 2).add_const (p.sigma^2)).sqrt (ne_of_gt hpos)
  have h := ((hx.div hr hroot).const_add p.rho).const_mul p.b
  convert h using 1 <;> try rfl
  · dsimp [curvature]
    have he := Real.sq_sqrt hpos.le
    field_simp
    rw [he]
    ring

theorem deriv_variance (p : Params) (hs : 0 < p.sigma) :
    deriv (variance p) = slope p := by
  funext k
  exact (variance_hasDerivAt p hs k).deriv

theorem deriv_slope (p : Params) (hs : 0 < p.sigma) :
    deriv (slope p) = curvature p := by
  funext k
  exact (slope_hasDerivAt p hs k).deriv

end SVI
end MathFin
