/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Analysis.DerivOfDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Almgren-Chriss optimal execution (deterministic closed form)

Liquidating `X_0` units of an asset over horizon `T` with linear temporary
impact (coefficient `η`) and price-variance risk aversion (coefficient `λ`),
the optimal trajectory `X(t)` (remaining inventory) minimises the
deterministic cost functional

  `∫_0^T (σ² λ · X(t)² + η · X'(t)²) dt`

subject to `X(0) = X_0` and `X(T) = 0`. The Euler-Lagrange equation reduces
to

  `X''(t) = κ² · X(t)`,    `κ² := σ² λ / η`,

a linear ODE with hyperbolic-cosine/sinh solutions. The boundary-condition-
satisfying solution is

  `X(t) = X_0 · sinh(κ · (T − t)) / sinh(κ · T)`.

We verify the closed form satisfies:
- the initial condition `X(0) = X_0`,
- the terminal condition `X(T) = 0`,
- the EL equation `X''(t) = κ² · X(t)`.

The full minimisation theorem (this closed form is optimal among all
admissible trajectories) is a calculus-of-variations claim that requires
function-space machinery beyond Mathlib's current pin.

## Main definitions

* `almgrenChrissPath`: the closed-form trajectory `X(t) = X_0 · sinh (κ (T − t)) / sinh (κ T)`.

## Main results

* `almgrenChrissPath_at_zero`: `X(0) = X_0`.
* `almgrenChrissPath_at_terminal`: `X(T) = 0`.
* `hasDerivAt_almgrenChrissPath`: first derivative.
* `almgrenChrissPath_satisfies_EL`: `X''(t) = κ² · X(t)`.

Neither derivative needs `sinh(κT) ≠ 0`: under Lean's `x / 0 = 0` the degenerate
closed form is the zero path, which satisfies both. Only the initial condition
uses it.

## References

* [Almgren and Chriss (2000)][AlmgrenChriss2000]

## Tags

optimal execution, market impact, liquidation, calculus of variations, Euler–Lagrange equation,
inventory, JEL G11, MSC 91G80, MSC 49L20
-/

@[expose] public section

namespace MathFin

open Real

/-- **Almgren-Chriss optimal-execution trajectory**:
`X(t) = X_0 · sinh(κ (T − t)) / sinh(κ T)`. Liquidation rate `−X'(t)` is
slow at the start and accelerates near `T`. -/
noncomputable def almgrenChrissPath (X_0 κ T t : ℝ) : ℝ :=
  X_0 * Real.sinh (κ * (T - t)) / Real.sinh (κ * T)

/-- **Initial condition**: `X(0) = X_0`. -/
theorem almgrenChrissPath_at_zero (X_0 κ T : ℝ) (hT : Real.sinh (κ * T) ≠ 0) :
    almgrenChrissPath X_0 κ T 0 = X_0 := by
  unfold almgrenChrissPath
  rw [sub_zero]
  field_simp

/-- **Terminal condition**: `X(T) = 0`. -/
theorem almgrenChrissPath_at_terminal (X_0 κ T : ℝ) :
    almgrenChrissPath X_0 κ T T = 0 := by
  unfold almgrenChrissPath
  rw [sub_self, mul_zero, Real.sinh_zero]
  simp

/-- **First derivative**: `X'(t) = −X_0 · κ · cosh(κ (T − t)) / sinh(κ T)`. -/
theorem hasDerivAt_almgrenChrissPath (X_0 κ T t : ℝ) :
    HasDerivAt (almgrenChrissPath X_0 κ T)
      (-(X_0 * κ * Real.cosh (κ * (T - t)) / Real.sinh (κ * T))) t := by
  have hd : HasDerivAt (fun t : ℝ ↦ κ * (T - t)) (-κ) t := by
    simpa using ((hasDerivAt_id t).const_sub T).const_mul κ
  unfold almgrenChrissPath
  convert (hd.sinh.const_mul X_0).div_const (Real.sinh (κ * T)) using 1; ring

/-- The t-derivative of the first-derivative formula `−X₀ κ cosh(κ (T − t)) / sinh(κ T)` is
`κ² · X(t)`: the same `sinh(κ (T − t))` shape, multiplied by `κ²`. -/
private lemma hasDerivAt_almgrenChrissPath_deriv_formula (X_0 κ T t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ -(X_0 * κ * Real.cosh (κ * (T - s)) / Real.sinh (κ * T)))
      (κ ^ 2 * almgrenChrissPath X_0 κ T t) t := by
  have hd : HasDerivAt (fun t : ℝ ↦ κ * (T - t)) (-κ) t := by
    simpa using ((hasDerivAt_id t).const_sub T).const_mul κ
  unfold almgrenChrissPath
  convert ((hd.cosh.const_mul (X_0 * κ)).div_const (Real.sinh (κ * T))).neg using 1; ring

/-- **Almgren-Chriss EL equation**: the closed-form trajectory satisfies `X''(t) = κ² · X(t)`,
the Euler-Lagrange equation of the cost functional: `hasDerivAt_almgrenChrissPath` gives `X'`
at every `t`, and the derivative of that formula is `κ² · X(t)`. -/
theorem almgrenChrissPath_satisfies_EL (X_0 κ T t : ℝ) :
    HasDerivAt (deriv (almgrenChrissPath X_0 κ T)) (κ ^ 2 * almgrenChrissPath X_0 κ T t) t :=
  hasDerivAt_deriv_of_eventually (.of_forall (hasDerivAt_almgrenChrissPath X_0 κ T))
    (hasDerivAt_almgrenChrissPath_deriv_formula X_0 κ T t)

end MathFin
