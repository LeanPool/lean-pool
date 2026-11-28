/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Second derivatives, from a formula or from convexity

A higher-order sensitivity is usually computed by differentiating an explicit formula for a
lower-order one: gamma as `∂_S Φ(d₁)`, because the call delta is `Φ(d₁)`. That computation is a
statement about the formula. It becomes a statement about the price once the formula is known
to *be* the price's derivative on a neighbourhood of the point: then `deriv` of the price agrees
with the formula near the point, and so do their derivatives there.

* `hasDerivAt_deriv_of_eventually`: `f' = g` near `x` and `g'(x) = c` give `(deriv f)'(x) = c`.
* `hasDerivAt_deriv_param_of_eventually`: the same for a mixed partial `s ↦ ∂_y F(s, y)` at
  `x`, when `∂_y F(s, y) = g s` for every `s` near `x`.
* `deriv_deriv_nonneg_of_convexOn`: the converse direction of the second-derivative test. A
  convex function's second derivative is non-negative on an open set where it is
  differentiable.

## Main results

* `hasDerivAt_deriv_param_of_eventually`: if `F s` has derivative `g s` at `y` for all `s` near
  `x` and `g` has derivative `g'` at `x`, then `s ↦ deriv (F s) y` has derivative `g'` at `x`.
* `deriv_deriv_nonneg_of_convexOn`: a function convex on an open set `S` and differentiable at
  every point of `S` has `0 ≤ deriv (deriv f) x` for `x ∈ S`.

## Tags

gamma, second derivative, convexity test, Greeks, sensitivity, differentiation of formula,
MSC 91G20, JEL G13
-/

@[expose] public section

open Topology

namespace MathFin

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- If `f` has derivative `g y` at every `y` near `x`, and `g` has derivative `g'` at `x`,
then `deriv f` has derivative `g'` at `x`: the second derivative of `f` at `x` is the
derivative of its first-derivative formula. -/
theorem hasDerivAt_deriv_of_eventually {f g : 𝕜 → E} {x : 𝕜} {g' : E}
    (hf : ∀ᶠ y in 𝓝 x, HasDerivAt f (g y) y) (hg : HasDerivAt g g' x) :
    HasDerivAt (deriv f) g' x :=
  hg.congr_of_eventuallyEq (hf.mono fun _ hy ↦ hy.deriv)

/-- The mixed-partial form: if for every `s` near `x` the function `F s` has derivative
`g s` at `y`, and `g` has derivative `g'` at `x`, then `s ↦ deriv (F s) y` has derivative
`g'` at `x`. -/
theorem hasDerivAt_deriv_param_of_eventually {F : 𝕜 → 𝕜 → E} {g : 𝕜 → E} {x y : 𝕜} {g' : E}
    (hF : ∀ᶠ s in 𝓝 x, HasDerivAt (F s) (g s) y) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun s ↦ deriv (F s) y) g' x :=
  hg.congr_of_eventuallyEq (hF.mono fun _ hs ↦ hs.deriv)

/-- A convex function has a non-negative second derivative on an open set where it is
differentiable: its derivative is monotone there (`ConvexOn.monotoneOn_deriv`), and a monotone
function's derivative is non-negative. The converse direction of `convexOn_of_deriv2_nonneg'`. -/
theorem deriv_deriv_nonneg_of_convexOn {S : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ S f)
    (hS : IsOpen S) (hd : ∀ x ∈ S, DifferentiableAt ℝ f x) {x : ℝ} (hx : x ∈ S) :
    0 ≤ deriv (deriv f) x := by
  rw [← derivWithin_of_isOpen hS hx]
  exact (hf.monotoneOn_deriv hd).derivWithin_nonneg

end MathFin
