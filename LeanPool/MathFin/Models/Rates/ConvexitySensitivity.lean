/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.DurationSensitivity
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Convexity as the second derivative of bond price (first-principles)

For a coupon bond with discrete-compounded yield `y` and cashflows `c_i` at
integer times `t_i`,

  `P(y) = Σ c_i / (1 + y)^{t_i}`,
  `P'(y) = −Σ t_i · c_i / (1 + y)^{t_i + 1} = −ModNum(y)` (`DurationSensitivity`),
  `P''(y) = Σ t_i · (t_i + 1) · c_i / (1 + y)^{t_i + 2} =: ConvNum(y)`.

The **convexity** is `C(y) := ConvNum(y) / P(y)` — the *percentage* second
derivative of price w.r.t. yield. Together with duration, it gives the
standard discrete yield Taylor expansion

  `ΔP/P ≈ −D_mod · Δy + ½ C · (Δy)²`.

This file derives the second-derivative identity from the per-cashflow
second derivative `d²/dy² [c / (1+y)^n] = n · (n+1) · c / (1+y)^{n+2}`,
obtained by applying `hasDerivAt_coupon_term` from `DurationSensitivity` a
second time.

## Why this is "first principles"

Pre-existing `Models.Rates.MacaulayModified` defines duration numerators
algebraically. `Models.Rates.DurationSensitivity` (phase 21) derives
`dP/dy = −ModNum`. This file completes the discrete yield-Taylor expansion
by deriving `d²P/dy² = ConvNum` — i.e., bond convexity is *literally* the
second derivative of price, not a separately-defined moment.

## Main definitions

* `convexityNumerator`: the convexity numerator `∑ t_i · (t_i + 1) · c_i / (1 + y)^{t_i + 2}`.

## Main results

* `hasDerivAt_modifiedNumerator`: `d/dy [ModNum(y)] = −ConvNum(y)`.
* `hasDerivAt_bondPriceDisc_secondDeriv`: `d²P/dy² = ConvNum(y)` (stated as
  the derivative of `P'(y) = −ModNum(y)`).

## Tags

bond convexity, second derivative of price, yield Taylor expansion, price–yield curve, coupon bond,
interest rate sensitivity, MSC 91G30, JEL G12
-/

@[expose] public section

namespace MathFin

open Finset

variable {ι : Type*}

/-- Convexity numerator: `∑ t_i · (t_i + 1) · c_i / (1 + y)^{t_i + 2}`. -/
noncomputable def convexityNumerator (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, (t i : ℝ) * ((t i : ℝ) + 1) * c i / (1 + y) ^ (t i + 2)

/-- **Derivative of `ModNum(y)`** is `−ConvNum(y)`. Proof: for each term
`(t_i : ℝ) · c_i / (1 + y')^(t_i + 1)`, the derivative is

  `d/dy [(t_i : ℝ) · c_i / (1 + y')^(t_i + 1)]
    = (t_i : ℝ) · (−(t_i + 1) · c_i / (1 + y)^(t_i + 2))
    = −(t_i : ℝ) · ((t_i : ℝ) + 1) · c_i / (1 + y)^(t_i + 2)`.

Summing over cashflows: `d/dy ModNum = −ConvNum`. -/
theorem hasDerivAt_modifiedNumerator
    (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) {y : ℝ} (hy : 1 + y ≠ 0) :
    HasDerivAt (fun y' ↦ modifiedNumerator s t c y')
               (-convexityNumerator s t c y) y := by
  unfold modifiedNumerator convexityNumerator
  rw [show -∑ i ∈ s, (t i : ℝ) * ((t i : ℝ) + 1) * c i / (1 + y) ^ (t i + 2) =
      ∑ i ∈ s, (-((t i : ℝ) * ((t i : ℝ) + 1) * c i / (1 + y) ^ (t i + 2))) from by
    rw [← Finset.sum_neg_distrib]]
  apply HasDerivAt.fun_sum
  intros i _
  have h_term : HasDerivAt (fun y' : ℝ ↦ c i / (1 + y') ^ (t i + 1))
                (-(((t i + 1 : ℕ) : ℝ) * c i / (1 + y) ^ (t i + 1 + 1))) y :=
    hasDerivAt_coupon_term (c i) (t i + 1) hy
  have h_pulled := h_term.const_mul ((t i : ℝ))
  have h_func :
      (fun y' : ℝ ↦ (t i : ℝ) * (c i / (1 + y') ^ (t i + 1))) =
      (fun y' : ℝ ↦ (t i : ℝ) * c i / (1 + y') ^ (t i + 1)) := by
    funext y'; ring
  rw [h_func] at h_pulled
  convert h_pulled using 1
  push_cast
  have : t i + 1 + 1 = t i + 2 := by omega
  rw [this]
  ring

/-- **Second derivative of bond price**: `P''(y) = ConvNum(y)`, stated as the
derivative of `P'(y) = −ModNum(y)`.

Combined with `hasDerivAt_bondPriceDisc` (from `DurationSensitivity`), this
gives the full discrete yield Taylor expansion of the bond price:

  `P(y + Δy) ≈ P(y) − ModNum(y) · Δy + ½ · ConvNum(y) · (Δy)²`. -/
theorem hasDerivAt_bondPriceDisc_secondDeriv
    (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) {y : ℝ} (hy : 1 + y ≠ 0) :
    HasDerivAt (fun y' ↦ -modifiedNumerator s t c y')
               (convexityNumerator s t c y) y := by
  have h := (hasDerivAt_modifiedNumerator s t c hy).neg
  rw [neg_neg] at h
  exact h

/-- **Convexity-sensitivity identity**: `P''(y)/P(y) = C(y) = ConvNum/P`. The
percentage second derivative of price equals convexity, completing the
duration-convexity yield Taylor expansion. -/
theorem bondPriceDisc_secondDeriv_eq_convexity_times_price
    (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) {y : ℝ}
    (hy : 1 + y ≠ 0) :
    ∃ P'' : ℝ, HasDerivAt (fun y' ↦ -modifiedNumerator s t c y') P'' y ∧
      P'' / bondPriceDisc s t c y =
        convexityNumerator s t c y / bondPriceDisc s t c y := by
  refine ⟨convexityNumerator s t c y,
          hasDerivAt_bondPriceDisc_secondDeriv s t c hy, rfl⟩

end MathFin
