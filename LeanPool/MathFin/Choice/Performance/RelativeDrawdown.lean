/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Performance.DownsideMetrics

/-!
# Relative drawdown is scale invariant

The **relative drawdown** of an equity curve `E` at time `t` is the fraction of the running
peak lost, `1 − E t / max_{s ≤ t} E s`. The running peak is Mathlib's `partialSups E`.

`MathFin.maximumDrawdown` (`Choice/Performance/DownsideMetrics.lean`) measures the largest
*absolute* decline, and is positively homogeneous: scaling the curve by `c > 0` scales it by
`c` (`maximumDrawdown_scale`). The relative drawdown is instead *invariant* under
`E ↦ c E`: a fund ten times the size, run with the same strategy, has the same relative
drawdown at every date. This is why relative drawdown, not absolute drawdown, compares
portfolios of different sizes, or denominated in different currencies at a fixed conversion
rate.

The identity holds for every `E`; the value is a drawdown fraction only where the running peak
is positive.

## Main definitions

* `relativeDrawdown`: `1 − E t / max_{s ≤ t} E s`, the fraction of the running peak lost by time
  `t`, with the peak `partialSups E`.
* `maxRelativeDrawdown`: the largest relative drawdown at any `s ≤ t`.

## Main results

* `relativeDrawdown_const_mul`: for `c > 0`, the relative drawdown of `c E` equals that of `E`.
* `maxRelativeDrawdown_const_mul`: hence so does the maximum relative drawdown up to any time.
* `partialSups_mul_relativeDrawdown_le_maximumDrawdown`: on a finite path the two notions are
  tied: the relative drawdown at `t`, scaled back up by the running peak `partialSups E t`, is
  at most `maximumDrawdown E`.

## References

* [C. Bacon, *Practical Portfolio Performance Measurement and Attribution*][Bacon2008]
* [Young (1991)][Young1991]

## Tags

relative drawdown, running peak, scale invariance, equity curve, drawdown, MSC 91G10, JEL G11
-/

@[expose] public section

namespace MathFin

variable {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]

/-- Relative drawdown `1 − E t / max_{s ≤ t} E s` of an equity curve `E` at time `t`: the
fraction of the running peak lost by time `t`. It is a drawdown fraction only where
`partialSups E t > 0`; elsewhere the value is junk. -/
noncomputable def relativeDrawdown (E : ι → ℝ) (t : ι) : ℝ := 1 - E t / partialSups E t

/-- Maximum relative drawdown up to time `t`: the largest relative drawdown at any `s ≤ t`. -/
noncomputable def maxRelativeDrawdown (E : ι → ℝ) (t : ι) : ℝ :=
  partialSups (relativeDrawdown E) t

/-- **Relative drawdown is scale invariant**: scaling the equity curve by `c > 0` leaves the
relative drawdown unchanged at every time — unlike the absolute `maximumDrawdown`, which
scales by `c`. -/
theorem relativeDrawdown_const_mul {c : ℝ} (hc : 0 < c) (E : ι → ℝ) :
    relativeDrawdown (fun s ↦ c * E s) = relativeDrawdown E := by
  funext t
  simp only [relativeDrawdown, partialSups_const_mul₀ hc, mul_div_mul_left _ _ hc.ne']

/-- The maximum relative drawdown up to any time is scale invariant. -/
theorem maxRelativeDrawdown_const_mul {c : ℝ} (hc : 0 < c) (E : ι → ℝ) :
    maxRelativeDrawdown (fun s ↦ c * E s) = maxRelativeDrawdown E :=
  congrArg (fun f t ↦ partialSups f t) (relativeDrawdown_const_mul hc E)

/-- **Relative drawdown, rescaled by the running peak, is bounded by the absolute maximum
drawdown**: for a nonzero running peak, `(max_{s ≤ t} E s) · relativeDrawdown E t` is the
absolute decline `max_{s ≤ t} E s − E t`, which `maximumDrawdown E` dominates. At a zero running
peak the left side is `0`, and `maximumDrawdown` is nonnegative. -/
theorem partialSups_mul_relativeDrawdown_le_maximumDrawdown {n : ℕ} (E : Fin n → ℝ)
    (t : Fin n) : partialSups E t * relativeDrawdown E t ≤ maximumDrawdown E := by
  rcases eq_or_ne (partialSups E t) 0 with h | h
  · simpa [h] using maximumDrawdown_nonneg E
  rw [relativeDrawdown, mul_sub, mul_one, mul_div_cancel₀ _ h]
  exact partialSups_sub_le_maximumDrawdown E t

end MathFin
