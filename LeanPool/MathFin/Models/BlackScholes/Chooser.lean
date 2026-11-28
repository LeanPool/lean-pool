/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

/-!
# Chooser option

At the chooser date `t` the holder picks `max(C_t, P_t)`. Using `C_t - P_t =
S_t - K · e^{-r(T-t)}` (put-call parity at time `t`), this rearranges to

`max(C_t, P_t) = C_t + max(0, K · e^{-r(T-t)} - S_t)`,

so a chooser option is a portfolio: a long call (strike `K`, maturity `T`) plus
a long put-payoff at the chooser date with strike `K · e^{-r(T-t)}`.

Both lemmas are pure real-number algebra; the financial content is the
identification of the second piece as a put at the chooser date.

## Main results

* `chooser_payoff_decompose`: `max C P = C + max 0 (P - C)`.
* `chooser_via_pcp`: under `C - P = S - K_disc`,
  `max C P = C + max 0 (K_disc - S)`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 26.7
* [M. Rubinstein, *Options for the undecided*][Rubinstein1991]

## Tags

chooser option, as-you-like-it option, put–call parity, exotic option, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

/-- Generic chooser-style decomposition: `max C P = C + max 0 (P − C)`. -/
lemma chooser_payoff_decompose (C P : ℝ) :
    max C P = C + max 0 (P - C) := by
  by_cases h : C ≤ P
  · rw [max_eq_right h, max_eq_right (by linarith : (0:ℝ) ≤ P - C)]; ring
  · push Not at h
    rw [max_eq_left h.le, max_eq_left (by linarith : P - C ≤ 0)]; ring

/-- **Chooser option payoff** via put-call parity at the chooser date.
If `C - P = S - K_disc` (PCP), then `max(C, P) = C + max(0, K_disc - S)`. -/
lemma chooser_via_pcp (C P S K_disc : ℝ) (hPCP : C - P = S - K_disc) :
    max C P = C + max 0 (K_disc - S) := by
  rw [chooser_payoff_decompose]
  have : P - C = K_disc - S := by linarith
  rw [this]

end MathFin
