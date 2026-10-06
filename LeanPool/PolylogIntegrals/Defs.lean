/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Basic definitions

Mathlib does not (yet) have polylogarithms or Catalan's constant, so we define them here by
their series.

* `LeanPolyLog.Li s z`: the polylogarithm `Li_s(z) = ∑_{n ≥ 1} z^n / n^s` on `ℂ`.
* `LeanPolyLog.Lir s x`: the same series on `ℝ`.
* `LeanPolyLog.G`: Catalan's constant `∑_{n ≥ 0} (-1)^n / (2n+1)^2`.
* `LeanPolyLog.zeta3`: Apéry's constant `∑_{n ≥ 1} 1/n^3`.

For `s ≥ 2` the polylog series converges absolutely on the closed unit disk. Outside the disk
`tsum` returns the junk value `0`. Every statement in this project therefore evaluates `Li`
only for `‖z‖ ≤ 1`; for instance A014 is stated in a form that avoids `Li₃(1+i)`.
-/

namespace LeanPolyLog

/-- The polylogarithm `Li_s(z) = ∑_{n=1}^∞ z^n / n^s`, as a series. Meaningful for `‖z‖ ≤ 1`
and `s ≥ 2`. -/
@[expose] public noncomputable def Li (s : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℂ) ^ s)

/-- The real polylogarithm `Li_s(x) = ∑_{n=1}^∞ x^n / n^s`, meaningful for `|x| ≤ 1`
and `s ≥ 2`. -/
@[expose] public noncomputable def Lir (s : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ (n + 1) / ((n + 1 : ℝ) ^ s)

/-- Catalan's constant `G = ∑_{n=0}^∞ (-1)^n / (2n+1)^2 ≈ 0.9159655941772190`. -/
@[expose] public noncomputable def G : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * n + 1 : ℝ) ^ 2

/-- Apéry's constant `ζ(3) = ∑_{n=1}^∞ 1/n^3 ≈ 1.2020569031595943`. -/
@[expose] public noncomputable def zeta3 : ℝ :=
  ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ 3)

end LeanPolyLog
