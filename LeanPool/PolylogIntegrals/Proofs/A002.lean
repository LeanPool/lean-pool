/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.DilogComplex
public import LeanPool.PolylogIntegrals.Proofs.A001

/-!
# A002: `Li₂(1/(1+i)) = 5π²/96 - log²2/8 + i(π log 2 / 8 - G)`

Landen's identity `Li₂(z) + Li₂(z/(z-1)) = -½ log²(1 - z)` at `z = i`, where
`i/(i-1) = 1/(1+i)`, gives `Li₂(1/(1+i)) = -½ log²(1 - i) - Li₂(i)`. Then:
* `log(1 - i) = ½ log 2 - (π/4) i`, so `-½ log²(1 - i) = π²/32 - log²2/8 + i π log 2 / 8`;
* `Li₂(i) = -π²/48 + iG` (A001).

The real parts add up to `π²/32 + π²/48 - log²2/8 = 5π²/96 - log²2/8`.
-/

open Real

namespace LeanPolyLog.Proofs

/-- A002: `Li₂(1/(1+i)) = 5π²/96 - log²2/8 + i(π log 2 / 8 - G)`. -/
public theorem A002 : Li 2 (1 / (1 + Complex.I)) =
    ((5 * π ^ 2 / 96 - Real.log 2 ^ 2 / 8 : ℝ) : ℂ)
      + ((π / 8 * Real.log 2 - G : ℝ) : ℂ) * Complex.I := by
  have hI : (1 : ℂ) / (1 + Complex.I) = Complex.I / (Complex.I - 1) := by
    have h1 : (1 : ℂ) + Complex.I ≠ 0 := by
      intro h
      simpa using congrArg Complex.re h
    have h2 : Complex.I - 1 ≠ 0 := by
      intro h
      simpa using congrArg Complex.re h
    rw [div_eq_div_iff h1 h2]
    linear_combination -Complex.I_sq
  have hL := Dilog.Li_two_add_Li_two_div_sub_one (z := Complex.I) (by simp) (by simp)
  rw [A001, Dilog.log_one_sub_I] at hL
  rw [hI]
  push_cast at hL ⊢
  linear_combination hL - ((π : ℂ) ^ 2 / 32) * Complex.I_sq

end LeanPolyLog.Proofs
