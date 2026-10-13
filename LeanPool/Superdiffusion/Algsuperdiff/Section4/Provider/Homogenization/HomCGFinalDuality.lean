/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGFinalTestClass

/-!
# HomCGFinalDuality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-4 duality carrier, produced from the smooth dual at the lower order

## What this file supplies

`HomCGFinalTestClass` proves the test-class comparison at `s′ < s`.  This file
turns it into the Step-4 consumer's carrier and records the numeral
compatibility of the two constants.

* `weakNegDualBoundOn_of_smoothDualLevel` — from a smooth-dual level `D` at
  order `s′` to `WeakNegDualBoundOn Q s (K_test·D)` at the DATA order `s`;
* `conjugate_toReal_le_two` — the conjugate exponent is at most `2` as soon as
  `2 ≤ p`, from `ENNReal.conjExponent p = 1 + (p-1)⁻¹` alone;
* `two_le_exponent_of_guard` — the bundle's printed guard forces `2 ≤ p`.

## The numeral check: compatible, and free

The admissible window of the order-loss route is `0 < (s-s′)·p′ < d`.  At the
spine's own numerals this is satisfied with room to spare, and — the point —
it needs NOTHING beyond the bundle's printed guard:

* the bundle carries `0 < p` and `s + d/p ≤ 1/2`, hence `s ≤ 1/2`, and (for
  `d ≥ 1`, with `s > 0`) `d/p < 1/2`, i.e. `p > 2d ≥ 2`, so `p′ ≤ 2`;
* choosing `s′ ∈ [s/2, s)` — e.g. `s′ = s/2`, `CoarseGraining`'s `fractionalOrderHalf` —
  gives `s - s′ ≤ s/2 ≤ 1/4`, so `(s-s′)·p′ ≤ 1/2 < 1 ≤ d`.

At the pin `p = 4d` this reads `p′ = 4d/(4d-1) ≤ 4/3` and `s ≤ 1/4`, so the
margin is larger still.  With `s = |log γ|⁻¹` the constraint is vacuous.  There
is no interaction with `s₁ = s/4` or with `s < s₂ < 1`: the re-cut's choice of
`s′` is independent of both, because `s′` occurs ONLY on the `CoarseGraining` side of the
conversion.
-/

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The conjugate exponent is at most `2` above `2` -/

/-- **`p ≥ 2 ⟹ p′ ≤ 2`**, straight from `conjExponent p = 1 + (p-1)⁻¹`. -/
theorem conjugate_toReal_le_two {p : FiniteLpExponent} (hp : 2 ≤ p.exponent) :
    p.conjugate.exponent.toReal ≤ 2 := by
  have hconj : p.conjugate.exponent = 1 + (p.exponent - 1)⁻¹ := rfl
  have hadd : (1 : ℝ≥0∞) + 1 ≤ p.exponent := by
    rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
    exact hp
  have h1 : (1 : ℝ≥0∞) ≤ p.exponent - 1 :=
    ENNReal.le_sub_of_add_le_right (by norm_num) hadd
  have h2 : (p.exponent - 1)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr h1
  have h3 : p.conjugate.exponent ≤ 2 := by
    rw [hconj]
    calc (1 : ℝ≥0∞) + (p.exponent - 1)⁻¹ ≤ 1 + 1 := by gcongr
      _ = 2 := by norm_num
  have h4 := ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h3
  simpa using h4

/-- The printed guard `s + d/p ≤ 1/2` forces `2 ≤ p` once `1 ≤ d` and `0 < s`. -/
theorem two_le_exponent_of_guard {p : FiniteLpExponent} (hd : 1 ≤ d) {s : ℝ}
    (hs0 : 0 < s) (hguard : s + (d : ℝ) / p.exponent.toReal ≤ 1 / 2) :
    2 ≤ p.exponent := by
  have htpos : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hquot : (d : ℝ) / p.exponent.toReal < 1 / 2 := by linarith only [hguard, hs0]
  have hmul : (d : ℝ) < 1 / 2 * p.exponent.toReal := by
    rw [div_lt_iff₀ htpos] at hquot
    linarith only [hquot]
  have hreal : (2 : ℝ) ≤ p.exponent.toReal := by linarith only [hmul, hdR]
  have hne : p.exponent ≠ ⊤ := p.lt_top.ne
  rw [← ENNReal.ofReal_toReal hne]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ## 3. The Step-4 carrier from a smooth-dual level -/

/-- **The Step-4 duality carrier, produced.**

`D` is any real level of the smooth `W^{-s′,p}` dual of `F` on `Q`; the output
is the `WeakNegDualBoundOn` at the DATA order `s`, level `K_test·D`.  With `D =
3^{s′m}·RHS` (the display's own level at `s′`) and `K_test =
d·3^{m(s-s′)}·(1+C)`, the produced level is `d(1+C)·3^{sm}·RHS` — the printed
duality level, up to the dimensional constant which the bundle's `C_cg`
absorbs. -/
theorem weakNegDualBoundOn_of_smoothDualLevel {Q : TriadicCube d}
    (s' s : FractionalOrder) (p : FiniteLpExponent)
    (hlo : 0 < (s.1 - s'.1) * p.conjugate.exponent.toReal)
    (hhi : (s.1 - s'.1) * p.conjugate.exponent.toReal < (d : ℝ))
    {F : CubeEuclideanLpField Q FiniteLpExponent.two} {D : ℝ} (hD : 0 ≤ D)
    (hF : cubeEuclideanNegativeWspSmoothDualENorm Q s' p F ≤ ENNReal.ofReal D) :
    WeakNegDualBoundOn Q s.1
      (cgTestConst d Q s.1 s'.1 p.conjugate.exponent.toReal * D) F.toField :=
  weakNegDualBoundOn_of_smoothDualAt
    (cgTestConst_nonneg d Q hlo)
    (smoothDualDominatesHolderTestsAt Q s' s p hlo hhi) hD hF

end

end Algsuperdiff.Section4.Provider.Homogenization
