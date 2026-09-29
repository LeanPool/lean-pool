/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
Upstream FloatLib code retains its MIT license below. The Lean Pool integration changes are
covered by the standard header above.

MIT License

Copyright (c) 2026 FloatLib

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Core
import Mathlib.Tactic.Ring

/-!
# Bounds for normal field packing

A normal exponent becomes a positive, in-range biased field, and removing the hidden bit from a
normalized significand leaves a legal fraction. Together these bounds show that the finite-range
packing guard accepts every in-range IEEE normal value.

The arithmetic facts are shared by nearest and directed rounding before either correctness proof
layer is imported.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- The smallest normal exponent does not exceed the largest normal exponent. -/
theorem minNormalExponent_le_maxNormalExponent (fmt : FloatFormat) :
    fmt.minNormalExponent ≤ fmt.maxNormalExponent := by
  unfold FloatFormat.minNormalExponent FloatFormat.maxNormalExponent
  have hmax : (0 : Int) < Int.ofNat fmt.maxFiniteExpField :=
    Int.natCast_pos.mpr fmt.maxFiniteExpField_pos
  omega

/-! ## Normal field bounds -/

/-- A normal unbiased exponent produces a positive biased exponent field. -/
theorem biasedExponent_pos (fmt : FloatFormat) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent) :
    0 < exponent + Int.ofNat fmt.exponentBias := by
  unfold FloatFormat.minNormalExponent at hmin
  omega

/-- Conversion of a normal biased exponent through `Int.toNat` is exact. -/
theorem ofNat_toNat_biasedExponent (fmt : FloatFormat) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent) :
    Int.ofNat (Int.toNat (exponent + Int.ofNat fmt.exponentBias)) =
      exponent + Int.ofNat fmt.exponentBias :=
  Int.toNat_of_nonneg (biasedExponent_pos fmt exponent hmin).le

/-- A representable normal exponent remains within the descriptor's finite exponent range. -/
theorem encodedExponent_le_maxFiniteExpField
    (fmt : FloatFormat) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hmax : exponent ≤ fmt.maxNormalExponent) :
    Int.toNat (exponent + Int.ofNat fmt.exponentBias) ≤
      fmt.maxFiniteExpField := by
  have hencoded :
      Int.ofNat (Int.toNat (exponent + Int.ofNat fmt.exponentBias)) =
        exponent + Int.ofNat fmt.exponentBias :=
    ofNat_toNat_biasedExponent fmt exponent hmin
  have hupper :
      Int.ofNat (Int.toNat (exponent + Int.ofNat fmt.exponentBias)) ≤
        Int.ofNat fmt.maxFiniteExpField := by
    rw [hencoded]
    unfold FloatFormat.maxNormalExponent at hmax
    omega
  exact Int.ofNat_le.mp hupper

/-- A normal unbiased exponent never encodes as the zero exponent field. -/
theorem encodedExponent_ne_zero
    (fmt : FloatFormat) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent) :
    Int.toNat (exponent + Int.ofNat fmt.exponentBias) ≠ 0 := by
  have hpositiveInt :
      (0 : Int) < Int.ofNat (Int.toNat (exponent + Int.ofNat fmt.exponentBias)) := by
    rw [ofNat_toNat_biasedExponent fmt exponent hmin]
    exact biasedExponent_pos fmt exponent hmin
  exact Nat.ne_of_gt (Int.natCast_pos.mp hpositiveInt)

/-- Decoding a normal biased exponent recovers the intended normalized dyadic scale. -/
theorem decode_encodedExponent
    (fmt : FloatFormat) (exponent : Int)
    (hmin : fmt.minNormalExponent ≤ exponent) :
    Int.ofNat (Int.toNat (exponent + Int.ofNat fmt.exponentBias)) -
        Int.ofNat fmt.exponentBias - Int.ofNat fmt.fracWidth =
      exponent - Int.ofNat fmt.fracWidth := by
  rw [ofNat_toNat_biasedExponent fmt exponent hmin]
  ring

/-- Removing the implicit leading bit from a normalized mantissa fits the fraction field. -/
theorem normalizedMantissa_sub_pow2_lt
    (fmt : FloatFormat) (mantissa : Nat)
    (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1)) :
    mantissa - pow2 fmt.fracWidth < 2 ^ fmt.fracWidth := by
  rw [pow2_eq_two_pow] at hlow hhigh ⊢
  rw [pow_succ] at hhigh
  omega

/-- Restoring the implicit leading bit reconstructs a normalized mantissa exactly. -/
theorem pow2_add_normalizedMantissa_sub (fmt : FloatFormat) (mantissa : Nat)
    (hlow : pow2 fmt.fracWidth ≤ mantissa) :
    pow2 fmt.fracWidth + (mantissa - pow2 fmt.fracWidth) = mantissa :=
  Nat.add_sub_of_le hlow

namespace Directed.Internal

/--
Removing the hidden bit from a normalized IEEE significand leaves a legal fraction field.

Both dyadic and rational packing use this fact. Keeping it here makes the format argument
independent of the exact-number representation used by the caller.
-/
theorem fraction_le_maxFiniteFracField_ieee
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mantissa : Nat)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1)) :
    mantissa - pow2 fmt.fracWidth ≤ fmt.maxFiniteFracField := by
  have hfraction : mantissa - pow2 fmt.fracWidth < pow2 fmt.fracWidth := by
    by_cases hlow : pow2 fmt.fracWidth ≤ mantissa
    · simpa [pow2_eq_two_pow] using
        normalizedMantissa_sub_pow2_lt fmt mantissa hlow hhigh
    · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hlow)]
      simp [pow2_eq_two_pow]
  simp only [FloatFormat.maxFiniteFracField,
    FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt,
    FloatFormat.fracMaskNat, pow2_eq_two_pow]
  simpa [pow2_eq_two_pow] using Nat.le_sub_one_of_lt hfraction

/--
In-range normal fields cannot trigger the overflow guard shared by the dyadic and rational
packers.
-/
theorem packingGuard_eq_false
    (fmt : FloatFormat) (exponent : Int) (fraction : Nat)
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hmax : exponent ≤ fmt.maxNormalExponent)
    (hfraction : fraction ≤ fmt.maxFiniteFracField) :
    let encodedExponent :=
      Int.toNat (exponent + Int.ofNat fmt.exponentBias)
    (decide (encodedExponent > fmt.maxFiniteExpField) ||
        encodedExponent == fmt.maxFiniteExpField &&
          decide (fraction > fmt.maxFiniteFracField)) =
      false := by
  have hexponent :=
    encodedExponent_le_maxFiniteExpField fmt exponent hmin hmax
  have hexponentNot :
      ¬Int.toNat (exponent + Int.ofNat fmt.exponentBias) >
        fmt.maxFiniteExpField :=
    not_lt_of_ge hexponent
  have hfractionNot : ¬fraction > fmt.maxFiniteFracField :=
    not_lt_of_ge hfraction
  simp only [hexponentNot, hfractionNot, decide_false,
    Bool.and_false, Bool.or_false]

/--
A normalized in-range IEEE significand cannot trigger the overflow guard shared by the dyadic and
rational packers: the encoded exponent does not exceed the maximal finite field and the fraction
is legal.
-/
theorem normalizedGuard_eq_false
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mantissa : Nat)
    (exponent : Int)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1))
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hmax : exponent ≤ fmt.maxNormalExponent) :
    let encodedExponent :=
      Int.toNat (exponent + Int.ofNat fmt.exponentBias)
    let fraction := mantissa - pow2 fmt.fracWidth
    (decide (encodedExponent > fmt.maxFiniteExpField) ||
        encodedExponent == fmt.maxFiniteExpField &&
          decide (fraction > fmt.maxFiniteFracField)) =
      false :=
  packingGuard_eq_false fmt exponent (mantissa - pow2 fmt.fracWidth) hmin hmax
    (fraction_le_maxFiniteFracField_ieee fmt hfmt mantissa hhigh)

end Directed.Internal
end Model
end FloatLib.Floats.Formats.BinaryInterchange
