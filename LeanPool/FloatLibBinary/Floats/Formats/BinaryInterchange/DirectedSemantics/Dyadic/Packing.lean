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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Basic

/-!
# Field packing for directed dyadic rounding

Directed rounding first chooses a point on the representable dyadic grid and then packs that point
into exponent and fraction fields. This module proves that the normal and subnormal packing
formulas preserve the chosen exact value.

The field-width bounds prevent truncation during packing. Normal packing also requires a
finiteness hypothesis, since some encoding policies reserve patterns within those widths for
exceptional values.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats

section

/-! ## Field-packing semantics -/

/--
Packing a normalized mantissa at an in-range exponent preserves its exact value when the packed
word is finite.
-/
theorem toReal_ofFields_normalized
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1))
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hmax : exponent ≤ fmt.maxNormalExponent)
    (hfinite :
      isFinite
          (ofFields fmt false
            (Int.toNat (exponent + Int.ofNat fmt.exponentBias))
            (mantissa - pow2 fmt.fracWidth)) =
        true) :
    toReal
        (ofFields fmt false
          (Int.toNat (exponent + Int.ofNat fmt.exponentBias))
          (mantissa - pow2 fmt.fracWidth)) =
      (mantissa : ℝ) * bpow (exponent - Int.ofNat fmt.fracWidth) := by
  rw [toReal_ofFields_normal_of_isFinite fmt false
    (Int.toNat (exponent + Int.ofNat fmt.exponentBias))
    (mantissa - pow2 fmt.fracWidth)
    (encodedExponent_ne_zero fmt exponent hmin)
    ((encodedExponent_le_maxFiniteExpField fmt exponent hmin hmax).trans_lt
      fmt.maxFiniteExpField_lt_two_pow)
    (normalizedMantissa_sub_pow2_lt fmt mantissa hlow hhigh)
    hfinite]
  simp only [Bool.false_eq_true, ite_false, one_mul]
  rw [pow2_add_normalizedMantissa_sub fmt mantissa hlow]
  rw [decode_encodedExponent fmt exponent hmin]

/-- The downward zero-or-subnormal branch denotes its mantissa on the subnormal grid. -/
theorem toReal_roundSubnormalDown
    (fmt : FloatFormat) (mantissa : Nat)
    (hhigh : mantissa < pow2 fmt.fracWidth) :
    toReal
        (if mantissa = 0 then
          zero fmt false
        else
          ofFields fmt false 0 mantissa) =
      (mantissa : ℝ) * bpow (fmt.minSubnormalExponent) := by
  by_cases hzero : mantissa = 0
  · simp [hzero]
  · rw [ite_eq_right hzero]
    rw [toReal_ofFields_subnormal fmt false mantissa hzero]
    · simp
    · simpa [pow2_eq_two_pow] using hhigh

/-- The minimum normal exponent encodes as biased exponent field one. -/
theorem encodedExponent_minNormal_eq_one (fmt : FloatFormat) :
    Int.toNat
        (fmt.minNormalExponent + Int.ofNat fmt.exponentBias) = 1 := by
  unfold FloatFormat.minNormalExponent
  simp

/--
The upward subnormal branch, including its smallest-normal boundary, preserves its grid value.
-/
theorem toReal_roundSubnormalUp
    (fmt : FloatFormat) (mantissa : Nat)
    (hzero : mantissa ≠ 0)
    (hhigh : mantissa ≤ pow2 fmt.fracWidth) :
    toReal
        (if mantissa = 0 then
          posMinSubnormal fmt
        else if pow2 fmt.fracWidth ≤ mantissa then
          ofFields fmt false 1 0
        else
          ofFields fmt false 0 mantissa) =
      (mantissa : ℝ) * bpow (fmt.minSubnormalExponent) := by
  rw [ite_eq_right hzero]
  by_cases hnormal : pow2 fmt.fracWidth ≤ mantissa
  · have heq : mantissa = pow2 fmt.fracWidth :=
      Nat.le_antisymm hhigh hnormal
    rw [ite_eq_left hnormal, heq]
    rw [show (1 : Nat) = Int.toNat
        (fmt.minNormalExponent + Int.ofNat fmt.exponentBias) by
      symm
      exact encodedExponent_minNormal_eq_one fmt]
    have hpack :
        toReal
            (ofFields fmt false
              (Int.toNat
                (fmt.minNormalExponent + Int.ofNat fmt.exponentBias))
              0) =
          (pow2 fmt.fracWidth : ℝ) *
            bpow
              (fmt.minNormalExponent -
                Int.ofNat fmt.fracWidth) := by
      have hmaxExp : 1 ≤ fmt.maxFiniteExpField :=
        Nat.succ_le_iff.mpr fmt.maxFiniteExpField_pos
      have hpair :
          1 < fmt.maxFiniteExpField ∨
            1 = fmt.maxFiniteExpField ∧
              0 ≤ fmt.maxFiniteFracField := by
        rcases hmaxExp.lt_or_eq with hlt | heq
        · exact Or.inl hlt
        · exact Or.inr ⟨heq, Nat.zero_le _⟩
      have hfiniteOne :
          isFinite (ofFields fmt false 1 0) = true :=
        isFinite_ofFields_normal_of_le_maxFinite fmt false 1 0
          (by decide)
          (hmaxExp.trans_lt fmt.maxFiniteExpField_lt_two_pow)
          (Nat.two_pow_pos _)
          hpair
      have hfinite :
          isFinite
              (ofFields fmt false
                (Int.toNat
                  (fmt.minNormalExponent + Int.ofNat fmt.exponentBias))
                0) =
            true := by
        rw [encodedExponent_minNormal_eq_one]
        exact hfiniteOne
      simpa using
        toReal_ofFields_normalized fmt (pow2 fmt.fracWidth)
          (fmt.minNormalExponent) le_rfl
          (pow2_lt_pow2_succ fmt.fracWidth) le_rfl
          (minNormalExponent_le_maxNormalExponent fmt)
          (by simpa only [Nat.sub_self] using hfinite)
    rw [hpack]
    congr 1
  · rw [ite_eq_right hnormal]
    rw [toReal_ofFields_subnormal fmt false mantissa hzero]
    · simp
    · simpa [pow2_eq_two_pow] using Nat.lt_of_not_ge hnormal


end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
