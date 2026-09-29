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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Quotient

/-!
# Branch equations for nearest-even rational packing

`roundRatScaled` rejects a zero denominator, returns a signed zero for a zero numerator, and
otherwise selects an overflow, underflow, subnormal, normal, or carry-out result from the leading
exponent of the quotient. The equations below describe each positive-magnitude branch of the IEEE
path in terms of the descriptor's semantic exponent bounds. They are used in the finiteness and
rounded-real proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Numerics

section

/-! ## Positive packing branches -/

/--
The IEEE path of `roundRatScaled` on a positive nonzero rational, with every executable test
rewritten to the descriptor's semantic exponent bounds and to propositional conditions.
-/
theorem roundRatScaled_false_eq_of_isIEEE
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    roundRatScaled fmt false numerator denominator exponent =
      let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
      let totalExponent := rationalExponent + exponent
      if fmt.maxNormalExponent < totalExponent then
        posInf fmt
      else if totalExponent < fmt.minSubnormalExponent - 1 then
        posZero fmt
      else if totalExponent < fmt.minNormalExponent then
        let scaled :=
          Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))
        let rounded := roundQuotientEven scaled.1 scaled.2
        if rounded = 0 then
          posZero fmt
        else if pow2 fmt.fracWidth ≤ rounded then
          ofFields fmt false 1 0
        else
          ofFields fmt false 0 rounded
      else
        let scaled :=
          Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (Int.ofNat fmt.fracWidth - rationalExponent)
        let rounded := roundQuotientEven scaled.1 scaled.2
        if rounded = pow2 (fmt.fracWidth + 1) then
          if fmt.maxNormalExponent < totalExponent + 1 then
            posInf fmt
          else
            ofFields fmt false
              (Int.toNat (totalExponent + 1 + Int.ofNat fmt.exponentBias)) 0
        else
          ofFields fmt false
            (Int.toNat (totalExponent + Int.ofNat fmt.exponentBias))
            (rounded - pow2 fmt.fracWidth) := by
  simp only [roundRatScaled, dite_eq_left hfmt]
  unfold ieeeRoundRatScaled
  rw [← FloatFormat.maxNormalExponent_eq_ieee fmt hfmt,
    ← FloatFormat.minNormalExponent_eq_ieee fmt hfmt,
    ← FloatFormat.exponentBias_eq_bias_of_isIEEE fmt hfmt,
    neg_normalMantissaExpOffset_eq_minSubnormalExponent_sub_one]
  simp only [show (denominator == 0) = false by simp [hdenominator],
    show (numerator == 0) = false by simp [hnumerator],
    Bool.false_eq_true, ite_false, beq_iff_eq, gt_iff_lt]
  split_ifs <;> first
    | rfl
    | (rw [Nat.sub_self])
    | (split <;> first | rfl | exact absurd ‹_ ≤ _› ‹¬_ ≤ _›)

/-- Positive nearest-even packing overflows to positive infinity above the normal range. -/
theorem roundRatScaled_false_eq_posInf_of_maxNormal_lt
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hoverflow :
      fmt.maxNormalExponent <
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent) :
    roundRatScaled fmt false numerator denominator exponent = posInf fmt := by
  rw [roundRatScaled_false_eq_of_isIEEE fmt numerator denominator exponent hfmt
    hnumerator hdenominator]
  simp only [ite_eq_left hoverflow]

/-- Below half of the smallest subnormal, positive nearest-even packing returns positive zero. -/
theorem roundRatScaled_false_eq_posZero_of_lt_minSubnormal_sub_one
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hunderflow :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minSubnormalExponent - 1) :
    roundRatScaled fmt false numerator denominator exponent = posZero fmt := by
  rw [roundRatScaled_false_eq_of_isIEEE fmt numerator denominator exponent hfmt
    hnumerator hdenominator]
  simp only [ite_eq_right (not_lt_of_ge hmax), ite_eq_left hunderflow]

/--
In the subnormal range, positive nearest-even packing rounds the quotient on the subnormal grid
and promotes a full mantissa to the smallest normal value.
-/
theorem roundRatScaled_false_eq_subnormal
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hlow :
      fmt.minSubnormalExponent - 1 ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hhigh :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minNormalExponent) :
    roundRatScaled fmt false numerator denominator exponent =
      if roundQuotientEven
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))).1
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))).2 = 0 then
        posZero fmt
      else if pow2 fmt.fracWidth ≤
          roundQuotientEven
            (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
              (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))).1
            (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
              (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))).2 then
        ofFields fmt false 1 0
      else
        ofFields fmt false 0
          (roundQuotientEven
            (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
              (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))).1
            (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
              (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))).2) := by
  have hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent :=
    hhigh.le.trans (minNormalExponent_le_maxNormalExponent fmt)
  rw [roundRatScaled_false_eq_of_isIEEE fmt numerator denominator exponent hfmt
    hnumerator hdenominator]
  simp only [ite_eq_right (not_lt_of_ge hmax), ite_eq_right (not_lt_of_ge hlow), ite_eq_left hhigh]

/--
In the normal range without a carry-out, positive nearest-even packing stores the rounded
mantissa at the leading exponent.
-/
theorem roundRatScaled_false_eq_normal_of_ne_carry
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hnormal :
      fmt.minNormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator)
      roundQuotientEven scaled.1 scaled.2 ≠ pow2 (fmt.fracWidth + 1)) :
    roundRatScaled fmt false numerator denominator exponent =
      ofFields fmt false
        (Int.toNat
          (Numerics.RationalBinary.floorLog2 numerator denominator + exponent +
            Int.ofNat fmt.exponentBias))
        (roundQuotientEven
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator)).1
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator)).2 -
          pow2 fmt.fracWidth) := by
  have hnotUnderflow :
      ¬Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minSubnormalExponent - 1 := by
    have := minSubnormalExponent_lt_minNormalExponent fmt
    omega
  rw [roundRatScaled_false_eq_of_isIEEE fmt numerator denominator exponent hfmt
    hnumerator hdenominator]
  simp only [ite_eq_right (not_lt_of_ge hmax), ite_eq_right hnotUnderflow,
    ite_eq_right (not_lt_of_ge hnormal),
    ite_eq_right hcarry]

/--
A carry-out whose incremented exponent still fits stores the smallest mantissa one binade
higher.
-/
theorem roundRatScaled_false_eq_normal_of_carry
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hnormal :
      fmt.minNormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hcarry :
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator)
      roundQuotientEven scaled.1 scaled.2 = pow2 (fmt.fracWidth + 1))
    (hcarryMax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1 ≤
        fmt.maxNormalExponent) :
    roundRatScaled fmt false numerator denominator exponent =
      ofFields fmt false
        (Int.toNat
          (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1 +
            Int.ofNat fmt.exponentBias))
        0 := by
  have hnotUnderflow :
      ¬Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minSubnormalExponent - 1 := by
    have := minSubnormalExponent_lt_minNormalExponent fmt
    omega
  rw [roundRatScaled_false_eq_of_isIEEE fmt numerator denominator exponent hfmt
    hnumerator hdenominator]
  have hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent := by
    omega
  simp only [ite_eq_right (not_lt_of_ge hmax), ite_eq_right hnotUnderflow,
    ite_eq_right (not_lt_of_ge hnormal), ite_eq_left hcarry, ite_eq_right (not_lt_of_ge hcarryMax)]

/-- A carry-out past the largest normal exponent overflows to positive infinity. -/
theorem roundRatScaled_false_eq_posInf_of_carry
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hnormal :
      fmt.minNormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator)
      roundQuotientEven scaled.1 scaled.2 = pow2 (fmt.fracWidth + 1))
    (hcarryOverflow :
      fmt.maxNormalExponent <
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1) :
    roundRatScaled fmt false numerator denominator exponent = posInf fmt := by
  have hnotUnderflow :
      ¬Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minSubnormalExponent - 1 := by
    have := minSubnormalExponent_lt_minNormalExponent fmt
    omega
  rw [roundRatScaled_false_eq_of_isIEEE fmt numerator denominator exponent hfmt
    hnumerator hdenominator]
  simp only [ite_eq_right (not_lt_of_ge hmax), ite_eq_right hnotUnderflow,
    ite_eq_right (not_lt_of_ge hnormal),
    ite_eq_left hcarry, ite_eq_left hcarryOverflow]

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
