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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Packing.Grid
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Internal
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime

/-!
# Branch equations for directed rational packing

`roundRatMagnitudeDirectedScaled` checks the denominator and zero before choosing an overflow,
underflow, subnormal, normal, or carry-out result. The equations below isolate its
positive-magnitude branches for the directed bound proofs. Sign restoration is proved separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/-! ## Positive packing branches -/

/--
Positive directed packing of a nonzero rational, exposing the exponent, significand, and
finite-field guards.
-/
theorem roundRatMagnitudeDirectedScaled_pos_eq
    (fmt : FloatFormat) (roundUp : Bool) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    roundRatMagnitudeDirectedScaled fmt roundUp false numerator denominator exponent =
      let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
      let totalExponent := rationalExponent + exponent
      if fmt.maxNormalExponent < totalExponent then
        directedOverflow fmt false roundUp
      else if totalExponent < fmt.minSubnormalExponent then
        if roundUp then posMinSubnormal fmt else zero fmt false
      else if totalExponent < fmt.minNormalExponent then
        let scaled :=
          Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))
        let rounded := roundQuotDirected roundUp scaled.1 scaled.2
        if rounded = 0 then
          zero fmt false
        else if pow2 fmt.fracWidth ≤ rounded then
          ofFields fmt false 1 0
        else
          ofFields fmt false 0 rounded
      else
        let scaled :=
          Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (Int.ofNat fmt.fracWidth - rationalExponent)
        let rounded := roundQuotDirected roundUp scaled.1 scaled.2
        let normalizedExponent :=
          if rounded = pow2 (fmt.fracWidth + 1) then totalExponent + 1 else totalExponent
        let normalizedMantissa :=
          if rounded = pow2 (fmt.fracWidth + 1) then pow2 fmt.fracWidth else rounded
        let encodedExponent := Int.toNat (normalizedExponent + Int.ofNat fmt.exponentBias)
        let fraction := normalizedMantissa - pow2 fmt.fracWidth
        if fmt.maxNormalExponent < normalizedExponent then
          directedOverflow fmt false roundUp
        else if (decide (encodedExponent > fmt.maxFiniteExpField) ||
            encodedExponent == fmt.maxFiniteExpField &&
              decide (fraction > fmt.maxFiniteFracField)) = true then
          directedOverflow fmt false roundUp
        else
          ofFields fmt false encodedExponent fraction := by
  unfold roundRatMagnitudeDirectedScaled packRoundedSubnormal packRoundedNormal
  simp only [show (denominator == 0) = false by simp [hdenominator],
    show (numerator == 0) = false by simp [hnumerator],
    Bool.false_eq_true, ite_false, beq_iff_eq, gt_iff_lt, ge_iff_le, FloatFormat.subnormalAlignExp]
  rfl

/-- Above the largest normal exponent, positive directed packing returns the directed overflow
  result. -/
theorem roundRatMagnitudeDirectedScaled_pos_eq_overflow
    (fmt : FloatFormat) (roundUp : Bool) (numerator denominator : Nat)
    (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hoverflow :
      fmt.maxNormalExponent <
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent) :
    roundRatMagnitudeDirectedScaled
        fmt roundUp false numerator denominator exponent =
      directedOverflow fmt false roundUp := by
  rw [roundRatMagnitudeDirectedScaled_pos_eq fmt roundUp numerator denominator exponent
    hnumerator hdenominator]
  simp only [ite_eq_left hoverflow]

/--
Below the smallest subnormal exponent, positive directed packing returns the smallest subnormal when
rounding up and zero when rounding down.
-/
theorem roundRatMagnitudeDirectedScaled_pos_eq_underflow
    (fmt : FloatFormat) (roundUp : Bool) (numerator denominator : Nat)
    (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hunderflow :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minSubnormalExponent) :
    roundRatMagnitudeDirectedScaled
        fmt roundUp false numerator denominator exponent =
      if roundUp then posMinSubnormal fmt else zero fmt false := by
  rw [roundRatMagnitudeDirectedScaled_pos_eq fmt roundUp numerator denominator exponent
    hnumerator hdenominator]
  simp only [ite_eq_right (not_lt_of_ge hmax), ite_eq_left hunderflow]

/-- In the subnormal range, positive downward packing stores the truncated quotient as a
  subnormal. -/
theorem roundRatMagnitudeDirectedScaled_pos_eq_subnormal_down
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hlow :
      fmt.minSubnormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hhigh :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minNormalExponent) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))
    let rounded := roundQuotDirected false scaled.1 scaled.2
    roundRatMagnitudeDirectedScaled
        fmt false false numerator denominator exponent =
      ofFields fmt false 0 rounded := by
  dsimp only
  have hpos :=
    (roundQuotDirected_subnormal_bounds fmt false numerator denominator exponent
      hnumerator hdenominator hlow hhigh).1
  have hlt :=
    roundQuotDirected_false_subnormal_lt_pow2
      fmt numerator denominator exponent hnumerator hdenominator hlow hhigh
  rw [roundRatMagnitudeDirectedScaled_pos_eq fmt false numerator denominator exponent
    hnumerator hdenominator]
  simp only [ite_eq_right (not_lt_of_ge hmax), ite_eq_right (not_lt_of_ge hlow), ite_eq_left hhigh,
    ite_eq_right (Nat.one_le_iff_ne_zero.mp hpos), ite_eq_right (not_le_of_gt hlt)]

/--
In the subnormal range, positive upward packing stores the ceiling quotient as a subnormal, or the
smallest normal value when the quotient fills the mantissa.
-/
theorem roundRatMagnitudeDirectedScaled_pos_eq_subnormal_up
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hlow :
      fmt.minSubnormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hhigh :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minNormalExponent) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))
    let rounded := roundQuotDirected true scaled.1 scaled.2
    roundRatMagnitudeDirectedScaled
        fmt true false numerator denominator exponent =
      if pow2 fmt.fracWidth ≤ rounded then
        ofFields fmt false 1 0
      else
        ofFields fmt false 0 rounded := by
  dsimp only
  have hpos :=
    (roundQuotDirected_subnormal_bounds fmt true numerator denominator exponent
      hnumerator hdenominator hlow hhigh).1
  rw [roundRatMagnitudeDirectedScaled_pos_eq fmt true numerator denominator exponent
    hnumerator hdenominator]
  simp only [ite_eq_right (not_lt_of_ge hmax), ite_eq_right (not_lt_of_ge hlow), ite_eq_left hhigh,
    ite_eq_right (Nat.one_le_iff_ne_zero.mp hpos)]

/--
In the normal range of an IEEE descriptor, positive downward packing stores the truncated
mantissa at the leading exponent.
-/
theorem roundRatMagnitudeDirectedScaled_pos_eq_normal_down
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hnormal :
      fmt.minNormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent) :
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let totalExponent := rationalExponent + exponent
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (Int.ofNat fmt.fracWidth - rationalExponent)
    let rounded := roundQuotDirected false scaled.1 scaled.2
    roundRatMagnitudeDirectedScaled
        fmt false false numerator denominator exponent =
      ofFields fmt false
        (Int.toNat (totalExponent + Int.ofNat fmt.exponentBias))
        (rounded - pow2 fmt.fracWidth) := by
  dsimp only
  have hnotUnderflow :
      ¬Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minSubnormalExponent :=
    not_lt_of_ge ((minSubnormalExponent_lt_minNormalExponent fmt).le.trans hnormal)
  have hlt :=
    roundQuotDirected_false_normal_lt_pow2_succ fmt numerator denominator hnumerator hdenominator
  have hguard := Directed.Internal.normalizedGuard_eq_false fmt hfmt _ _ hlt hnormal hmax
  dsimp only at hlt hguard
  rw [roundRatMagnitudeDirectedScaled_pos_eq fmt false numerator denominator exponent
    hnumerator hdenominator]
  simp only [ite_eq_right (not_lt_of_ge hmax), hnotUnderflow, ite_false,
    ite_eq_right (not_lt_of_ge hnormal),
    ite_eq_right (ne_of_lt hlt), hguard, Bool.false_eq_true]

/--
In the normal range of an IEEE descriptor, upward packing without a carry stores the ceiling
mantissa at the leading exponent.
-/
theorem roundRatMagnitudeDirectedScaled_pos_eq_normal_up_no_carry
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
      let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (Int.ofNat fmt.fracWidth - rationalExponent)
      roundQuotDirected true scaled.1 scaled.2 ≠
        pow2 (fmt.fracWidth + 1)) :
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let totalExponent := rationalExponent + exponent
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (Int.ofNat fmt.fracWidth - rationalExponent)
    let rounded := roundQuotDirected true scaled.1 scaled.2
    roundRatMagnitudeDirectedScaled
        fmt true false numerator denominator exponent =
      ofFields fmt false
        (Int.toNat (totalExponent + Int.ofNat fmt.exponentBias))
        (rounded - pow2 fmt.fracWidth) := by
  dsimp only
  dsimp only at hcarry
  have hnotUnderflow :
      ¬Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minSubnormalExponent :=
    not_lt_of_ge ((minSubnormalExponent_lt_minNormalExponent fmt).le.trans hnormal)
  have hlt :=
    lt_of_le_of_ne
      (roundQuotDirected_normal_bounds fmt true numerator denominator hnumerator hdenominator).2
      hcarry
  have hguard := Directed.Internal.normalizedGuard_eq_false fmt hfmt _ _ hlt hnormal hmax
  dsimp only at hguard
  rw [roundRatMagnitudeDirectedScaled_pos_eq fmt true numerator denominator exponent
    hnumerator hdenominator]
  simp only [ite_eq_right (not_lt_of_ge hmax), hnotUnderflow, ite_false,
    ite_eq_right (not_lt_of_ge hnormal),
    ite_eq_right hcarry, hguard, Bool.false_eq_true]

/-- A carry-out whose incremented exponent still fits stores the smallest mantissa one binade
  higher. -/
theorem roundRatMagnitudeDirectedScaled_pos_eq_normal_up_carry
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hnormal :
      fmt.minNormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (Int.ofNat fmt.fracWidth - rationalExponent)
      roundQuotDirected true scaled.1 scaled.2 =
        pow2 (fmt.fracWidth + 1))
    (hcarryMax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1 ≤
        fmt.maxNormalExponent) :
    roundRatMagnitudeDirectedScaled
        fmt true false numerator denominator exponent =
      ofFields fmt false
        (Int.toNat
          (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1 +
            Int.ofNat fmt.exponentBias))
        0 := by
  dsimp only at hcarry
  have hnotUnderflow :
      ¬Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minSubnormalExponent :=
    not_lt_of_ge ((minSubnormalExponent_lt_minNormalExponent fmt).le.trans hnormal)
  have hguard :=
    Directed.Internal.packingGuard_eq_false fmt
      (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1) 0
      (by omega) hcarryMax (Nat.zero_le _)
  dsimp only at hguard
  rw [roundRatMagnitudeDirectedScaled_pos_eq fmt true numerator denominator exponent
    hnumerator hdenominator]
  simp only [ite_eq_right (not_lt_of_ge hmax), hnotUnderflow, ite_false,
    ite_eq_right (not_lt_of_ge hnormal),
    ite_eq_left hcarry, ite_eq_right (not_lt_of_ge hcarryMax), Nat.sub_self, hguard,
      Bool.false_eq_true]

/-- A carry-out past the largest normal exponent returns the directed overflow result. -/
theorem roundRatMagnitudeDirectedScaled_pos_eq_normal_up_carry_overflow
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hnormal :
      fmt.minNormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (Int.ofNat fmt.fracWidth - rationalExponent)
      roundQuotDirected true scaled.1 scaled.2 =
        pow2 (fmt.fracWidth + 1))
    (hcarryOverflow :
      fmt.maxNormalExponent <
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1) :
    roundRatMagnitudeDirectedScaled
        fmt true false numerator denominator exponent =
      directedOverflow fmt false true := by
  dsimp only at hcarry
  have hnotUnderflow :
      ¬Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minSubnormalExponent :=
    not_lt_of_ge ((minSubnormalExponent_lt_minNormalExponent fmt).le.trans hnormal)
  rw [roundRatMagnitudeDirectedScaled_pos_eq fmt true numerator denominator exponent
    hnumerator hdenominator]
  simp only [ite_eq_right (not_lt_of_ge hmax), hnotUnderflow, ite_false,
    ite_eq_right (not_lt_of_ge hnormal),
    ite_eq_left hcarry, ite_eq_left hcarryOverflow]

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
