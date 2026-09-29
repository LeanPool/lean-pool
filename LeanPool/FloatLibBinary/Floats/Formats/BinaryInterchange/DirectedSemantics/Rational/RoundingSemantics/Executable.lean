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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.RoundedReal

/-!
# Executable packing semantics

For a descriptor with `fmt.isIEEE = true` and a nonzero rational input, a finite result produced
by `roundRatScaled` denotes exactly `roundAt` applied to the corresponding real value.

The positive proof covers underflow, subnormal and normal results, including a carry into the next
exponent. Finiteness excludes the overflow branches. The signed theorem restores the sign through
the symmetry proved in `RoundedReal`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
open Directed.Internal

section

/-! ## Executable packing semantics -/

/--
Positive scaled-rational rounding denotes the independent nearest-even rounded-real value whenever
the executable result is finite.
-/
theorem toReal_roundRatScaled_false_eq_roundAt
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hfinite : isFinite (roundRatScaled fmt false numerator denominator exponent) = true) :
    toReal (roundRatScaled fmt false numerator denominator exponent) =
      roundAt fmt (signedScaledRatToReal false numerator denominator exponent) := by
  have hinfinity := FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt
  have hsubnormalLt := minSubnormalExponent_lt_minNormalExponent fmt
  have hround :=
    roundAt_scaledRat_eq fmt false numerator denominator exponent hnumerator hdenominator
  simp only [Bool.false_eq_true, ite_false, Int.ofNat_eq_natCast, Int.cast_natCast] at hround
  rcases lt_or_ge fmt.maxNormalExponent
      (Numerics.RationalBinary.floorLog2 numerator denominator + exponent) with hoverflow | hmax
  · rw [roundRatScaled_false_eq_posInf_of_maxNormal_lt
      fmt numerator denominator exponent hfmt hnumerator hdenominator hoverflow,
      isFinite_posInf fmt hinfinity] at hfinite
    exact absurd hfinite Bool.false_ne_true
  rcases lt_or_ge (Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
      (fmt.minSubnormalExponent - 1) with hunderflow | hlow
  · rw [fexpOf_total_eq_minSubnormal fmt _ (by omega),
      roundQuotientEven_scaled_eq_zero numerator denominator _ hnumerator hdenominator
        (by omega)] at hround
    rw [roundRatScaled_false_eq_posZero_of_lt_minSubnormal_sub_one
      fmt numerator denominator exponent hfmt hnumerator hdenominator hmax hunderflow,
      toReal_posZero fmt hfmt, hround]
    simp
  rcases lt_or_ge (Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
      fmt.minNormalExponent with hsubnormal | hnormal
  · have halign := subnormalAlignExp_add_minSubnormalExponent fmt
    rw [fexpOf_total_eq_minSubnormal fmt _ hsubnormal,
      show exponent - fmt.minSubnormalExponent =
        exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt) by omega] at hround
    rw [roundRatScaled_false_eq_subnormal
      fmt numerator denominator exponent hfmt hnumerator hdenominator hlow hsubnormal, hround]
    generalize hrounded :
      roundQuotientEven
        (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))).1
        (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))).2 = rounded
    have hroundedLe : rounded ≤ pow2 fmt.fracWidth := by
      rw [← hrounded]
      rcases lt_or_ge (Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
          fmt.minSubnormalExponent with hbelow | hlow'
      · exact (roundQuotientEven_le_one_of_lt _ _
          (Numerics.RationalBinary.scaleByPowerOfTwo_fst_ne_zero numerator denominator _
            hnumerator)
          (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator _
            hdenominator)
          (scaleByPowerOfTwo_fst_lt_snd_of_neg_log numerator denominator _
            hnumerator hdenominator (by omega))).trans (Nat.succ_le_of_lt (pow2_pos _))
      · exact roundQuotientEven_subnormal_le
          fmt numerator denominator exponent hnumerator hdenominator hlow' hsubnormal
    by_cases hzero : rounded = 0
    · simp [hzero, toReal_posZero fmt hfmt]
    · simpa [hzero] using toReal_roundSubnormalUp fmt rounded hzero hroundedLe
  rw [fexpOf_total_eq_normal fmt _ hnormal,
    show exponent -
        (Numerics.RationalBinary.floorLog2 numerator denominator + exponent -
          Int.ofNat fmt.fracWidth) =
      Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator by
      omega] at hround
  have hbounds :=
    roundQuotientEven_normal_bounds fmt numerator denominator hnumerator hdenominator
  by_cases hcarry :
      roundQuotientEven
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator)).1
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator)).2 =
        pow2 (fmt.fracWidth + 1)
  · have hcarryMax :
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1 ≤
          fmt.maxNormalExponent := by
      by_contra hnot
      rw [roundRatScaled_false_eq_posInf_of_carry
        fmt numerator denominator exponent hfmt hnumerator hdenominator hnormal hmax hcarry
          (lt_of_not_ge hnot),
        isFinite_posInf fmt hinfinity] at hfinite
      exact absurd hfinite Bool.false_ne_true
    rw [roundRatScaled_false_eq_normal_of_carry
      fmt numerator denominator exponent hfmt hnumerator hdenominator hnormal hcarry hcarryMax]
      at hfinite ⊢
    have hvalue :=
      toReal_ofFields_normalized fmt (pow2 fmt.fracWidth)
        (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1)
        le_rfl (pow2_lt_pow2_succ fmt.fracWidth) (by omega) hcarryMax
        (by simpa only [Nat.sub_self] using hfinite)
    rw [Nat.sub_self] at hvalue
    rw [hvalue, hround, hcarry]
    exact normalizationCarry_value fmt _
  · rw [roundRatScaled_false_eq_normal_of_ne_carry
      fmt numerator denominator exponent hfmt hnumerator hdenominator hnormal hmax hcarry]
      at hfinite ⊢
    rw [toReal_ofFields_normalized fmt _ _ hbounds.1 (lt_of_le_of_ne hbounds.2 hcarry)
      hnormal hmax hfinite, hround]

/--
Finite scaled rational rounding is exact signed rational evaluation followed by one nearest-even
rounding in the destination format.
-/
theorem toReal_roundRatScaled_eq_roundAt
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0)
    (hfinite : isFinite (roundRatScaled fmt sign numerator denominator exponent) = true) :
    toReal (roundRatScaled fmt sign numerator denominator exponent) =
      roundAt fmt
        (signedScaledRatToReal sign numerator denominator exponent) := by
  cases sign with
  | false =>
      exact toReal_roundRatScaled_false_eq_roundAt
        fmt numerator denominator exponent hfmt hnumerator hdenominator hfinite
  | true =>
      rw [roundRatScaled_true_eq_neg_false
        fmt numerator denominator exponent hfmt hdenominator] at hfinite ⊢
      have hfiniteFalse :
          isFinite (roundRatScaled fmt false numerator denominator exponent) = true := by
        simpa using hfinite
      rw [toReal_neg _ hfiniteFalse,
        toReal_roundRatScaled_false_eq_roundAt
          fmt numerator denominator exponent hfmt hnumerator hdenominator hfiniteFalse]
      simp [signedScaledRatToReal]


end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
