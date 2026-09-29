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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Branches

/-!
# Rounded-real semantics

Scaled rational inputs connect to the independent real-number rounding definition `roundAt`
through their exponent and mantissa. The proof removes the sign, identifies the exact exponent
and scaled mantissa seen by the generic rounding theory, and proves that nearest-even quotient
selection makes the same tie decision.

For descriptors with `fmt.isIEEE = true`, the remaining lemmas show that an exact magnitude at
most the largest finite value produces a finite packed result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
open Directed.Internal

section

/-! ## Sign reduction -/

/-- Non-NaN scaled rational rounding restores a negative sign by exact sign-bit negation. -/
theorem roundRatScaled_true_eq_neg_false
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hdenominator : denominator ≠ 0) :
    roundRatScaled fmt true numerator denominator exponent =
      neg (roundRatScaled fmt false numerator denominator exponent) := by
  by_cases hnumerator : numerator = 0
  · subst numerator
    rw [roundRatScaled_num_zero fmt true denominator exponent hdenominator,
      roundRatScaled_num_zero fmt false denominator exponent hdenominator]
    simp [zero]
  simp only [roundRatScaled, dite_eq_left hfmt]
  unfold ieeeRoundRatScaled
  have hsigned := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
  simp only [show (denominator == 0) = false by simp [hdenominator],
    show (numerator == 0) = false by simp [hnumerator],
    Bool.false_eq_true, ite_false]
  split
  · simp [neg_posInf]
  · split
    · simp [neg_posZero, zero, hsigned]
    · split
      · split
        · simp [neg_posZero, zero, hsigned]
        · split <;>
            simp [neg_ofFields_of_supportsSignedZero fmt hsigned]
      · split
        · split <;>
            simp [neg_posInf,
              neg_ofFields_of_supportsSignedZero fmt hsigned]
        · exact (neg_ofFields_of_supportsSignedZero fmt hsigned false _ _).symm

/-! ## Rounded-real exponent and mantissa -/

/-- The absolute value of a signed scaled rational is its unsigned magnitude. -/
theorem abs_signedScaledRatToReal
    (sign : Bool) (numerator denominator : Nat) (exponent : Int) :
    |signedScaledRatToReal sign numerator denominator exponent| =
      scaledRatToReal numerator denominator exponent := by
  have hnonnegative :=
    scaledRatToReal_nonneg numerator denominator exponent
  cases sign <;>
    simp [signedScaledRatToReal, abs_of_nonneg hnonnegative]

/--
The Flocq magnitude of a nonzero scaled rational is one above its leading binary exponent,
`Numerics.RationalBinary.floorLog2 numerator denominator + exponent`.
-/
theorem magnitude_signedScaledRatToReal
    (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    magnitude Numerics.binaryRadix
        (signedScaledRatToReal sign numerator denominator exponent) =
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1 := by
  let value := signedScaledRatToReal sign numerator denominator exponent
  have hpositive :=
    scaledRatToReal_pos numerator denominator exponent hnumerator hdenominator
  have hvalue : value ≠ 0 := by
    cases sign <;> simp [value, signedScaledRatToReal, hpositive.ne']
  have hbounds :=
    scaledRatToReal_floorLog2_bounds
      numerator denominator exponent hnumerator hdenominator
  apply magnitude_eq_of_bpow_bounds
    Numerics.binaryRadix value
      (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1) hvalue
  · rw [abs_signedScaledRatToReal]
    have hexponent :
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1 - 1 =
          Numerics.RationalBinary.floorLog2 numerator denominator + exponent := by
      omega
    rw [hexponent]
    exact hbounds.1
  · rw [abs_signedScaledRatToReal]
    exact hbounds.2

/-- The rounded-real model and rational implementation choose the same target exponent. -/
theorem cexp_signedScaledRatToReal
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0) :
    cexp Numerics.binaryRadix (fexpOf fmt)
        (signedScaledRatToReal sign numerator denominator exponent) =
      fexpOf fmt (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1) := by
  rw [cexp,
    magnitude_signedScaledRatToReal
      sign numerator denominator exponent hnumerator hdenominator]

/--
The canonical scaled mantissa of a rational is the same quotient after moving the selected
binary exponent into its natural numerator or denominator.
-/
theorem scaledMantissa_signedScaledRatToReal
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0) :
    let target := fexpOf fmt
      (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1)
    let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (exponent -
      target)
    scaledMantissa Numerics.binaryRadix (fexpOf fmt)
        (signedScaledRatToReal sign numerator denominator exponent) =
      if sign then
        -((scaled.1 : Real) / (scaled.2 : Real))
      else
        (scaled.1 : Real) / (scaled.2 : Real) := by
  dsimp only
  let target := fexpOf fmt
    (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1)
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (exponent - target)
  rw [scaledMantissa_eq_div, cexp_signedScaledRatToReal
    fmt sign numerator denominator exponent hnumerator hdenominator]
  have hscale :
      (scaled.1 : Real) / (scaled.2 : Real) =
        scaledRatToReal numerator denominator (exponent - target) := by
    exact scaleByPowerOfTwo_real numerator denominator (exponent - target)
  have hcombine :
      scaledRatToReal numerator denominator exponent * bpow (-target) =
        scaledRatToReal numerator denominator (exponent - target) := by
    simpa [sub_eq_add_neg] using
      scaledRatToReal_mul_bpow numerator denominator exponent (-target)
  cases sign with
  | false =>
      simp only [signedScaledRatToReal, Bool.false_eq_true, ite_false]
      rw [div_eq_mul_inv, ← bpow.neg_exp]
      change
        scaledRatToReal numerator denominator exponent * bpow (-target) =
          (scaled.1 : Real) / (scaled.2 : Real)
      rw [hcombine, ← hscale]
  | true =>
      simp only [signedScaledRatToReal, ite_true]
      rw [div_eq_mul_inv, ← bpow.neg_exp]
      change
        -scaledRatToReal numerator denominator exponent * bpow (-target) =
          -((scaled.1 : Real) / (scaled.2 : Real))
      rw [neg_mul, hcombine, ← hscale]

/-- Nearest-even selection of the scaled rational is `roundQuotientEven`, with its sign restored. -/
theorem nearestEven_scaledRat
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0) :
    let target := fexpOf fmt
      (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1)
    let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (exponent -
      target)
    nearestEven
        (scaledMantissa Numerics.binaryRadix (fexpOf fmt)
          (signedScaledRatToReal sign numerator denominator exponent)) =
      if sign then
        -Int.ofNat (roundQuotientEven scaled.1 scaled.2)
      else
        Int.ofNat (roundQuotientEven scaled.1 scaled.2) := by
  dsimp only
  let target := fexpOf fmt
    (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1)
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (exponent - target)
  rw [scaledMantissa_signedScaledRatToReal
    fmt sign numerator denominator exponent hnumerator hdenominator]
  have hscaledDenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator
      (exponent - target) hdenominator
  have hround :=
    nearestEven_div_eq_roundQuotientEven
      scaled.1 scaled.2 hscaledDenominator
  cases sign with
  | false =>
      change
        nearestEven ((scaled.1 : Real) / (scaled.2 : Real)) =
          Int.ofNat (roundQuotientEven scaled.1 scaled.2)
      exact hround
  | true =>
      change
        nearestEven (-((scaled.1 : Real) / (scaled.2 : Real))) =
          -Int.ofNat (roundQuotientEven scaled.1 scaled.2)
      rw [nearestEven_neg, hround]

/-- Rounded-real nearest-even semantics of a nonzero signed scaled rational. -/
theorem roundAt_scaledRat_eq
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0) :
    let target := fexpOf fmt
      (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1)
    let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (exponent -
      target)
    let rounded := roundQuotientEven scaled.1 scaled.2
    roundAt fmt (signedScaledRatToReal sign numerator denominator exponent) =
      ((if sign then -Int.ofNat rounded else Int.ofNat rounded) : Int) *
        bpow target := by
  dsimp only
  let target := fexpOf fmt
    (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1)
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (exponent - target)
  let rounded := roundQuotientEven scaled.1 scaled.2
  have hround :=
    nearestEven_scaledRat
      fmt sign numerator denominator exponent hnumerator hdenominator
  change
    round (β := Numerics.binaryRadix) (fexp := fexpOf fmt)
        nearestEven
        (signedScaledRatToReal sign numerator denominator exponent) =
      ((if sign then -Int.ofNat rounded else Int.ofNat rounded) : Int) *
        bpow target
  rw [round_eq_toReal_of_scaled_round_eq
    nearestEven
    (signedScaledRatToReal sign numerator denominator exponent)
    (if sign then -Int.ofNat rounded else Int.ofNat rounded)]
  · rw [cexp_signedScaledRatToReal
      fmt sign numerator denominator exponent hnumerator hdenominator]
    rfl
  · simpa [target, scaled, rounded] using hround

private theorem scaledRatLeadingExponent_le_maxNormal
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hbound :
      scaledRatToReal numerator denominator exponent ≤
        toReal (posMaxFinite fmt)) :
    Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
      fmt.maxNormalExponent := by
  have hbounds :=
    scaledRatToReal_floorLog2_bounds
      numerator denominator exponent hnumerator hdenominator
  have hpow :
      bpow (Numerics.RationalBinary.floorLog2 numerator denominator + exponent) <
        bpow (fmt.maxNormalExponent + 1) :=
    hbounds.1.trans_lt (hbound.trans_lt (toReal_posMaxFinite_lt_bpow fmt))
  have hexponent :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.maxNormalExponent + 1 :=
    (bpow_lt_bpow_iff Numerics.binaryRadix _ _).mp hpow
  omega

private theorem roundQuotientEven_ne_top_of_bound_at_max
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent =
        fmt.maxNormalExponent)
    (hbound :
      scaledRatToReal numerator denominator exponent ≤
        toReal (posMaxFinite fmt)) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator)
    roundQuotientEven scaled.1 scaled.2 ≠ pow2 (fmt.fracWidth + 1) := by
  dsimp only
  intro hcarry
  have hround :=
    roundAt_scaledRat_eq
      fmt false numerator denominator exponent hnumerator hdenominator
  have hnormal :
      fmt.minNormalExponent ≤
        fmt.maxNormalExponent :=
    minNormalExponent_le_maxNormalExponent fmt
  have htarget :
      fexpOf fmt
          (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1) =
        fmt.maxNormalExponent -
          Int.ofNat fmt.fracWidth := by
    rw [hmax]
    exact fexpOf_total_eq_normal
      fmt (fmt.maxNormalExponent) hnormal
  have hroundValue :
      roundAt fmt
          (signedScaledRatToReal false numerator denominator exponent) =
        bpow (fmt.maxNormalExponent + 1) := by
    simp only [Bool.false_eq_true, ite_false] at hround
    rw [htarget] at hround
    have hscaled :
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (exponent -
              (fmt.maxNormalExponent -
                Int.ofNat fmt.fracWidth)) =
          Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (Int.ofNat fmt.fracWidth -
              Numerics.RationalBinary.floorLog2 numerator denominator) := by
      congr 1
      omega
    rw [hscaled, hcarry] at hround
    rw [hround]
    change
      (pow2 (fmt.fracWidth + 1) : Real) *
          bpow (fmt.maxNormalExponent -
            Int.ofNat fmt.fracWidth) =
        bpow (fmt.maxNormalExponent + 1)
    rw [← bpow_ofNat (fmt.fracWidth + 1), ← bpow_add]
    congr 1
    simp only [Int.ofNat_eq_natCast, Int.natCast_add]
    ring
  have hmono :
      roundAt fmt
          (signedScaledRatToReal false numerator denominator exponent) ≤
        roundAt fmt (toReal (posMaxFinite fmt)) := by
    apply roundAt_mono
    simpa [signedScaledRatToReal] using hbound
  rw [hroundValue,
    roundAt_toReal_eq (posMaxFinite fmt) (isFinite_posMaxFinite fmt)] at hmono
  exact (not_lt_of_ge hmono) (toReal_posMaxFinite_lt_bpow fmt)

private theorem isFinite_roundRatScaled_false_of_le_posMaxFinite
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hbound :
      scaledRatToReal numerator denominator exponent ≤
        toReal (posMaxFinite fmt)) :
    isFinite (roundRatScaled fmt false numerator denominator exponent) = true := by
  have hmax :=
    scaledRatLeadingExponent_le_maxNormal
      fmt numerator denominator exponent hnumerator hdenominator hbound
  rcases lt_or_ge (Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
      (fmt.minSubnormalExponent - 1) with hunderflow | hlow
  · rw [roundRatScaled_false_eq_posZero_of_lt_minSubnormal_sub_one
      fmt numerator denominator exponent hfmt hnumerator hdenominator hmax hunderflow]
    exact isFinite_posZero fmt
  rcases lt_or_ge (Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
      fmt.minNormalExponent with hsubnormal | hnormal
  · rw [roundRatScaled_false_eq_subnormal
      fmt numerator denominator exponent hfmt hnumerator hdenominator hlow hsubnormal]
    split_ifs
    · exact isFinite_posZero fmt
    · exact isFinite_ofFields_ieee fmt hfmt false 1 0 (FloatFormat.one_lt_expAllOnesNat fmt)
    · exact isFinite_ofFields_ieee fmt hfmt false 0 _ fmt.expAllOnesNat_pos
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
      rcases hmax.lt_or_eq with hlt | heq
      · omega
      · exact absurd hcarry
          (roundQuotientEven_ne_top_of_bound_at_max
            fmt numerator denominator exponent hnumerator hdenominator heq hbound)
    rw [roundRatScaled_false_eq_normal_of_carry
      fmt numerator denominator exponent hfmt hnumerator hdenominator hnormal hcarry hcarryMax]
    exact isFinite_ofFields_ieee fmt hfmt false _ 0
      (encodedExponent_lt_expAllOnes_ieee fmt hfmt _ (by omega) hcarryMax)
  · rw [roundRatScaled_false_eq_normal_of_ne_carry
      fmt numerator denominator exponent hfmt hnumerator hdenominator hnormal hmax hcarry]
    exact isFinite_ofFields_ieee fmt hfmt false _ _
      (encodedExponent_lt_expAllOnes_ieee fmt hfmt _ hnormal hmax)

/--
Nearest-even scaled-rational rounding cannot overflow when the exact magnitude is at most the
largest finite value of the destination format.
-/
theorem isFinite_roundRatScaled_of_abs_le_posMaxFinite
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true)
    (hdenominator : denominator ≠ 0)
    (hbound :
      |signedScaledRatToReal sign numerator denominator exponent| ≤
        toReal (posMaxFinite fmt)) :
    isFinite (roundRatScaled fmt sign numerator denominator exponent) = true := by
  by_cases hnumerator : numerator = 0
  · cases sign <;> simp [roundRatScaled, hfmt, ieeeRoundRatScaled,
      hdenominator, hnumerator]
  have hmagnitude :
      scaledRatToReal numerator denominator exponent ≤
        toReal (posMaxFinite fmt) := by
    rw [← abs_signedScaledRatToReal sign]
    exact hbound
  cases sign with
  | false =>
      exact isFinite_roundRatScaled_false_of_le_posMaxFinite
        fmt numerator denominator exponent
          hfmt hnumerator hdenominator hmagnitude
  | true =>
      rw [roundRatScaled_true_eq_neg_false
        fmt numerator denominator exponent hfmt hdenominator, isFinite_neg]
      exact isFinite_roundRatScaled_false_of_le_posMaxFinite
        fmt numerator denominator exponent
          hfmt hnumerator hdenominator hmagnitude


end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
