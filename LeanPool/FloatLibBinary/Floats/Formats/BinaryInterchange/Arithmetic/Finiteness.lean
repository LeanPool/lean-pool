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
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Proof

/-!
# Symbolic finiteness conditions

The executable arithmetic refinement theorems are stated over real values, but IEEE overflow is
observable only on the encoded result. This module connects those views: an exact dyadic whose
magnitude is at most the largest finite value of the destination format cannot round to infinity.

The result is uniform in the exponent and fraction widths and is intended as the common foundation
for operation-specific no-overflow theorems.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

private theorem toReal_posMaxFinite_ieee
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    toReal (posMaxFinite fmt) =
      ((pow2 (fmt.fracWidth + 1) - 1 : Nat) : ℝ) *
        bpow (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) -
      Int.ofNat fmt.fracWidth) := by
  obtain ⟨hencoding, _⟩ :=
    (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt
  rw [toReal_posMaxFinite, FloatFormat.maxNormalExponent_eq_ieee fmt hfmt]
  congr 1
  simp only [FloatFormat.maxFiniteFracField, FloatFormat.fracMaskNat,
    hencoding, pow2_eq_two_pow, pow_succ]
  have hpow : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  exact_mod_cast show
      2 ^ fmt.fracWidth + (2 ^ fmt.fracWidth - 1) =
        2 ^ fmt.fracWidth * 2 - 1 by
    omega

private theorem encodedExponent_lt_expAllOnesNat_ieee
    (fmt : FloatFormat) (exponent : Int)
    (hmin : FloatFormat.ieeeMinNormalExponent fmt ≤ exponent)
    (hmax : exponent ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) :
    Int.toNat (exponent + Int.ofNat fmt.bias) <
      FloatFormat.expAllOnesNat fmt := by
  have hpositive : 0 ≤ exponent + Int.ofNat fmt.bias := by
    unfold FloatFormat.ieeeMinNormalExponent at hmin
    omega
  have hencoded :
      Int.ofNat (Int.toNat (exponent + Int.ofNat fmt.bias)) =
        exponent + Int.ofNat fmt.bias :=
    Int.toNat_of_nonneg hpositive
  have hupper :
      Int.toNat (exponent + Int.ofNat fmt.bias) ≤ 2 * fmt.bias := by
    apply Int.ofNat_le.mp
    calc
      Int.ofNat (Int.toNat (exponent + Int.ofNat fmt.bias)) =
          exponent + Int.ofNat fmt.bias := hencoded
      _ ≤ Int.ofNat fmt.bias + Int.ofNat fmt.bias := by
        unfold FloatFormat.ieeeMaxNormalExponent at hmax
        exact add_le_add_left hmax _
      _ = Int.ofNat (2 * fmt.bias) := by
        simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
        ring
  have hge := fmt.expWidth_ge_two
  have hwidth : fmt.expWidth = (fmt.expWidth - 1) + 1 := by
    omega
  have hpow :
      2 ^ fmt.expWidth = 2 * 2 ^ (fmt.expWidth - 1) := by
    rw [hwidth, pow_succ]
    exact Nat.mul_comm _ _
  have hbiasDouble : 2 * fmt.bias = 2 ^ fmt.expWidth - 2 := by
    unfold FloatFormat.bias
    rw [hpow]
    omega
  rw [hbiasDouble] at hupper
  have hfour : 4 ≤ 2 ^ fmt.expWidth := by
    simpa using
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) fmt.expWidth_ge_two
  unfold FloatFormat.expAllOnesNat
  omega

private theorem bpow_le_abs_toReal_of_mant_ne_zero
    (d : Numerics.Dyadic) (hm : d.significand ≠ 0) :
    bpow (Int.ofNat d.significand.log2 + d.exponent) ≤ |d.toReal| := by
  rw [Dyadic.abs_toReal]
  have hleading : pow2 d.significand.log2 ≤ d.significand :=
    pow2_log2_le hm
  have hleadingReal : (pow2 d.significand.log2 : ℝ) ≤ d.significand := by
    exact_mod_cast hleading
  calc
    bpow (Int.ofNat d.significand.log2 + d.exponent) =
        bpow (Int.ofNat d.significand.log2) * bpow d.exponent := bpow_add _ _
    _ = (pow2 d.significand.log2 : ℝ) * bpow d.exponent := by
      rw [bpow_ofNat]
    _ ≤ (d.significand : ℝ) * bpow d.exponent :=
      mul_le_mul_of_nonneg_right hleadingReal (bpow_nonneg _)

private theorem leadingExponent_le_maxNormal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (d : Numerics.Dyadic) (hm : d.significand ≠ 0)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    Int.ofNat d.significand.log2 + d.exponent ≤
      Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
  have hmaximum :=
    toReal_posMaxFinite_lt_bpow fmt
  rw [FloatFormat.maxNormalExponent_eq_ieee fmt hfmt] at hmaximum
  have hpow :
      bpow (Int.ofNat d.significand.log2 + d.exponent) <
        bpow (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) + 1) :=
    (bpow_le_abs_toReal_of_mant_ne_zero d hm).trans_lt
      (hbound.trans_lt hmaximum)
  have hexponent :
      Int.ofNat d.significand.log2 + d.exponent <
        Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) + 1 :=
    (bpow_lt_bpow_iff Numerics.binaryRadix _ _).mp hpow
  omega

private theorem roundMantissaToLeadingBitEven_lt_top_of_bound_at_max
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (d : Numerics.Dyadic)
    (hk :
      Int.ofNat d.significand.log2 + d.exponent =
        Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt))
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    roundMantissaToLeadingBitEven d.significand fmt.fracWidth <
      pow2 (fmt.fracWidth + 1) := by
  let target : Int :=
    Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) -
      Int.ofNat fmt.fracWidth
  let scaled : ℝ :=
    (d.significand : ℝ) * bpow (d.exponent - target)
  let maximumMantissa : Nat := pow2 (fmt.fracWidth + 1) - 1
  have hscale : 0 < bpow target := bpow_pos target
  have habs :
      |d.toReal| = scaled * bpow target := by
    rw [Dyadic.abs_toReal]
    dsimp only [scaled]
    have hpow :
        bpow d.exponent = bpow (d.exponent - target) * bpow target := by
      rw [← bpow_add]
      congr 1
      omega
    change
      (d.significand : ℝ) * bpow d.exponent =
        (d.significand : ℝ) * bpow (d.exponent - target) * bpow target
    rw [hpow]
    ring
  have hmaximum :
      toReal (posMaxFinite fmt) =
        (maximumMantissa : ℝ) * bpow target := by
    rw [toReal_posMaxFinite_ieee fmt hfmt]
  have hscaled : scaled ≤ (maximumMantissa : ℝ) := by
    have hmul :
        scaled * bpow target ≤ (maximumMantissa : ℝ) * bpow target := by
      rw [← habs, ← hmaximum]
      exact hbound
    exact le_of_mul_le_mul_right hmul hscale
  have hround :
      nearestEven scaled ≤ nearestEven (maximumMantissa : ℝ) :=
    ValidRnd.monotone scaled maximumMantissa hscaled
  have hscaledEq :
      nearestEven scaled =
        Int.ofNat (roundMantissaToLeadingBitEven d.significand fmt.fracWidth) := by
    dsimp only [scaled, target]
    rw [nearestEven_scaledMagnitude]
    have htarget :
        Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) -
            Int.ofNat fmt.fracWidth =
          Int.ofNat d.significand.log2 + d.exponent - Int.ofNat fmt.fracWidth := by
      omega
    rw [htarget]
    exact congrArg Int.ofNat
      (roundMantissaAtExponentEven_eq_roundMantissaToLeadingBitEven
        d.significand fmt.fracWidth d.exponent)
  have hmaximumRound :
      nearestEven (maximumMantissa : ℝ) = Int.ofNat maximumMantissa := by
    change nearestEven ((Int.ofNat maximumMantissa : Int) : ℝ) =
      Int.ofNat maximumMantissa
    exact ValidRnd.id (Int.ofNat maximumMantissa)
  rw [hscaledEq, hmaximumRound] at hround
  have hnat :
      roundMantissaToLeadingBitEven d.significand fmt.fracWidth ≤ maximumMantissa := by
    exact Int.ofNat_le.mp hround
  dsimp only [maximumMantissa] at hnat
  have htopPos : 0 < pow2 (fmt.fracWidth + 1) := pow2_pos _
  omega

/-- Both signed zeros of a conventional IEEE format are finite. -/
private theorem isFinite_signedZero_ieee (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (negative : Bool) :
    isFinite (if negative then negZero fmt else posZero fmt) = true := by
  cases negative
  · exact isFinite_posZero fmt
  · exact isFinite_negZero fmt (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt)

/--
Nearest-even rounding cannot overflow when the exact dyadic magnitude is at most the largest
finite value of the destination format.
-/
theorem isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (d : Numerics.Dyadic)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    isFinite (roundDyadic fmt d) = true := by
  rw [roundDyadic_eq_roundDyadicImpl]
  simp only [roundDyadicImpl, hfmt, ite_true]
  by_cases hm : d.significand = 0
  · rw [ieeeRoundDyadicImpl]
    simp only [beq_iff_eq, hm, ite_true]
    exact isFinite_signedZero_ieee fmt hfmt d.negative
  · let k : Int := Int.ofNat d.significand.log2 + d.exponent
    have hkmax :
        k ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) :=
      leadingExponent_le_maxNormal fmt hfmt d hm hbound
    by_cases hsub :
        k < FloatFormat.ieeeMinNormalExponent fmt
    · have hsub' :
          (d.significand.log2 : Int) + d.exponent <
            FloatFormat.ieeeMinNormalExponent fmt := by
        simpa [k] using hsub
      rw [ieeeRoundDyadicImpl]
      simp only [beq_iff_eq, hm, ite_false]
      rw [ite_eq_left hsub']
      let fraction :=
        match d.exponent + Int.ofNat (FloatFormat.ieeeSubnormalAlignExp fmt) with
        | .ofNat shift => d.significand <<< shift
        | .negSucc shift => Numerics.roundShiftRightEven d.significand (shift + 1)
      change
        isFinite
            (if fraction = 0 then
              if d.negative then negZero fmt else posZero fmt
            else if fraction = pow2 fmt.fracWidth then
              ofFields fmt d.negative 1 0
            else
              ofFields fmt d.negative 0 fraction) =
          true
      by_cases hzero : fraction = 0
      · rw [ite_eq_left hzero]
        exact isFinite_signedZero_ieee fmt hfmt d.negative
      · rw [ite_eq_right hzero]
        by_cases hminNormal : fraction = pow2 fmt.fracWidth
        · rw [ite_eq_left hminNormal]
          exact isFinite_ofFields_ieee fmt hfmt d.negative 1 0 (by
            have hfour : 4 ≤ 2 ^ fmt.expWidth := by
              simpa using
                Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
                  fmt.expWidth_ge_two
            unfold FloatFormat.expAllOnesNat
            omega)
        · rw [ite_eq_right hminNormal]
          exact isFinite_ofFields_ieee fmt hfmt d.negative 0 _
            fmt.expAllOnesNat_pos
    · have hnormal : FloatFormat.ieeeMinNormalExponent fmt ≤ k :=
        le_of_not_gt hsub
      have hnormal' :
          FloatFormat.ieeeMinNormalExponent fmt ≤
            (d.significand.log2 : Int) + d.exponent := by
        simpa [k] using hnormal
      let rounded :=
        roundMantissaToLeadingBitEven d.significand fmt.fracWidth
      have hraw :
          (if fmt.fracWidth ≤ d.significand.log2 then
              Numerics.roundShiftRightEven d.significand (d.significand.log2 - fmt.fracWidth)
            else
              d.significand <<< (fmt.fracWidth - d.significand.log2)) =
            rounded := by
        rfl
      have himpl :
          ieeeRoundDyadicImpl fmt d =
            let carry := rounded == pow2 (fmt.fracWidth + 1)
            let normalizedExponent := if carry then k + 1 else k
            if normalizedExponent >
                Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) then
              if d.negative then negInf fmt else posInf fmt
            else
              let normalizedMantissa :=
                if carry then pow2 fmt.fracWidth else rounded
              ofFields fmt d.negative
                (Int.toNat (normalizedExponent + Int.ofNat fmt.bias))
                (normalizedMantissa - pow2 fmt.fracWidth) := by
        unfold ieeeRoundDyadicImpl
        simp only [beq_iff_eq, hm, ite_false]
        rw [ite_eq_right (not_lt_of_ge hnormal'), hraw]
        rfl
      rw [himpl]
      simp only [beq_iff_eq]
      by_cases hcarry : rounded = pow2 (fmt.fracWidth + 1)
      · have hklt :
            k < Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
          apply lt_of_le_of_ne hkmax
          intro hEq
          have hroundedLt :=
            roundMantissaToLeadingBitEven_lt_top_of_bound_at_max
              fmt hfmt d hEq hbound
          exact (ne_of_lt hroundedLt) hcarry
        have hmaxCarry :
            k + 1 ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
          omega
        rw [ite_eq_left hcarry, ite_eq_right (not_lt_of_ge hmaxCarry)]
        exact isFinite_ofFields_ieee fmt hfmt d.negative _ _
          (encodedExponent_lt_expAllOnesNat_ieee fmt (k + 1)
            (by omega) hmaxCarry)
      · rw [ite_eq_right hcarry, ite_eq_right (not_lt_of_ge hkmax)]
        exact isFinite_ofFields_ieee fmt hfmt d.negative _ _
          (encodedExponent_lt_expAllOnesNat_ieee fmt k hnormal hkmax)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
