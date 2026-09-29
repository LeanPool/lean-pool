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

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Fields.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Packing.Finite
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.RealSemantics
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.ModelRounding.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.NearestEven
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Calculation.Round
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Theorems
import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Rounding.Generic
import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Rounding.Order

/-!
# Correctness of nearest-even real rounding

For conventional IEEE descriptors, `Model.roundDyadic` delegates normalization to Lean's generic
logical float model. This module relates that executable result to the independent Flocq-style
rounded-real semantics in `FloatLib.Floats.Formats.Flocq.FloatRep`. Exponent and fraction widths
remain symbolic. The grid membership and preservation results also cover custom biases and
encoding policies; the executable rounding refinement requires `fmt.isIEEE = true`.

The rounded-real model has gradual underflow but no infinities. Consequently refinement theorems
carry an explicit hypothesis that the executable result is finite; an overflowing IEEE result
cannot equal a real-valued rounding function.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019, Section 4.3.1.
- S. Boldo and G. Melquiond, "Flocq: A Unified Library for Proving Floating-Point Algorithms
  in Coq," ARITH 2011. https://doi.org/10.1109/ARITH.2011.40
- Lean 4, `Init.Data.Float.Model.Unpacked.Round`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

/-- Precision and gradual-underflow grid using the descriptor’s declared exponent bias. -/
def fexpOf (fmt : FloatFormat) : ℤ → ℤ :=
  fltExp fmt.minSubnormalExponent (fmt.fracWidth + 1)

instance (fmt : FloatFormat) : ValidExp (fexpOf fmt) :=
  fltValidExp (emin := fmt.minSubnormalExponent)
    (prec := fmt.fracWidth + 1) (by positivity)

/--
Nearest-even rounding with the descriptor's precision, bias, and gradual underflow.

The real grid has no upper exponent bound. Overflow and exceptional encodings belong to the
executable operation; its equality to `roundAt` needs the corresponding refinement hypotheses.
-/
noncomputable abbrev roundAt (fmt : FloatFormat) (x : ℝ) : ℝ :=
  round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) nearestEven x

/-- Nearest-even rounding on a binary format fixes zero. -/
theorem roundAt_zero (fmt : FloatFormat) : roundAt fmt 0 = 0 := by
  exact round_preserves_generic nearestEven 0 generic_format_zero

/-- Nearest-even rounding on a binary format commutes with negation. -/
@[simp] theorem roundAt_neg (fmt : FloatFormat) (x : ℝ) :
    roundAt fmt (-x) = -roundAt fmt x := by
  change
    round (β := Numerics.binaryRadix) (fexp := fexpOf fmt)
        nearestEven (-x) =
      -round (β := Numerics.binaryRadix) (fexp := fexpOf fmt)
        nearestEven x
  rw [round_neg]
  have hrnd : negRound nearestEven = nearestEven := by
    funext value
    simp [negRound, nearestEven_neg]
  rw [hrnd]

/-- Nearest-even rounding is monotone on the exact real input. -/
theorem roundAt_mono (fmt : FloatFormat) {x y : ℝ} (hxy : x ≤ y) :
    roundAt fmt x ≤ roundAt fmt y := by
  exact round_mono nearestEven hxy

/--
Every finite decoded word belongs to its descriptor's precision and gradual-underflow grid.
The result includes custom biases, FNUZ, and finite-only encodings.
-/
theorem toReal_genericFormat_of_isFinite {fmt : FloatFormat} (x : Model fmt)
    (hfin : isFinite x = true) :
    genericFormat Numerics.binaryRadix (fexpOf fmt) (toReal x) := by
  have hdecode := toDyadicOption_ofFields_of_isFinite fmt (signBit x) (expField x) (fracField x)
    (by simpa [← pow2_eq_two_pow] using expField_lt_pow2 x)
    (by simpa [← pow2_eq_two_pow] using fracField_lt_pow2 x)
    (by simpa only [ofFields_signBit_expField_fracField] using hfin)
  rw [ofFields_signBit_expField_fracField] at hdecode
  have hprec : (0 : ℤ) < fmt.fracWidth + 1 := by positivity
  apply (generic_format_FLT_iff fmt.minSubnormalExponent (fmt.fracWidth + 1) hprec _).2
  have hmin : fmt.minSubnormalExponent ≤ 0 := by
    have := fmt.exponentBias_pos
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  have hfrac := fracField_lt_pow2 x
  by_cases he : expField x = 0
  · by_cases hf : fracField x = 0
    · simp only [he, hf, ite_true] at hdecode
      refine ⟨hprec, ⟨0, 0⟩, ?_, by simp [Numerics.binaryRadix], hmin⟩
      simp [toReal_eq, hdecode, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
        Flocq.toReal]
    · simp only [he, hf, ite_true, ite_false] at hdecode
      refine ⟨hprec, ⟨if signBit x then -(fracField x : ℤ) else fracField x,
        fmt.minSubnormalExponent⟩, ?_, ?_, le_rfl⟩
      · cases hs : signBit x <;>
          simp [toReal_eq, hdecode, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
            Flocq.toReal, hs, bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
      · have hbound : fracField x < 2 ^ (fmt.fracWidth + 1) :=
          hfrac.trans (Nat.pow_lt_pow_right (by decide) (by omega))
        cases hs : signBit x <;> simpa [Numerics.binaryRadix, hs] using hbound
  · simp only [he, ite_false] at hdecode
    let m := pow2 fmt.fracWidth + fracField x
    refine ⟨hprec, ⟨if signBit x then -(m : ℤ) else m,
      (expField x : ℤ) - fmt.exponentBias - fmt.fracWidth⟩, ?_, ?_, ?_⟩
    · cases hs : signBit x <;>
        simp [toReal_eq, hdecode, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
          Flocq.toReal, hs, m, bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
    · have hbound : m < 2 ^ (fmt.fracWidth + 1) := by
        simp only [m, pow2_eq_two_pow, pow_succ]
        omega
      cases hs : signBit x <;> simpa [Numerics.binaryRadix, hs] using hbound
    · simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast]
      omega

/-- Rounding a finite decoded value back to its own format is an exact identity. -/
@[simp] theorem roundAt_toReal_eq {fmt : FloatFormat} (x : Model fmt)
    (hfin : isFinite x = true) :
    roundAt fmt (toReal x) = toReal x := by
  exact round_preserves_generic nearestEven (toReal x)
    (toReal_genericFormat_of_isFinite x hfin)

namespace Dyadic

/-- The absolute value of a dyadic ignores its stored sign bit. -/
theorem abs_toReal (d : Numerics.Dyadic) :
    |d.toReal| = (d.significand : ℝ) * bpow Numerics.binaryRadix d.exponent := by
  have hnonneg : 0 ≤ (d.significand : ℝ) * (2 : ℝ) ^ d.exponent :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg (by norm_num) _)
  cases hs : d.negative <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hs, hnonneg,
      abs_of_nonneg, bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/-- A nonzero dyadic has the leading exponent predicted by its integer mantissa. -/
theorem magnitude_toReal (d : Numerics.Dyadic) (hm : d.significand ≠ 0) :
    magnitude Numerics.binaryRadix d.toReal =
      Int.ofNat d.significand.log2 + d.exponent + 1 := by
  have hmpos : (0 : ℝ) < d.significand := by exact_mod_cast Nat.pos_of_ne_zero hm
  calc
    magnitude Numerics.binaryRadix d.toReal =
        magnitude Numerics.binaryRadix |d.toReal| := by simp [magnitude]
    _ = magnitude Numerics.binaryRadix (d.significand : ℝ) + d.exponent := by
      rw [abs_toReal, magnitude_mul_bpow _ _ _ hmpos.ne']
    _ = Int.ofNat d.significand.log2 + d.exponent + 1 := by
      rw [magnitude_eq_int_log_add_one _ _ hmpos.ne', abs_of_pos hmpos,
        Int.log_natCast]
      simp [Numerics.binaryRadix, Nat.log2_eq_log_two]
      omega

end Dyadic

/-- Lean's model and the rounded-real format choose the same exponent for a nonzero dyadic. -/
theorem cexp_toReal_eq_targetExponent (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hfmt : fmt.isIEEE = true) (hm : d.significand ≠ 0) :
    cexp Numerics.binaryRadix (fexpOf fmt) d.toReal =
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent d.significand d.exponent) := by
  rw [cexp, Dyadic.magnitude_toReal d hm]
  simp [fexpOf, fltExp, Float.Model.Format.targetExponent,
    Float.Model.totalExponent, Float.Model.Format.mantissaBits,
    Float.Model.Format.minExponent, FloatFormat.toModel,
    FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt,
    FloatFormat.ieeeMinSubnormalExponent, FloatFormat.bias]
  congr 1 <;> omega

/-- The canonical scaled mantissa of a dyadic is its signed magnitude at the target exponent. -/
theorem scaledMantissa_toReal (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hfmt : fmt.isIEEE = true) (hm : d.significand ≠ 0) :
    scaledMantissa Numerics.binaryRadix (fexpOf fmt) d.toReal =
      (if d.negative then (-1 : ℝ) else 1) * (d.significand : ℝ) *
        bpow Numerics.binaryRadix
          (d.exponent - (FloatFormat.toModel fmt).targetExponent
            (Float.Model.totalExponent d.significand d.exponent)) := by
  rw [scaledMantissa, cexp_toReal_eq_targetExponent fmt d hfmt hm]
  have hpow := bpow.add_exp Numerics.binaryRadix d.exponent
    (-(FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent d.significand d.exponent))
  rw [show d.exponent - (FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent d.significand d.exponent) =
      d.exponent + -(FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent d.significand d.exponent) by ring]
  rw [hpow]
  cases hs : d.negative <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hs,
      bpow, Numerics.binaryRadix, Numerics.Radix.toReal] <;>
    ring

/-- Nearest-even rounding of a nonnegative dyadic agrees with executable shift-and-round. -/
theorem nearestEven_scaledMagnitude (mantissa : Nat) (exponent targetExponent : Int) :
    nearestEven
        ((mantissa : ℝ) * bpow Numerics.binaryRadix (exponent - targetExponent)) =
      Int.ofNat (roundMantissaAtExponentEven mantissa exponent targetExponent) := by
  by_cases hle : exponent ≤ targetExponent
  · let shift := (targetExponent - exponent).toNat
    have hshiftInt : (shift : Int) = targetExponent - exponent := by
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hle)
    have hpow2 : (pow2 shift : ℝ) = (2 : ℝ) ^ shift := by
      simp [pow2, Nat.shiftLeft_eq]
    have hvalue :
        (mantissa : ℝ) * bpow Numerics.binaryRadix (exponent - targetExponent) =
          (mantissa : ℝ) / (pow2 shift : ℝ) := by
      rw [show exponent - targetExponent = -(shift : Int) by omega]
      rw [div_eq_mul_inv, hpow2]
      simp [bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
    rw [hvalue]
    simpa [roundMantissaAtExponentEven, hle, shift] using
      nearestEven_div_pow2_eq_roundShiftRightEven mantissa shift
  · let shift := (exponent - targetExponent).toNat
    have hshiftInt : (shift : Int) = exponent - targetExponent := by
      exact Int.toNat_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))
    have hvalue :
        (mantissa : ℝ) * bpow Numerics.binaryRadix (exponent - targetExponent) =
          (Nat.shiftLeft mantissa shift : Nat) := by
      rw [← hshiftInt]
      simp [bpow, Numerics.binaryRadix, Numerics.Radix.toReal, Nat.shiftLeft_eq]
    rw [hvalue]
    have hid :
        nearestEven ((Nat.shiftLeft mantissa shift : Nat) : ℝ) =
          Int.ofNat (Nat.shiftLeft mantissa shift) := by
      change nearestEven
          ((Int.ofNat (Nat.shiftLeft mantissa shift) : Int) : ℝ) =
        Int.ofNat (Nat.shiftLeft mantissa shift)
      exact ValidRnd.id (rnd := nearestEven)
        (Int.ofNat (Nat.shiftLeft mantissa shift))
    rw [hid]
    simp [roundMantissaAtExponentEven, hle, shift]

/-- Nearest-even rounding commutes with the sign stored in a dyadic value. -/
theorem nearestEven_scaledDyadic (sign : Bool) (mantissa : Nat)
    (exponent targetExponent : Int) :
    nearestEven
        ((if sign then (-1 : ℝ) else 1) * (mantissa : ℝ) *
          bpow Numerics.binaryRadix (exponent - targetExponent)) =
      if sign then
        -Int.ofNat (roundMantissaAtExponentEven mantissa exponent targetExponent)
      else
        Int.ofNat (roundMantissaAtExponentEven mantissa exponent targetExponent) := by
  cases sign <;>
    simp [nearestEven_scaledMagnitude,
      nearestEven_neg]

/-- The executable natural power of two has the same real value as the binary radix power. -/
theorem natCast_pow2_eq_bpow (exponent : Nat) :
    (pow2 exponent : ℝ) = bpow Numerics.binaryRadix exponent := by
  simp [pow2_eq_two_pow, bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/--
Rounded-real semantics of a nonzero dyadic at a conventional IEEE descriptor.

The integer on the right is computed entirely by shifts and nearest-even rounding. The exponent is
chosen by Lean's generic logical float model and independently characterized by `fexpOf`.
-/
theorem roundAt_dyadic_eq (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hfmt : fmt.isIEEE = true) (hm : d.significand ≠ 0) :
    let target := (FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent d.significand d.exponent)
    let rounded := roundMantissaAtExponentEven d.significand d.exponent target
    roundAt fmt d.toReal =
      ((if d.negative then -Int.ofNat rounded else Int.ofNat rounded) : Int) *
        bpow Numerics.binaryRadix target := by
  dsimp only
  let target := (FloatFormat.toModel fmt).targetExponent
    (Float.Model.totalExponent d.significand d.exponent)
  let rounded := roundMantissaAtExponentEven d.significand d.exponent target
  have hscaled :
      nearestEven (scaledMantissa Numerics.binaryRadix (fexpOf fmt) d.toReal) =
        if d.negative then -Int.ofNat rounded else Int.ofNat rounded := by
    rw [scaledMantissa_toReal fmt d hfmt hm]
    exact nearestEven_scaledDyadic d.negative d.significand d.exponent target
  calc
    roundAt fmt d.toReal =
        FloatLib.Floats.Formats.Flocq.toReal (β := Numerics.binaryRadix) {
          mantissa := if d.negative then -Int.ofNat rounded else Int.ofNat rounded
          exponent := cexp Numerics.binaryRadix (fexpOf fmt) d.toReal } :=
      round_eq_toReal_of_scaled_round_eq
        nearestEven d.toReal _ hscaled
    _ = ((if d.negative then -Int.ofNat rounded else Int.ofNat rounded) : Int) *
          bpow Numerics.binaryRadix target := by
      rw [cexp_toReal_eq_targetExponent fmt d hfmt hm]
      rfl

/--
Real value of a finished rounded mantissa on the subnormal grid.

The mantissa may be zero, in which case the packed value is a signed zero, or reach
`2 ^ fracWidth`, in which case it is the least normal value; both have the stated real value.
-/
theorem toReal_ofModel_finishRoundedMantissa_minSubnormal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Float.Model.UnpackedFloat.Sign)
      (rounded : Nat)
    (hle : rounded ≤ pow2 fmt.fracWidth) :
    toReal (ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) sign
          (rounded, FloatFormat.ieeeMinSubnormalExponent fmt))) =
      (if modelSignBit sign then (-1 : ℝ) else 1) *
        ((rounded : ℝ) *
          bpow Numerics.binaryRadix (FloatFormat.ieeeMinSubnormalExponent fmt)) := by
  by_cases hzero : rounded = 0
  · rw [hzero, finishRoundedMantissa_zero, toReal_ofModel_zero fmt hfmt]
    simp
  · rw [finishRoundedMantissa_at_minSubnormal fmt sign rounded hzero hle,
      toReal_ofModel_finite_at_minSubnormal fmt hfmt sign rounded hzero
        (by simpa [pow2_eq_two_pow] using hle)]
    ring

/--
Real value of a finished normalized rounded mantissa with leading bit at unbiased exponent `k`.

The mantissa lies in `[2 ^ fracWidth, 2 ^ (fracWidth + 1)]`; the upper endpoint is the carry that
`finishRoundedMantissa` renormalizes to exponent `k + 1`. The finiteness hypothesis excludes IEEE
overflow, which has no value in `ℝ`.
-/
theorem toReal_ofModel_finishRoundedMantissa_normal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Float.Model.UnpackedFloat.Sign)
      (rounded : Nat) (k : Int)
    (hlow : pow2 fmt.fracWidth ≤ rounded) (hhigh : rounded ≤ pow2 (fmt.fracWidth + 1))
    (hk : FloatFormat.ieeeMinNormalExponent fmt ≤ k)
    (hfin : isFinite (ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) sign
          (rounded, k - fmt.fracWidth))) = true) :
    toReal (ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) sign (rounded, k - fmt.fracWidth))) =
      (if modelSignBit sign then (-1 : ℝ) else 1) *
        ((rounded : ℝ) * bpow Numerics.binaryRadix (k - fmt.fracWidth)) := by
  have hbiased : ∀ e : Int, FloatFormat.ieeeMinNormalExponent fmt ≤ e →
      0 < e - fmt.fracWidth + (FloatFormat.toModel fmt).exponentBias +
        (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit := by
    intro e he
    change 0 < e - fmt.fracWidth + fmt.bias + fmt.fracWidth
    unfold FloatFormat.ieeeMinNormalExponent at he
    simp only [Int.ofNat_eq_natCast] at he ⊢
    omega
  by_cases hcarry : rounded = pow2 (fmt.fracWidth + 1)
  · rw [hcarry, finishRoundedMantissa_normalized_carry fmt sign k hk] at hfin ⊢
    have hpow : pow2 fmt.fracWidth ≠ 0 := by simp [pow2_eq_two_pow]
    rw [toReal_ofModel_finite_normal fmt hfmt sign (pow2 fmt.fracWidth) (k + 1 - fmt.fracWidth)
      hpow
      (by
        change (pow2 fmt.fracWidth).log2 + 1 = 1 + fmt.fracWidth
        simp [pow2_eq_two_pow, Nat.add_comm])
      (hbiased (k + 1) (by omega)).le (hbiased (k + 1) (by omega))
      (noOverflow_of_isFinite_ofModel_finite fmt hfmt sign (pow2 fmt.fracWidth)
        (k + 1 - fmt.fracWidth) hpow hfin)]
    rw [natCast_pow2_eq_bpow, natCast_pow2_eq_bpow, mul_assoc, ← bpow.add_exp, ← bpow.add_exp]
    congr 2
    push_cast
    ring
  · have hhighLt : rounded < pow2 (fmt.fracWidth + 1) := lt_of_le_of_ne hhigh hcarry
    have hne : rounded ≠ 0 :=
      Nat.ne_of_gt ((show 0 < pow2 fmt.fracWidth by simp [pow2_eq_two_pow]).trans_le hlow)
    rw [finishRoundedMantissa_normalized fmt sign rounded k hlow hhighLt hk] at hfin ⊢
    rw [toReal_ofModel_finite_normal fmt hfmt sign rounded (k - fmt.fracWidth) hne
      (by
        change rounded.log2 + 1 = 1 + fmt.fracWidth
        rw [log2_eq_fracWidth_of_normalized fmt rounded hlow hhighLt]
        omega)
      (hbiased k hk).le (hbiased k hk)
      (noOverflow_of_isFinite_ofModel_finite fmt hfmt sign rounded (k - fmt.fracWidth) hne hfin)]
    ring

/--
Executable dyadic rounding refines the rounded-real semantics for conventional IEEE descriptors.

The finiteness hypothesis excludes the one case that has no value in `ℝ`: IEEE overflow to
infinity. Both the IEEE-descriptor condition and result finiteness are explicit hypotheses; custom
widths are allowed when they satisfy that descriptor condition.
-/
theorem toReal_roundDyadic_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (d : Numerics.Dyadic)
    (hfin : isFinite (roundDyadic fmt d) = true) :
    toReal (roundDyadic fmt d) = roundAt fmt d.toReal := by
  simp only [roundDyadic, hfmt, ite_true] at hfin ⊢
  by_cases hm : d.significand = 0
  · have hdzero : d.toReal = 0 := by
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hm]
    rw [hdzero, roundAt_zero]
    unfold ieeeRoundDyadic
    rw [hm, round_exact_zero, toReal_ofModel_zero fmt hfmt]
  · rw [roundAt_dyadic_eq fmt d hfmt hm]
    unfold ieeeRoundDyadic at hfin ⊢
    rw [round_exact_eq_finishRoundedMantissa _ _ _ _ hm] at hfin ⊢
    by_cases hsub : (d.significand.log2 : Int) + d.exponent < FloatFormat.ieeeMinNormalExponent fmt
    · rw [targetExponent_eq_minSubnormal_of_lt_minNormal fmt d.significand d.exponent hsub,
        toReal_ofModel_finishRoundedMantissa_minSubnormal fmt hfmt _ _
          (roundMantissaAtExponentEven_minSubnormal_le_pow2 fmt d.significand d.exponent hsub)]
      cases d.negative <;> simp [modelSign, modelSignBit]
    · have hnormal := le_of_not_gt hsub
      rw [targetExponent_eq_normal fmt d.significand d.exponent hnormal,
        roundMantissaAtExponentEven_eq_roundMantissaToLeadingBitEven] at hfin ⊢
      rw [toReal_ofModel_finishRoundedMantissa_normal fmt hfmt _ _ _
        (pow2_le_roundMantissaToLeadingBitEven d.significand fmt.fracWidth hm)
        (roundMantissaToLeadingBitEven_le_pow2_succ d.significand fmt.fracWidth) hnormal hfin]
      cases d.negative <;> simp [modelSign, modelSignBit]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
