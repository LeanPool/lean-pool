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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.ModelRounding.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Runtime
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Packing.Special
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Packing.Bounds

/-!
# Correctness of direct generic dyadic rounding

The executable integer implementation in `RoundDyadicImpl.Runtime` is extensionally equal to the
logical `Float.Model.UnpackedFloat.round` specification used by `ieeeRoundDyadic`. The
`@[csimp]` theorems install the direct implementation in compiled code while preserving the
model-facing definitions in the type theory.

The IEEE proof covers signed zero, subnormal rounding, the minimum-normal transition,
normalization carry, and overflow at arbitrary field widths. `roundDyadicGeneral_eq_roundDyadic`
then relates the descriptor-aware algorithm to the public specification, including non-IEEE
encoding policies.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

private theorem ofModel_zero_eq_signedZero (fmt : FloatFormat) (negative : Bool) :
    ofModel fmt (.zero (modelSign negative)) =
      if negative then negZero fmt else posZero fmt := by
  cases negative
  · exact (posZero_eq_ofModel_zero fmt).symm
  · exact (negZero_eq_ofModel_zero fmt).symm

private theorem ofModel_finite_subnormal_eq_ofFields
    (fmt : FloatFormat) (negative : Bool) (mantissa : Nat)
    (hm : mantissa ≠ 0) (hfit : mantissa < pow2 fmt.fracWidth) :
    ofModel fmt
        (.finite (modelSign negative) mantissa (FloatFormat.ieeeMinSubnormalExponent fmt)
          (Nat.pos_of_ne_zero hm)) =
      ofFields fmt negative 0 mantissa := by
  have hlog : mantissa.log2 + 1 < fmt.fracWidth + 1 := by
    apply Nat.add_lt_add_right
    apply (Nat.log2_lt hm).2
    simpa [pow2_eq_two_pow] using hfit
  have hnotNormal :
      ¬mantissa.log2 + 1 = (FloatFormat.toModel fmt).mantissaBits := by
    simp only [FloatFormat.toModel, Float.Model.Format.mantissaBits]
    omega
  have hnotOverflow :
      ¬2 ^ (FloatFormat.toModel fmt).exponentBits ≤
        (FloatFormat.ieeeMinSubnormalExponent fmt +
            (FloatFormat.toModel fmt).exponentBias +
            (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1 := by
    change ¬2 ^ fmt.expWidth ≤
      (FloatFormat.ieeeMinSubnormalExponent fmt + fmt.bias + fmt.fracWidth).toNat + 1
    have hfour : 4 ≤ 2 ^ fmt.expWidth := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
        fmt.expWidth_ge_two
    simp only [FloatFormat.ieeeMinSubnormalExponent, Int.ofNat_eq_natCast]
    omega
  unfold ofModel ofModelBits Float.Model.UnpackedFloat.pack
  simp only [hnotOverflow, ite_false, hnotNormal]
  rw [← ofModelBits_toModelBits (ofFields fmt negative 0 mantissa)]
  rw [toModelBits_ofFields]
  rfl

private theorem ofModel_finite_normal_eq_ofFields_raw
    (fmt : FloatFormat) (negative : Bool) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≠ 0)
    (hbits : mantissa.log2 + 1 = (FloatFormat.toModel fmt).mantissaBits)
    (hnoOverflow :
      ¬2 ^ (FloatFormat.toModel fmt).exponentBits ≤
        (exponent + (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1) :
    ofModel fmt
        (.finite (modelSign negative) mantissa exponent (Nat.pos_of_ne_zero hm)) =
      ofFields fmt negative
        (exponent + (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat
        mantissa := by
  unfold ofModel ofModelBits Float.Model.UnpackedFloat.pack
  simp only [hnoOverflow, ite_false, hbits, ite_true]
  rw [← ofModelBits_toModelBits
    (ofFields fmt negative
      (exponent + (FloatFormat.toModel fmt).exponentBias +
        (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat
      mantissa)]
  rw [toModelBits_ofFields]
  rfl

private theorem ofModel_finite_overflow_eq_signedInfinity
    (fmt : FloatFormat) (negative : Bool) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≠ 0)
    (hoverflow :
      2 ^ (FloatFormat.toModel fmt).exponentBits ≤
        (exponent + (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1) :
    ofModel fmt
        (.finite (modelSign negative) mantissa exponent (Nat.pos_of_ne_zero hm)) =
      if negative then negInf fmt else posInf fmt := by
  have hpack :
      ofModel fmt
          (.finite (modelSign negative) mantissa exponent (Nat.pos_of_ne_zero hm)) =
        ofModel fmt (.infinity (modelSign negative)) := by
    unfold ofModel ofModelBits Float.Model.UnpackedFloat.pack
    simp only [hoverflow, ite_true]
  rw [hpack]
  cases negative
  · exact (posInf_eq_ofModel_infinity fmt).symm
  · exact (negInf_eq_ofModel_infinity fmt).symm

private theorem ofModel_finite_minNormal_eq_ofFields
    (fmt : FloatFormat) (negative : Bool) :
    ofModel fmt
        (.finite (modelSign negative) (pow2 fmt.fracWidth)
          (FloatFormat.ieeeMinSubnormalExponent fmt)
          (Nat.pos_of_ne_zero (by simp [pow2_eq_two_pow]))) =
      ofFields fmt negative 1 0 := by
  have hbits :
      (pow2 fmt.fracWidth).log2 + 1 =
        (FloatFormat.toModel fmt).mantissaBits := by
    simp [pow2_eq_two_pow, FloatFormat.toModel,
      Float.Model.Format.mantissaBits, Nat.add_comm]
  have hnoOverflow :
      ¬2 ^ (FloatFormat.toModel fmt).exponentBits ≤
        (FloatFormat.ieeeMinSubnormalExponent fmt +
          (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1 := by
    have hfour : 4 ≤ 2 ^ fmt.expWidth := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
        fmt.expWidth_ge_two
    change
      ¬2 ^ fmt.expWidth ≤
        (FloatFormat.ieeeMinSubnormalExponent fmt + fmt.bias + fmt.fracWidth).toNat + 1
    unfold FloatFormat.ieeeMinSubnormalExponent
    simp only [Int.ofNat_eq_natCast]
    omega
  rw [ofModel_finite_normal_eq_ofFields_raw fmt negative
    (pow2 fmt.fracWidth) (FloatFormat.ieeeMinSubnormalExponent fmt)
    (by simp [pow2_eq_two_pow]) hbits hnoOverflow]
  have hexponent :
      (FloatFormat.ieeeMinSubnormalExponent fmt +
        (FloatFormat.toModel fmt).exponentBias +
        (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat = 1 := by
    change
      (FloatFormat.ieeeMinSubnormalExponent fmt + fmt.bias + fmt.fracWidth).toNat = 1
    unfold FloatFormat.ieeeMinSubnormalExponent
    simp only [Int.ofNat_eq_natCast]
    omega
  rw [hexponent]
  have hfraction :
      BitVec.ofNat fmt.fracWidth (pow2 fmt.fracWidth) = 0#fmt.fracWidth := by
    apply BitVec.eq_of_toNat_eq
    simp [pow2_eq_two_pow]
  rw [← ofModelBits_toModelBits
    (ofFields fmt negative 1 (pow2 fmt.fracWidth))]
  rw [← ofModelBits_toModelBits (ofFields fmt negative 1 0)]
  rw [toModelBits_ofFields, toModelBits_ofFields]
  rw [hfraction]

private theorem ieeeSubnormalAlignExp_eq_neg_minSubnormalExp (fmt : FloatFormat) :
    Int.ofNat (FloatFormat.ieeeSubnormalAlignExp fmt) =
      -FloatFormat.ieeeMinSubnormalExponent fmt := by
  unfold FloatFormat.ieeeSubnormalAlignExp FloatFormat.ieeeMinSubnormalExponent
  have hbias : 0 < fmt.bias := by
    unfold FloatFormat.bias
    have hwidth := fmt.expWidth_ge_two
    have hpow : 2 ≤ 2 ^ (fmt.expWidth - 1) := by
      exact Nat.one_lt_two_pow (by omega)
    omega
  have hsum : 1 ≤ fmt.bias + fmt.fracWidth := by omega
  have hnat :
      FloatFormat.ieeeSubnormalAlignExp fmt + 1 = fmt.bias + fmt.fracWidth :=
    Nat.sub_add_cancel hsum
  have hcast :
      ((FloatFormat.ieeeSubnormalAlignExp fmt : Nat) : Int) + 1 =
        ((fmt.bias + fmt.fracWidth : Nat) : Int) := by
    exact_mod_cast hnat
  simp only [Int.ofNat_eq_natCast] at ⊢
  omega

private theorem roundMantissaAtExponentEven_minSubnormal_eq_match
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) :
    roundMantissaAtExponentEven mantissa exponent
        (FloatFormat.ieeeMinSubnormalExponent fmt) =
      match exponent + Int.ofNat (FloatFormat.ieeeSubnormalAlignExp fmt) with
      | .ofNat shift => mantissa <<< shift
      | .negSucc shift => Numerics.roundShiftRightEven mantissa (shift + 1) := by
  rw [ieeeSubnormalAlignExp_eq_neg_minSubnormalExp]
  have hsub :
      exponent + -FloatFormat.ieeeMinSubnormalExponent fmt =
        exponent - FloatFormat.ieeeMinSubnormalExponent fmt := by omega
  rw [hsub]
  generalize hdifference :
    exponent - FloatFormat.ieeeMinSubnormalExponent fmt = difference
  cases difference with
  | ofNat shift =>
      simp only [Int.ofNat_eq_natCast] at hdifference
      by_cases hshift : shift = 0
      · subst shift
        simp only [Nat.cast_zero] at hdifference
        have hexponent :
            exponent = FloatFormat.ieeeMinSubnormalExponent fmt := by omega
        simp [roundMantissaAtExponentEven, Numerics.roundShiftRightEven_def, hexponent]
      · have htarget :
            FloatFormat.ieeeMinSubnormalExponent fmt < exponent := by omega
        have hshiftNat :
            (exponent - FloatFormat.ieeeMinSubnormalExponent fmt).toNat = shift := by
          rw [hdifference]
          rfl
        simp [roundMantissaAtExponentEven, not_le_of_gt htarget, hshiftNat]
  | negSucc shift =>
      have hexponent :
          exponent < FloatFormat.ieeeMinSubnormalExponent fmt := by omega
      have hshiftNat :
          (FloatFormat.ieeeMinSubnormalExponent fmt - exponent).toNat = shift + 1 := by
        omega
      simp [roundMantissaAtExponentEven, hexponent.le, hshiftNat]

private theorem modelOverflow_iff_gt_maxNormal
    (fmt : FloatFormat) (exponent : Int)
    (hmin : FloatFormat.ieeeMinNormalExponent fmt ≤ exponent) :
    (2 ^ (FloatFormat.toModel fmt).exponentBits ≤
        (exponent - fmt.fracWidth +
          (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1) ↔
      Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) < exponent := by
  change
    (2 ^ fmt.expWidth ≤
        (exponent - fmt.fracWidth + fmt.bias + fmt.fracWidth).toNat + 1) ↔
      Int.ofNat fmt.bias < exponent
  have hbiased : 0 ≤ exponent + Int.ofNat fmt.bias := by
    unfold FloatFormat.ieeeMinNormalExponent at hmin
    omega
  have hexponent :
      exponent - Int.ofNat fmt.fracWidth + Int.ofNat fmt.bias +
          Int.ofNat fmt.fracWidth =
        exponent + Int.ofNat fmt.bias := by omega
  simp only [Int.ofNat_eq_natCast] at hbiased hexponent ⊢
  rw [hexponent, FloatFormat.two_pow_expWidth_eq_two_mul_bias_add_two]
  let encoded := (exponent + (fmt.bias : Int)).toNat
  have hencoded : (encoded : Int) = exponent + (fmt.bias : Int) :=
    Int.toNat_of_nonneg hbiased
  change 2 * fmt.bias + 2 ≤ encoded + 1 ↔ (fmt.bias : Int) < exponent
  omega

/--
Packing a normalized finite model value agrees with direct field construction.
-/
theorem ofModel_finite_normalized_eq_ofFields
    (fmt : FloatFormat) (negative : Bool) (mantissa : Nat) (exponent : Int)
    (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1))
    (hmin : FloatFormat.ieeeMinNormalExponent fmt ≤ exponent)
    (hmax : exponent ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) :
    ofModel fmt
        (.finite (modelSign negative) mantissa (exponent - fmt.fracWidth)
          (Nat.pos_of_ne_zero
            (Nat.ne_of_gt ((show 0 < pow2 fmt.fracWidth by
              simp [pow2_eq_two_pow]).trans_le hlow)))) =
      ofFields fmt negative
        (Int.toNat (exponent + Int.ofNat fmt.bias))
        (mantissa - pow2 fmt.fracWidth) := by
  have hm : mantissa ≠ 0 :=
    Nat.ne_of_gt ((show 0 < pow2 fmt.fracWidth by
      simp [pow2_eq_two_pow]).trans_le hlow)
  have hbits :
      mantissa.log2 + 1 = (FloatFormat.toModel fmt).mantissaBits := by
    change mantissa.log2 + 1 = 1 + fmt.fracWidth
    rw [log2_eq_fracWidth_of_normalized fmt mantissa hlow hhigh]
    omega
  have hnoOverflow :
      ¬2 ^ (FloatFormat.toModel fmt).exponentBits ≤
        (exponent - fmt.fracWidth +
          (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1 := by
    rw [modelOverflow_iff_gt_maxNormal fmt exponent hmin]
    exact not_lt_of_ge hmax
  rw [ofModel_finite_normal_eq_ofFields_raw fmt negative mantissa
    (exponent - fmt.fracWidth) hm hbits hnoOverflow]
  have hexponent :
      (exponent - fmt.fracWidth +
        (FloatFormat.toModel fmt).exponentBias +
        (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat =
      Int.toNat (exponent + Int.ofNat fmt.bias) := by
    congr 1
    change
      exponent - Int.ofNat fmt.fracWidth + Int.ofNat fmt.bias +
          Int.ofNat fmt.fracWidth =
        exponent + Int.ofNat fmt.bias
    omega
  rw [hexponent]
  have hfraction :
      BitVec.ofNat fmt.fracWidth mantissa =
        BitVec.ofNat fmt.fracWidth (mantissa - pow2 fmt.fracWidth) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have hlow' : 2 ^ fmt.fracWidth ≤ mantissa := by
      simpa [pow2_eq_two_pow] using hlow
    simpa [pow2_eq_two_pow] using Nat.mod_eq_sub_mod hlow'
  rw [← ofModelBits_toModelBits
    (ofFields fmt negative
      (Int.toNat (exponent + Int.ofNat fmt.bias)) mantissa)]
  rw [← ofModelBits_toModelBits
    (ofFields fmt negative
      (Int.toNat (exponent + Int.ofNat fmt.bias))
      (mantissa - pow2 fmt.fracWidth))]
  rw [toModelBits_ofFields, toModelBits_ofFields, hfraction]

private theorem ieeeRoundDyadic_eq_ieeeRoundDyadicImpl_of_subnormal
    (fmt : FloatFormat) (d : Numerics.Dyadic) (hm : d.significand ≠ 0)
    (hsub : (d.significand.log2 : Int) + d.exponent <
      FloatFormat.ieeeMinNormalExponent fmt) :
    ieeeRoundDyadic fmt d = ieeeRoundDyadicImpl fmt d := by
  let rounded :=
    roundMantissaAtExponentEven d.significand d.exponent
      (FloatFormat.ieeeMinSubnormalExponent fmt)
  have htarget :
      (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent d.significand d.exponent) =
        FloatFormat.ieeeMinSubnormalExponent fmt :=
    targetExponent_eq_minSubnormal_of_lt_minNormal fmt d.significand d.exponent hsub
  have hroundedLe : rounded ≤ pow2 fmt.fracWidth := by
    exact roundMantissaAtExponentEven_minSubnormal_le_pow2
      fmt d.significand d.exponent hsub
  have himpl :
      ieeeRoundDyadicImpl fmt d =
        if rounded == 0 then
          if d.negative then negZero fmt else posZero fmt
        else if rounded == pow2 fmt.fracWidth then
          ofFields fmt d.negative 1 0
        else
          ofFields fmt d.negative 0 rounded := by
    have hrounded :
        (match d.exponent + Int.ofNat (FloatFormat.ieeeSubnormalAlignExp fmt) with
          | .ofNat shift => d.significand <<< shift
          | .negSucc shift => Numerics.roundShiftRightEven d.significand (shift + 1)) =
        rounded := by
      dsimp only [rounded]
      exact
        (roundMantissaAtExponentEven_minSubnormal_eq_match
          fmt d.significand d.exponent).symm
    unfold ieeeRoundDyadicImpl
    simp only [beq_iff_eq, hm, ite_false]
    rw [ite_eq_left hsub]
    exact congrArg
      (fun fraction : Nat =>
        if fraction = 0 then
          if d.negative then negZero fmt else posZero fmt
        else if fraction = pow2 fmt.fracWidth then
          ofFields fmt d.negative 1 0
        else
          ofFields fmt d.negative 0 fraction)
      hrounded
  rw [himpl]
  unfold ieeeRoundDyadic
  rw [round_exact_eq_finishRoundedMantissa _ _ _ _ hm, htarget]
  change
    ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) (modelSign d.negative)
          (rounded, FloatFormat.ieeeMinSubnormalExponent fmt)) =
      _
  by_cases hzero : rounded = 0
  · rw [hzero, finishRoundedMantissa_zero,
      ofModel_zero_eq_signedZero]
    simp
  · by_cases hcarry : rounded = pow2 fmt.fracWidth
    · rw [hcarry, finishRoundedMantissa_at_minSubnormal
        fmt (modelSign d.negative) (pow2 fmt.fracWidth)
        (by simp [pow2_eq_two_pow]) le_rfl]
      rw [ofModel_finite_minNormal_eq_ofFields]
      have hpow : pow2 fmt.fracWidth ≠ 0 := by
        simp [pow2_eq_two_pow]
      simp [hpow]
    · have hroundedLt : rounded < pow2 fmt.fracWidth :=
        lt_of_le_of_ne hroundedLe hcarry
      rw [finishRoundedMantissa_at_minSubnormal
        fmt (modelSign d.negative) rounded hzero hroundedLe]
      rw [ofModel_finite_subnormal_eq_ofFields
        fmt d.negative rounded hzero hroundedLt]
      simp [hzero, hcarry]

private theorem ieeeRoundDyadic_eq_ieeeRoundDyadicImpl_of_normal
    (fmt : FloatFormat) (d : Numerics.Dyadic) (hm : d.significand ≠ 0)
    (hnormal : FloatFormat.ieeeMinNormalExponent fmt ≤
      (d.significand.log2 : Int) + d.exponent) :
    ieeeRoundDyadic fmt d = ieeeRoundDyadicImpl fmt d := by
  let exponent : Int := (d.significand.log2 : Int) + d.exponent
  let rounded := roundMantissaToLeadingBitEven d.significand fmt.fracWidth
  have htarget :
      (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent d.significand d.exponent) =
        exponent - fmt.fracWidth := by
    exact targetExponent_eq_normal fmt d.significand d.exponent hnormal
  have hrounded :
      roundMantissaAtExponentEven d.significand d.exponent
          (exponent - fmt.fracWidth) =
        rounded := by
    exact roundMantissaAtExponentEven_eq_roundMantissaToLeadingBitEven
      d.significand fmt.fracWidth d.exponent
  have hlow : pow2 fmt.fracWidth ≤ rounded :=
    pow2_le_roundMantissaToLeadingBitEven d.significand fmt.fracWidth hm
  have hhighLe : rounded ≤ pow2 (fmt.fracWidth + 1) :=
    roundMantissaToLeadingBitEven_le_pow2_succ d.significand fmt.fracWidth
  have himpl :
      ieeeRoundDyadicImpl fmt d =
        let carry := rounded == pow2 (fmt.fracWidth + 1)
        let normalizedExponent := if carry then exponent + 1 else exponent
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
    rw [ite_eq_right (not_lt_of_ge hnormal)]
    rfl
  rw [himpl]
  unfold ieeeRoundDyadic
  rw [round_exact_eq_finishRoundedMantissa _ _ _ _ hm, htarget, hrounded]
  by_cases hcarry : rounded = pow2 (fmt.fracWidth + 1)
  · rw [hcarry, finishRoundedMantissa_normalized_carry
      fmt (modelSign d.negative) exponent hnormal]
    have hminCarry :
        FloatFormat.ieeeMinNormalExponent fmt ≤ exponent + 1 := by
      dsimp only [exponent] at hnormal ⊢
      omega
    by_cases hoverflow :
        Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) < exponent + 1
    · have hmodelOverflow :=
        (modelOverflow_iff_gt_maxNormal fmt (exponent + 1) hminCarry).2
          hoverflow
      rw [ofModel_finite_overflow_eq_signedInfinity
        fmt d.negative (pow2 fmt.fracWidth)
        (exponent + 1 - fmt.fracWidth)
        (by simp [pow2_eq_two_pow]) hmodelOverflow]
      simp only [beq_iff_eq, ite_true]
      rw [ite_eq_left hoverflow]
    · have hmax :
          exponent + 1 ≤
            Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) :=
        le_of_not_gt hoverflow
      rw [ofModel_finite_normalized_eq_ofFields
        fmt d.negative (pow2 fmt.fracWidth) (exponent + 1)
        le_rfl
        (by
          have hp : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
          simp only [pow2_eq_two_pow, pow_succ]
          omega)
        hminCarry hmax]
      simp only [beq_iff_eq, ite_true]
      rw [ite_eq_right (not_lt_of_ge hmax)]
  · have hhigh : rounded < pow2 (fmt.fracWidth + 1) :=
      lt_of_le_of_ne hhighLe hcarry
    have hroundedNe : rounded ≠ 0 :=
      Nat.ne_of_gt ((show 0 < pow2 fmt.fracWidth by
        simp [pow2_eq_two_pow]).trans_le hlow)
    rw [finishRoundedMantissa_normalized
      fmt (modelSign d.negative) rounded exponent
      hlow hhigh hnormal]
    by_cases hoverflow :
        Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) < exponent
    · have hmodelOverflow :=
        (modelOverflow_iff_gt_maxNormal fmt exponent hnormal).2 hoverflow
      rw [ofModel_finite_overflow_eq_signedInfinity
        fmt d.negative rounded (exponent - fmt.fracWidth)
        hroundedNe hmodelOverflow]
      simp only [beq_iff_eq, hcarry, ite_false]
      rw [ite_eq_left hoverflow]
    · have hmax :
          exponent ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) :=
        le_of_not_gt hoverflow
      rw [ofModel_finite_normalized_eq_ofFields
        fmt d.negative rounded exponent hlow hhigh hnormal hmax]
      simp only [beq_iff_eq, hcarry, ite_false]
      rw [ite_eq_right (not_lt_of_ge hmax)]

/--
The direct integer dyadic rounder computes the same result as Lean's format-parameterized logical
float model. The compiler uses this checked equality to replace the logical model at runtime.
-/
@[csimp] theorem ieeeRoundDyadic_eq_ieeeRoundDyadicImpl :
    @ieeeRoundDyadic = @ieeeRoundDyadicImpl := by
  funext fmt d
  by_cases hm : d.significand = 0
  · unfold ieeeRoundDyadic ieeeRoundDyadicImpl
    rw [hm, round_exact_zero, ofModel_zero_eq_signedZero]
    simp
  · by_cases hsub :
      (d.significand.log2 : Int) + d.exponent <
        FloatFormat.ieeeMinNormalExponent fmt
    · exact ieeeRoundDyadic_eq_ieeeRoundDyadicImpl_of_subnormal fmt d hm hsub
    · exact ieeeRoundDyadic_eq_ieeeRoundDyadicImpl_of_normal fmt d hm (le_of_not_gt hsub)

private theorem ieeeRoundDyadicImpl_of_normal
    (fmt : FloatFormat) (d : Numerics.Dyadic) (hm : d.significand ≠ 0)
    (hnormal :
      FloatFormat.ieeeMinNormalExponent fmt ≤ (d.significand.log2 : Int) + d.exponent) :
    ieeeRoundDyadicImpl fmt d =
      let totalExponent := (d.significand.log2 : Int) + d.exponent
      let rounded := roundMantissaToLeadingBitEven d.significand fmt.fracWidth
      let carry := rounded == pow2 (fmt.fracWidth + 1)
      let normalizedExponent := if carry then totalExponent + 1 else totalExponent
      if normalizedExponent > Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) then
        if d.negative then negInf fmt else posInf fmt
      else
        let normalizedMantissa := if carry then pow2 fmt.fracWidth else rounded
        ofFields fmt d.negative
          (Int.toNat (normalizedExponent + Int.ofNat fmt.bias))
          (normalizedMantissa - pow2 fmt.fracWidth) := by
  unfold ieeeRoundDyadicImpl
  simp only [beq_iff_eq, hm, ite_false]
  rw [ite_eq_right (not_lt_of_ge hnormal)]
  rfl

private theorem roundDyadicNormalCase (fmt : FloatFormat) (d : Numerics.Dyadic) (hfmt :
  fmt.isIEEE = true)
  (hmin : fmt.minNormalExponent = fmt.ieeeMinNormalExponent)
  (hmax : fmt.maxNormalExponent = Int.ofNat fmt.ieeeMaxNormalExponent) (hbias : fmt.exponentBias
    = fmt.bias)
  (hm : ¬d.significand = 0) :
  let totalExponent := ↑d.significand.log2 + d.exponent;
  ¬fmt.maxNormalExponent < totalExponent →
    totalExponent ≤ fmt.maxNormalExponent →
      ¬fmt.maxNormalExponent < ↑d.significand.log2 + d.exponent →
        ¬totalExponent < fmt.minNormalExponent →
          fmt.minNormalExponent ≤ totalExponent → roundDyadicGeneral fmt d = ieeeRoundDyadicImpl
            fmt d := by
  intro totalExponent hoverflow htotalMax hoverflow' hsub hnormal
  have hsub' :
      ¬(d.significand.log2 : Int) + d.exponent <
        fmt.minNormalExponent := by
    simpa only [totalExponent] using hsub
  have hnormalIEEE :
      FloatFormat.ieeeMinNormalExponent fmt ≤ totalExponent := by
    rwa [← hmin]
  let rounded :=
    roundMantissaToLeadingBitEven d.significand fmt.fracWidth
  have hroundedHigh :
      rounded ≤ pow2 (fmt.fracWidth + 1) :=
    roundMantissaToLeadingBitEven_le_pow2_succ
      d.significand fmt.fracWidth
  have hgeneral :
      roundDyadicGeneral fmt d =
        let carry := rounded == pow2 (fmt.fracWidth + 1)
        let normalizedExponent :=
          if carry then totalExponent + 1 else totalExponent
        let normalizedMantissa :=
          if carry then pow2 fmt.fracWidth else rounded
        let encodedExponent :=
          Int.toNat
            (normalizedExponent + Int.ofNat fmt.exponentBias)
        let encodedFraction :=
          normalizedMantissa - pow2 fmt.fracWidth
        if normalizedExponent > fmt.maxNormalExponent ||
            encodedExponent > fmt.maxFiniteExpField ||
            (encodedExponent == fmt.maxFiniteExpField &&
              encodedFraction > fmt.maxFiniteFracField) then
          nativeOverflow fmt d.negative
        else
          ofFields fmt d.negative encodedExponent encodedFraction := by
    unfold roundDyadicGeneral
    simp only [beq_iff_eq, hm, ite_false]
    rw [ite_eq_right hoverflow', ite_eq_right hsub']
    simp only [packRoundedNormal, rounded, roundMantissaToLeadingBitEven, totalExponent,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ite_or]
  rw [hgeneral, ieeeRoundDyadicImpl_of_normal fmt d hm hnormalIEEE]
  rw [show roundMantissaToLeadingBitEven d.significand fmt.fracWidth = rounded from rfl,
    show (d.significand.log2 : Int) + d.exponent = totalExponent from rfl]
  simp only [beq_iff_eq]
  by_cases hcarry : rounded = pow2 (fmt.fracWidth + 1)
  · have hnormalizedMin :
        fmt.minNormalExponent ≤ totalExponent + 1 := by
      omega
    have hmantissaHigh :
        pow2 fmt.fracWidth < pow2 (fmt.fracWidth + 1) := by
      simp [pow2_eq_two_pow, pow_succ]
    by_cases hnormalizedOverflow :
        fmt.maxNormalExponent < totalExponent + 1
    · have hnormalizedOverflowIEEE :
          Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) <
            totalExponent + 1 := by
        rwa [← hmax]
      have hnormalizedOverflowBool :
          decide (fmt.maxNormalExponent < totalExponent + 1) = true :=
        decide_eq_true hnormalizedOverflow
      simp only [hcarry, ite_true, hnormalizedOverflowBool,
        Bool.true_or, nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt]
      rw [ite_eq_left hnormalizedOverflowIEEE]
    · have hnormalizedMax :
          totalExponent + 1 ≤ fmt.maxNormalExponent :=
        le_of_not_gt hnormalizedOverflow
      have hguard :=
        Directed.Internal.normalizedGuard_eq_false fmt hfmt
          (pow2 fmt.fracWidth) (totalExponent + 1)
          hmantissaHigh hnormalizedMin hnormalizedMax
      dsimp only at hguard
      have hnormalizedMaxIEEE :
          totalExponent + 1 ≤
            Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
        rwa [← hmax]
      have hnormalizedOverflowBool :
          decide (fmt.maxNormalExponent < totalExponent + 1) = false :=
        decide_eq_false hnormalizedOverflow
      simp only [hcarry, ite_true, hnormalizedOverflowBool,
        Bool.false_or, hguard, Bool.false_eq_true, ite_false]
      rw [ite_eq_right (not_lt_of_ge hnormalizedMaxIEEE)]
      rw [hbias]
  · have hmantissaHigh :
        rounded < pow2 (fmt.fracWidth + 1) :=
      lt_of_le_of_ne hroundedHigh hcarry
    have hguard :=
      Directed.Internal.normalizedGuard_eq_false fmt hfmt
        rounded totalExponent hmantissaHigh hnormal htotalMax
    dsimp only at hguard
    have htotalMaxIEEE :
        totalExponent ≤
          Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
      rwa [← hmax]
    have hoverflowBool :
        decide (fmt.maxNormalExponent < totalExponent) = false :=
      decide_eq_false hoverflow
    simp only [hcarry, ite_false, hoverflowBool, Bool.false_or,
      hguard, Bool.false_eq_true, ite_false]
    rw [ite_eq_right (not_lt_of_ge htotalMaxIEEE)]
    rw [hbias]

/--
On conventional IEEE descriptors, the descriptor-general integer rounder and the specialized
IEEE integer rounder produce the same packed word.

This is an algorithmic equality: it compares signed zero, subnormal carry, normalization carry,
overflow, and the final exponent/fraction fields directly. It does not pass through real-valued
semantics.
-/
private theorem roundDyadicGeneral_eq_ieeeRoundDyadicImpl_of_isIEEE
    (fmt : FloatFormat) (d : Numerics.Dyadic) (hfmt : fmt.isIEEE = true) :
    roundDyadicGeneral fmt d = ieeeRoundDyadicImpl fmt d := by
  have hmin :=
    FloatFormat.minNormalExponent_eq_ieee fmt hfmt
  have hsubnormal :=
    FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt
  have hmax :=
    FloatFormat.maxNormalExponent_eq_ieee fmt hfmt
  have hbias :=
    FloatFormat.exponentBias_eq_bias_of_isIEEE fmt hfmt
  have halign :
      d.exponent - fmt.minSubnormalExponent =
        d.exponent + Int.ofNat (FloatFormat.ieeeSubnormalAlignExp fmt) := by
    rw [hsubnormal, ieeeSubnormalAlignExp_eq_neg_minSubnormalExp]
    omega
  by_cases hm : d.significand = 0
  · simp [roundDyadicGeneral, ieeeRoundDyadicImpl, hm,
      zero_eq_signedZero_of_isIEEE fmt hfmt]
  · let totalExponent : Int :=
      (d.significand.log2 : Int) + d.exponent
    by_cases hoverflow : fmt.maxNormalExponent < totalExponent
    · have hoverflow' :
          fmt.maxNormalExponent <
            (d.significand.log2 : Int) + d.exponent := by
        simpa only [totalExponent] using hoverflow
      have hoverflowIEEE :
          Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) < totalExponent := by
        rwa [← hmax]
      have hnormalBounds :
          FloatFormat.ieeeMinNormalExponent fmt ≤
            Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
        rw [← hmin, ← hmax]
        exact minNormalExponent_le_maxNormalExponent fmt
      have hnormalIEEE :
          FloatFormat.ieeeMinNormalExponent fmt ≤ totalExponent :=
        hnormalBounds.trans hoverflowIEEE.le
      let rounded :=
        roundMantissaToLeadingBitEven d.significand fmt.fracWidth
      have hgeneral :
          roundDyadicGeneral fmt d = nativeOverflow fmt d.negative := by
        unfold roundDyadicGeneral
        simp only [beq_iff_eq, hm, ite_false]
        rw [ite_eq_left hoverflow']
      rw [hgeneral, ieeeRoundDyadicImpl_of_normal fmt d hm hnormalIEEE,
        nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt]
      rw [show roundMantissaToLeadingBitEven d.significand fmt.fracWidth = rounded from rfl,
        show (d.significand.log2 : Int) + d.exponent = totalExponent from rfl]
      simp only [beq_iff_eq]
      by_cases hcarry : rounded = pow2 (fmt.fracWidth + 1)
      · have hoverflowCarry :
            Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) <
              totalExponent + 1 := by
          omega
        simp only [hcarry, ite_true]
        rw [ite_eq_left hoverflowCarry]
      · simp only [hcarry, ite_false]
        rw [ite_eq_left hoverflowIEEE]
    · have htotalMax : totalExponent ≤ fmt.maxNormalExponent :=
        le_of_not_gt hoverflow
      have hoverflow' :
          ¬fmt.maxNormalExponent <
            (d.significand.log2 : Int) + d.exponent := by
        simpa only [totalExponent] using hoverflow
      by_cases hsub : totalExponent < fmt.minNormalExponent
      · have hsub' :
            (d.significand.log2 : Int) + d.exponent <
              fmt.minNormalExponent := by
          simpa only [totalExponent] using hsub
        have hsubIEEE :
            totalExponent < FloatFormat.ieeeMinNormalExponent fmt := by
          rwa [← hmin]
        have hsubIEEE' :
            (d.significand.log2 : Int) + d.exponent <
              FloatFormat.ieeeMinNormalExponent fmt := by
          simpa only [totalExponent] using hsubIEEE
        let fraction :=
          match d.exponent +
              Int.ofNat (FloatFormat.ieeeSubnormalAlignExp fmt) with
          | .ofNat shift => d.significand <<< shift
          | .negSucc shift => Numerics.roundShiftRightEven d.significand (shift + 1)
        have hfractionEq :
            roundMantissaAtExponentEven d.significand d.exponent
                (FloatFormat.ieeeMinSubnormalExponent fmt) =
              fraction := by
          simpa only [fraction] using
            roundMantissaAtExponentEven_minSubnormal_eq_match
              fmt d.significand d.exponent
        have hfractionLe : fraction ≤ pow2 fmt.fracWidth := by
          rw [← hfractionEq]
          exact roundMantissaAtExponentEven_minSubnormal_le_pow2
            fmt d.significand d.exponent hsubIEEE
        have hgeneral :
            roundDyadicGeneral fmt d =
              if fraction == 0 then
                zero fmt d.negative
              else if fraction ≥ pow2 fmt.fracWidth then
                ofFields fmt d.negative 1 0
              else
                ofFields fmt d.negative 0 fraction := by
          unfold roundDyadicGeneral
          simp only [beq_iff_eq, hm, ite_false]
          rw [ite_eq_right hoverflow', ite_eq_left hsub', halign]
          simp only [packRoundedSubnormal, beq_iff_eq, fraction]
          rfl
        have himpl :
            ieeeRoundDyadicImpl fmt d =
              if fraction == 0 then
                if d.negative then negZero fmt else posZero fmt
              else if fraction == pow2 fmt.fracWidth then
                ofFields fmt d.negative 1 0
              else
                ofFields fmt d.negative 0 fraction := by
          unfold ieeeRoundDyadicImpl
          simp only [beq_iff_eq, hm, ite_false]
          rw [ite_eq_left hsubIEEE']
          rfl
        rw [hgeneral, himpl]
        by_cases hzero : fraction = 0
        · simp [hzero, zero_eq_signedZero_of_isIEEE fmt hfmt]
        · by_cases hcarry : fraction = pow2 fmt.fracWidth
          · have hpow : pow2 fmt.fracWidth ≠ 0 :=
              Nat.ne_of_gt (by simp [pow2_eq_two_pow])
            simp [hcarry, hpow]
          · have hbelow : ¬fraction ≥ pow2 fmt.fracWidth := by
              omega
            simp [hzero, hcarry, hbelow]
      · have hnormal : fmt.minNormalExponent ≤ totalExponent :=
          le_of_not_gt hsub
        exact roundDyadicNormalCase (fmt := fmt) (d := d) (hfmt := hfmt) (hmin := hmin)
          (hmax := hmax) (hbias := hbias) (hm := hm) hoverflow htotalMax hoverflow' hsub
          hnormal

/--
The descriptor-general nearest-even dyadic algorithm agrees exactly with the public dyadic
rounding specification, including signed zero and every packed exceptional result.
-/
theorem roundDyadicGeneral_eq_roundDyadic
    (fmt : FloatFormat) (d : Numerics.Dyadic) :
    roundDyadicGeneral fmt d = roundDyadic fmt d := by
  by_cases hfmt : fmt.isIEEE = true
  · rw [roundDyadic, ite_eq_left hfmt,
      ieeeRoundDyadic_eq_ieeeRoundDyadicImpl]
    exact roundDyadicGeneral_eq_ieeeRoundDyadicImpl_of_isIEEE fmt d hfmt
  · have hfmtFalse : fmt.isIEEE = false :=
      Bool.eq_false_of_not_eq_true hfmt
    simp [roundDyadic, hfmtFalse]

/-- Compiler substitution preserves the complete-format dyadic rounding specification. -/
@[csimp] theorem roundDyadic_eq_roundDyadicImpl :
    @roundDyadic = @roundDyadicImpl := by
  funext fmt d
  by_cases hieee : fmt.isIEEE
  · simp [roundDyadic, roundDyadicImpl, hieee,
      ieeeRoundDyadic_eq_ieeeRoundDyadicImpl]
  · simp [roundDyadic, roundDyadicImpl, hieee]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
