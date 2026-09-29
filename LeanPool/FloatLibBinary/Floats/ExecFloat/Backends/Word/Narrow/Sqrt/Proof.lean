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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Agreement
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Finite.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Sqrt.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.IntegerSquareRoot.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.SqrtArithmetic
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.SqrtNormalRounding
public import Init.Data.Float.Model.Unpacked.Operations.Sqrt

/-!
# Correctness of native binary32 square root

For positive finite binary32 inputs, including subnormals, exponent parity determines an exact
integer radicand. Its floor square root and remainder determine the rounded significand. The
proof relates this calculation and final packing to the generic `Model` square-root kernel.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

open FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic

private theorem sqrt_target_exponent
    (leading scale : Nat) (hleading : leading < 24) :
    let inputExponent := Int.ofNat scale - 149
    let position := leading + scale
    let rootExponent := Int.ofNat ((position + 105) / 2) - 127
    min (inputExponent.ediv 2)
        ((FloatFormat.toModel FloatFormat.binary32).targetExponent
          ((Float.Model.totalExponent (2 ^ leading) inputExponent + 1).ediv 2)) =
      rootExponent - 23 := by
  dsimp only
  norm_num [Float.Model.Format.targetExponent, Float.Model.Format.minExponent,
    Float.Model.Format.mantissaBits, FloatFormat.toModel, FloatFormat.binary32,
    Float.Model.totalExponent, Nat.log2_two_pow]
  exact
    FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic.target_exponent
      leading scale 149 105 127 23
      (by omega) (by decide) (by decide) (by decide) (by decide)

private theorem sqrt_shift_amount
    (leading scale : Nat) (hleading : leading < 24) :
    let inputExponent := Int.ofNat scale - 149
    let position := leading + scale
    let rootExponent := Int.ofNat ((position + 105) / 2) - 127
    (inputExponent - 2 * (rootExponent - 23)).toNat =
      if position % 2 = 0 then 47 - leading else 46 - leading := by
  dsimp only
  simpa using
    FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic.shift_amount_of_odd_offset
      leading scale 149 105 127 23 (by omega) (by decide) (by decide)

private def sqrtPositiveFiniteSpec (mantissa scale : Nat) : UInt32 :=
  let leading := mantissa.log2
  let position := leading + scale
  let shift := if position % 2 == 0 then 47 - leading else 46 - leading
  let scaledMantissa := mantissa <<< shift
  let root := Nat.sqrt scaledMantissa
  let remainder := scaledMantissa - root * root
  let roundedRoot := if remainder ≤ root then root else root + 1
  let carry := roundedRoot == Model.pow2 24
  let encodedExponent := (position + 105) / 2 + if carry then 1 else 0
  let roundedMantissa := if carry then Model.pow2 23 else roundedRoot
  mkBits false encodedExponent (roundedMantissa - Model.pow2 23)

private theorem packRoundedSquareRoot32 (mantissa scale : UInt64) :
  let nativeLeading := mantissa.log2;
  let nativePosition := nativeLeading + scale;
  let nativeShift := if (nativePosition % 2 == 0) = true then 47 - nativeLeading else 46 -
    nativeLeading;
  let nativeScaled := mantissa <<< nativeShift;
  let nativeRoot := Numerics.FixedWord.IntegerSquareRoot.sqrt nativeScaled;
  let nativeRemainder := nativeScaled - nativeRoot * nativeRoot;
  let nativeRounded := if nativeRemainder ≤ nativeRoot then nativeRoot else nativeRoot + 1;
  let nativeCarry := nativeRounded == 16777216;
  let nativeEncoded := (nativePosition + 105) / 2 + if nativeCarry = true then 1 else 0;
  let nativeRoundedMantissa := if nativeCarry = true then 8388608 else nativeRounded;
  let nativeFraction := nativeRoundedMantissa - 8388608;
  let genericLeading := mantissa.toNat.log2;
  let genericPosition := genericLeading + scale.toNat;
  let genericShift := if (genericPosition % 2 == 0) = true then 47 - genericLeading else 46 -
    genericLeading;
  let genericScaled := mantissa.toNat <<< genericShift;
  let genericRoot := genericScaled.sqrt;
  let genericRemainder := genericScaled - genericRoot * genericRoot;
  let genericRounded := if genericRemainder ≤ genericRoot then genericRoot else genericRoot + 1;
  let genericCarry := genericRounded == pow2 24;
  let genericEncoded := (genericPosition + 105) / 2 + if genericCarry = true then 1 else 0;
  let genericRoundedMantissa := if genericCarry = true then pow2 23 else genericRounded;
  let genericFraction := genericRoundedMantissa - pow2 23;
  mantissa.toNat ≠ 0 →
    nativeLeading.toNat = genericLeading →
      genericLeading < 24 →
        genericPosition ≤ 276 →
          nativePosition.toNat = genericPosition →
            nativeRoot.toNat = genericRoot →
              genericRoot < 2 ^ 24 →
                (nativeRemainder ≤ nativeRoot ↔ genericRemainder ≤ genericRoot) →
                  mkBits false nativeEncoded.toNat nativeFraction.toNat =
                    mkBits false genericEncoded genericFraction := by
  intro nativeLeading nativePosition nativeShift nativeScaled nativeRoot nativeRemainder
    nativeRounded nativeCarry nativeEncoded nativeRoundedMantissa nativeFraction genericLeading
    genericPosition genericShift genericScaled genericRoot genericRemainder genericRounded
    genericCarry genericEncoded genericRoundedMantissa genericFraction hmantissaNat hleading
    hleadingLt hpositionLe hposition hroot hrootLt hremainderLe
  have hrounded : nativeRounded.toNat = genericRounded := by
    dsimp only [nativeRounded, genericRounded]
    by_cases hle : nativeRemainder ≤ nativeRoot
    · rw [ite_eq_left hle, ite_eq_left (hremainderLe.mp hle), hroot]
    · rw [ite_eq_right hle, ite_eq_right ((not_congr hremainderLe).mp hle)]
      have hrootSuccFit : genericRoot + 1 < 2 ^ 64 := by
        have hpow : 2 ^ 24 < 2 ^ 64 :=
          Nat.pow_lt_pow_right (by decide) (by omega)
        omega
      rw [UInt64.toNat_add, hroot]
      change (genericRoot + 1) % 2 ^ 64 = genericRoot + 1
      exact Nat.mod_eq_of_lt hrootSuccFit
  have hcarry : nativeCarry = genericCarry := by
    dsimp only [nativeCarry, genericCarry]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rw [← UInt64.toNat_inj]
    simp [hrounded, Model.pow2_eq_two_pow]
  have hpositionAdd :
      (nativePosition + 105).toNat = genericPosition + 105 := by
    rw [UInt64.toNat_add, hposition]
    change (genericPosition + 105) % 2 ^ 64 = genericPosition + 105
    apply Nat.mod_eq_of_lt
    omega
  have hpositionHalf :
      ((nativePosition + 105) / 2).toNat = (genericPosition + 105) / 2 := by
    rw [UInt64.toNat_div, hpositionAdd]
    change (genericPosition + 105) / 2 = (genericPosition + 105) / 2
    rfl
  have hencoded : nativeEncoded.toNat = genericEncoded := by
    dsimp only [nativeEncoded, genericEncoded]
    rw [hcarry]
    by_cases hgenericCarry : genericCarry = true
    · simp only [hgenericCarry, ite_true]
      have hhalfLe :
          (genericPosition + 105) / 2 ≤ genericPosition + 105 :=
        Nat.div_le_self _ _
      have hencodedFit :
          (genericPosition + 105) / 2 + 1 < 2 ^ 64 := by
        omega
      rw [UInt64.toNat_add, hpositionHalf]
      change
        ((genericPosition + 105) / 2 + 1) % 2 ^ 64 =
          (genericPosition + 105) / 2 + 1
      exact Nat.mod_eq_of_lt hencodedFit
    · have hgenericCarryFalse := Bool.eq_false_of_not_eq_true hgenericCarry
      simp [hgenericCarryFalse, hpositionHalf]
  have hroundedLower : 2 ^ 23 ≤ genericRounded := by
    have hpowLeading : 2 ^ genericLeading ≤ mantissa.toNat := by
      dsimp only [genericLeading]
      exact (Nat.le_log2 hmantissaNat).mp le_rfl
    have hscaledExponentLower :
        46 ≤ genericLeading + genericShift := by
      dsimp only [genericShift]
      split <;> omega
    have hscaledLower : 2 ^ 46 ≤ genericScaled := by
      dsimp only [genericScaled]
      rw [Nat.shiftLeft_eq]
      calc
        2 ^ 46 ≤ 2 ^ (genericLeading + genericShift) :=
          Nat.pow_le_pow_right (by decide) hscaledExponentLower
        _ = 2 ^ genericLeading * 2 ^ genericShift := Nat.pow_add ..
        _ ≤ mantissa.toNat * 2 ^ genericShift :=
          Nat.mul_le_mul_right (2 ^ genericShift) hpowLeading
    have hrootLower : 2 ^ 23 ≤ genericRoot := by
      dsimp only [genericRoot]
      rw [Nat.le_sqrt, ← Nat.pow_add]
      norm_num
      exact hscaledLower
    dsimp only [genericRounded]
    split <;> omega
  have hroundedMantissa :
      nativeRoundedMantissa.toNat = genericRoundedMantissa := by
    dsimp only [nativeRoundedMantissa, genericRoundedMantissa]
    rw [hcarry]
    by_cases hgenericCarry : genericCarry = true
    · simp [hgenericCarry, Model.pow2_eq_two_pow]
    · simp [Bool.eq_false_of_not_eq_true hgenericCarry, hrounded]
  have hroundedMantissaLower :
      2 ^ 23 ≤ genericRoundedMantissa := by
    dsimp only [genericRoundedMantissa]
    split
    · norm_num [Model.pow2_eq_two_pow]
    · exact hroundedLower
  have hroundedMantissaWordLower :
      (0x800000 : UInt64) ≤ nativeRoundedMantissa := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hroundedMantissa]
    exact hroundedMantissaLower
  have hfraction : nativeFraction.toNat = genericFraction := by
    dsimp only [nativeFraction, genericFraction]
    rw [UInt64.toNat_sub_of_le _ _ hroundedMantissaWordLower,
      hroundedMantissa]
    change
      genericRoundedMantissa - 8388608 =
        genericRoundedMantissa - Model.pow2 23
    norm_num [Model.pow2_eq_two_pow]
  rw [hencoded, hfraction]

private theorem sqrtPositiveFiniteCore_eq_spec
    (mantissa scale : UInt64)
    (hmantissa : mantissa ≠ 0)
    (hmantissaBound : mantissa.toNat < 2 ^ 24)
    (hscaleBound : scale.toNat ≤ 253) :
    sqrtPositiveFiniteCore mantissa scale =
      sqrtPositiveFiniteSpec mantissa.toNat scale.toNat := by
  let nativeLeading := mantissa.log2
  let nativePosition := nativeLeading + scale
  let nativeShift : UInt64 :=
    if nativePosition % 2 == 0 then 47 - nativeLeading else 46 - nativeLeading
  let nativeScaled := mantissa <<< nativeShift
  let nativeRoot := FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrt nativeScaled
  let nativeRemainder := nativeScaled - nativeRoot * nativeRoot
  let nativeRounded :=
    if nativeRemainder ≤ nativeRoot then nativeRoot else nativeRoot + 1
  let nativeCarry := nativeRounded == 0x1000000
  let nativeEncoded :=
    (nativePosition + 105) / 2 + if nativeCarry then 1 else 0
  let nativeRoundedMantissa :=
    if nativeCarry then 0x800000 else nativeRounded
  let nativeFraction := nativeRoundedMantissa - 0x800000
  let genericLeading := mantissa.toNat.log2
  let genericPosition := genericLeading + scale.toNat
  let genericShift :=
    if genericPosition % 2 == 0 then 47 - genericLeading else 46 - genericLeading
  let genericScaled := mantissa.toNat <<< genericShift
  let genericRoot := Nat.sqrt genericScaled
  let genericRemainder := genericScaled - genericRoot * genericRoot
  let genericRounded :=
    if genericRemainder ≤ genericRoot then genericRoot else genericRoot + 1
  let genericCarry := genericRounded == Model.pow2 24
  let genericEncoded :=
    (genericPosition + 105) / 2 + if genericCarry then 1 else 0
  let genericRoundedMantissa :=
    if genericCarry then Model.pow2 23 else genericRounded
  let genericFraction := genericRoundedMantissa - Model.pow2 23
  change
    mkBits false nativeEncoded.toNat nativeFraction.toNat =
      mkBits false genericEncoded genericFraction
  have hmantissaNat : mantissa.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hmantissa
  have hleading : nativeLeading.toNat = genericLeading := by
    dsimp only [nativeLeading, genericLeading]
    exact FloatLib.Numerics.FixedWord.log2_toNat mantissa
  have hleadingLt : genericLeading < 24 := by
    dsimp only [genericLeading]
    rw [Nat.log2_lt hmantissaNat]
    exact hmantissaBound
  have hpositionBound : genericPosition < 2 ^ 64 := by
    dsimp only [genericPosition]
    omega
  have hpositionLe : genericPosition ≤ 276 := by
    dsimp only [genericPosition]
    omega
  have hposition : nativePosition.toNat = genericPosition := by
    dsimp only [nativePosition]
    rw [UInt64.toNat_add, hleading, Nat.mod_eq_of_lt hpositionBound]
  have hpositionEven :
      nativePosition % 2 = 0 ↔ genericPosition % 2 = 0 := by
    constructor
    · intro h
      have hnat := congrArg UInt64.toNat h
      rw [UInt64.toNat_mod, hposition] at hnat
      norm_num at hnat ⊢
      exact hnat
    · intro h
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mod, hposition]
      norm_num
      exact h
  have hparity :
      (nativePosition % 2 == 0) = (genericPosition % 2 == 0) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq] using hpositionEven
  have hshift : nativeShift.toNat = genericShift := by
    dsimp only [nativeShift, genericShift]
    rw [hparity]
    by_cases heven : genericPosition % 2 = 0
    · have hevenBool : (genericPosition % 2 == 0) = true := by
        simpa only [beq_iff_eq] using heven
      rw [hevenBool]
      simp only [ite_true]
      have h47 : (47 : UInt64).toNat = 47 := by decide
      have hleadingWord : nativeLeading ≤ (47 : UInt64) := by
        apply UInt64.le_iff_toNat_le.mpr
        rw [hleading, h47]
        omega
      rw [UInt64.toNat_sub_of_le _ _ hleadingWord, h47, hleading]
    · have hevenBool : (genericPosition % 2 == 0) = false :=
        beq_eq_false_iff_ne.mpr heven
      rw [hevenBool]
      simp only [Bool.false_eq_true, ite_false]
      have h46 : (46 : UInt64).toNat = 46 := by decide
      have hleadingWord : nativeLeading ≤ (46 : UInt64) := by
        apply UInt64.le_iff_toNat_le.mpr
        rw [hleading, h46]
        omega
      rw [UInt64.toNat_sub_of_le _ _ hleadingWord, h46, hleading]
  have hshiftLt : genericShift < 64 := by
    dsimp only [genericShift]
    split <;> omega
  have hscaledExponentLe :
      genericLeading + 1 + genericShift ≤ 48 := by
    dsimp only [genericShift]
    split <;> omega
  have hscaledLt : genericScaled < 2 ^ 48 := by
    dsimp only [genericScaled]
    exact lt_of_lt_of_le
      (Nat.shiftLeft_lt Nat.lt_log2_self)
      (Nat.pow_le_pow_right (by decide) hscaledExponentLe)
  have hscaledFit : genericScaled < 2 ^ 64 :=
    lt_trans hscaledLt (Nat.pow_lt_pow_right (by decide) (by omega))
  have hscaled : nativeScaled.toNat = genericScaled := by
    simpa only [nativeScaled, genericScaled, ← hshift, UInt64.ofNat_toNat] using
      FloatLib.Numerics.FixedWord.shiftLeft_toNat mantissa genericShift hshiftLt hscaledFit
  have hroot : nativeRoot.toNat = genericRoot := by
    dsimp only [nativeRoot, genericRoot]
    rw [FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrt_toNat, hscaled]
  have hrootLt : genericRoot < 2 ^ 24 := by
    dsimp only [genericRoot]
    rw [Nat.sqrt_lt]
    rw [← Nat.pow_add]
    norm_num
    exact hscaledLt
  have hrootProductFit : genericRoot * genericRoot < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.sqrt_le genericScaled) hscaledFit
  have hrootProduct :
      (nativeRoot * nativeRoot).toNat = genericRoot * genericRoot := by
    rw [UInt64.toNat_mul, hroot, Nat.mod_eq_of_lt hrootProductFit]
  have hrootProductLe : nativeRoot * nativeRoot ≤ nativeScaled := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hrootProduct, hscaled]
    exact Nat.sqrt_le genericScaled
  have hremainder : nativeRemainder.toNat = genericRemainder := by
    dsimp only [nativeRemainder, genericRemainder]
    rw [UInt64.toNat_sub_of_le _ _ hrootProductLe, hscaled, hrootProduct]
  have hremainderLe :
      nativeRemainder ≤ nativeRoot ↔ genericRemainder ≤ genericRoot := by
    rw [UInt64.le_iff_toNat_le, hremainder, hroot]
  exact packRoundedSquareRoot32 (mantissa := mantissa) (scale := scale) hmantissaNat hleading
    hleadingLt hpositionLe hposition hroot hrootLt hremainderLe

/-- For a positive, finite, nonzero binary32 input the fast square root agrees with the generic
kernel. -/
theorem sqrt_eq_generic_of_positive_finite
    (x : Value)
    (hexponent :
      Model.expField x ≠ FloatFormat.expAllOnesNat FloatFormat.binary32)
    (hnonzero : Model.isZero x = false)
    (hsign : Model.signBit x = false) :
    ofUInt32
        (sqrtPositiveFinite
          (expField (toUInt32 x))
          (fracField (toUInt32 x))) =
      Model.ofModel FloatFormat.binary32 (
        Float.Model.UnpackedFloat.sqrt
          (FloatFormat.toModel FloatFormat.binary32)
          (Model.toModel x)) := by
  let bits := toUInt32 x
  let exponent := expField bits
  let fraction := fracField bits
  let mantissa := finiteMantissa exponent fraction
  let scale := finiteScale exponent
  have hfraction : fraction.toNat < 2 ^ 23 := by
    simpa only [fraction, bits] using fracField_lt x
  have hexponentNative : exponent ≠ 0xff := by
    intro h
    apply hexponent
    rw [← expField_toNat x]
    simp only [bits, exponent, h]
    decide
  have hmantissa : mantissa ≠ 0 := by
    intro h
    have hmantissaNat : mantissa.toNat = 0 := congrArg UInt64.toNat h
    rw [finiteMantissa_toNat exponent fraction hfraction] at hmantissaNat
    by_cases hexponentZero : exponent = 0
    · simp only [hexponentZero, ite_true] at hmantissaNat
      have hfractionZero : fraction = 0 := by
        apply UInt32.toNat_inj.mp
        simpa using hmantissaNat
      have hzero : Model.isZero x = true := by
        change Model.IEEE.isZero x = true
        unfold Model.IEEE.isZero
        rw [← expField_beq_zero x, ← fracField_beq_zero x]
        simp only [bits, exponent, fraction, hexponentZero, hfractionZero, beq_self_eq_true,
          Bool.true_and]
      rw [hzero] at hnonzero
      contradiction
    · simp only [hexponentZero, ite_false] at hmantissaNat
      simp [Model.pow2_eq_two_pow] at hmantissaNat
  have hsignNative : signBit bits = false := by
    simpa only [bits, signBit_eq] using hsign
  have hmantissaNat : mantissa.toNat ≠ 0 := by
    intro h
    apply hmantissa
    apply UInt64.toNat_inj.mp
    simpa using h
  have hdecode :
      Model.toDyadicOption x =
        some
          ({ negative := false
             significand := mantissa.toNat
             exponent := Int.ofNat scale.toNat - 149 } : Numerics.Dyadic) := by
    rw [← toDyadic_eq x, toDyadic_eq_finiteComponents x]
    simp only [bits, exponent, fraction, mantissa, scale, hexponentNative, ite_false,
      hmantissa, hsignNative]
  have htoModel :
      Model.toModel x =
        .finite .positive mantissa.toNat (Int.ofNat scale.toNat - 149)
          (Nat.pos_of_ne_zero hmantissaNat) := by
    have hieeeDecode :
        Model.ieeeToDyadicOption x =
          some
            ({ negative := false
               significand := mantissa.toNat
               exponent := Int.ofNat scale.toNat - 149 } : Numerics.Dyadic) := by
      simpa [Model.toDyadicOption, show FloatFormat.binary32.isIEEE = true by decide]
        using hdecode
    simpa [Model.modelSign] using
      Model.toModel_eq_finite_of_ieeeToDyadicOption_eq_some
        x false mantissa.toNat (Int.ofNat scale.toNat - 149)
        hmantissaNat hieeeDecode
  rw [htoModel]
  have hmantissaBound : mantissa.toNat < 2 ^ 24 := by
    simpa only [mantissa, exponent, fraction, bits] using
      finiteMantissa_lt_of_value x
  have hscaleBound : scale.toNat ≤ 253 := by
    simpa only [scale, exponent, bits] using
      finiteScale_le_of_value x (by
        simpa only [exponent, bits] using hexponentNative)
  have hleading : mantissa.toNat.log2 < 24 := by
    rw [Nat.log2_lt hmantissaNat]
    exact hmantissaBound
  have hfracWidth : FloatFormat.binary32.fracWidth = 23 := by decide
  have hbias : FloatFormat.binary32.bias = 127 := by decide
  rw [Model.ofModel_sqrt_finite_positive_eq_ofFields FloatFormat.binary32 mantissa.toNat
    (if (mantissa.toNat.log2 + scale.toNat) % 2 = 0 then 47 - mantissa.toNat.log2
      else 46 - mantissa.toNat.log2)
    ((mantissa.toNat.log2 + scale.toNat + 105) / 2) (Int.ofNat scale.toNat - 149)
    (Nat.pos_of_ne_zero hmantissaNat)
    (by rw [hfracWidth]; split <;> omega) (by rw [hfracWidth]; split <;> omega)
    (by omega) (by rw [hbias]; omega)
    (by simpa only [hfracWidth, hbias, Float.Model.totalExponent, Nat.log2_two_pow,
      Int.ofNat_eq_natCast, Nat.cast_ofNat] using
        sqrt_target_exponent mantissa.toNat.log2 scale.toNat hleading)
    (by simpa only [hfracWidth, hbias, Int.ofNat_eq_natCast, Nat.cast_ofNat] using
      sqrt_shift_amount mantissa.toNat.log2 scale.toNat hleading)]
  change ofUInt32 (sqrtPositiveFiniteCore mantissa scale) = _
  rw [sqrtPositiveFiniteCore_eq_spec mantissa scale hmantissa hmantissaBound hscaleBound]
  simp only [sqrtPositiveFiniteSpec, beq_iff_eq, ofUInt32_mkBits, hfracWidth]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
