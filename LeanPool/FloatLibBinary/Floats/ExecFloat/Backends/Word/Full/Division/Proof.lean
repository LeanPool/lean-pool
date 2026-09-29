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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Core.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Division.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Quotient.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.QuotientRound.Proof

/-!
# Verified native normal-result division for binary64

The native path generates quotient bits with a restoring `UInt64` loop. Every accepted result
equals the exact-rational finite result as an encoded value. `divFiniteFastImpl_eq` extends this
agreement to the complete optional finite operation, including declined inputs.

Zeros and quotients outside the normal-result path use the generic finite kernel. Non-finite
operands remain the responsibility of the outer arithmetic dispatcher.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord.RestoringQuotient
open FloatLib.Numerics.FixedWord

private theorem roundNormalNative_eq_spec
    (sign : Bool) (num den : UInt64) (exponent : Int)
    (hnum : num ≠ 0) (hden : den ≠ 0)
    (hnumFit : num.toNat < 2 ^ 53)
    (hdenFit : den.toNat < 2 ^ 53) :
    (let rationalExponent :=
        floorLog2RatWord num den
      let totalExponent := rationalExponent + exponent
      if totalExponent < -1022 || 1023 < totalExponent then
        (none : Option Value)
      else
        let shift := Int.toNat (52 - rationalExponent)
        let roundedMantissa :=
          roundScaledQuotient num den shift
        let carry := roundedMantissa == 0x0020000000000000
        let normalizedExponent :=
          if carry then totalExponent + 1 else totalExponent
        if 1023 < normalizedExponent then
          none
        else
          let normalizedMantissa :=
            if carry then 0x0010000000000000 else roundedMantissa
          let encodedExponent :=
            UInt64.ofNat (Int.toNat (normalizedExponent + 1023))
          let fraction := normalizedMantissa - 0x0010000000000000
          some <| ofUInt64 <|
            packFieldsWord sign encodedExponent fraction) =
      FiniteQuotientRound.normalSpecOption FloatFormat.binary64
        sign num.toNat den.toNat exponent := by
  have hnumNat : num.toNat ≠ 0 :=
    (uint64_toNat_eq_zero num).not.mpr hnum
  have hdenNat : den.toNat ≠ 0 :=
    (uint64_toNat_eq_zero den).not.mpr hden
  have hnumZero : (num.toNat == 0) = false := by
    simp [hnumNat]
  have hdenZero : (den.toNat == 0) = false := by
    simp [hdenNat]
  have hfloor :=
    floorLog2RatWord_eq num den hnum hden
  have hshift :
      Int.ofNat
          (Int.toNat
            (52 - floorLog2RatWord num den)) =
        52 - floorLog2RatWord num den := by
    simpa only [
      show Int.ofNat FloatFormat.binary64.fracWidth = (52 : Int) by decide
    ] using
      (NativeWordQuotient.normalShift_eq
        FloatFormat.binary64 num den hnum hnumFit)
  have hquotientFit :
      (num.toNat <<<
            Int.toNat (52 - floorLog2RatWord num den)) /
          den.toNat + 1 < 2 ^ 63 := by
    simpa only [
      show Int.ofNat FloatFormat.binary64.fracWidth = (52 : Int) by decide
    ] using
      (NativeWordQuotient.quotient_lt_two_pow_63
        FloatFormat.binary64 num den hnum hden hnumFit (by decide))
  have hquotient :=
    roundScaledQuotient_toNat num den
      (Int.toNat
        (52 - floorLog2RatWord num den))
      hden (lt_trans hdenFit (by norm_num))
      hquotientFit
  have hfracWidth :
      FloatFormat.binary64.fracWidth = 52 := by decide
  have hbias :
      FloatFormat.binary64.bias = 1023 := by decide
  have hminExponent :
      FloatFormat.binary64.ieeeMinNormalExponent = -1022 := by decide
  have hmaxExponent :
      FloatFormat.binary64.ieeeMaxNormalExponent = 1023 := by decide
  unfold FiniteQuotientRound.normalSpecOption
  simp only [hfracWidth, hbias, hminExponent, hmaxExponent,
    Int.ofNat_eq_natCast, Nat.cast_ofNat]
  rw [← hfloor]
  by_cases hrange :
      floorLog2RatWord num den + exponent < -1022 ∨
        1023 <
          floorLog2RatWord num den + exponent
  · simp [hrange, hnumZero, hdenZero]
  have hlow :
      ¬floorLog2RatWord num den + exponent < -1022 :=
    fun h => hrange (Or.inl h)
  have hhigh :
      ¬1023 < floorLog2RatWord num den + exponent :=
    fun h => hrange (Or.inr h)
  let shift :=
    Int.toNat
      (52 - floorLog2RatWord num den)
  let nativeMantissa := roundScaledQuotient num den shift
  let genericMantissa :=
    Numerics.roundQuotientEven (num.toNat <<< shift) den.toNat
  have hmantissa :
      nativeMantissa.toNat = genericMantissa := by
    simpa only [shift, nativeMantissa, genericMantissa] using hquotient
  have hcarry :
      nativeMantissa = 0x0020000000000000 ↔
        genericMantissa = Model.pow2 53 := by
    rw [← UInt64.toNat_inj, hmantissa]
    have hword :
        (0x0020000000000000 : UInt64).toNat =
          9007199254740992 := by decide
    rw [hword]
    norm_num [Model.pow2_eq_two_pow]
  have hbounds :
      2 ^ 52 ≤ genericMantissa ∧ genericMantissa ≤ 2 ^ 53 := by
    simpa only [shift, genericMantissa,
      show FloatFormat.binary64.fracWidth = 52 by decide,
      Int.ofNat_eq_natCast, Nat.cast_ofNat, Nat.reduceAdd] using
      (NativeWordQuotient.roundedMantissa_bounds
        FloatFormat.binary64 num den hnum hden hnumFit)
  by_cases hnativeCarry :
      nativeMantissa = 0x0020000000000000
  · have hgenericCarry := hcarry.mp hnativeCarry
    have hnativeCarryBool :
        (nativeMantissa == 0x0020000000000000) = true := by
      simpa using hnativeCarry
    have hgenericCarryBool :
        (genericMantissa == Model.pow2 53) = true := by
      simpa using hgenericCarry
    simp only [shift, nativeMantissa, genericMantissa,
      hnativeCarryBool, hgenericCarryBool]
    simp only [Int.reduceNeg, hlow, decide_false, hhigh, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte,
      Order.lt_add_one_iff, UInt64.sub_self, hdenZero, hnumZero, pow2_eq_two_pow, Nat.reducePow,
        tsub_self]
    split
    · rfl
    · exact congrArg (fun value : Value => some value)
        (packFieldsWord_eq_ofNat sign _ 0)
  · have hgenericCarry :
        genericMantissa ≠ Model.pow2 53 :=
      (not_congr hcarry).mp hnativeCarry
    have hnativeCarryBool :
        (nativeMantissa == 0x0020000000000000) = false := by
      simpa using hnativeCarry
    have hgenericCarryBool :
        (genericMantissa == Model.pow2 53) = false := by
      simpa using hgenericCarry
    have hbase :
        (0x0010000000000000 : UInt64).toNat = 2 ^ 52 := by
      decide
    have hbaseLe :
        (0x0010000000000000 : UInt64) ≤ nativeMantissa := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [hbase, hmantissa]
      exact hbounds.1
    have hfractionFit :
        genericMantissa - 2 ^ 52 < 2 ^ 64 := by
      omega
    have hfraction :
        nativeMantissa - 0x0010000000000000 =
          UInt64.ofNat (genericMantissa - 2 ^ 52) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ hbaseLe, hbase, hmantissa]
      exact (UInt64.toNat_ofNat_of_lt hfractionFit).symm
    simp only [shift, nativeMantissa, genericMantissa,
      hnativeCarryBool, hgenericCarryBool]
    simp only [Int.reduceNeg, hlow, decide_false, hhigh, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, hdenZero,
      hnumZero, pow2_eq_two_pow, Nat.reducePow, Option.some.injEq]
    rw [hfraction]
    norm_num at hfraction ⊢
    exact packFieldsWord_eq_ofNat sign _ _

private theorem divNormal_refines
    (x y result : Value)
    (hresult : divNormalOption x y = some result) :
    NativeBinary64.divFiniteImplOption x y = some result := by
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  let xFraction := fracField xBits
  let yFraction := fracField yBits
  let xMantissa := finiteMantissa xExponent xFraction
  let yMantissa := finiteMantissa yExponent yFraction
  by_cases hxExceptional : xExponent = 0x7ff
  · simp [divNormalOption, xBits, xExponent, hxExceptional] at hresult
  by_cases hyExceptional : yExponent = 0x7ff
  · simp [divNormalOption, yBits, yExponent, hyExceptional] at hresult
  by_cases hxZero : xMantissa = 0
  · simp [divNormalOption, xBits, yBits, xExponent, yExponent,
      xFraction, xMantissa,
      hxExceptional, hyExceptional, hxZero] at hresult
  by_cases hyZero : yMantissa = 0
  · simp [divNormalOption, xBits, yBits, xExponent, yExponent,
      yFraction, yMantissa, hxExceptional, hyExceptional,
      hyZero] at hresult
  have hxFractionBound : xFraction.toNat < 2 ^ 52 := by
    simpa only [xFraction, xBits] using fracField_lt x
  have hyFractionBound : yFraction.toNat < 2 ^ 52 := by
    simpa only [yFraction, yBits] using fracField_lt y
  have hxMantissaFit : xMantissa.toNat < 2 ^ 53 := by
    simpa only [xMantissa] using
      finiteMantissa_lt xExponent xFraction hxFractionBound
  have hyMantissaFit : yMantissa.toNat < 2 ^ 53 := by
    simpa only [yMantissa] using
      finiteMantissa_lt yExponent yFraction hyFractionBound
  let exponent :=
    Int.ofNat (finiteScale xExponent).toNat -
      Int.ofNat (finiteScale yExponent).toNat
  let rationalExponent :=
    floorLog2RatWord xMantissa yMantissa
  have hround :
      (let totalExponent := rationalExponent + exponent
        if totalExponent < -1022 || 1023 < totalExponent then
          (none : Option Value)
        else
          let shift := Int.toNat (52 - rationalExponent)
          let roundedMantissa :=
            roundScaledQuotient xMantissa yMantissa shift
          let carry := roundedMantissa == 0x0020000000000000
          let normalizedExponent :=
            if carry then totalExponent + 1 else totalExponent
          if 1023 < normalizedExponent then
            none
          else
            let normalizedMantissa :=
              if carry then 0x0010000000000000 else roundedMantissa
            let encodedExponent :=
              UInt64.ofNat (Int.toNat (normalizedExponent + 1023))
            let fraction := normalizedMantissa - 0x0010000000000000
            some <| ofUInt64 <|
              packFieldsWord
                (Bool.xor (signBit xBits) (signBit yBits))
                encodedExponent fraction) =
        some result := by
    simpa [divNormalOption, xBits, yBits, xExponent, yExponent,
      xFraction, yFraction, xMantissa, yMantissa, exponent,
      rationalExponent, hxExceptional, hyExceptional, hxZero, hyZero,
      beq_iff_eq] using hresult
  have hspec :
      FiniteQuotientRound.normalSpecOption FloatFormat.binary64
          (Bool.xor (signBit xBits) (signBit yBits))
          xMantissa.toNat yMantissa.toNat exponent =
        some result := by
    rw [← roundNormalNative_eq_spec
      (Bool.xor (signBit xBits) (signBit yBits))
      xMantissa yMantissa exponent hxZero hyZero
      hxMantissaFit hyMantissaFit]
    exact hround
  have hfloor :=
    floorLog2RatWord_eq
      xMantissa yMantissa hxZero hyZero
  have hshiftInt :
      Int.ofNat
          (Int.toNat
            (52 - floorLog2RatWord xMantissa yMantissa)) =
        52 - floorLog2RatWord xMantissa yMantissa := by
    simpa only [
      show Int.ofNat FloatFormat.binary64.fracWidth = (52 : Int) by decide
    ] using
      (NativeWordQuotient.normalShift_eq
        FloatFormat.binary64 xMantissa yMantissa hxZero hxMantissaFit)
  have hshiftNonnegative :
      0 ≤
        52 -
          Numerics.RationalBinary.floorLog2
            xMantissa.toNat yMantissa.toNat := by
    rw [← hfloor, ← hshiftInt]
    exact Int.natCast_nonneg _
  have hshiftNonnegative' :
      0 ≤ Int.ofNat FloatFormat.binary64.fracWidth -
        Numerics.RationalBinary.floorLog2
          xMantissa.toNat yMantissa.toNat := by
    norm_num at hshiftNonnegative ⊢
    exact hshiftNonnegative
  have hrounded :=
    FiniteQuotientRound.normalSpec_eq_roundRatScaled_of_some
      FloatFormat.binary64 (by decide)
      (Bool.xor (signBit xBits) (signBit yBits))
      xMantissa.toNat yMantissa.toNat exponent result
      hshiftNonnegative' hspec
  unfold NativeBinary64.divFiniteImplOption NativeBinary64.decodeOption
  simp only [xBits, yBits, xExponent, yExponent, hxExceptional,
    hyExceptional, beq_iff_eq, ite_false, Option.some.injEq]
  change
    FiniteKernel.divComponents FloatFormat.binary64
        { sign := signBit xBits
          exponent := xExponent.toNat
          mantissa := xMantissa.toNat }
        { sign := signBit yBits
          exponent := yExponent.toNat
          mantissa := yMantissa.toNat } =
      result
  unfold FiniteKernel.divComponents
  have hxZeroNat : xMantissa.toNat ≠ 0 :=
    (uint64_toNat_eq_zero xMantissa).not.mpr hxZero
  have hyZeroNat : yMantissa.toNat ≠ 0 :=
    (uint64_toNat_eq_zero yMantissa).not.mpr hyZero
  simp only [hxZeroNat, hyZeroNat, beq_iff_eq, ite_false]
  have hxScale :
      FiniteKernel.scale xExponent.toNat =
        (finiteScale xExponent).toNat := by
    by_cases hxExponentZero : xExponent = 0
    · simp [FiniteKernel.scale, finiteScale_toNat, hxExponentZero]
    · have hxExponentNatZero : xExponent.toNat ≠ 0 := by
        intro h
        apply hxExponentZero
        apply UInt64.toNat_inj.mp
        simpa using h
      simp [FiniteKernel.scale, finiteScale_toNat, hxExponentZero,
        hxExponentNatZero]
  have hyScale :
      FiniteKernel.scale yExponent.toNat =
        (finiteScale yExponent).toNat := by
    by_cases hyExponentZero : yExponent = 0
    · simp [FiniteKernel.scale, finiteScale_toNat, hyExponentZero]
    · have hyExponentNatZero : yExponent.toNat ≠ 0 := by
        intro h
        apply hyExponentZero
        apply UInt64.toNat_inj.mp
        simpa using h
      simp [FiniteKernel.scale, finiteScale_toNat, hyExponentZero,
        hyExponentNatZero]
  rw [hxScale, hyScale]
  simpa only [exponent] using hrounded.symm

/-- The native candidate plus certified general route equals the existing finite binary64
  implementation. -/
theorem divFiniteFastImpl_eq (x y : Value) :
    divFiniteFastImplOption x y = NativeBinary64.divFiniteImplOption x y := by
  cases hfast : divNormalOption x y with
  | none => simp [divFiniteFastImplOption, hfast]
  | some result =>
      simp [divFiniteFastImplOption, hfast, divNormal_refines x y result hfast]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
