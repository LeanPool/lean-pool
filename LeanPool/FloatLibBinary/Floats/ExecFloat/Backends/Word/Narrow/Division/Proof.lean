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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Division.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.DivisionReference
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Finite.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Quotient.Proof

/-!
# Correctness of native-word division for binary32

The proof connects the native logarithm, quotient rounding, and complete finite divider to the
generic exact-rational specification. Runtime clients can import `Division.Runtime` without this
development.

For significands below `2^24`, the scaling shifts and rounded quotient fit in `UInt64`.
The proof uses those bounds to connect native quotient-and-remainder rounding to exact rational
rounding, including ties, subnormal results, and overflow.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
open FloatLib.Numerics.FixedWord.RestoringQuotient

private theorem subnormal_num_shift_bounds
    (num den : UInt64) (exponent : Int) (shift : Nat)
    (hnum : num ≠ 0) (hden : den ≠ 0)
    (hnumFit : num.toNat < 2 ^ 24)
    (hdenFit : den.toNat < 2 ^ 24)
    (hscale : exponent + 149 = Int.ofNat shift)
    (hhigh : floorLog2RatWord num den + exponent < -126) :
    shift < 64 ∧ num.toNat <<< shift < 2 ^ 63 := by
  have hnumLog : num.log2.toNat < 24 :=
    FloatLib.Numerics.FixedWord.log2_toNat_lt_of_toNat_lt_two_pow
      num 24 hnum hnumFit
  have hdenLog : den.log2.toNat < 24 :=
    FloatLib.Numerics.FixedWord.log2_toNat_lt_of_toNat_lt_two_pow
      den 24 hden hdenFit
  have hrange := floorLog2RatWord_log_bounds num den
  simp only [Int.ofNat_eq_natCast] at hrange hscale
  have hshiftLt : shift < 64 := by omega
  have hexponent :
      num.log2.toNat + 1 + shift ≤ 63 := by
    omega
  have hbound :
      num.toNat <<< shift <
        2 ^ (num.toNat.log2 + 1 + shift) :=
    Nat.shiftLeft_lt Nat.lt_log2_self
  rw [← FloatLib.Numerics.FixedWord.log2_toNat] at hbound
  exact ⟨hshiftLt, lt_of_lt_of_le hbound <|
    Nat.pow_le_pow_right (by decide) hexponent⟩

private theorem subnormal_den_shift_bounds
    (num den : UInt64) (exponent : Int) (shift : Nat)
    (hnum : num ≠ 0) (hden : den ≠ 0)
    (hnumFit : num.toNat < 2 ^ 24)
    (hdenFit : den.toNat < 2 ^ 24)
    (hscale : exponent + 149 = Int.negSucc shift)
    (hlow : ¬floorLog2RatWord num den + exponent < -150) :
    shift + 1 < 64 ∧ den.toNat <<< (shift + 1) < 2 ^ 63 := by
  have hnumLog : num.log2.toNat < 24 :=
    FloatLib.Numerics.FixedWord.log2_toNat_lt_of_toNat_lt_two_pow
      num 24 hnum hnumFit
  have hdenLog : den.log2.toNat < 24 :=
    FloatLib.Numerics.FixedWord.log2_toNat_lt_of_toNat_lt_two_pow
      den 24 hden hdenFit
  have hrange := floorLog2RatWord_log_bounds num den
  simp only [Int.ofNat_eq_natCast] at hrange
  have hshiftLt : shift + 1 < 64 := by
    simp only [Int.negSucc_eq] at hscale
    omega
  have hexponent :
      den.log2.toNat + 1 + (shift + 1) ≤ 63 := by
    simp only [Int.negSucc_eq] at hscale
    omega
  have hbound :
      den.toNat <<< (shift + 1) <
        2 ^ (den.toNat.log2 + 1 + (shift + 1)) :=
    Nat.shiftLeft_lt Nat.lt_log2_self
  rw [← FloatLib.Numerics.FixedWord.log2_toNat] at hbound
  exact ⟨hshiftLt, lt_of_lt_of_le hbound <|
    Nat.pow_le_pow_right (by decide) hexponent⟩

private theorem roundQuotientEven_num_shift_toNat
    (num den : UInt64) (shift : Nat)
    (hden : den ≠ 0)
    (hshift : shift < 64)
    (hnumShiftFit : num.toNat <<< shift < 2 ^ 63) :
    (FloatLib.Numerics.FixedWord.roundQuotientEven
        (num <<< UInt64.ofNat shift) den).toNat =
      Numerics.roundQuotientEven (num.toNat <<< shift) den.toNat := by
  have hwordFit : num.toNat <<< shift < 2 ^ 64 :=
    lt_trans hnumShiftFit (by norm_num)
  have hshifted :
      (num <<< UInt64.ofNat shift).toNat =
        num.toNat <<< shift :=
    FloatLib.Numerics.FixedWord.shiftLeft_toNat num shift hshift hwordFit
  have hquotientFit :
      (num.toNat <<< shift) / den.toNat + 1 < 2 ^ 64 := by
    have hquotientLe :
        (num.toNat <<< shift) / den.toNat ≤ num.toNat <<< shift :=
      Nat.div_le_self _ _
    omega
  rw [FloatLib.Numerics.FixedWord.roundQuotientEven_toNat _ _ hden]
  · rw [hshifted]
  · simpa [hshifted] using hquotientFit

private theorem roundQuotientEven_den_shift_toNat
    (num den : UInt64) (shift : Nat)
    (hden : den ≠ 0)
    (hshift : shift < 64)
    (hnumFit : num.toNat < 2 ^ 63)
    (hdenShiftFit : den.toNat <<< shift < 2 ^ 63) :
    (FloatLib.Numerics.FixedWord.roundQuotientEven
        num (den <<< UInt64.ofNat shift)).toNat =
      Numerics.roundQuotientEven num.toNat (den.toNat <<< shift) := by
  have hwordFit : den.toNat <<< shift < 2 ^ 64 :=
    lt_trans hdenShiftFit (by norm_num)
  have hshifted :
      (den <<< UInt64.ofNat shift).toNat =
        den.toNat <<< shift :=
    FloatLib.Numerics.FixedWord.shiftLeft_toNat den shift hshift hwordFit
  have hdenNat : den.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hden
  have hshiftedNatNonzero : den.toNat <<< shift ≠ 0 := by
    simp [Nat.shiftLeft_eq, hdenNat]
  have hshiftedNonzero :
      den <<< UInt64.ofNat shift ≠ 0 := by
    intro hzero
    apply hshiftedNatNonzero
    rw [← hshifted, hzero]
    rfl
  have hquotientFit :
      num.toNat / (den.toNat <<< shift) + 1 < 2 ^ 64 := by
    have hquotientLe :
        num.toNat / (den.toNat <<< shift) ≤ num.toNat :=
      Nat.div_le_self _ _
    omega
  rw [FloatLib.Numerics.FixedWord.roundQuotientEven_toNat _ _ hshiftedNonzero]
  · rw [hshifted]
  · simpa [hshifted] using hquotientFit

private theorem roundSubnormalWord_eq
    (sign : Bool) (nativeFraction : UInt64) (genericFraction : Nat)
    (hfraction : nativeFraction.toNat = genericFraction) :
    (if nativeFraction == 0 then
        if sign then (0x80000000 : UInt32) else 0
      else if nativeFraction ≥ 0x800000 then
        mkBits sign 1 0
      else
        mkBits sign 0 nativeFraction.toNat) =
      if genericFraction == 0 then
        if sign then (0x80000000 : UInt32) else 0
      else
        match Nat.decLe (Model.pow2 23) genericFraction with
        | isTrue _ => mkBits sign 1 0
        | isFalse _ => mkBits sign 0 genericFraction := by
  have hzero :
      nativeFraction = 0 ↔ genericFraction = 0 := by
    rw [← UInt64.toNat_inj]
    simp [hfraction]
  have hnormal :
      0x800000 ≤ nativeFraction ↔
        Model.pow2 23 ≤ genericFraction := by
    rw [UInt64.le_iff_toNat_le, hfraction]
    change 8388608 ≤ genericFraction ↔
      Model.pow2 23 ≤ genericFraction
    norm_num [Model.pow2_eq_two_pow]
  by_cases hfzero : nativeFraction = 0
  · have hgenericZero := hzero.mp hfzero
    simp [hfzero, hgenericZero]
  · have hgenericNonzero : genericFraction ≠ 0 :=
      (not_congr hzero).mp hfzero
    by_cases hfnormal : 0x800000 ≤ nativeFraction
    · have hgenericNormal := hnormal.mp hfnormal
      simp only [beq_iff_eq, hfzero, hgenericNonzero, ite_false,
        hfnormal, ite_true]
      cases hdecision : Nat.decLe (Model.pow2 23) genericFraction with
      | isTrue _ => rfl
      | isFalse h => exact (h hgenericNormal).elim
    · have hgenericSubnormal : ¬Model.pow2 23 ≤ genericFraction :=
        (not_congr hnormal).mp hfnormal
      simp only [beq_iff_eq, hfzero, hgenericNonzero, ite_false,
        hfnormal, hfraction]
      cases hdecision : Nat.decLe (Model.pow2 23) genericFraction with
      | isTrue h => exact (hgenericSubnormal h).elim
      | isFalse _ => rfl

private theorem roundNormalWord_eq
    (sign : Bool) (totalExponent : Int)
    (nativeMantissa : UInt64) (genericMantissa : Nat)
    (hmantissa : nativeMantissa.toNat = genericMantissa) :
    (let carry := nativeMantissa == 0x1000000
      let normalizedExponent :=
        if carry then totalExponent + 1 else totalExponent
      let normalizedMantissa :=
        if carry then (0x800000 : UInt64) else nativeMantissa
      if normalizedExponent > 127 then
        if sign then (0xff800000 : UInt32) else 0x7f800000
      else
        mkBits sign (Int.toNat (normalizedExponent + 127))
          (normalizedMantissa.toNat - 0x800000)) =
      (let normalizedExponent :=
        if genericMantissa == Model.pow2 24 then
          totalExponent + 1
        else
          totalExponent
      let normalizedMantissa :=
        if genericMantissa == Model.pow2 24 then
          Model.pow2 23
        else
          genericMantissa
      if normalizedExponent > 127 then
        if sign then (0xff800000 : UInt32) else 0x7f800000
      else
        mkBits sign (Int.toNat (normalizedExponent + 127))
          (normalizedMantissa - Model.pow2 23)) := by
  have hcarry :
      nativeMantissa = 0x1000000 ↔
        genericMantissa = Model.pow2 24 := by
    rw [← UInt64.toNat_inj, hmantissa]
    have hword : (0x1000000 : UInt64).toNat = 16777216 := by
      decide
    rw [hword]
    norm_num [Model.pow2_eq_two_pow]
  by_cases hnativeCarry : nativeMantissa = 0x1000000
  · have hgenericCarry := hcarry.mp hnativeCarry
    have hgenericCarryNat : genericMantissa = 16777216 := by
      simpa [Model.pow2_eq_two_pow] using hgenericCarry
    simp [hnativeCarry, hgenericCarryNat, Model.pow2_eq_two_pow]
  · have hgenericCarry : genericMantissa ≠ Model.pow2 24 :=
      (not_congr hcarry).mp hnativeCarry
    have hgenericCarryNat : genericMantissa ≠ 16777216 := by
      simpa [Model.pow2_eq_two_pow] using hgenericCarry
    simp [hnativeCarry, hgenericCarryNat, hmantissa,
      Model.pow2_eq_two_pow]

/-- Native-word rational rounding agrees with the existing exact binary32 rounder. -/
theorem roundRatScaledWord_eq
    (sign : Bool) (num den : UInt64) (exponent : Int)
    (hnumFit : num.toNat < 2 ^ 24)
    (hdenFit : den.toNat < 2 ^ 24) :
    roundRatScaledWord sign num den exponent =
      NativeBinary32.roundRatScaled sign num.toNat den.toNat exponent := by
  by_cases hdenZero : den = 0
  · simp [roundRatScaledWord, NativeBinary32.roundRatScaled, hdenZero]
  have hdenNatNonzero : den.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hdenZero
  by_cases hnumZero : num = 0
  · simp [roundRatScaledWord, NativeBinary32.roundRatScaled,
      hdenZero, hdenNatNonzero, hnumZero]
  have hnumNatNonzero : num.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hnumZero
  have hfloor := floorLog2RatWord_eq num den hnumZero hdenZero
  unfold roundRatScaledWord NativeBinary32.roundRatScaled
  simp only [beq_iff_eq, hdenZero, hdenNatNonzero, hnumZero,
    hnumNatNonzero, ite_false]
  rw [hfloor]
  by_cases hoverflow :
      Numerics.RationalBinary.floorLog2 num.toNat den.toNat + exponent > 127
  · simp [hoverflow]
  simp only [hoverflow, ite_false]
  by_cases hunderflow :
      Numerics.RationalBinary.floorLog2 num.toNat den.toNat + exponent < -150
  · simp [hunderflow]
  simp only [hunderflow, ite_false]
  by_cases hsubnormal :
      Numerics.RationalBinary.floorLog2 num.toNat den.toNat + exponent < -126
  · simp only [hsubnormal, ite_true]
    have hhighWord :
        floorLog2RatWord num den + exponent < -126 := by
      simpa [hfloor] using hsubnormal
    have hlowWord :
        ¬floorLog2RatWord num den + exponent < -150 := by
      simpa [hfloor] using hunderflow
    cases hscale : exponent + 149 with
    | ofNat shift =>
        have hbounds :=
          subnormal_num_shift_bounds num den exponent shift
            hnumZero hdenZero hnumFit hdenFit hscale hhighWord
        have hfraction :=
          roundQuotientEven_num_shift_toNat num den shift hdenZero
            hbounds.1 hbounds.2
        convert roundSubnormalWord_eq sign
            (FloatLib.Numerics.FixedWord.roundQuotientEven
              (num <<< UInt64.ofNat shift) den)
            (Numerics.roundQuotientEven
              (num.toNat <<< shift) den.toNat)
            hfraction using 1
        all_goals
          simp [Numerics.RationalBinary.scaleByPowerOfTwo,
            Numerics.RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq] <;>
            split <;> rfl
    | negSucc shift =>
        have hbounds :=
          subnormal_den_shift_bounds num den exponent shift
            hnumZero hdenZero hnumFit hdenFit hscale hlowWord
        have hnumFit63 : num.toNat < 2 ^ 63 :=
          lt_trans hnumFit (by norm_num)
        have hfraction :=
          roundQuotientEven_den_shift_toNat num den (shift + 1)
            hdenZero hbounds.1 hnumFit63 hbounds.2
        convert roundSubnormalWord_eq sign
            (FloatLib.Numerics.FixedWord.roundQuotientEven num
              (den <<< UInt64.ofNat (shift + 1)))
            (Numerics.roundQuotientEven num.toNat
              (den.toNat <<< (shift + 1)))
            hfraction using 1
        all_goals
          simp [Numerics.RationalBinary.scaleByPowerOfTwo,
            Numerics.RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq] <;>
            split <;> rfl
  · simp only [hsubnormal, ite_false]
    let rationalExponent :=
      Numerics.RationalBinary.floorLog2 num.toNat den.toNat
    let shift := Int.toNat (23 - rationalExponent)
    have hbounds :
        shift < 64 ∧ num.toNat <<< shift < 2 ^ 63 := by
      simpa [rationalExponent, shift, hfloor,
        show FloatFormat.binary32.fracWidth = 23 by
          decide] using
        (NativeWordQuotient.normalShift_bounds
          FloatFormat.binary32 num den hnumZero hdenZero hnumFit hdenFit
          (by decide))
    have hfraction :=
      roundQuotientEven_num_shift_toNat num den shift hdenZero
        hbounds.1 hbounds.2
    have hshiftInt :
        Int.ofNat shift = 23 - rationalExponent := by
      simpa [shift, rationalExponent, hfloor,
        show FloatFormat.binary32.fracWidth = 23 by
          decide] using
        (NativeWordQuotient.normalShift_eq
          FloatFormat.binary32 num den hnumZero hnumFit)
    have hscale :
        23 - Numerics.RationalBinary.floorLog2 num.toNat den.toNat =
          Int.ofNat shift := by
      simpa [rationalExponent] using hshiftInt.symm
    simp only [hscale, Numerics.RationalBinary.scaleByPowerOfTwo]
    have htoNat : (Int.ofNat shift).toNat = shift := rfl
    rw [htoNat]
    have hnatShift :
        num.toNat.shiftLeft shift = num.toNat <<< shift := by
      rfl
    rw [hnatShift]
    simpa only [beq_iff_eq, rationalExponent] using
      roundNormalWord_eq sign
        (rationalExponent + exponent)
        (FloatLib.Numerics.FixedWord.roundQuotientEven
          (num <<< UInt64.ofNat shift) den)
        (Numerics.roundQuotientEven
          (num.toNat <<< shift) den.toNat)
        hfraction

/-- The one-word finite division kernel equals the generic exact-rational implementation. -/
theorem divFiniteImpl_eq (x y : Value) :
    divFiniteImplOption x y = divFiniteOption x y := by
  unfold divFiniteImplOption divFiniteOption
  rw [toDyadic_eq_finiteComponents x, toDyadic_eq_finiteComponents y]
  dsimp only
  simp only [Bool.or_eq_true, beq_iff_eq]
  set xExponent := expField (toUInt32 x) with hxExponent
  set yExponent := expField (toUInt32 y) with hyExponent
  set xFraction := fracField (toUInt32 x) with hxFraction
  set yFraction := fracField (toUInt32 y) with hyFraction
  set xMantissa : UInt64 := finiteMantissa xExponent xFraction with hxMantissa
  set yMantissa : UInt64 := finiteMantissa yExponent yFraction with hyMantissa
  set xScale : UInt64 := finiteScale xExponent with hxScale
  set yScale : UInt64 := finiteScale yExponent with hyScale
  by_cases hxExceptional : xExponent = 0xff
  · simp [hxExceptional]
  by_cases hyExceptional : yExponent = 0xff
  · simp [hxExceptional, hyExceptional]
  by_cases hyZero : yMantissa = 0
  · by_cases hxZero : xMantissa = 0
    · simp [hxExceptional, hyExceptional, hxZero, hyZero]
    · have hxNatNonzero : xMantissa.toNat ≠ 0 := by
        intro h
        apply hxZero
        apply UInt64.toNat_inj.mp
        simpa using h
      simp [hxExceptional, hyExceptional, hxZero, hyZero, hxNatNonzero]
  by_cases hxZero : xMantissa = 0
  · have hyNatNonzero : yMantissa.toNat ≠ 0 := by
      intro h
      apply hyZero
      apply UInt64.toNat_inj.mp
      simpa using h
    simp [hxExceptional, hyExceptional, hxZero, hyZero, hyNatNonzero]
  have hxNatNonzero : xMantissa.toNat ≠ 0 := by
    exact
      (FloatLib.Numerics.FixedWord.uint64_toNat_eq_zero xMantissa).not.mpr hxZero
  have hyNatNonzero : yMantissa.toNat ≠ 0 :=
    (FloatLib.Numerics.FixedWord.uint64_toNat_eq_zero yMantissa).not.mpr hyZero
  simp only [hxExceptional, hyExceptional, hxZero, hyZero, hxNatNonzero,
    hyNatNonzero, ite_false]
  have hxMantissaLt :=
    finiteMantissa_lt_of_components x hxExponent hxFraction hxMantissa
  have hyMantissaLt :=
    finiteMantissa_lt_of_components y hyExponent hyFraction hyMantissa
  have hexponent :
      Int.ofNat xScale.toNat - Int.ofNat yScale.toNat =
        (Int.ofNat xScale.toNat - 149) -
          (Int.ofNat yScale.toNat - 149) := by
    omega
  rw [hexponent]
  exact congrArg (fun bits => some (ofUInt32 bits)) <|
    roundRatScaledWord_eq
      (Bool.xor (signBit (toUInt32 x)) (signBit (toUInt32 y)))
      xMantissa yMantissa
      ((Int.ofNat xScale.toNat - 149) -
        (Int.ofNat yScale.toNat - 149))
      hxMantissaLt hyMantissaLt

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
