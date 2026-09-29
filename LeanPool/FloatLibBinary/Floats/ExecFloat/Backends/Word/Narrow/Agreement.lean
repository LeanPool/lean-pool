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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.DivisionReference
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Addition.Runtime -- shake: keep
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Fma.Runtime -- shake: keep
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Multiplication.Runtime -- shake: keep
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Addition.Proof -- shake: keep
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Fma.Proof -- shake: keep
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Multiplication.Proof -- shake: keep
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Base.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Decode

/-!
# Agreement between native binary32 words and the generic model

The narrow-word core implements finite binary32 arithmetic with `UInt32` and `UInt64`. This module
contains the proof-side bridge back to the generic `Model FloatFormat.binary32` representation:
field packing, decoding, rounding, and the shared finite-operation specifications.

The operation-specific `Addition`, `Multiplication`, and `Fma` proof modules connect their native
implementations to the finite specifications used here. Together, these results connect native
arithmetic to the generic binary32 model. Runtime clients can import the corresponding `Runtime`
modules without this proof development.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- Native and generic binary32 field packing produce the same storage word. -/
theorem toUInt32_ofFields (sign : Bool) (exponent fraction : Nat) :
    toUInt32 (Model.ofFields FloatFormat.binary32 sign exponent fraction) =
      mkBits sign exponent fraction := by
  apply UInt32.toBitVec_inj.1
  cases sign <;> rfl

/-- Rewrapping native field packing equals generic `Model.ofFields`. -/
theorem ofUInt32_mkBits (sign : Bool) (exponent fraction : Nat) :
    ofUInt32 (mkBits sign exponent fraction) =
      Model.ofFields FloatFormat.binary32 sign exponent fraction := by
  rw [← toUInt32_ofFields]
  exact ofUInt32_toUInt32 _

/-- Native and generic binary32 exponent extraction have the same natural-number value. -/
theorem expField_toNat (x : Value) :
    (expField (toUInt32 x)).toNat = Model.expField x := by
  rfl

/-- Native and generic binary32 fraction extraction have the same natural-number value. -/
theorem fracField_toNat (x : Value) :
    (fracField (toUInt32 x)).toNat = Model.fracField x := by
  rfl

/-- Native and generic binary32 sign extraction agree. -/
theorem signBit_eq (x : Value) :
    signBit (toUInt32 x) = Model.signBit x := by
  unfold signBit toUInt32 Model.signBit
  have hbits :
      (UInt32.ofBitVec x.bits &&& 0x80000000).toBitVec =
        x.bits &&& FloatFormat.binary32.signMask := by
    rfl
  apply Bool.eq_iff_iff.mpr
  rw [bne_iff_ne, bne_iff_ne]
  constructor
  · intro hNative hGeneric
    apply hNative
    apply UInt32.toBitVec_inj.mp
    rw [hbits, hGeneric, UInt32.toBitVec_zero]
    rfl
  · intro hGeneric hNative
    apply hGeneric
    rw [← hbits, hNative, UInt32.toBitVec_zero]
    rfl

/-- Native and generic binary32 exponent zero tests agree. -/
theorem expField_beq_zero (x : Value) :
    (expField (toUInt32 x) == 0) = (Model.expField x == 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq, ← expField_toNat x]
  exact UInt32.toNat_inj.symm

/-- Native and generic binary32 exceptional-exponent tests agree. -/
theorem expField_beq_allOnes (x : Value) :
    (expField (toUInt32 x) == 0xff) = (Model.expField x == 255) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq, ← expField_toNat x]
  exact UInt32.toNat_inj.symm

/-- Native and generic binary32 fraction zero tests agree. -/
theorem fracField_beq_zero (x : Value) :
    (fracField (toUInt32 x) == 0) = (Model.fracField x == 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq, ← fracField_toNat x]
  exact UInt32.toNat_inj.symm

private theorem isNaN_or_isInf_eq_expAllOnes (x : Value) :
    (Model.IEEE.isNaN x || Model.IEEE.isInf x) =
      (Model.expField x == 255) := by
  unfold Model.IEEE.isNaN Model.IEEE.isInf
  simp only [show FloatFormat.binary32.expAllOnesNat = 255 by decide]
  by_cases hexponent : Model.expField x = 255
  · rw [show (Model.expField x == 255) = true from beq_iff_eq.mpr hexponent]
    by_cases hfraction : Model.fracField x = 0
    · rw [show (Model.fracField x != 0) = false from
          bne_eq_false_iff_eq.mpr hfraction]
      rw [show (Model.fracField x == 0) = true from beq_iff_eq.mpr hfraction]
      rfl
    · rw [show (Model.fracField x != 0) = true from bne_iff_ne.mpr hfraction]
      rw [show (Model.fracField x == 0) = false from
          beq_eq_false_iff_ne.mpr hfraction]
      rfl
  · rw [show (Model.expField x == 255) = false from
        beq_eq_false_iff_ne.mpr hexponent]
    rfl

/-- Native field extraction decodes the same exact dyadic as generic binary32. -/
theorem toDyadic_eq (x : Value) :
    toDyadicOption (toUInt32 x) = Model.toDyadicOption x := by
  unfold toDyadicOption Model.toDyadicOption
  simp only [show FloatFormat.binary32.isIEEE = true by decide]
  unfold Model.ieeeToDyadicOption
  let exponent := expField (toUInt32 x)
  let fraction := fracField (toUInt32 x)
  have hexponent : exponent.toNat = Model.expField x := expField_toNat x
  have hfraction : fraction.toNat = Model.fracField x := fracField_toNat x
  have hsign := signBit_eq x
  change
    (if exponent == 0xff then none
      else
        let sign := signBit (toUInt32 x)
        if exponent == 0 then
          if fraction == 0 then
            some ({ negative := sign, significand := 0, exponent := 0 } : Numerics.Dyadic)
          else
            some
              ({ negative := sign
                 significand := fraction.toNat
                 exponent := -149 } : Numerics.Dyadic)
        else
          some ({
            negative := sign
            significand := Model.pow2 23 + fraction.toNat
            exponent := Int.ofNat exponent.toNat - 150 } : Numerics.Dyadic)) =
      _
  simp only [show FloatFormat.binary32.fracWidth = 23 by decide,
    show FloatFormat.binary32.ieeeMinSubnormalExponent = -149 by decide]
  have hexceptional :
      (exponent == 0xff) = (Model.expField x == 255) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, beq_iff_eq, ← hexponent]
    exact UInt32.toNat_inj.symm
  have hexponentZero :
      (exponent == 0) = (Model.expField x == 0) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, beq_iff_eq, ← hexponent]
    exact UInt32.toNat_inj.symm
  have hfractionZero :
      (fraction == 0) = (Model.fracField x == 0) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, beq_iff_eq, ← hfraction]
    exact UInt32.toNat_inj.symm
  rw [hexceptional, hexponentZero, hfractionZero]
  rw [isNaN_or_isInf_eq_expAllOnes]
  rw [hsign, hexponent, hfraction]
  rfl

private theorem ofUInt32_posZero :
    ofUInt32 0 = Model.posZero FloatFormat.binary32 :=
  rfl

private theorem ofUInt32_negZero :
    ofUInt32 0x80000000 = Model.negZero FloatFormat.binary32 := by
  decide

private theorem ofUInt32_posInf :
    ofUInt32 0x7f800000 = Model.posInf FloatFormat.binary32 := by
  decide

private theorem ofUInt32_negInf :
    ofUInt32 0xff800000 = Model.negInf FloatFormat.binary32 := by
  decide

private theorem ofUInt32_canonicalNaN :
    ofUInt32 0x7fc00000 = Model.canonicalNaN FloatFormat.binary32 := by
  decide

private theorem ofUInt32_signedZero (sign : Bool) :
    ofUInt32 (if sign then 0x80000000 else 0) =
      if sign then Model.negZero FloatFormat.binary32
      else Model.posZero FloatFormat.binary32 := by
  cases sign <;> simp [ofUInt32_posZero, ofUInt32_negZero]

private theorem ofUInt32_signedInf (sign : Bool) :
    ofUInt32 (if sign then 0xff800000 else 0x7f800000) =
      if sign then Model.negInf FloatFormat.binary32
      else Model.posInf FloatFormat.binary32 := by
  cases sign <;> simp [ofUInt32_posInf, ofUInt32_negInf]

private theorem binary32_fracWidth :
    FloatFormat.binary32.fracWidth = 23 := by
  decide

private theorem binary32_maxNormalUnbiasedExp :
    FloatFormat.binary32.ieeeMaxNormalExponent = 127 := by
  decide

private theorem binary32_minNormalUnbiasedExp :
    FloatFormat.binary32.ieeeMinNormalExponent = -126 := by
  decide

private theorem binary32_subnormalAlignExp :
    FloatFormat.binary32.subnormalAlignExp = 149 := by
  decide

private theorem binary32_normalMantissaExpOffset :
    FloatFormat.binary32.normalMantissaExpOffset = 150 := by
  decide

private theorem binary32_bias :
    FloatFormat.binary32.bias = 127 := by
  decide

/-- Native rational rounding agrees with generic binary32 rational rounding. -/
theorem ofUInt32_roundRatScaled (sign : Bool) (num den : Nat) (exponent : Int) :
    ofUInt32 (roundRatScaled sign num den exponent) =
      Model.roundRatScaled FloatFormat.binary32 sign num den exponent := by
  unfold roundRatScaled Model.roundRatScaled Model.ieeeRoundRatScaled
  simp only [show FloatFormat.binary32.isIEEE = true by decide]
  simp only [binary32_fracWidth, binary32_maxNormalUnbiasedExp,
    binary32_minNormalUnbiasedExp, binary32_subnormalAlignExp,
    binary32_normalMantissaExpOffset, binary32_bias]
  norm_num
  split_ifs <;>
    simp only [ofUInt32_canonicalNaN, ofUInt32_negZero, ofUInt32_posZero, ofUInt32_negInf,
      ofUInt32_posInf, Int.ofNat_eq_natCast, tsub_self, ofUInt32_mkBits]
  split <;>
    rw [binary32_fracWidth, binary32_subnormalAlignExp] <;>
    simp_all [ofUInt32_mkBits]

/-- Native dyadic rounding agrees with generic binary32 rounding. -/
theorem ofUInt32_roundDyadic (value : Numerics.Dyadic) :
    ofUInt32 (roundDyadic value) =
      Model.roundDyadic FloatFormat.binary32 value := by
  rw [Model.roundDyadic_eq_roundDyadicImpl]
  unfold roundDyadic
  simp only [beq_iff_eq]
  by_cases hmantissa : value.significand = 0
  · rw [ite_eq_left hmantissa]
    have himpl :
        Model.roundDyadicImpl FloatFormat.binary32 value =
          if value.negative then Model.negZero FloatFormat.binary32
          else Model.posZero FloatFormat.binary32 := by
      unfold Model.roundDyadicImpl Model.ieeeRoundDyadicImpl
      simp only [show FloatFormat.binary32.isIEEE = true by decide, ite_true]
      simp only [beq_iff_eq, hmantissa, ite_eq_left]
    rw [himpl]
    exact ofUInt32_signedZero value.negative
  · rw [ite_eq_right hmantissa]
    let totalExponent := (value.significand.log2 : Int) + value.exponent
    by_cases hsubnormal : totalExponent < -126
    · have hsubnormal' :
          (value.significand.log2 : Int) + value.exponent < -126 := by
        simpa [totalExponent] using hsubnormal
      let fraction :=
        match value.exponent + 149 with
        | .ofNat shift => value.significand <<< shift
        | .negSucc shift => Numerics.roundShiftRightEven value.significand (shift + 1)
      have himpl :
          Model.roundDyadicImpl FloatFormat.binary32 value =
            if fraction = 0 then
              if value.negative then Model.negZero FloatFormat.binary32
              else Model.posZero FloatFormat.binary32
            else if fraction = Model.pow2 23 then
              Model.ofFields FloatFormat.binary32 value.negative 1 0
            else
              Model.ofFields FloatFormat.binary32 value.negative 0 fraction := by
        unfold Model.roundDyadicImpl Model.ieeeRoundDyadicImpl
        simp only [show FloatFormat.binary32.isIEEE = true by decide, ite_true]
        simp only [binary32_fracWidth, binary32_maxNormalUnbiasedExp,
          binary32_minNormalUnbiasedExp, binary32_bias,
          beq_iff_eq, hmantissa, ite_false]
        rw [ite_eq_left hsubnormal']
        rfl
      rw [himpl]
      have hsubnormalNative :
          Int.ofNat value.significand.log2 + value.exponent < -126 := by
        simpa [totalExponent] using hsubnormal
      simp only [hsubnormalNative, ite_eq_left]
      change
        ofUInt32
            (if fraction = 0 then
              if value.negative then 0x80000000 else 0
            else if fraction = Model.pow2 23 then
              mkBits value.negative 1 0
            else
              mkBits value.negative 0 fraction) =
          if fraction = 0 then
            if value.negative then Model.negZero FloatFormat.binary32
            else Model.posZero FloatFormat.binary32
          else if fraction = Model.pow2 23 then
            Model.ofFields FloatFormat.binary32 value.negative 1 0
          else
            Model.ofFields FloatFormat.binary32 value.negative 0 fraction
      by_cases hfractionZero : fraction = 0
      · rw [ite_eq_left hfractionZero, ite_eq_left hfractionZero]
        exact ofUInt32_signedZero value.negative
      · rw [ite_eq_right hfractionZero, ite_eq_right hfractionZero]
        by_cases hfractionNormal : fraction = Model.pow2 23
        · rw [ite_eq_left hfractionNormal, ite_eq_left hfractionNormal]
          exact ofUInt32_mkBits value.negative 1 0
        · rw [ite_eq_right hfractionNormal, ite_eq_right hfractionNormal]
          exact ofUInt32_mkBits value.negative 0 fraction
    · have hsubnormal' :
          ¬(value.significand.log2 : Int) + value.exponent < -126 := by
        simpa [totalExponent] using hsubnormal
      let roundedMantissa :=
        if 23 ≤ value.significand.log2 then
          Numerics.roundShiftRightEven value.significand (value.significand.log2 - 23)
        else
          value.significand <<< (23 - value.significand.log2)
      let normalizedExponent :=
        if roundedMantissa = Model.pow2 24 then totalExponent + 1
        else totalExponent
      let normalizedMantissa :=
        if roundedMantissa = Model.pow2 24 then Model.pow2 23
        else roundedMantissa
      have himpl :
          Model.roundDyadicImpl FloatFormat.binary32 value =
            if normalizedExponent > 127 then
              if value.negative then Model.negInf FloatFormat.binary32
              else Model.posInf FloatFormat.binary32
            else
              Model.ofFields FloatFormat.binary32 value.negative
                (Int.toNat (normalizedExponent + 127))
                (normalizedMantissa - Model.pow2 23) := by
        unfold Model.roundDyadicImpl Model.ieeeRoundDyadicImpl
        simp only [show FloatFormat.binary32.isIEEE = true by decide, ite_true]
        simp only [binary32_fracWidth, binary32_maxNormalUnbiasedExp,
          binary32_minNormalUnbiasedExp, binary32_bias,
          beq_iff_eq, hmantissa, ite_false]
        rw [ite_eq_right hsubnormal']
        rfl
      rw [himpl]
      have hsubnormalNative :
          ¬Int.ofNat value.significand.log2 + value.exponent < -126 := by
        simpa [totalExponent] using hsubnormal
      simp only [hsubnormalNative, ite_false]
      change
        ofUInt32
            (if normalizedExponent > 127 then
              if value.negative then 0xff800000 else 0x7f800000
            else
              mkBits value.negative (Int.toNat (normalizedExponent + 127))
                (normalizedMantissa - Model.pow2 23)) =
          if normalizedExponent > 127 then
            if value.negative then Model.negInf FloatFormat.binary32
            else Model.posInf FloatFormat.binary32
          else
            Model.ofFields FloatFormat.binary32 value.negative
              (Int.toNat (normalizedExponent + 127))
              (normalizedMantissa - Model.pow2 23)
      by_cases hoverflow : normalizedExponent > 127
      · rw [ite_eq_left hoverflow, ite_eq_left hoverflow]
        exact ofUInt32_signedInf value.negative
      · rw [ite_eq_right hoverflow, ite_eq_right hoverflow]
        exact ofUInt32_mkBits value.negative
          (Int.toNat (normalizedExponent + 127))
          (normalizedMantissa - Model.pow2 23)

/-- The native finite add result is exactly the generic finite add result. -/
theorem addFinite_eq (x y : Value) :
    addFiniteOption x y =
      match Model.toDyadicOption x, Model.toDyadicOption y with
      | some dx, some dy =>
          some (Model.roundDyadic FloatFormat.binary32 (Model.addDyadic dx dy))
      | _, _ => none := by
  unfold addFiniteOption
  rw [toDyadic_eq, toDyadic_eq]
  cases hx : Model.toDyadicOption x <;>
    cases hy : Model.toDyadicOption y <;>
    simp [ofUInt32_roundDyadic]

/-- The native finite multiply result is exactly the generic finite multiply result. -/
theorem mulFinite_eq (x y : Value) :
    mulFiniteOption x y =
      match Model.toDyadicOption x, Model.toDyadicOption y with
      | some dx, some dy =>
          let sign := Bool.xor dx.negative dy.negative
          if dx.significand == 0 || dy.significand == 0 then
            some (if sign then Model.negZero FloatFormat.binary32
              else Model.posZero FloatFormat.binary32)
          else
            some (Model.roundDyadic FloatFormat.binary32 {
              negative := sign
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent })
      | _, _ => none := by
  unfold mulFiniteOption
  rw [toDyadic_eq, toDyadic_eq]
  cases hx : Model.toDyadicOption x with
  | none =>
      cases hy : Model.toDyadicOption y <;> rfl
  | some dx =>
      cases hy : Model.toDyadicOption y with
      | none => rfl
      | some dy =>
          dsimp only
          by_cases hzero : dx.significand = 0 ∨ dy.significand = 0
          · simp only [beq_iff_eq, Bool.or_eq_true, hzero, ite_eq_left]
            exact congrArg some (ofUInt32_signedZero (Bool.xor dx.negative dy.negative))
          · simp only [beq_iff_eq, Bool.or_eq_true, hzero, ite_false]
            exact congrArg some (ofUInt32_roundDyadic {
              negative := Bool.xor dx.negative dy.negative,
              significand := dx.significand * dy.significand,
              exponent := dx.exponent + dy.exponent })

/-- The native finite divide result is exactly the generic finite divide result. -/
theorem divFinite_eq (x y : Value) :
    divFiniteOption x y =
      match Model.toDyadicOption x, Model.toDyadicOption y with
      | some dx, some dy =>
          let sign := Bool.xor dx.negative dy.negative
          some <|
            if dy.significand == 0 then
              if dx.significand == 0 then Model.canonicalNaN FloatFormat.binary32
              else if sign then Model.negInf FloatFormat.binary32
              else Model.posInf FloatFormat.binary32
            else if dx.significand == 0 then
              if sign then Model.negZero FloatFormat.binary32
              else Model.posZero FloatFormat.binary32
            else
              Model.roundRatScaled FloatFormat.binary32
                sign dx.significand dy.significand (dx.exponent - dy.exponent)
      | _, _ => none := by
  unfold divFiniteOption
  rw [toDyadic_eq, toDyadic_eq]
  cases hx : Model.toDyadicOption x with
  | none =>
      cases hy : Model.toDyadicOption y <;> rfl
  | some dx =>
      cases hy : Model.toDyadicOption y with
      | none => rfl
      | some dy =>
          dsimp only
          by_cases hyzero : dy.significand = 0
          · simp only [beq_iff_eq, hyzero, ite_eq_left]
            by_cases hxzero : dx.significand = 0
            · simp only [hxzero, ite_eq_left, ofUInt32_canonicalNaN]
            · simp only [hxzero, ite_false]
              exact congrArg some (ofUInt32_signedInf (Bool.xor dx.negative dy.negative))
          · simp only [beq_iff_eq, hyzero, ite_false]
            by_cases hxzero : dx.significand = 0
            · simp only [hxzero, ite_eq_left]
              exact congrArg some (ofUInt32_signedZero (Bool.xor dx.negative dy.negative))
            · simp only [hxzero, ite_false, ofUInt32_roundRatScaled]

/-- The native finite fused multiply-add result is exactly the generic finite result. -/
theorem fmaFinite_eq (x y z : Value) :
    fmaFiniteOption x y z =
      match Model.toDyadicOption x, Model.toDyadicOption y, Model.toDyadicOption z with
      | some dx, some dy, some dz =>
          let product : Numerics.Dyadic := {
            negative := Bool.xor dx.negative dy.negative,
            significand := dx.significand * dy.significand,
            exponent := dx.exponent + dy.exponent }
          some (Model.roundDyadic FloatFormat.binary32
            (Model.addDyadic product dz))
      | _, _, _ => none := by
  unfold fmaFiniteOption
  rw [toDyadic_eq, toDyadic_eq, toDyadic_eq]
  cases hx : Model.toDyadicOption x <;>
    cases hy : Model.toDyadicOption y <;>
    cases hz : Model.toDyadicOption z <;>
    simp [ofUInt32_roundDyadic]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
