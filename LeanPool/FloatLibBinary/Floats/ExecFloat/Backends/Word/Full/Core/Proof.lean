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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Core.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Proof
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Native-storage finite arithmetic for binary64

Native binary64 field decoding agrees with the generic finite decoder, and accepted two-limb
products agree with exact nearest-even rounding. The public value remains `Model
FloatFormat.binary64`.

A product of normal significands needs at most 106 bits. The multiplication path keeps it in two
`UInt64` limbs through normalization and rounding. The finite adapters defined here supply the
shared-kernel baseline for addition, division, and fused multiply-add; their specialized paths
are proved in the corresponding operation modules.

Non-finite policy remains in `Model.Arithmetic`; finite entry points return `none` whenever an
operand has an all-ones exponent.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord

/-- Repacking the stored word returns the value. -/
@[simp] theorem ofUInt64_toUInt64 (x : Value) :
    ofUInt64 (toUInt64 x) = x := by
  cases x
  rfl

/-- Unpacking a freshly packed word returns the word. -/
@[simp] theorem toUInt64_ofUInt64 (bits : UInt64) :
    toUInt64 (ofUInt64 bits) = bits :=
  rfl

/-- Packing natural-number fields through native words agrees with the binary64 model. -/
theorem packFieldsWord_eq_ofNat
    (sign : Bool) (exponent fraction : Nat) :
    ofUInt64
        (packFieldsWord sign (UInt64.ofNat exponent)
          (UInt64.ofNat fraction)) =
      Model.ofFields FloatFormat.binary64 sign exponent fraction := by
  have hword :
      toUInt64
          (Model.ofFields FloatFormat.binary64 sign exponent fraction) =
        packFieldsWord sign (UInt64.ofNat exponent)
          (UInt64.ofNat fraction) := by
    apply UInt64.toBitVec_inj.1
    cases sign <;> rfl
  rw [← hword]
  exact ofUInt64_toUInt64 _

/-- Word negation is the model sign flip. -/
@[simp] theorem negate_eq (x : Value) :
    negate x = Model.neg x := by
  cases x
  rfl

/-- Negation is an involution on binary64 words. -/
theorem negate_negate (x : Value) :
    negate (negate x) = x := by
  rw [negate_eq, negate_eq]
  rw [Model.neg_eq_toggleSign_of_supportsSignedZero _ (by decide),
    Model.neg_eq_toggleSign_of_supportsSignedZero _ (by decide)]
  exact Model.toggleSign_toggleSign x

/-- Reference finite multiplication through the compact native decoder. -/
private def mulFiniteSpecOption (x y : Value) : Option Value :=
  match decodeOption x, decodeOption y with
  | some dx, some dy =>
      some <| FiniteProductRound.round FloatFormat.binary64
        (Bool.xor dx.sign dy.sign)
        (dx.mantissa * dy.mantissa)
        (FiniteKernel.scale dx.exponent + FiniteKernel.scale dy.exponent)
  | _, _ => none

/-- Native and generic binary64 exponent extraction have the same natural-number value. -/
theorem expField_toNat (x : Value) :
    (expField (toUInt64 x)).toNat = Model.expField x := by
  rfl

/-- Native and generic binary64 fraction extraction have the same natural-number value. -/
theorem fracField_toNat (x : Value) :
    (fracField (toUInt64 x)).toNat = Model.fracField x := by
  rfl

/-- Native and generic binary64 sign extraction agree. -/
theorem signBit_eq (x : Value) :
    signBit (toUInt64 x) = Model.signBit x := by
  unfold signBit toUInt64 Model.signBit
  change
    ((UInt64.ofBitVec x.bits &&& 0x8000000000000000) != 0) =
      (((show BitVec 64 from x.bits) &&&
        (0x8000000000000000 : UInt64).toBitVec) != 0)
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  constructor
  · intro hNative hGeneric
    apply hNative
    apply UInt64.toBitVec_inj.mp
    simpa using hGeneric
  · intro hGeneric hNative
    apply hGeneric
    have h := congrArg UInt64.toBitVec hNative
    simpa using h

/-- The binary64 fraction field has 52 explicit bits. -/
theorem binary64_fracWidth :
    FloatFormat.binary64.fracWidth = 52 := by
  decide

private theorem binary64_expAllOnesNat :
    FloatFormat.expAllOnesNat FloatFormat.binary64 = 2047 := by
  decide

/-- A decoded binary64 fraction fits in its 52-bit field. -/
theorem fracField_lt (x : Value) :
    (fracField (toUInt64 x)).toNat < 2 ^ 52 := by
  change Model.fracField x < 2 ^ 52
  simpa only [show FloatFormat.binary64.fracWidth = 52 by decide] using
    Model.fracField_lt_pow2 x

/-- A decoded binary64 exponent fits in its 11-bit field. -/
theorem expField_lt (x : Value) :
    (expField (toUInt64 x)).toNat < 2 ^ 11 := by
  change Model.expField x < 2 ^ 11
  simpa only [show FloatFormat.binary64.expWidth = 11 by decide] using
    Model.expField_lt_pow2 x

/-- A nonzero, nonexceptional native exponent is in the binary64 normal range. -/
theorem normalExponent_bounds (x : Value)
    (hnonzero : expField (toUInt64 x) ≠ 0)
    (hnotAllOnes : expField (toUInt64 x) ≠ 0x7ff) :
    0 < (expField (toUInt64 x)).toNat ∧
      (expField (toUInt64 x)).toNat < 2047 := by
  have hnonzeroModel : Model.expField x ≠ 0 := by
    rw [← expField_toNat x]
    intro h
    apply hnonzero
    apply UInt64.toNat_inj.mp
    simpa using h
  have hnotAllOnesModel :
      Model.expField x ≠ FloatFormat.binary64.expAllOnesNat := by
    rw [binary64_expAllOnesNat, ← expField_toNat x]
    intro h
    apply hnotAllOnes
    apply UInt64.toNat_inj.mp
    simpa using h
  have hbounds :=
    Model.expField_interior_bounds x hnonzeroModel hnotAllOnesModel
  simpa only [← expField_toNat x, binary64_expAllOnesNat] using hbounds

/-- Interpret normal binary64 finite-kernel components as their exact dyadic value. -/
theorem normalComponents_toDyadic
    (sign : Bool) (exponent mantissa : Nat)
    (hexponent : exponent ≠ 0) (hmantissa : mantissa ≠ 0) :
    FiniteKernel.Components.toDyadic FloatFormat.binary64 {
        sign
        exponent
        mantissa } =
      { negative := sign
        significand := mantissa
        exponent := Int.ofNat exponent - 1075 } := by
  simp [FiniteKernel.Components.toDyadic, FiniteKernel.dyadicExponent,
    FloatFormat.binary64, hexponent, hmantissa]
  omega

/-- Normalize the scale used by binary64 product-round kernels. -/
theorem roundScaleExponent (exponent : Nat) :
    Int.ofNat (exponent + 1073) -
        Int.ofNat
          (2 * FloatFormat.ieeeSubnormalAlignExp FloatFormat.binary64) =
      Int.ofNat exponent - 1075 := by
  change
    Int.ofNat (exponent + 1073) - Int.ofNat (2 * 1074) =
      Int.ofNat exponent - 1075
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  omega

/-- Natural-number view of the decoded finite binary64 significand. -/
theorem finiteMantissa_toNat
    (exponent fraction : UInt64) (hfraction : fraction.toNat < 2 ^ 52) :
    (finiteMantissa exponent fraction).toNat =
      if exponent = 0 then fraction.toNat
      else Model.pow2 52 + fraction.toNat := by
  by_cases hexponent : exponent = 0
  · simp [finiteMantissa, hexponent]
  · simp only [finiteMantissa, beq_iff_eq, hexponent, ite_false, UInt64.toNat_or]
    rw [show (0x0010000000000000 : UInt64).toNat = 2 ^ 52 by decide]
    rw [Nat.or_two_pow_eq_add_of_lt hfraction]
    rw [Model.pow2_eq_two_pow, Nat.add_comm]

/-- Every decoded normal binary64 significand has exactly 53 significant bits. -/
theorem finiteMantissa_bounds
    (exponent fraction : UInt64) (hexponent : exponent ≠ 0)
    (hfraction : fraction.toNat < 2 ^ 52) :
    2 ^ 52 ≤ (finiteMantissa exponent fraction).toNat ∧
      (finiteMantissa exponent fraction).toNat < 2 ^ 53 := by
  rw [finiteMantissa_toNat exponent fraction hfraction]
  simp only [ite_eq_right hexponent, Model.pow2_eq_two_pow]
  omega

/-- Every decoded binary64 significand, normal or subnormal, has at most 53 significant bits. -/
theorem finiteMantissa_lt
    (exponent fraction : UInt64) (hfraction : fraction.toNat < 2 ^ 52) :
    (finiteMantissa exponent fraction).toNat < 2 ^ 53 := by
  rw [finiteMantissa_toNat exponent fraction hfraction]
  split
  · omega
  · rw [Model.pow2_eq_two_pow]
    omega

/-- Every finite binary64 exponent field decodes to a scale of at most 2045. -/
theorem finiteScale_le
    (exponent : UInt64) (hexponent : exponent.toNat < 2 ^ 11) (hfinite : exponent ≠ 0x7ff) :
    (finiteScale exponent).toNat ≤ 2045 := by
  rw [finiteScale_toNat]
  split
  · omega
  · have hnot2047 : exponent.toNat ≠ 2047 := fun h =>
      hfinite (UInt64.toNat_inj.mp (by simpa using h))
    norm_num at hexponent
    omega

/--
Decoding a finite native binary64 value exposes the fields used by the generic finite kernels.

An all-ones exponent characterizes non-finite values, so callers that have ruled out that
exponent can replace the optional decoder with these concrete components.
-/
theorem decode_of_finiteExponent (x : Value)
    (hfinite : expField (toUInt64 x) ≠ 0x7ff) :
    decodeOption x =
      some {
        sign := signBit (toUInt64 x)
        exponent := (expField (toUInt64 x)).toNat
        mantissa :=
          (finiteMantissa (expField (toUInt64 x))
            (fracField (toUInt64 x))).toNat } := by
  unfold decodeOption
  simp [hfinite]

private theorem highLimb_lt_shift (product : UInt128) (leading : UInt64)
  (hleading : leading.toNat = product.toNat.log2) (hproductNe : product.toNat ≠ 0)
  (hshift : (leading - 52).toNat = product.toNat.log2 - 52) : product.hi.toNat < 2 ^ (leading -
    52).toNat := by
  have hupper :
      product.toNat < 2 ^ (leading.toNat + 1) := by
    have hbounds := (Nat.log2_eq_iff hproductNe).1 hleading.symm
    exact hbounds.2
  by_contra hnot
  have hhi :
      2 ^ (leading - 52).toNat ≤ product.hi.toNat := by
    omega
  have hbase :
      product.hi.toNat * 2 ^ 64 ≤ product.toNat := by
    unfold FloatLib.Numerics.FixedWord.UInt128.toNat
    omega
  have hpow :
      2 ^ (leading.toNat + 1) ≤
        2 ^ (leading - 52).toNat * 2 ^ 64 := by
    rw [hshift, ← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hmul :
      2 ^ (leading - 52).toNat * 2 ^ 64 ≤
        product.hi.toNat * 2 ^ 64 :=
    Nat.mul_le_mul_right (2 ^ 64) hhi
  omega

/--
Fixed-limb normal rounding is the normal branch of the generic product rounder.

The magnitude bound includes one extra bit beyond a binary64 significand product so fused
multiply-add can reuse the same native rounding and packing pipeline after exact alignment.
-/
theorem roundNormalProduct_refines
    (sign : Bool) (xExponent yExponent : UInt64)
    (product : FloatLib.Numerics.FixedWord.UInt128) (leading : UInt64)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < 2047)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < 2047)
    (hleading : leading.toNat = product.toNat.log2)
    (hleadingRange : 53 ≤ leading.toNat ∧ leading.toNat ≤ 106)
    (hproductLower : 2 ^ 52 ≤ product.toNat)
    (hproduct : product.toNat < 2 ^ 107)
    (result : Value)
    (hresult :
      roundNormalProductOption sign xExponent yExponent product leading =
        some result) :
    result =
      FiniteProductRound.round FloatFormat.binary64 sign product.toNat
        ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
  unfold roundNormalProductOption at hresult
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  have hxOne : (1 : UInt64) ≤ xExponent := by
    apply UInt64.le_iff_toNat_le.mpr
    simp only [UInt64.reduceToNat]
    omega
  have hyOne : (1 : UInt64) ≤ yExponent := by
    apply UInt64.le_iff_toNat_le.mpr
    simp only [UInt64.reduceToNat]
    omega
  have hxScale :
      (xExponent - 1).toNat = xExponent.toNat - 1 := by
    exact UInt64.toNat_sub_of_le xExponent 1 hxOne
  have hyScale :
      (yExponent - 1).toNat = yExponent.toNat - 1 := by
    exact UInt64.toNat_sub_of_le yExponent 1 hyOne
  have hscale :
      scale.toNat = (xExponent.toNat - 1) + (yExponent.toNat - 1) := by
    unfold scale
    rw [UInt64.toNat_add, hxScale, hyScale]
    apply Nat.mod_eq_of_lt
    omega
  have hposition :
      position.toNat =
        product.toNat.log2 +
          ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
    unfold position
    rw [UInt64.toNat_add, hleading, hscale]
    apply Nat.mod_eq_of_lt
    omega
  by_cases hsubnormal : position < 1126
  · simp [position, scale, hsubnormal] at hresult
  change
    ¬leading + (xExponent - 1 + (yExponent - 1)) < 1126 at hsubnormal
  let rounded := product.roundShiftRightEven (leading - 52).toNat
  let carry := rounded == 0x0020000000000000
  let normalizedPosition := if carry then position + 1 else position
  by_cases hoverflow : 3171 < normalizedPosition
  · have hprocessed := hresult
    simp only [hsubnormal, ↓reduceIte, beq_iff_eq, Option.ite_none_left_eq_some, UInt64.not_lt,
      Option.some.injEq] at hprocessed
    have hle : normalizedPosition ≤ (3171 : UInt64) := by
      simpa [normalizedPosition, carry, rounded, position, scale] using
        hprocessed.1
    have hleNat := UInt64.le_iff_toNat_le.mp hle
    have hltNat := UInt64.lt_iff_toNat_lt.mp hoverflow
    omega
  have hprocessed := hresult
  simp only [hsubnormal, ↓reduceIte, beq_iff_eq, Option.ite_none_left_eq_some, UInt64.not_lt,
    Option.some.injEq] at hprocessed
  have hresultEq :
      ofFields FloatFormat.binary64 sign
          (normalizedPosition.toNat - 1125)
          ((if carry then (0x0010000000000000 : UInt64) else rounded).toNat -
            0x0010000000000000) =
        result := by
    simpa [position, scale, rounded, carry, normalizedPosition] using
      hprocessed.2
  have hresultValue :
      result =
        ofFields FloatFormat.binary64 sign
          (normalizedPosition.toNat - 1125)
          ((if carry then (0x0010000000000000 : UInt64) else rounded).toNat -
            0x0010000000000000) := by
    exact hresultEq.symm
  rw [hresultValue]
  have hproductNe : product.toNat ≠ 0 := by omega
  have hnormal :
      ¬product.toNat.log2 +
          ((xExponent.toNat - 1) + (yExponent.toNat - 1)) < 1126 := by
    intro h
    apply hsubnormal
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [hposition]
    exact h
  have hleadingWord : (52 : UInt64) ≤ leading := by
    apply UInt64.le_iff_toNat_le.mpr
    change 52 ≤ leading.toNat
    omega
  have hshift :
      (leading - 52).toNat = product.toNat.log2 - 52 := by
    rw [UInt64.toNat_sub_of_le leading 52 hleadingWord]
    change leading.toNat - 52 = product.toNat.log2 - 52
    rw [hleading]
  have hshiftRange :
      1 ≤ (leading - 52).toNat ∧ (leading - 52).toNat ≤ 54 := by
    rw [hshift, ← hleading]
    omega
  have hhigh :
      product.hi.toNat < 2 ^ (leading - 52).toNat := by
    exact highLimb_lt_shift (product := product) (leading := leading) (hleading := hleading)
      (hproductNe := hproductNe) (hshift := hshift)
  have hquotient :
      (product.toNat >>> (leading - 52).toNat) + 1 < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]
    have hbase :
        product.toNat / 2 ^ (leading - 52).toNat < 2 ^ 53 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      have hupper :
          product.toNat < 2 ^ (leading.toNat + 1) := by
        have hbounds := (Nat.log2_eq_iff hproductNe).1 hleading.symm
        exact hbounds.2
      calc
        product.toNat < 2 ^ (leading.toNat + 1) := hupper
        _ = 2 ^ 53 * 2 ^ (leading - 52).toNat := by
          rw [← pow_add, hshift]
          congr 1
          omega
    norm_num at hbase ⊢
    omega
  have hrounded :
      rounded.toNat =
        Numerics.roundShiftRightEven product.toNat (product.toNat.log2 - 52) := by
    unfold rounded
    rw [FloatLib.Numerics.FixedWord.UInt128.roundShiftRightEven_toNat product
      (leading - 52).toNat (by omega) (by omega) hhigh hquotient]
    rw [hshift]
  have hfracLe : 52 ≤ product.toNat.log2 := by
    rw [← hleading]
    omega
  have hlog2Le : product.toNat.log2 ≤ 106 := by
    rw [← hleading]
    omega
  have hpositionAdd :
      (position + 1).toNat = position.toNat + 1 := by
    rw [UInt64.toNat_add]
    change (position.toNat + 1) % 2 ^ 64 = position.toNat + 1
    apply Nat.mod_eq_of_lt
    rw [hposition]
    omega
  have hpow52 : pow2 52 = 0x0010000000000000 := by
    norm_num [pow2_eq_two_pow]
  have hpow53 : pow2 (52 + 1) = 0x0020000000000000 := by
    norm_num [pow2_eq_two_pow]
  have hpow53' : pow2 53 = 0x0020000000000000 := by
    norm_num [pow2_eq_two_pow]
  have hcarry :
      carry = true ↔ rounded.toNat = pow2 (52 + 1) := by
    simp [carry, hpow53, ← UInt64.toNat_inj]
  have hnormalized :
      normalizedPosition.toNat =
        if rounded.toNat = pow2 (52 + 1) then
          product.toNat.log2 +
            ((xExponent.toNat - 1) + (yExponent.toNat - 1)) + 1
        else
          product.toNat.log2 +
            ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
    by_cases hcarryTrue : carry = true
    · rw [ite_eq_left (hcarry.mp hcarryTrue)]
      simp [normalizedPosition, hcarryTrue, hpositionAdd, hposition]
    · have hcarryFalse : carry = false := Bool.eq_false_of_not_eq_true hcarryTrue
      rw [ite_eq_right (fun h => hcarryTrue (hcarry.mpr h))]
      simp [normalizedPosition, hcarryFalse, hposition]
  have hoverflowGeneric :
      ¬3171 <
        if rounded.toNat = pow2 (52 + 1) then
          product.toNat.log2 +
            ((xExponent.toNat - 1) + (yExponent.toNat - 1)) + 1
        else
          product.toNat.log2 +
            ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
    rw [← hnormalized]
    intro h
    apply hoverflow
    apply UInt64.lt_iff_toNat_lt.mpr
    simpa using h
  unfold FiniteProductRound.round
  simp only [beq_iff_eq, hproductNe, ite_false]
  rw [show FloatFormat.binary64.bias + 2 * FloatFormat.binary64.fracWidth - 1 =
      1126 by decide]
  rw [ite_eq_right hnormal]
  rw [show FloatFormat.binary64.fracWidth = 52 by decide, ite_eq_left hfracLe]
  rw [← hrounded]
  rw [show 3 * FloatFormat.binary64.bias + 2 * 52 - 2 = 3171 by decide]
  rw [ite_eq_right hoverflowGeneric]
  rw [show FloatFormat.binary64.bias + 2 * 52 - 2 = 1125 by decide]
  rw [hpow52]
  rw [hnormalized]
  by_cases hcarryTrue : carry = true
  · rw [ite_eq_left (hcarry.mp hcarryTrue)]
    have hroundedCarry : rounded.toNat = 0x0020000000000000 := by
      simpa [hpow53] using hcarry.mp hcarryTrue
    simp [hcarryTrue, hroundedCarry, hpow53']
  · have hcarryFalse : carry = false := Bool.eq_false_of_not_eq_true hcarryTrue
    rw [ite_eq_right (fun h => hcarryTrue (hcarry.mpr h))]
    have hroundedNot : rounded.toNat ≠ pow2 53 := by
      intro h
      apply hcarryTrue
      apply hcarry.mpr
      simpa using h
    simp [hcarryFalse, hroundedNot]

private theorem roundNormalLimb_refines
    (sign : Bool) (xExponent yExponent : UInt64)
    (xMantissa yMantissa : UInt64)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < 2047)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < 2047)
    (hxMantissa :
      2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53)
    (hyMantissa :
      2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53)
    (result : Value)
    (hresult :
      roundNormalLimbOption sign xExponent yExponent xMantissa yMantissa =
        some result) :
    result =
      FiniteProductRound.round FloatFormat.binary64 sign
        (xMantissa.toNat * yMantissa.toNat)
        ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let leading : UInt64 :=
    if product.hi < ((1 : UInt64) <<< 41) then 104 else 105
  have hproduct :
      product.toNat = xMantissa.toNat * yMantissa.toNat := by
    simp [product]
  have hproductLower : 2 ^ 104 ≤ product.toNat := by
    rw [hproduct]
    nlinarith
  have hproductUpper : product.toNat < 2 ^ 106 := by
    rw [hproduct]
    nlinarith
  have hproductNe : product.toNat ≠ 0 := by omega
  have hleadingRange : 104 ≤ leading.toNat ∧ leading.toNat ≤ 106 := by
    unfold leading
    split <;> decide
  have hleading : leading.toNat = product.toNat.log2 := by
    by_cases hhigh : product.hi < ((1 : UInt64) <<< 41)
    · have hhighNat : product.hi.toNat < 2 ^ 41 := by
        rw [UInt64.lt_iff_toNat_lt] at hhigh
        norm_num at hhigh ⊢
        exact hhigh
      have hproductLt : product.toNat < 2 ^ 105 := by
        unfold FloatLib.Numerics.FixedWord.UInt128.toNat
        have hlo := product.lo.toNat_lt
        norm_num at hhighNat hlo ⊢
        nlinarith
      have hlog : product.toNat.log2 = 104 :=
        (Nat.log2_eq_iff hproductNe).2
          ⟨hproductLower, by
            norm_num at hproductLt ⊢
            exact hproductLt⟩
      simp [leading, hhigh, hlog]
    · have hhighNat : 2 ^ 41 ≤ product.hi.toNat := by
        have hnot := UInt64.lt_iff_toNat_lt.not.mp hhigh
        norm_num at hnot ⊢
        exact hnot
      have hproductGe : 2 ^ 105 ≤ product.toNat := by
        unfold FloatLib.Numerics.FixedWord.UInt128.toNat
        norm_num at hhighNat ⊢
        nlinarith
      have hlog : product.toNat.log2 = 105 :=
        (Nat.log2_eq_iff hproductNe).2
          ⟨hproductGe, by
            norm_num at hproductUpper ⊢
            exact hproductUpper⟩
      simp [leading, hhigh, hlog]
  rw [← hproduct]
  apply roundNormalProduct_refines sign xExponent yExponent product leading
    hxExponent hyExponent hleading (by omega) (by omega)
    (lt_trans hproductUpper (by norm_num))
    result
  simpa [roundNormalLimbOption, product, leading] using hresult

/--
Every result returned by the binary64 normal-product kernel is the exact compact finite result.
-/
theorem mulNormalLimb_refines
    (x y result : Value)
    (hresult : mulNormalLimbOption x y = some result) :
    mulFiniteImplOption x y = some result := by
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  let xFraction := fracField xBits
  let yFraction := fracField yBits
  let xMantissa := xFraction ||| 0x0010000000000000
  let yMantissa := yFraction ||| 0x0010000000000000
  by_cases hxZero : xExponent = 0
  · simp [mulNormalLimbOption, xBits, xExponent, hxZero] at hresult
  by_cases hxExceptional : xExponent = 0x7ff
  · simp [mulNormalLimbOption, xBits, xExponent, hxExceptional] at hresult
  by_cases hyZero : yExponent = 0
  · simp [mulNormalLimbOption, yBits, yExponent, hyZero] at hresult
  by_cases hyExceptional : yExponent = 0x7ff
  · simp [mulNormalLimbOption, yBits, yExponent, hyExceptional] at hresult
  have hround :
      roundNormalLimbOption
          (Bool.xor (signBit xBits) (signBit yBits))
          xExponent yExponent xMantissa yMantissa =
        some result := by
    simpa [mulNormalLimbOption, xBits, yBits, xExponent, yExponent, xFraction,
      yFraction, xMantissa, yMantissa, hxZero, hxExceptional, hyZero,
      hyExceptional] using hresult
  have hxExponentBounds :
      0 < xExponent.toNat ∧ xExponent.toNat < 2047 := by
    simpa [xExponent, xBits] using
      normalExponent_bounds x hxZero hxExceptional
  have hyExponentBounds :
      0 < yExponent.toNat ∧ yExponent.toNat < 2047 := by
    simpa [yExponent, yBits] using
      normalExponent_bounds y hyZero hyExceptional
  have hxFractionBound : xFraction.toNat < 2 ^ 52 := by
    simpa [xFraction, xBits] using fracField_lt x
  have hyFractionBound : yFraction.toNat < 2 ^ 52 := by
    simpa [yFraction, yBits] using fracField_lt y
  have hxMantissaBounds :
      2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53 := by
    simpa [xMantissa, finiteMantissa, xFraction, xExponent, hxZero] using
      finiteMantissa_bounds xExponent xFraction hxZero hxFractionBound
  have hyMantissaBounds :
      2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53 := by
    simpa [yMantissa, finiteMantissa, yFraction, yExponent, hyZero] using
      finiteMantissa_bounds yExponent yFraction hyZero hyFractionBound
  have hrefines :=
    roundNormalLimb_refines
      (Bool.xor (signBit xBits) (signBit yBits))
      xExponent yExponent xMantissa yMantissa
      hxExponentBounds hyExponentBounds hxMantissaBounds hyMantissaBounds
      result hround
  unfold mulFiniteImplOption
  simp only
  rw [ite_eq_right (by simp [xExponent, xBits, hxExceptional, yExponent, yBits,
    hyExceptional])]
  simp only [Option.some.injEq]
  rw [finiteScale_toNat xExponent, finiteScale_toNat yExponent]
  simp only [ite_eq_right hxZero, ite_eq_right hyZero]
  simpa [xBits, yBits, xExponent, yExponent, xFraction, yFraction,
    xMantissa, yMantissa, finiteMantissa, hxZero, hyZero] using
      hrefines.symm

private theorem mulFiniteImpl_eq_spec (x y : Value) :
    mulFiniteImplOption x y = mulFiniteSpecOption x y := by
  unfold mulFiniteImplOption mulFiniteSpecOption decodeOption
  dsimp only
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  by_cases hx : xExponent = 0x7ff
  · simp [xBits, xExponent, hx]
  by_cases hy : yExponent = 0x7ff
  · simp [xBits, yBits, xExponent, yExponent, hx, hy]
  · simp [xBits, yBits, xExponent, yExponent, hx, hy, finiteScale_toNat,
      uint64_toNat_eq_zero, FiniteKernel.scale]

/-- Native binary64 decoding equals the width-generic compact decoder. -/
theorem decode_eq (x : Value) :
    decodeOption x = FiniteKernel.decodeOption x := by
  unfold decodeOption FiniteKernel.decodeOption
  dsimp only
  simp only [FiniteKernel.decodeMantissa, binary64_fracWidth]
  have hnonfinite :
      (!Model.isFinite x) = (Model.expField x == 2047) := by
    change (!Model.IEEE.isFinite x) = _
    unfold Model.IEEE.isFinite
    rw [binary64_expAllOnesNat]
    simp only [bne, Bool.not_not]
  rw [hnonfinite]
  let bits := toUInt64 x
  let exponent := expField bits
  let fraction := fracField bits
  have hexponent :
      exponent.toNat = Model.expField x := by
    simpa [exponent, bits] using expField_toNat x
  have hfraction :
      fraction.toNat = Model.fracField x := by
    simpa [fraction, bits] using fracField_toNat x
  have hsign :
      signBit bits = Model.signBit x := by
    simpa [bits] using signBit_eq x
  have hfractionLt : fraction.toNat < 2 ^ 52 := by
    simpa [fraction, bits] using fracField_lt x
  change
    (if exponent == (0x7ff : UInt64) then
        (none : Option FiniteKernel.Components)
      else
        some ({
          sign := signBit bits
          exponent := exponent.toNat
          mantissa := (finiteMantissa exponent fraction).toNat } :
            FiniteKernel.Components)) =
      if Model.expField x == 2047 then
        (none : Option FiniteKernel.Components)
      else
        some ({
          sign := Model.signBit x
          exponent := Model.expField x
          mantissa :=
            if Model.expField x == 0 then
              Model.fracField x
            else
              Model.pow2 52 +
                Model.fracField x } :
            FiniteKernel.Components)
  by_cases hexceptional : exponent = 0x7ff
  · have hgenericExceptional :
        Model.expField x = 2047 := by
      rw [← hexponent]
      simp [hexceptional]
    simp [hexceptional, hgenericExceptional]
  · have hgenericFinite :
        Model.expField x ≠ 2047 := by
      intro h
      apply hexceptional
      apply UInt64.toNat_inj.mp
      rw [hexponent]
      simpa using h
    by_cases hexponentZero : exponent = 0
    · have hgenericZero :
          Model.expField x = 0 := by
        rw [← hexponent]
        simp [hexponentZero]
      simp [hexponentZero, hgenericZero, hfraction, hsign, finiteMantissa]
    · rw [finiteMantissa_toNat exponent fraction hfractionLt]
      have hgenericNonzero :
          Model.expField x ≠ 0 := by
        intro h
        apply hexponentZero
        apply UInt64.toNat_inj.mp
        rw [hexponent]
        simpa using h
      simp [hexceptional, hgenericFinite, hexponentZero, hgenericNonzero,
        hexponent, hfraction, hsign]

/--
Native-storage finite addition equals the width-generic compact kernel.

The runtime names the compiled `addComponentsImpl`; `addComponentsImpl_eq` identifies it with the
exact `addComponents` used by `FiniteKernel.addOption`.
-/
theorem addFiniteImpl_eq (x y : Value) :
    addFiniteImplOption x y = FiniteKernel.addOption x y := by
  unfold addFiniteImplOption FiniteKernel.addOption
  rw [decode_eq x, decode_eq y]
  cases FiniteKernel.decodeOption x <;> cases FiniteKernel.decodeOption y <;>
    simp [FiniteKernel.addComponentsImpl_eq]

/-- Native-storage finite addition is commutative. -/
theorem addFiniteImpl_comm (x y : Value) :
    addFiniteImplOption x y = addFiniteImplOption y x := by
  unfold addFiniteImplOption
  cases hx : decodeOption x with
  | none =>
      cases decodeOption y <;> simp
  | some dx =>
      cases hy : decodeOption y with
      | none => simp
      | some dy =>
          simp only [Option.some.injEq, FiniteKernel.addComponentsImpl_eq]
          exact FiniteKernel.addComponents_comm FloatFormat.binary64 dx dy

/-- Native-storage finite multiplication equals the generic proved finite kernel. -/
theorem mulFiniteImpl_eq (x y : Value) :
    mulFiniteImplOption x y = FiniteKernel.mulOption x y := by
  rw [mulFiniteImpl_eq_spec]
  unfold mulFiniteSpecOption FiniteKernel.mulOption
  rw [decode_eq x, decode_eq y]
  cases hx : FiniteKernel.decodeOption x with
  | none =>
      cases FiniteKernel.decodeOption y <;> simp
  | some dx =>
    cases hy : FiniteKernel.decodeOption y with
    | none => simp
    | some dy =>
      by_cases hxZero : dx.mantissa = 0
      · by_cases hsign : dx.sign = dy.sign <;>
          simp [hxZero, FiniteProductRound.round, zero, hsign]
      by_cases hyZero : dy.mantissa = 0
      · by_cases hsign : dx.sign = dy.sign <;>
          simp [hyZero, FiniteProductRound.round, zero, hsign]
      · simp only [hxZero, hyZero, beq_iff_eq, Bool.or_eq_true, or_false,
          ite_false]
        rw [ite_eq_left (by decide : FloatFormat.binary64.isIEEE = true)]

/-- Native-storage finite division equals the width-generic compact kernel. -/
theorem divFiniteImpl_eq (x y : Value) :
    divFiniteImplOption x y = FiniteKernel.divOption x y := by
  unfold divFiniteImplOption FiniteKernel.divOption
  rw [decode_eq x, decode_eq y]
  rfl

/--
Native-storage finite FMA equals the width-generic compact kernel.

The runtime names the compiled `fmaComponentsImpl`; `fmaComponentsImpl_eq` identifies it with the
exact `fmaComponents` used by `FiniteKernel.fmaOption`.
-/
theorem fmaFiniteImpl_eq (x y z : Value) :
    fmaFiniteImplOption x y z = FiniteKernel.fmaOption x y z := by
  unfold fmaFiniteImplOption FiniteKernel.fmaOption
  rw [decode_eq x, decode_eq y, decode_eq z]
  cases FiniteKernel.decodeOption x <;> cases FiniteKernel.decodeOption y <;>
    cases FiniteKernel.decodeOption z <;> simp [FiniteKernel.fmaComponentsImpl_eq]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
