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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ScaleAdd.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.AddDyadic.Proof
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Fields.Proof
import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Arithmetic.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Decode
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Proof

/-!
# Correctness of width-generic finite arithmetic

The executable arbitrary-precision kernels live in `Kernel.Runtime`. This module proves that the
compact field-scale implementations agree with the exact dyadic specifications and installs the
verified compiler substitutions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteKernel

/-- Negating a conventional IEEE value flips only the decoded sign. -/
theorem decodeOption_neg {fmt : FloatFormat} (hieee : fmt.isIEEE = true) (m : Model fmt) :
    decodeOption (neg m) = (decodeOption m).map fun c => { c with sign := !c.sign } := by
  have hencoding : fmt.encoding = .ieee := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
  have hsigned := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hieee
  have hfinite : isFinite (neg m) = isFinite m := by
    rw [isFinite, isFinite, hencoding]
    exact IEEE.isFinite_neg m
  unfold decodeOption
  rw [hfinite, signBit_neg, hsigned, expField_neg, fracField_neg]
  by_cases hfin : isFinite m = true <;> simp [hfin]

/-- The dyadic of a component triple carries the component sign. -/
@[simp] theorem Components.toDyadic_negative (fmt : FloatFormat) (value : Components) :
    (value.toDyadic fmt).negative = value.sign := by
  by_cases h : value.mantissa = 0 <;>
    simp [Components.toDyadic, h]

/-- The dyadic of a component triple has the component mantissa as significand. -/
@[simp] theorem Components.toDyadic_mant (fmt : FloatFormat) (value : Components) :
    (value.toDyadic fmt).significand = value.mantissa := by
  by_cases h : value.mantissa = 0 <;>
    simp [Components.toDyadic, h]

/-- For a nonzero mantissa, the dyadic exponent is the descriptor-adjusted component exponent. -/
theorem Components.toDyadic_exp_of_mantissa_ne_zero
    (fmt : FloatFormat) (value : Components) (h : value.mantissa ≠ 0) :
    (value.toDyadic fmt).exponent = dyadicExponent fmt value.exponent := by
  simp [Components.toDyadic, h]

/-- Scalar finite decoding is extensionally equal to binding the component decoder. -/
theorem withFinite_eq {fmt : FloatFormat} {α : Type}
    (x : Model fmt) (k : Bool → Nat → Nat → Option α) :
    withFiniteOption x k =
      (decodeOption x).bind fun value =>
        k value.sign value.exponent value.mantissa := by
  by_cases hieee : fmt.isIEEE = true
  · have hencoding : fmt.encoding = .ieee :=
      ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
    simp only [withFiniteOption, hieee, ite_true]
    unfold decodeOption isFinite IEEE.isFinite
    rw [hencoding]
    simp only
    rw [signBit_eq_signBitImpl_apply, expField_eq_expFieldImpl_apply,
      fracField_eq_fracFieldImpl_apply]
    unfold signBitImpl expFieldImpl fracFieldImpl
    by_cases hexponent :
        x.toNatBits >>> fmt.fracWidth &&& fmt.expAllOnesNat =
          fmt.expAllOnesNat <;>
      simp [hexponent]
  · simp only [withFiniteOption, hieee]
    cases hdecode : decodeOption x <;>
      simp

private theorem finiteScaleOffset_add_one (fmt : FloatFormat) :
    finiteScaleOffset fmt + 1 = fmt.exponentBias + fmt.fracWidth := by
  unfold finiteScaleOffset
  have hfrac := fmt.fracWidth_pos
  omega

/-- The unsigned finite scale denotes the same signed exponent as the public decoder. -/
theorem exponent_eq_scale (fmt : FloatFormat) (encoded : Nat) :
    dyadicExponent fmt encoded =
      Int.ofNat (scale encoded) -
        Int.ofNat (finiteScaleOffset fmt) := by
  have halign := finiteScaleOffset_add_one fmt
  have halignInt :
      (finiteScaleOffset fmt : Int) + 1 =
        (fmt.exponentBias : Int) + (fmt.fracWidth : Int) := by
    exact_mod_cast halign
  by_cases hzero : encoded = 0
  · subst encoded
    unfold dyadicExponent scale FloatFormat.minSubnormalExponent
      FloatFormat.minNormalExponent
    simp only [beq_self_eq_true, ite_true, Int.ofNat_eq_natCast, Nat.cast_zero]
    omega
  · have hone : 1 ≤ encoded := Nat.one_le_iff_ne_zero.mpr hzero
    have hpred : encoded - 1 + 1 = encoded := Nat.sub_add_cancel hone
    have hpredInt :
        ((encoded - 1 : Nat) : Int) + 1 = (encoded : Int) := by
      exact_mod_cast hpred
    unfold dyadicExponent scale
    simp only [beq_iff_eq, hzero, ite_false, Int.ofNat_eq_natCast]
    omega

private theorem finiteScaleOffset_eq_ieeeAlign
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    finiteScaleOffset fmt = FloatFormat.ieeeSubnormalAlignExp fmt := by
  have hbias := (fmt.isIEEE_eq_true_iff.mp hfmt).2
  simp [finiteScaleOffset, FloatFormat.ieeeSubnormalAlignExp, hbias]

/--
Adding nonzero components with the same sign and exponent reduces to one product-round call.

The scale is derived entirely from the format descriptor, so fixed-width backends do not need
their own binary32, binary64, or binary128 versions of this argument.
-/
theorem addComponents_sameSign_sameExponent
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (left right exponent : Nat)
    (hleft : left ≠ 0) (hright : right ≠ 0) :
    addComponents fmt
        { sign, exponent, mantissa := left }
        { sign, exponent, mantissa := right } =
      FiniteProductRound.round fmt sign (left + right)
        (scale exponent + finiteScaleOffset fmt) := by
  have hleftDyadic :
      Components.toDyadic fmt { sign, exponent, mantissa := left } =
        { negative := sign
          significand := left
          exponent := dyadicExponent fmt exponent } := by
    simp [Components.toDyadic, hleft]
  have hrightDyadic :
      Components.toDyadic fmt { sign, exponent, mantissa := right } =
        { negative := sign
          significand := right
          exponent := dyadicExponent fmt exponent } := by
    simp [Components.toDyadic, hright]
  have hscale :
      Int.ofNat (scale exponent + finiteScaleOffset fmt) -
          Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) =
        dyadicExponent fmt exponent := by
    rw [exponent_eq_scale, finiteScaleOffset_eq_ieeeAlign fmt hfmt]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  unfold addComponents
  rw [← roundDyadic_eq_roundDyadicImpl, hleftDyadic, hrightDyadic,
    Model.addDyadic_sameSign_sameExponent sign left right
      (dyadicExponent fmt exponent) hleft hright,
    FiniteProductRound.round_eq_roundDyadic fmt hfmt, hscale]

private theorem scaleRoundExponent_eq
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (encoded : Nat) :
    FiniteScaleAdd.exponent fmt (scale encoded) (finiteScaleOffset fmt) =
      dyadicExponent fmt encoded := by
  rw [exponent_eq_scale, finiteScaleOffset_eq_ieeeAlign fmt hfmt]
  unfold FiniteScaleAdd.exponent
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

private theorem productRoundExponent_eq
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (leftScale rightScale : Nat) :
    FiniteScaleAdd.exponent fmt (leftScale + rightScale) 0 =
      Int.ofNat (leftScale + rightScale) -
        Int.ofNat (2 * finiteScaleOffset fmt) := by
  rw [finiteScaleOffset_eq_ieeeAlign fmt hfmt]
  unfold FiniteScaleAdd.exponent
  simp

private theorem addScaleDyadics_eq
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y : Components) :
    addDyadic
        { negative := x.sign
          significand := x.mantissa
          exponent :=
            FiniteScaleAdd.exponent fmt (scale x.exponent)
              (finiteScaleOffset fmt) }
        { negative := y.sign
          significand := y.mantissa
          exponent :=
            FiniteScaleAdd.exponent fmt (scale y.exponent)
              (finiteScaleOffset fmt) } =
      addDyadic (x.toDyadic fmt) (y.toDyadic fmt) := by
  rw [scaleRoundExponent_eq fmt hfmt, scaleRoundExponent_eq fmt hfmt]
  by_cases hx : x.mantissa = 0 <;>
    by_cases hy : y.mantissa = 0 <;>
    simp [Components.toDyadic, addDyadic, hx, hy]

/-- Compact decoding produces exactly the same finite dyadic as `toDyadicOption`. -/
theorem toDyadic_eq_decode {fmt : FloatFormat} (x : Model fmt) :
    toDyadicOption x = (decodeOption x).map (Components.toDyadic fmt) := by
  by_cases hfinite : isFinite x = true
  · have hfieldFinite :
        isFinite (ofFields fmt (signBit x) (expField x) (fracField x)) = true := by
      simpa only [ofFields_signBit_expField_fracField] using hfinite
    have hdecoded := toDyadicOption_ofFields_of_isFinite
      fmt (signBit x) (expField x) (fracField x)
      (expField_lt_pow2 x) (fracField_lt_pow2 x) hfieldFinite
    rw [ofFields_signBit_expField_fracField] at hdecoded
    rw [hdecoded]
    unfold decodeOption decodeMantissa Components.toDyadic dyadicExponent
    simp only [hfinite, Bool.not_true, beq_iff_eq]
    by_cases hexponent : expField x = 0
    · by_cases hfraction : fracField x = 0
      · simp [hexponent, hfraction]
      · simp [hexponent, hfraction]
    · have hpow : pow2 fmt.fracWidth ≠ 0 := by
        simp [pow2_eq_two_pow]
      simp [hexponent, hpow]
  · cases hdecoded : toDyadicOption x with
    | none =>
        simp [decodeOption, hfinite]
    | some d =>
        have hsome : isFinite x = true := by
          have := congrArg Option.isSome hdecoded
          rw [toDyadicOption_isSome_eq_isFinite] at this
          simpa using this
        exact (hfinite hsome).elim

/-- Finite component addition is commutative for every format descriptor. -/
theorem addComponents_comm
    (fmt : FloatFormat) (x y : Components) :
    addComponents fmt x y = addComponents fmt y x := by
  unfold addComponents
  rw [addDyadic_comm]

/-- Unsigned-scale finite addition is extensionally equal to the public component operation. -/
theorem addComponentsImpl_eq
    (fmt : FloatFormat) (x y : Components) :
    addComponentsImpl fmt x y = addComponents fmt x y := by
  unfold addComponentsImpl addComponents
  simp only [← roundDyadic_eq_roundDyadicImpl]
  by_cases hfmt : fmt.isIEEE = true
  · rw [ite_eq_left hfmt, FiniteScaleAdd.roundSum_eq fmt hfmt]
    rw [addScaleDyadics_eq fmt hfmt]
  · rw [ite_eq_right hfmt]

/-- Compile finite addition through unsigned scale alignment on conventional IEEE formats. -/
@[csimp] theorem addComponents_eq_addComponentsImpl :
    addComponents = addComponentsImpl := by
  funext fmt x y
  exact (addComponentsImpl_eq fmt x y).symm

/-- Compact finite addition equals the public exact-dyadic finite path. -/
theorem add_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    addOption x y =
      match toDyadicOption x, toDyadicOption y with
      | some dx, some dy => some <| roundDyadic fmt (addDyadic dx dy)
      | _, _ => none := by
  rw [toDyadic_eq_decode x, toDyadic_eq_decode y]
  unfold addOption
  cases decodeOption x <;>
    cases decodeOption y <;>
    simp [addComponents, ← roundDyadic_eq_roundDyadicImpl]

private theorem exponent_add_eq_scales (fmt : FloatFormat) (x y : Nat) :
    dyadicExponent fmt x + dyadicExponent fmt y =
      Int.ofNat (scale x + scale y) -
        Int.ofNat (2 * finiteScaleOffset fmt) := by
  rw [exponent_eq_scale, exponent_eq_scale]
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

private theorem exponent_sub_eq_scales (fmt : FloatFormat) (x y : Nat) :
    dyadicExponent fmt x - dyadicExponent fmt y =
      Int.ofNat (scale x) - Int.ofNat (scale y) := by
  rw [exponent_eq_scale, exponent_eq_scale]
  omega

/-- The compact finite multiplication kernel equals the public exact-dyadic finite path. -/
theorem mul_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    mulOption x y =
      match toDyadicOption x, toDyadicOption y with
      | some dx, some dy =>
          let sign := Bool.xor dx.negative dy.negative
          if dx.significand == 0 || dy.significand == 0 then
            some (zero fmt sign)
          else
            some <| roundDyadic fmt {
              negative := sign
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
      | _, _ => none := by
  rw [toDyadic_eq_decode x, toDyadic_eq_decode y]
  unfold mulOption
  simp only [← roundDyadic_eq_roundDyadicImpl]
  cases hx : decodeOption x with
  | none =>
      cases decodeOption y <;> simp
  | some dx =>
    cases hy : decodeOption y with
      | none => simp
      | some dy =>
          simp only [Option.map_some]
          rw [Components.toDyadic_negative, Components.toDyadic_negative,
            Components.toDyadic_mant, Components.toDyadic_mant]
          by_cases hxZero : dx.mantissa = 0
          · simp [hxZero]
          by_cases hyZero : dy.mantissa = 0
          · simp [hyZero]
          · simp only [hxZero, hyZero, beq_iff_eq, Bool.or_eq_true, or_false,
              ite_false]
            rw [Components.toDyadic_exp_of_mantissa_ne_zero fmt dx hxZero,
              Components.toDyadic_exp_of_mantissa_ne_zero fmt dy hyZero]
            rw [exponent_add_eq_scales]
            by_cases hieee : fmt.isIEEE
            · have hbias := (fmt.isIEEE_eq_true_iff.mp hieee).2
              have hoffset :
                  finiteScaleOffset fmt =
                    FloatFormat.ieeeSubnormalAlignExp fmt := by
                simp [finiteScaleOffset, FloatFormat.ieeeSubnormalAlignExp, hbias]
              simp only [hieee, ite_true, Option.some.injEq]
              simpa only [hoffset] using
                FiniteProductRound.round_eq_roundDyadic
                  fmt hieee (Bool.xor dx.sign dy.sign)
                    (dx.mantissa * dy.mantissa)
                    (scale dx.exponent + scale dy.exponent)
            · simp [hieee]

/-- The compact finite division kernel equals the public exact-dyadic finite path. -/
theorem div_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    divOption x y =
      match toDyadicOption x, toDyadicOption y with
      | some dx, some dy =>
          let sign := Bool.xor dx.negative dy.negative
          if dy.significand == 0 then
            some <| if dx.significand == 0 then
              invalidResult fmt
            else
              nativeOverflow fmt sign
          else if dx.significand == 0 then
            some <| zero fmt sign
          else
            some <|
              roundRatScaled fmt sign dx.significand dy.significand
                (dx.exponent - dy.exponent)
      | _, _ => none := by
  rw [toDyadic_eq_decode x, toDyadic_eq_decode y]
  unfold divOption
  cases hx : decodeOption x with
  | none =>
      cases decodeOption y <;> simp
  | some dx =>
    cases hy : decodeOption y with
      | none => simp
      | some dy =>
          simp only [Option.map_some]
          rw [Components.toDyadic_negative, Components.toDyadic_negative,
            Components.toDyadic_mant, Components.toDyadic_mant]
          by_cases hyZero : dy.mantissa = 0
          · simp [divComponents, hyZero]
          by_cases hxZero : dx.mantissa = 0
          · simp [divComponents, hyZero, hxZero]
          · simp only [hyZero, hxZero, beq_iff_eq, ite_false]
            unfold divComponents
            simp only [hyZero, hxZero, beq_iff_eq, ite_false]
            rw [Components.toDyadic_exp_of_mantissa_ne_zero fmt dx hxZero,
              Components.toDyadic_exp_of_mantissa_ne_zero fmt dy hyZero]
            rw [exponent_sub_eq_scales]

private theorem add_productDyadic_eq
    (fmt : FloatFormat) (x y z : Components) :
    addDyadic (productDyadic fmt x y) (z.toDyadic fmt) =
      addDyadic
        { negative := Bool.xor (x.toDyadic fmt).negative (y.toDyadic fmt).negative
          significand := (x.toDyadic fmt).significand * (y.toDyadic fmt).significand
          exponent := (x.toDyadic fmt).exponent + (y.toDyadic fmt).exponent }
        (z.toDyadic fmt) := by
  rw [Components.toDyadic_negative, Components.toDyadic_negative,
    Components.toDyadic_mant, Components.toDyadic_mant]
  by_cases hxZero : x.mantissa = 0
  · simp [productDyadic, addDyadic, hxZero]
  by_cases hyZero : y.mantissa = 0
  · simp [productDyadic, addDyadic, hyZero]
  · rw [Components.toDyadic_exp_of_mantissa_ne_zero fmt x hxZero,
      Components.toDyadic_exp_of_mantissa_ne_zero fmt y hyZero]
    rw [exponent_add_eq_scales]
    rfl

private theorem addScaledProduct_eq
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y z : Components) :
    addDyadic
        { negative := Bool.xor x.sign y.sign
          significand := x.mantissa * y.mantissa
          exponent :=
            FiniteScaleAdd.exponent fmt
              (scale x.exponent + scale y.exponent) 0 }
        { negative := z.sign
          significand := z.mantissa
          exponent :=
            FiniteScaleAdd.exponent fmt
              (scale z.exponent + finiteScaleOffset fmt) 0 } =
      addDyadic (productDyadic fmt x y) (z.toDyadic fmt) := by
  rw [productRoundExponent_eq fmt hfmt]
  have hzExponent :
      FiniteScaleAdd.exponent fmt
          (scale z.exponent + finiteScaleOffset fmt) 0 =
        dyadicExponent fmt z.exponent := by
    rw [← scaleRoundExponent_eq fmt hfmt]
    unfold FiniteScaleAdd.exponent
    simp only [Nat.add_zero]
  rw [hzExponent]
  by_cases hz : z.mantissa = 0
  · simp [Components.toDyadic, productDyadic, addDyadic, hz]
  · simp [productDyadic, Components.toDyadic, hz]

/-- Unsigned-scale FMA is extensionally equal to the public exact component operation. -/
theorem fmaComponentsImpl_eq
    (fmt : FloatFormat) (x y z : Components) :
    fmaComponentsImpl fmt x y z = fmaComponents fmt x y z := by
  unfold fmaComponentsImpl fmaComponents
  simp only [← roundDyadic_eq_roundDyadicImpl]
  by_cases hfmt : fmt.isIEEE = true
  · rw [ite_eq_left hfmt, FiniteScaleAdd.roundSum_eq fmt hfmt]
    rw [addScaledProduct_eq fmt hfmt]
  · rw [ite_eq_right hfmt]

/--
An aligned same-sign FMA reduces to one product-round call for every IEEE binary format.

The caller supplies the significand alignment width. The exponent offset remains descriptor
derived, so binary32, binary64, binary128, and custom IEEE descriptors share this proof.
-/
theorem fmaComponents_sameSign_aligned
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (alignment : Nat)
    (xSign ySign : Bool)
    (xExponent yExponent zExponent xMantissa yMantissa zMantissa : Nat)
    (hxExponent : xExponent ≠ 0)
    (hyExponent : yExponent ≠ 0)
    (hzExponent : zExponent ≠ 0)
    (hxMantissa : xMantissa ≠ 0)
    (hyMantissa : yMantissa ≠ 0)
    (hzMantissa : zMantissa ≠ 0)
    (haligned :
      (xExponent - 1) + (yExponent - 1) + alignment =
        (zExponent - 1) + finiteScaleOffset fmt) :
    fmaComponents fmt
        { sign := xSign
          exponent := xExponent
          mantissa := xMantissa }
        { sign := ySign
          exponent := yExponent
          mantissa := yMantissa }
        { sign := Bool.xor xSign ySign
          exponent := zExponent
          mantissa := zMantissa } =
      FiniteProductRound.round fmt
        (Bool.xor xSign ySign)
        (xMantissa * yMantissa + (zMantissa <<< alignment))
        ((xExponent - 1) + (yExponent - 1)) := by
  rw [← fmaComponentsImpl_eq]
  unfold fmaComponentsImpl
  rw [ite_eq_left hfmt]
  unfold FiniteScaleAdd.roundSum
  simp only [scale, hxExponent, hyExponent, hzExponent,
    ite_false, hxMantissa, hyMantissa, hzMantissa, mul_eq_zero,
    beq_iff_eq]
  have hscale :
      (xExponent - 1) + (yExponent - 1) ≤
        (zExponent - 1) + finiteScaleOffset fmt := by
    omega
  simp only [or_self, ite_false]
  rw [ite_eq_left hscale]
  unfold FiniteScaleAdd.roundMagnitudes
  simp only [beq_self_eq_true, ite_true]
  unfold FiniteScaleAdd.roundMagnitude
  change
    FiniteProductRound.round fmt
        (Bool.xor xSign ySign)
        (xMantissa * yMantissa +
          (zMantissa <<<
            ((zExponent - 1) + finiteScaleOffset fmt -
              ((xExponent - 1) + (yExponent - 1)))))
        ((xExponent - 1) + (yExponent - 1)) =
      _
  have hshift :
      (zExponent - 1) + finiteScaleOffset fmt -
          ((xExponent - 1) + (yExponent - 1)) =
        alignment := by
    omega
  rw [hshift]

/-- Compile finite FMA through the verified unsigned-scale implementation on IEEE formats. -/
@[csimp] theorem fmaComponents_eq_fmaComponentsImpl :
    fmaComponents = fmaComponentsImpl := by
  funext fmt x y z
  exact (fmaComponentsImpl_eq fmt x y z).symm

/-- The compact finite FMA kernel equals the public exact-dyadic finite path. -/
theorem fma_eq_spec {fmt : FloatFormat} (x y z : Model fmt) :
    fmaOption x y z =
      match toDyadicOption x, toDyadicOption y, toDyadicOption z with
      | some dx, some dy, some dz =>
          let product : Numerics.Dyadic :=
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
          some <| roundDyadic fmt (addDyadic product dz)
      | _, _, _ => none := by
  rw [toDyadic_eq_decode x, toDyadic_eq_decode y, toDyadic_eq_decode z]
  unfold fmaOption
  cases hx : decodeOption x with
  | none =>
      cases decodeOption y <;>
        cases decodeOption z <;>
        simp
  | some dx =>
    cases hy : decodeOption y with
    | none =>
        cases decodeOption z <;> simp
    | some dy =>
      cases hz : decodeOption z with
      | none => simp
      | some dz =>
          simp only [Option.map_some]
          unfold fmaComponents
          rw [← roundDyadic_eq_roundDyadicImpl, add_productDyadic_eq]

/-- Scalar-field addition agrees with component addition. -/
theorem addFields_eq
    (fmt : FloatFormat)
    (xSign : Bool) (xExponent xMantissa : Nat)
    (ySign : Bool) (yExponent yMantissa : Nat) :
    addFields fmt xSign xExponent xMantissa ySign yExponent yMantissa =
      addComponents fmt
        { sign := xSign, exponent := xExponent, mantissa := xMantissa }
        { sign := ySign, exponent := yExponent, mantissa := yMantissa } := by
  by_cases hieee : fmt.isIEEE = true
  · simpa [addFields, addComponentsImpl, hieee] using
      addComponentsImpl_eq fmt
        { sign := xSign, exponent := xExponent, mantissa := xMantissa }
        { sign := ySign, exponent := yExponent, mantissa := yMantissa }
  · simp [addFields, hieee]

/-- The scalar-field addition entry point preserves `addOption`. -/
theorem addRuntime_eq {fmt : FloatFormat} (x y : Model fmt) :
    addRuntimeOption x y = addOption x y := by
  simp only [addRuntimeOption, withFinite_eq]
  unfold addOption
  cases decodeOption x <;>
    cases decodeOption y <;>
    simp [addFields_eq]

/-- Compile finite addition through the scalar decoder. -/
@[csimp] theorem add_eq_addRuntime :
    @addOption = @addRuntimeOption := by
  funext fmt x y
  exact (addRuntime_eq x y).symm

/-- The scalar-field multiplication entry point preserves `mulOption`. -/
theorem mulRuntime_eq {fmt : FloatFormat} (x y : Model fmt) :
    mulRuntimeOption x y = mulOption x y := by
  simp only [mulRuntimeOption, withFinite_eq]
  unfold mulOption mulFields
  cases decodeOption x <;>
    cases decodeOption y <;>
    simp only [Option.bind_none, Option.bind_some]
  rename_i dx dy
  by_cases hzero : dx.mantissa = 0 ∨ dy.mantissa = 0
  · simp [hzero]
  · by_cases hieee : fmt.isIEEE = true <;>
      simp [hzero, hieee]

/-- Compile finite multiplication through the scalar decoder. -/
@[csimp] theorem mul_eq_mulRuntime :
    @mulOption = @mulRuntimeOption := by
  funext fmt x y
  exact (mulRuntime_eq x y).symm

/-- The scalar-field division entry point preserves `divOption`. -/
theorem divRuntime_eq {fmt : FloatFormat} (x y : Model fmt) :
    divRuntimeOption x y = divOption x y := by
  simp only [divRuntimeOption, withFinite_eq]
  unfold divOption divFields divComponents
  cases decodeOption x <;>
    cases decodeOption y <;>
    rfl

/-- Compile finite division through the scalar decoder. -/
@[csimp] theorem div_eq_divRuntime :
    @divOption = @divRuntimeOption := by
  funext fmt x y
  exact (divRuntime_eq x y).symm

/-- Scalar-field FMA agrees with component FMA. -/
theorem fmaFields_eq
    (fmt : FloatFormat)
    (xSign : Bool) (xExponent xMantissa : Nat)
    (ySign : Bool) (yExponent yMantissa : Nat)
    (zSign : Bool) (zExponent zMantissa : Nat) :
    fmaFields fmt
        xSign xExponent xMantissa ySign yExponent yMantissa
        zSign zExponent zMantissa =
      fmaComponents fmt
        { sign := xSign, exponent := xExponent, mantissa := xMantissa }
        { sign := ySign, exponent := yExponent, mantissa := yMantissa }
        { sign := zSign, exponent := zExponent, mantissa := zMantissa } := by
  by_cases hieee : fmt.isIEEE = true
  · simpa [fmaFields, fmaComponentsImpl, hieee] using
      fmaComponentsImpl_eq fmt
        { sign := xSign, exponent := xExponent, mantissa := xMantissa }
        { sign := ySign, exponent := yExponent, mantissa := yMantissa }
        { sign := zSign, exponent := zExponent, mantissa := zMantissa }
  · simp [fmaFields, hieee]

/-- The scalar-field FMA entry point preserves `fmaOption`. -/
theorem fmaRuntime_eq {fmt : FloatFormat} (x y z : Model fmt) :
    fmaRuntimeOption x y z = fmaOption x y z := by
  simp only [fmaRuntimeOption, withFinite_eq]
  unfold fmaOption
  cases decodeOption x <;>
    cases decodeOption y <;>
    cases decodeOption z <;>
    simp [fmaFields_eq]

/-- The straight-line decoder agrees with the continuation decoder. -/
theorem fmaRuntimeFlat_eq {fmt : FloatFormat} (x y z : Model fmt) :
    fmaRuntimeFlatOption x y z = fmaRuntimeOption x y z := by
  by_cases hieee : fmt.isIEEE = true
  · simp [fmaRuntimeFlatOption, fmaRuntimeOption, withFiniteOption, decodeMantissa, hieee]
  · simp [fmaRuntimeFlatOption, hieee]

/-- Compile finite FMA through the scalar decoder. -/
@[csimp] theorem fma_eq_fmaRuntime :
    @fmaOption = @fmaRuntimeFlatOption := by
  funext fmt x y z
  exact ((fmaRuntimeFlat_eq x y z).trans (fmaRuntime_eq x y z)).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteKernel
