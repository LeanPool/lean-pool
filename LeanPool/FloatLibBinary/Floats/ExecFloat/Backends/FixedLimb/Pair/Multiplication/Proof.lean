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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Multiplication.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Proof
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.ModelRounding.Proof

/-!
# Correctness of two-word normal multiplication

The runtime kernel multiplies two normal significands exactly in four native words, rounds the
product of at most `2 * fracWidth + 2` bits to nearest-even, and packs a normal result. Subnormal
operands and results, overflow, NaNs, and infinities are left to the operation dispatcher.

`roundNormalProduct_refines` is shared with the fused multiply-add kernel: it accepts any
four-limb magnitude in `[2^(2 * fracWidth), 2^(2 * fracWidth + 3))` together with its
leading-bit position, which covers both the product and the aligned product-plus-addend sum.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Numerics.FixedWord

variable {fmt : FloatFormat}

/-! ## Threshold words -/

/-- The first normal leading-bit position fits a native word. -/
theorem normalThreshold_toNat (h : Eligible fmt) :
    (UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 1)).toNat =
      fmt.bias + 2 * fmt.fracWidth - 1 := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have hbias := h.bias_lt
  have hfrac := h.frac_le
  norm_num at hbias ⊢
  omega

/-- The largest finite normal leading-bit position fits a native word. -/
theorem overflowThreshold_toNat (h : Eligible fmt) :
    (UInt64.ofNat (3 * fmt.bias + 2 * fmt.fracWidth - 2)).toNat =
      3 * fmt.bias + 2 * fmt.fracWidth - 2 := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have hbias := h.bias_lt
  have hfrac := h.frac_le
  norm_num at hbias ⊢
  omega

/-- The product exponent offset fits a native word. -/
theorem exponentOffset_toNat (h : Eligible fmt) :
    (UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2)).toNat =
      fmt.bias + 2 * fmt.fracWidth - 2 := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have hbias := h.bias_lt
  have hfrac := h.frac_le
  norm_num at hbias ⊢
  omega

/-- The fraction width fits a native word. -/
theorem fracWidth_toNat (h : Eligible fmt) :
    (UInt64.ofNat fmt.fracWidth).toNat = fmt.fracWidth := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have hfrac := h.frac_le
  omega

/-! ## Rounding a four-limb magnitude -/

private theorem roundProductAfterNormalBounds {fmt : FloatFormat} (h : Eligible fmt) (sign : Bool)
  (xExponent yExponent : UInt64) (product : UInt256) (leading : UInt64)
  (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < fmt.expAllOnesNat)
  (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < fmt.expAllOnesNat)
  (hleading : leading.toNat = product.toNat.log2)
  (hleadingRange : 2 * fmt.fracWidth ≤ leading.toNat ∧ leading.toNat ≤ 2 * fmt.fracWidth + 2)
    (result : Model fmt)
  (hfrac : 64 < fmt.fracWidth) (hfracLe : fmt.fracWidth ≤ 125) (hallOnes : fmt.expAllOnesNat = 2
    * fmt.bias + 1)
  (hbias : fmt.bias < 2 ^ 61)
  (hoverflowWord : (UInt64.ofNat (3 * fmt.bias + 2 * fmt.fracWidth - 2)).toNat = 3 * fmt.bias + 2
    * fmt.fracWidth - 2)
  (hoffsetWord : (UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2)).toNat = fmt.bias + 2 *
    fmt.fracWidth - 2)
  (hfracWord : (UInt64.ofNat fmt.fracWidth).toNat = fmt.fracWidth) :
  let scale := xExponent - 1 + (yExponent - 1);
  let position := leading + scale;
  (yExponent - 1).toNat = yExponent.toNat - 1 →
    scale.toNat = xExponent.toNat - 1 + (yExponent.toNat - 1) →
      position.toNat = product.toNat.log2 + (xExponent.toNat - 1 + (yExponent.toNat - 1)) →
        let rounded := product.roundShiftRightEven128 (leading - UInt64.ofNat fmt.fracWidth).toNat;
        let carry := isCarry fmt rounded;
        let normalizedPosition := if carry = true then position + 1 else position;
        ¬UInt64.ofNat (3 * fmt.bias + 2 * fmt.fracWidth - 2) < normalizedPosition →
          packNormal fmt sign (normalizedPosition - UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2))
                (normalizeCarry fmt carry rounded) =
              result →
            product.toNat ≠ 0 →
              ¬product.toNat.log2 + (xExponent.toNat - 1 + (yExponent.toNat - 1)) < fmt.bias + 2
                * fmt.fracWidth - 1 →
                result =
                  FiniteProductRound.round fmt sign product.toNat (xExponent.toNat - 1 +
                    (yExponent.toNat - 1)) := by
  intro scale position hyScale hscale hposition rounded carry normalizedPosition hoverflow
    hpackResult hproductNe hnormal
  have hfracLog : fmt.fracWidth ≤ product.toNat.log2 := by omega
  have hleadingWord : UInt64.ofNat fmt.fracWidth ≤ leading := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hfracWord, hleading]
    exact hfracLog
  have hshift :
      (leading - UInt64.ofNat fmt.fracWidth).toNat =
        product.toNat.log2 - fmt.fracWidth := by
    rw [UInt64.toNat_sub_of_le _ _ hleadingWord, hleading, hfracWord]
  have hlimb3 : product.limb3.toNat * 2 ^ 192 ≤ product.toNat := by
    unfold UInt256.toNat
    exact Nat.le_add_left _ _
  have hproductUpper : product.toNat < 2 ^ (product.toNat.log2 + 1) := Nat.lt_log2_self
  have htop :
      product.limb3.toNat <
        2 ^ ((leading - UInt64.ofNat fmt.fracWidth).toNat - 64) := by
    have hbound :
        product.limb3.toNat * 2 ^ 192 <
          2 ^ ((leading - UInt64.ofNat fmt.fracWidth).toNat - 64) * 2 ^ 192 := by
      calc
        product.limb3.toNat * 2 ^ 192 ≤ product.toNat := hlimb3
        _ < 2 ^ (product.toNat.log2 + 1) := hproductUpper
        _ ≤ 2 ^ ((leading - UInt64.ofNat fmt.fracWidth).toNat - 64 + 192) :=
          Nat.pow_le_pow_right (by decide) (by rw [hshift]; omega)
        _ = 2 ^ ((leading - UInt64.ofNat fmt.fracWidth).toNat - 64) * 2 ^ 192 :=
          pow_add 2 _ 192
    exact Nat.lt_of_mul_lt_mul_right hbound
  have hquotient :
      (product.toNat >>> (leading - UInt64.ofNat fmt.fracWidth).toNat) + 1 < 2 ^ 128 := by
    rw [Nat.shiftRight_eq_div_pow, hshift]
    have hdiv :
        product.toNat / 2 ^ (product.toNat.log2 - fmt.fracWidth) <
          2 ^ (fmt.fracWidth + 1) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
        show fmt.fracWidth + 1 + (product.toNat.log2 - fmt.fracWidth) =
          product.toNat.log2 + 1 by omega]
      exact hproductUpper
    have hcapacity : 2 ^ (fmt.fracWidth + 1) < 2 ^ 128 :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have hrounded :
      rounded.toNat =
        Numerics.roundShiftRightEven product.toNat (product.toNat.log2 - fmt.fracWidth) := by
    unfold rounded
    rw [UInt256.roundShiftRightEven128_toNat product _
      (by rw [hshift]; omega) (by rw [hshift]; omega) htop hquotient, hshift]
  have hcarry : carry = true ↔ rounded.toNat = pow2 (fmt.fracWidth + 1) :=
    isCarry_iff h rounded
  have hroundedLower : 2 ^ fmt.fracWidth ≤ rounded.toNat := by
    rw [hrounded]
    simpa [roundMantissaToLeadingBitEven, hfracLog, pow2_eq_two_pow] using
      pow2_le_roundMantissaToLeadingBitEven product.toNat fmt.fracWidth hproductNe
  have hroundedUpper : rounded.toNat ≤ 2 ^ (fmt.fracWidth + 1) := by
    rw [hrounded]
    simpa [roundMantissaToLeadingBitEven, hfracLog, pow2_eq_two_pow] using
      roundMantissaToLeadingBitEven_le_pow2_succ product.toNat fmt.fracWidth
  have hnormalizedLower :
      2 ^ fmt.fracWidth ≤ (normalizeCarry fmt carry rounded).toNat := by
    rw [normalizeCarry_toNat h]
    split
    · simp [pow2_eq_two_pow]
    · exact hroundedLower
  have hnormalizedUpper :
      (normalizeCarry fmt carry rounded).toNat < 2 ^ (fmt.fracWidth + 1) := by
    rw [normalizeCarry_toNat h]
    by_cases hcarryTrue : carry = true
    · rw [ite_eq_left hcarryTrue, pow2_eq_two_pow]
      exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
    · rw [ite_eq_right hcarryTrue]
      have hne : rounded.toNat ≠ 2 ^ (fmt.fracWidth + 1) := by
        intro heq
        apply hcarryTrue
        apply hcarry.mpr
        rw [pow2_eq_two_pow]
        exact heq
      exact lt_of_le_of_ne hroundedUpper hne
  have hpositionAdd : (position + 1).toNat = position.toNat + 1 := by
    rw [UInt64.toNat_add]
    change (position.toNat + 1) % 2 ^ 64 = position.toNat + 1
    apply Nat.mod_eq_of_lt
    rw [hposition]
    norm_num at hbias ⊢
    omega
  have hnormalized :
      normalizedPosition.toNat =
        if rounded.toNat = pow2 (fmt.fracWidth + 1) then
          product.toNat.log2 + ((xExponent.toNat - 1) + (yExponent.toNat - 1)) + 1
        else
          product.toNat.log2 + ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
    by_cases hcarryTrue : carry = true
    · rw [ite_eq_left (hcarry.mp hcarryTrue)]
      simp [normalizedPosition, hcarryTrue, hpositionAdd, hposition]
    · have hcarryFalse : carry = false := Bool.eq_false_of_not_eq_true hcarryTrue
      rw [ite_eq_right (fun hc => hcarryTrue (hcarry.mpr hc))]
      simp [normalizedPosition, hcarryFalse, hposition]
  have hoverflowGeneric :
      ¬3 * fmt.bias + 2 * fmt.fracWidth - 2 <
        if rounded.toNat = pow2 (fmt.fracWidth + 1) then
          product.toNat.log2 + ((xExponent.toNat - 1) + (yExponent.toNat - 1)) + 1
        else
          product.toNat.log2 + ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
    rw [← hnormalized]
    intro hlt
    apply hoverflow
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [hoverflowWord]
    exact hlt
  have hnormalizedPositionLower :
      fmt.bias + 2 * fmt.fracWidth - 2 ≤ normalizedPosition.toNat := by
    rw [hnormalized]
    split <;> omega
  have hnormalizedPositionUpper :
      normalizedPosition.toNat ≤ 3 * fmt.bias + 2 * fmt.fracWidth - 2 := by
    by_contra hcon
    apply hoverflow
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [hoverflowWord]
    omega
  have hexponentLe :
      UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2) ≤ normalizedPosition := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hoffsetWord]
    exact hnormalizedPositionLower
  have hexponentNat :
      (normalizedPosition - UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2)).toNat =
        normalizedPosition.toNat - (fmt.bias + 2 * fmt.fracWidth - 2) := by
    rw [UInt64.toNat_sub_of_le _ _ hexponentLe, hoffsetWord]
  have hexponentBound :
      (normalizedPosition - UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2)).toNat <
        2 ^ fmt.expWidth := by
    rw [hexponentNat, fmt.two_pow_expWidth_eq_two_mul_bias_add_two]
    omega
  have hpackCanonical :=
    packNormal_eq_ofFields h sign
      (normalizedPosition - UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2))
      (normalizeCarry fmt carry rounded)
      hexponentBound hnormalizedLower hnormalizedUpper
  have hresultEq :
      ofFields fmt sign
          (normalizedPosition.toNat - (fmt.bias + 2 * fmt.fracWidth - 2))
          ((normalizeCarry fmt carry rounded).toNat - pow2 fmt.fracWidth) =
        result := by
    rw [← hexponentNat]
    exact hpackCanonical.symm.trans hpackResult
  rw [← hresultEq]
  unfold FiniteProductRound.round
  simp only [beq_iff_eq, hproductNe, ite_false]
  rw [ite_eq_right hnormal, ite_eq_left hfracLog, ← hrounded,
    ite_eq_right hoverflowGeneric, hnormalized,
    normalizeCarry_toNat h]
  by_cases hcarryTrue : carry = true
  · have hroundedCarry := hcarry.mp hcarryTrue
    rw [ite_eq_left hroundedCarry, ite_eq_left hcarryTrue, ite_eq_left hroundedCarry]
  · have hroundedNot : ¬rounded.toNat = pow2 (fmt.fracWidth + 1) :=
      fun hc => hcarryTrue (hcarry.mpr hc)
    rw [ite_eq_right hroundedNot, ite_eq_right hcarryTrue, ite_eq_right hroundedNot]

/-- The fixed-limb normal branch agrees with generic unsigned product rounding. -/
theorem roundNormalProduct_refines (h : Eligible fmt)
    (sign : Bool) (xExponent yExponent : UInt64)
    (product : UInt256) (leading : UInt64)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < fmt.expAllOnesNat)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < fmt.expAllOnesNat)
    (hleading : leading.toNat = product.toNat.log2)
    (hleadingRange :
      2 * fmt.fracWidth ≤ leading.toNat ∧ leading.toNat ≤ 2 * fmt.fracWidth + 2)
    (hproductLower : 2 ^ (2 * fmt.fracWidth) ≤ product.toNat)
    (result : Model fmt)
    (hresult :
      roundNormalProductOption sign xExponent yExponent product leading = some result) :
    result =
      FiniteProductRound.round fmt sign product.toNat
        ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
  have hfrac := h.frac_gt
  have hfracLe := h.frac_le
  have hallOnes := fmt.expAllOnesNat_eq_two_mul_bias_add_one
  have hbias := h.bias_lt
  have hnormalWord := normalThreshold_toNat h
  have hoverflowWord := overflowThreshold_toNat h
  have hoffsetWord := exponentOffset_toNat h
  have hfracWord := fracWidth_toNat h
  have hlog2Le : product.toNat.log2 ≤ 2 * fmt.fracWidth + 2 := hleading ▸ hleadingRange.2
  have hlog2Ge : 2 * fmt.fracWidth ≤ product.toNat.log2 := hleading ▸ hleadingRange.1
  unfold roundNormalProductOption at hresult
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  have hxOne : (1 : UInt64) ≤ xExponent := by
    apply UInt64.le_iff_toNat_le.mpr
    change 1 ≤ xExponent.toNat
    omega
  have hyOne : (1 : UInt64) ≤ yExponent := by
    apply UInt64.le_iff_toNat_le.mpr
    change 1 ≤ yExponent.toNat
    omega
  have hxScale : (xExponent - 1).toNat = xExponent.toNat - 1 :=
    UInt64.toNat_sub_of_le xExponent 1 hxOne
  have hyScale : (yExponent - 1).toNat = yExponent.toNat - 1 :=
    UInt64.toNat_sub_of_le yExponent 1 hyOne
  have hscale : scale.toNat = (xExponent.toNat - 1) + (yExponent.toNat - 1) := by
    unfold scale
    rw [UInt64.toNat_add, hxScale, hyScale]
    apply Nat.mod_eq_of_lt
    norm_num at hbias ⊢
    omega
  have hposition :
      position.toNat =
        product.toNat.log2 + ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
    unfold position
    rw [UInt64.toNat_add, hleading, hscale]
    apply Nat.mod_eq_of_lt
    norm_num at hbias ⊢
    omega
  by_cases hsubnormal : position < UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 1)
  · simp [position, scale, hsubnormal] at hresult
  change ¬leading + (xExponent - 1 + (yExponent - 1)) <
    UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 1) at hsubnormal
  let rounded := product.roundShiftRightEven128 (leading - UInt64.ofNat fmt.fracWidth).toNat
  let carry := isCarry fmt rounded
  let normalizedPosition := if carry then position + 1 else position
  by_cases hoverflow :
      UInt64.ofNat (3 * fmt.bias + 2 * fmt.fracWidth - 2) < normalizedPosition
  · have hprocessed := hresult
    simp only [hsubnormal, ↓reduceIte, Option.ite_none_left_eq_some, UInt64.not_lt,
      Option.some.injEq] at hprocessed
    have hle : normalizedPosition ≤ UInt64.ofNat (3 * fmt.bias + 2 * fmt.fracWidth - 2) := by
      simpa [normalizedPosition, carry, rounded, position, scale] using hprocessed.1
    have hleNat := UInt64.le_iff_toNat_le.mp hle
    have hltNat := UInt64.lt_iff_toNat_lt.mp hoverflow
    omega
  have hprocessed := hresult
  simp only [hsubnormal, ↓reduceIte, Option.ite_none_left_eq_some, UInt64.not_lt,
    Option.some.injEq] at hprocessed
  have hpackResult :
      packNormal fmt sign
          (normalizedPosition - UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2))
          (normalizeCarry fmt carry rounded) =
        result := by
    simpa [position, scale, rounded, carry, normalizedPosition] using hprocessed.2
  have hproductNe : product.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hproductLower)
  have hnormal :
      ¬product.toNat.log2 + ((xExponent.toNat - 1) + (yExponent.toNat - 1)) <
        fmt.bias + 2 * fmt.fracWidth - 1 := by
    intro hlt
    apply hsubnormal
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [hposition, hnormalWord]
    exact hlt
  exact roundProductAfterNormalBounds (h := h) (sign := sign) (xExponent := xExponent)
    (yExponent := yExponent) (product := product) (leading := leading)
    (hxExponent := hxExponent) (hyExponent := hyExponent) (hleading := hleading)
    (hleadingRange := hleadingRange) (result := result) (hfrac := hfrac) (hfracLe := hfracLe)
    (hallOnes := hallOnes) (hbias := hbias) (hoverflowWord := hoverflowWord)
    (hoffsetWord := hoffsetWord) (hfracWord := hfracWord) hyScale hscale hposition hoverflow
    hpackResult hproductNe hnormal

/-! ## Normal products -/

private theorem roundNormalLimb_refines (h : Eligible fmt)
    (sign : Bool) (xExponent yExponent : UInt64)
    (xMantissa yMantissa : UInt128)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < fmt.expAllOnesNat)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < fmt.expAllOnesNat)
    (hxMantissa :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (result : Model fmt)
    (hresult :
      roundNormalLimbOption sign xExponent yExponent xMantissa yMantissa = some result) :
    result =
      FiniteProductRound.round fmt sign
        (xMantissa.toNat * yMantissa.toNat)
        ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
  let product := mul128 xMantissa yMantissa
  have hproduct : product.toNat = xMantissa.toNat * yMantissa.toNat := by
    simp [product]
  have hproductLower : 2 ^ (2 * fmt.fracWidth) ≤ product.toNat := by
    rw [hproduct, two_mul, pow_add]
    exact Nat.mul_le_mul hxMantissa.1 hyMantissa.1
  have hproductUpper : product.toNat < 2 ^ (2 * fmt.fracWidth + 2) := by
    rw [hproduct, show 2 * fmt.fracWidth + 2 = (fmt.fracWidth + 1) + (fmt.fracWidth + 1) by omega,
      pow_add]
    exact Nat.mul_lt_mul'' hxMantissa.2 hyMantissa.2
  have hproductNe : product.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hproductLower)
  have hlogLower : 2 * fmt.fracWidth ≤ product.toNat.log2 :=
    (Nat.le_log2 hproductNe).2 hproductLower
  have hlogUpper : product.toNat.log2 < 2 * fmt.fracWidth + 2 :=
    (Nat.log2_lt hproductNe).2 hproductUpper
  have hleading : (UInt64.ofNat product.log2).toNat = product.toNat.log2 := by
    rw [UInt256.log2_toNat, UInt64.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    have hfrac := h.frac_le
    omega
  rw [← hproduct]
  apply roundNormalProduct_refines h sign xExponent yExponent product
    (UInt64.ofNat product.log2) hxExponent hyExponent hleading
    (by rw [hleading]; omega) hproductLower result
  simpa [roundNormalLimbOption, product] using hresult

/-- Every result accepted by the pair multiplication kernel equals the exact finite kernel. -/
theorem mulNormalLimb_refines (h : Eligible fmt)
    (x y result : Model fmt)
    (hresult : mulNormalLimbOption x y = some result) :
    FiniteKernel.mulOption x y = some result := by
  let xWords := toWords x
  let yWords := toWords y
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  let xHigh := fracHigh fmt xWords.hi
  let yHigh := fracHigh fmt yWords.hi
  let xMantissa := normalMantissa fmt xHigh xWords.lo
  let yMantissa := normalMantissa fmt yHigh yWords.lo
  by_cases hxZero : xExponent = 0
  · simp [mulNormalLimbOption, xWords, xExponent, hxZero] at hresult
  by_cases hxExceptional : xExponent = expAllOnes fmt
  · simp [mulNormalLimbOption, xWords, xExponent, hxExceptional] at hresult
  by_cases hyZero : yExponent = 0
  · simp [mulNormalLimbOption, yWords, yExponent, hyZero] at hresult
  by_cases hyExceptional : yExponent = expAllOnes fmt
  · simp [mulNormalLimbOption, yWords, yExponent, hyExceptional] at hresult
  have hround :
      roundNormalLimbOption
          (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
          xExponent yExponent xMantissa yMantissa =
        some result := by
    simpa [mulNormalLimbOption, xWords, yWords, xExponent, yExponent,
      xHigh, yHigh, xMantissa, yMantissa, hxZero, hxExceptional,
      hyZero, hyExceptional] using hresult
  have hxExponentBounds :=
    normalExponent_bounds h x hxZero hxExceptional
  have hyExponentBounds :=
    normalExponent_bounds h y hyZero hyExceptional
  have hxMantissaBounds :=
    normalMantissa_bounds h xHigh xWords.lo (fracHigh_lt h xWords.hi)
  have hyMantissaBounds :=
    normalMantissa_bounds h yHigh yWords.lo (fracHigh_lt h yWords.hi)
  have hrefines :=
    roundNormalLimb_refines h
      (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
      xExponent yExponent xMantissa yMantissa
      hxExponentBounds hyExponentBounds hxMantissaBounds hyMantissaBounds
      result hround
  have hxMantissaNe :
      (normalMantissa fmt (fracHigh fmt (toWords x).hi) (toWords x).lo).toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hxMantissaBounds.1)
  have hyMantissaNe :
      (normalMantissa fmt (fracHigh fmt (toWords y).hi) (toWords y).lo).toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hyMantissaBounds.1)
  unfold FiniteKernel.mulOption
  rw [decode_of_normalExponent h x hxZero hxExceptional,
    decode_of_normalExponent h y hyZero hyExceptional]
  simp only [Bool.or_eq_true, beq_iff_eq, hxMantissaNe, hyMantissaNe, or_self, ↓reduceIte,
    h.isIEEE, FiniteKernel.scale, Nat.ne_of_gt hxExponentBounds.1,
    Nat.ne_of_gt hyExponentBounds.1, Option.some.injEq]
  exact hrefines.symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
