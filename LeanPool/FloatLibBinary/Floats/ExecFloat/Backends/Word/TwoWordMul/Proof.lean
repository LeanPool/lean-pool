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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.TwoWordMul.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Format.Catalog
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.NormalPair.Proof
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.ProductRound.Proof
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.ModelRounding.Proof
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Correctness of native two-word finite multiplication

The executable `64 x 64 -> 128` normal-product tier lives in `TwoWordMul.Runtime`. Its refinement
theorem identifies every successful native result with the exact format-generic product rounder.
The proof separates the two-word product and its leading-bit bounds from the shared one-word
carry and packing stage. Declined inputs remain the dispatcher's responsibility.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeTwoWordMul

open NativeSmallWord

/-- Binary64 is the standard specialization of the reusable two-word capacity tier. -/
theorem binary64_eligible : Eligible FloatFormat.binary64 := by
  decide

private theorem productLeading_toNat
    (fmt : FloatFormat)
    (hfracLower : 32 ≤ fmt.fracWidth)
    (hfracUpper : fmt.fracWidth ≤ 62)
    (xMantissa yMantissa : UInt64)
    (hxMantissa :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧
        xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧
        yMantissa.toNat < 2 ^ (fmt.fracWidth + 1)) :
    (productLeading fmt (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa)).toNat =
      (xMantissa.toNat * yMantissa.toNat).log2 := by
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let productNat := xMantissa.toNat * yMantissa.toNat
  let lower := 2 * fmt.fracWidth
  let thresholdShift := 2 * fmt.fracWidth + 1 - 64
  let threshold := (1 : UInt64) <<< UInt64.ofNat thresholdShift
  have hproduct :
      product.toNat = productNat := by
    simp [product, productNat]
  have hproductLower : 2 ^ lower ≤ productNat := by
    unfold lower productNat
    have hmul := Nat.mul_le_mul hxMantissa.1 hyMantissa.1
    simpa [← pow_add, two_mul] using hmul
  have hproductUpper : productNat < 2 ^ (lower + 2) := by
    unfold lower productNat
    have hmul := Nat.mul_lt_mul'' hxMantissa.2 hyMantissa.2
    rw [← pow_add] at hmul
    have hexponent :
        (fmt.fracWidth + 1) + (fmt.fracWidth + 1) =
          2 * fmt.fracWidth + 2 := by
      omega
    rwa [hexponent] at hmul
  have hproductNe : productNat ≠ 0 := by
    have hxPositive : 0 < xMantissa.toNat :=
      (Nat.two_pow_pos _).trans_le hxMantissa.1
    have hyPositive : 0 < yMantissa.toNat :=
      (Nat.two_pow_pos _).trans_le hyMantissa.1
    unfold productNat
    positivity
  have hlowerRange : 64 ≤ lower ∧ lower + 1 < 128 := by
    unfold lower
    omega
  have hshiftRange : 0 < thresholdShift ∧ thresholdShift < 64 := by
    unfold thresholdShift
    omega
  have hthreshold :
      threshold.toNat = 2 ^ thresholdShift := by
    unfold threshold
    rw [FloatLib.Numerics.FixedWord.shiftLeft_toNat]
    · simp [Nat.shiftLeft_eq]
    · exact hshiftRange.2
    · simp only [UInt64.reduceToNat, Nat.shiftLeft_eq, one_mul, Nat.reducePow]
      exact Nat.pow_lt_pow_right (by decide) hshiftRange.2
  have hbelow :
      product.hi < threshold ↔ productNat < 2 ^ (lower + 1) := by
    rw [UInt64.lt_iff_toNat_lt, hthreshold]
    rw [← hproduct]
    unfold FloatLib.Numerics.FixedWord.UInt128.toNat
    have hlo := product.lo.toNat_lt
    have hpow :
        2 ^ (lower + 1) = 2 ^ thresholdShift * 2 ^ 64 := by
      rw [← pow_add]
      apply congrArg (fun exponent : Nat => 2 ^ exponent)
      have hle : 64 ≤ 2 * fmt.fracWidth + 1 := by omega
      unfold thresholdShift lower
      omega
    rw [hpow]
    constructor
    · intro hhi
      calc
        product.lo.toNat + product.hi.toNat * 2 ^ 64 <
            2 ^ 64 + product.hi.toNat * 2 ^ 64 :=
          Nat.add_lt_add_right product.lo.toNat_lt _
        _ = (product.hi.toNat + 1) * 2 ^ 64 := by ring
        _ ≤ 2 ^ thresholdShift * 2 ^ 64 :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hhi)
    · intro htotal
      by_contra hhi
      have hhi' : 2 ^ thresholdShift ≤ product.hi.toNat :=
        Nat.le_of_not_gt hhi
      have hmul :
          2 ^ thresholdShift * 2 ^ 64 ≤
            product.hi.toNat * 2 ^ 64 :=
        Nat.mul_le_mul_right _ hhi'
      have htail :
          product.hi.toNat * 2 ^ 64 ≤
            product.lo.toNat + product.hi.toNat * 2 ^ 64 :=
        Nat.le_add_left _ _
      exact (Nat.not_lt_of_ge (hmul.trans htail)) htotal
  have hlowerWord :
      (UInt64.ofNat lower).toNat = lower := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    omega
  have hlowerSucc :
      (UInt64.ofNat lower + 1).toNat = lower + 1 := by
    rw [UInt64.toNat_add, hlowerWord]
    apply Nat.mod_eq_of_lt
    have hsmall : lower + 1 ≤ 125 := by
      unfold lower
      omega
    exact hsmall.trans_lt (by norm_num)
  by_cases hhigh : productNat < 2 ^ (lower + 1)
  · have hlog :
        productNat.log2 = lower :=
      (Nat.log2_eq_iff hproductNe).2 ⟨hproductLower, hhigh⟩
    have hnative : product.hi < threshold := hbelow.mpr hhigh
    unfold productLeading
    change
      (if product.hi < threshold then UInt64.ofNat lower
        else UInt64.ofNat lower + 1).toNat =
        productNat.log2
    rw [ite_eq_left hnative, hlowerWord, hlog]
  · have hge : 2 ^ (lower + 1) ≤ productNat :=
      Nat.le_of_not_gt hhigh
    have hlog :
        productNat.log2 = lower + 1 :=
      (Nat.log2_eq_iff hproductNe).2 ⟨hge, hproductUpper⟩
    have hnative : ¬product.hi < threshold := by
      intro h
      exact hhigh (hbelow.mp h)
    unfold productLeading
    change
      (if product.hi < threshold then UInt64.ofNat lower
        else UInt64.ofNat lower + 1).toNat =
        productNat.log2
    rw [ite_eq_right hnative, hlowerSucc, hlog]

private theorem roundProductAfterScaleBounds (fmt : FloatFormat) (hwidth : fmt.bitWidth ≤ 64)
  (hfracLower : 32 ≤ fmt.fracWidth) (hfracUpper : fmt.fracWidth ≤ 62) (sign : Bool)
  (xExponent yExponent xMantissa yMantissa : UInt64)
  (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < 2 ^ fmt.expWidth)
  (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < 2 ^ fmt.expWidth)
  (hxMantissa : 2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ (fmt.fracWidth + 1)) :
  let product := Numerics.FixedWord.mul64 xMantissa yMantissa;
  let productNat := xMantissa.toNat * yMantissa.toNat;
  let leading := productLeading fmt product;
  xExponent.toNat < 2 ^ 31 →
    yExponent.toNat < 2 ^ 31 →
      product.toNat = productNat →
        productNat ≠ 0 →
          productNat < 2 ^ (2 * fmt.fracWidth + 2) →
            leading.toNat = productNat.log2 →
              2 * fmt.fracWidth ≤ leading.toNat →
                leading.toNat < 2 * fmt.fracWidth + 2 →
                  fmt.fracWidth ≤ leading.toNat →
                    let scale := xExponent - 1 + (yExponent - 1);
                    scale.toNat = xExponent.toNat - 1 + (yExponent.toNat - 1) →
                      let position := leading + scale;
                      position.toNat = productNat.log2 + (xExponent.toNat - 1 + (yExponent.toNat
                        - 1)) →
                        fmt.bias < 2 ^ 31 →
                          ¬productNat.log2 + (xExponent.toNat - 1 + (yExponent.toNat - 1)) <
                                fmt.bias + 2 * fmt.fracWidth - 1 →
                            NativeWordProduct.finishOption fmt sign position
                                (product.roundShiftRightEven (leading - UInt64.ofNat
                                  fmt.fracWidth).toNat) =
                              if
                                  3 * fmt.bias + 2 * fmt.fracWidth - 2 <
                                    if
                                        Numerics.roundShiftRightEven productNat (productNat.log2
                                          - fmt.fracWidth) =
                                          pow2 (fmt.fracWidth + 1) then
                                      productNat.log2 + (xExponent.toNat - 1 + (yExponent.toNat -
                                        1)) + 1
                                    else productNat.log2 + (xExponent.toNat - 1 +
                                      (yExponent.toNat - 1)) then
                                none
                              else
                                some
                                  (ofFields fmt sign
                                    ((if
                                          Numerics.roundShiftRightEven productNat
                                            (productNat.log2 - fmt.fracWidth) =
                                            pow2 (fmt.fracWidth + 1) then
                                        productNat.log2 + (xExponent.toNat - 1 + (yExponent.toNat
                                          - 1)) + 1
                                      else productNat.log2 + (xExponent.toNat - 1 +
                                        (yExponent.toNat - 1))) -
                                      (fmt.bias + 2 * fmt.fracWidth - 2))
                                    ((if
                                          Numerics.roundShiftRightEven productNat
                                            (productNat.log2 - fmt.fracWidth) =
                                            pow2 (fmt.fracWidth + 1) then
                                        pow2 fmt.fracWidth
                                      else Numerics.roundShiftRightEven productNat
                                        (productNat.log2 - fmt.fracWidth)) -
                                      pow2 fmt.fracWidth)) := by
  intro product productNat leading hxExponent31 hyExponent31 hproduct hproductNe hproductUpper
    hleading hleadingLower hleadingUpper hfracLeading scale hscale position hposition hbias
    hsubnormal
  let rounded :=
    product.roundShiftRightEven
      (leading - UInt64.ofNat fmt.fracWidth).toNat
  let roundedNat :=
    Numerics.roundShiftRightEven productNat (productNat.log2 - fmt.fracWidth)
  have hfracWord :
      (UInt64.ofNat fmt.fracWidth).toNat = fmt.fracWidth := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    omega
  have hleadingWord :
      UInt64.ofNat fmt.fracWidth ≤ leading := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hfracWord]
    exact hfracLeading
  have hshift :
      (leading - UInt64.ofNat fmt.fracWidth).toNat =
        productNat.log2 - fmt.fracWidth := by
    rw [UInt64.toNat_sub_of_le _ _ hleadingWord, hleading, hfracWord]
  have hshiftLower :
      fmt.fracWidth ≤
        (leading - UInt64.ofNat fmt.fracWidth).toNat := by
    rw [hshift, ← hleading]
    omega
  have hshiftUpper :
      (leading - UInt64.ofNat fmt.fracWidth).toNat ≤
        fmt.fracWidth + 1 := by
    rw [hshift, ← hleading]
    omega
  have hshiftPositive :
      0 < (leading - UInt64.ofNat fmt.fracWidth).toNat := by
    omega
  have hshiftLt :
      (leading - UInt64.ofNat fmt.fracWidth).toNat < 64 := by
    omega
  have hproductWordUpper :
      product.toNat < 2 ^ (2 * fmt.fracWidth + 2) := by
    rwa [hproduct]
  have hhiSmall :
      product.hi.toNat <
        2 ^ (2 * fmt.fracWidth + 2 - 64) := by
    have hexponent :
        2 * fmt.fracWidth + 2 =
          (2 * fmt.fracWidth + 2 - 64) + 64 := by
      omega
    have hmul :
        product.hi.toNat * 2 ^ 64 <
          2 ^ (2 * fmt.fracWidth + 2) := by
      calc
        product.hi.toNat * 2 ^ 64 ≤ product.toNat := by
          unfold FloatLib.Numerics.FixedWord.UInt128.toNat
          exact Nat.le_add_left _ _
        _ < 2 ^ (2 * fmt.fracWidth + 2) := hproductWordUpper
    rw [hexponent, pow_add] at hmul
    exact (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ 64)).mp hmul
  have hhigh :
      product.hi.toNat <
        2 ^ (leading - UInt64.ofNat fmt.fracWidth).toNat := by
    exact hhiSmall.trans_le <|
      Nat.pow_le_pow_right (by decide) (by omega)
  have hlogUpper :
      productNat < 2 ^ (productNat.log2 + 1) :=
    ((Nat.log2_eq_iff hproductNe).mp rfl).2
  have hquotientBase :
      productNat /
          2 ^ (leading - UInt64.ofNat fmt.fracWidth).toNat <
        2 ^ (fmt.fracWidth + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [← pow_add]
    have hexponent :
        fmt.fracWidth + 1 +
            (leading - UInt64.ofNat fmt.fracWidth).toNat =
          productNat.log2 + 1 := by
      rw [hshift]
      omega
    rwa [hexponent]
  have hquotient :
      (product.toNat >>>
          (leading - UInt64.ofNat fmt.fracWidth).toNat) + 1 <
        2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow, hproduct]
    have hpow :
        2 ^ (fmt.fracWidth + 1) < 2 ^ 64 :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have hrounded :
      rounded.toNat = roundedNat := by
    unfold rounded roundedNat
    rw [FloatLib.Numerics.FixedWord.UInt128.roundShiftRightEven_toNat product
      (leading - UInt64.ofNat fmt.fracWidth).toNat
      hshiftPositive hshiftLt hhigh hquotient]
    rw [hproduct, hshift]
  have hhidden :
      (hiddenBit fmt).toNat = 2 ^ fmt.fracWidth :=
    NativeSmallWord.hiddenBit_toNat_of_width fmt hwidth
  have hcarryBit :
      (carryBit fmt).toNat = 2 ^ (fmt.fracWidth + 1) :=
    NativeSmallWord.carryBit_toNat_of_width fmt hwidth (by omega)
  have hroundedDef :
      product.roundShiftRightEven
          (leading - UInt64.ofNat fmt.fracWidth).toNat = rounded := rfl
  have hroundedNatDef :
      Numerics.roundShiftRightEven productNat
          (productNat.log2 - fmt.fracWidth) = roundedNat := rfl
  rw [hroundedDef, hroundedNatDef]
  have hpositionAdd :
      (position + 1).toNat = position.toNat + 1 := by
    apply FloatLib.Numerics.FixedWord.uint64_add_toNat_of_lt
    rw [hposition, UInt64.toNat_one]
    omega
  have hpositionAddNat :
      (position + 1).toNat =
        productNat.log2 +
          ((xExponent.toNat - 1) + (yExponent.toNat - 1)) + 1 := by
    rw [hpositionAdd, hposition]
  have hroundedLower :
      2 ^ fmt.fracWidth ≤ roundedNat := by
    have hfracLog : fmt.fracWidth ≤ productNat.log2 := by
      rwa [← hleading]
    unfold roundedNat
    simpa [roundMantissaToLeadingBitEven, hfracLog,
      pow2_eq_two_pow] using
      pow2_le_roundMantissaToLeadingBitEven productNat
        fmt.fracWidth hproductNe
  have hnormal :
      fmt.bias + 2 * fmt.fracWidth - 1 ≤
        productNat.log2 +
          ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
    omega
  exact NativeWordProduct.finish_eq fmt hwidth sign position rounded
    (productNat.log2 +
      ((xExponent.toNat - 1) + (yExponent.toNat - 1)))
    roundedNat hposition hpositionAddNat hrounded hnormal
    hhidden hcarryBit hroundedLower

private theorem roundNormalProduct_eq_spec
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 31)
    (hfracLower : 32 ≤ fmt.fracWidth)
    (hfracUpper : fmt.fracWidth ≤ 62)
    (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : UInt64)
    (hxExponent :
      0 < xExponent.toNat ∧ xExponent.toNat < 2 ^ fmt.expWidth)
    (hyExponent :
      0 < yExponent.toNat ∧ yExponent.toNat < 2 ^ fmt.expWidth)
    (hxMantissa :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧
        xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧
        yMantissa.toNat < 2 ^ (fmt.fracWidth + 1)) :
    roundNormalProductOption fmt sign xExponent yExponent xMantissa yMantissa =
      FiniteProductRound.normalSpecOption fmt sign
        xExponent.toNat yExponent.toNat xMantissa.toNat yMantissa.toNat := by
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let productNat := xMantissa.toNat * yMantissa.toNat
  let leading := productLeading fmt product
  have hpowExp :
      2 ^ fmt.expWidth ≤ 2 ^ 31 :=
    Nat.pow_le_pow_right (by decide) hexpWidth
  have hxExponent31 : xExponent.toNat < 2 ^ 31 :=
    hxExponent.2.trans_le hpowExp
  have hyExponent31 : yExponent.toNat < 2 ^ 31 :=
    hyExponent.2.trans_le hpowExp
  have hproduct :
      product.toNat = productNat := by
    simp [product, productNat]
  have hproductNe : productNat ≠ 0 := by
    have hxPositive : 0 < xMantissa.toNat :=
      (Nat.two_pow_pos _).trans_le hxMantissa.1
    have hyPositive : 0 < yMantissa.toNat :=
      (Nat.two_pow_pos _).trans_le hyMantissa.1
    unfold productNat
    positivity
  have hproductLower :
      2 ^ (2 * fmt.fracWidth) ≤ productNat := by
    unfold productNat
    have hmul := Nat.mul_le_mul hxMantissa.1 hyMantissa.1
    simpa [← pow_add, two_mul] using hmul
  have hproductUpper :
      productNat < 2 ^ (2 * fmt.fracWidth + 2) := by
    unfold productNat
    have hmul := Nat.mul_lt_mul'' hxMantissa.2 hyMantissa.2
    rw [← pow_add] at hmul
    have hexponent :
        (fmt.fracWidth + 1) + (fmt.fracWidth + 1) =
          2 * fmt.fracWidth + 2 := by
      omega
    rwa [hexponent] at hmul
  have hleading :
      leading.toNat = productNat.log2 := by
    unfold leading product
    exact productLeading_toNat fmt hfracLower hfracUpper
      xMantissa yMantissa hxMantissa hyMantissa
  have hleadingLower :
      2 * fmt.fracWidth ≤ leading.toNat := by
    rw [hleading]
    exact (Nat.le_log2 hproductNe).2 hproductLower
  have hleadingUpper :
      leading.toNat < 2 * fmt.fracWidth + 2 := by
    rw [hleading]
    exact (Nat.log2_lt hproductNe).2 hproductUpper
  have hfracLeading : fmt.fracWidth ≤ leading.toNat := by
    omega
  have hxOne : (1 : UInt64) ≤ xExponent := by
    apply UInt64.le_iff_toNat_le.mpr
    simp only [UInt64.reduceToNat]
    omega
  have hyOne : (1 : UInt64) ≤ yExponent := by
    apply UInt64.le_iff_toNat_le.mpr
    simp only [UInt64.reduceToNat]
    omega
  have hxScale :
      (xExponent - 1).toNat = xExponent.toNat - 1 :=
    UInt64.toNat_sub_of_le xExponent 1 hxOne
  have hyScale :
      (yExponent - 1).toNat = yExponent.toNat - 1 :=
    UInt64.toNat_sub_of_le yExponent 1 hyOne
  let scale := (xExponent - 1) + (yExponent - 1)
  have hscale :
      scale.toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) := by
    unfold scale
    rw [UInt64.toNat_add, hxScale, hyScale]
    apply Nat.mod_eq_of_lt
    omega
  let position := leading + scale
  have hposition :
      position.toNat =
        productNat.log2 +
          ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
    unfold position
    rw [UInt64.toNat_add, hleading, hscale]
    apply Nat.mod_eq_of_lt
    have hleading126 : leading.toNat < 126 := by omega
    norm_num at hxExponent31 hyExponent31 ⊢
    omega
  have hbias :
      fmt.bias < 2 ^ 31 :=
    (FloatFormat.bias_lt_pow_expWidth fmt).trans_le hpowExp
  have hnormalThreshold :
      (UInt64.ofNat
          (fmt.bias + 2 * fmt.fracWidth - 1)).toNat =
        fmt.bias + 2 * fmt.fracWidth - 1 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    norm_num at hbias ⊢
    omega
  unfold roundNormalProductOption FiniteProductRound.normalSpecOption
  dsimp only
  rw [show FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa = product by rfl]
  rw [show xMantissa.toNat * yMantissa.toNat = productNat by rfl]
  rw [show productLeading fmt product = leading by rfl]
  rw [show xExponent - 1 + (yExponent - 1) = scale by rfl]
  rw [show leading + scale = position by rfl]
  by_cases hsubnormal :
      productNat.log2 +
          ((xExponent.toNat - 1) + (yExponent.toNat - 1)) <
        fmt.bias + 2 * fmt.fracWidth - 1
  · have hsubnormalWord :
        position < UInt64.ofNat
          (fmt.bias + 2 * fmt.fracWidth - 1) := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [hposition, hnormalThreshold]
      exact hsubnormal
    rw [ite_eq_left hsubnormalWord, ite_eq_left hsubnormal]
  have hsubnormalWord :
      ¬position < UInt64.ofNat
        (fmt.bias + 2 * fmt.fracWidth - 1) := by
    intro h
    apply hsubnormal
    have hnat := UInt64.lt_iff_toNat_lt.mp h
    rwa [hposition, hnormalThreshold] at hnat
  rw [ite_eq_right hsubnormalWord, ite_eq_right hsubnormal]
  exact roundProductAfterScaleBounds (fmt := fmt) (hwidth := hwidth)
    (hfracLower := hfracLower) (hfracUpper := hfracUpper) (sign := sign)
    (xExponent := xExponent) (yExponent := yExponent) (xMantissa := xMantissa)
    (yMantissa := yMantissa) (hxExponent := hxExponent) (hyExponent := hyExponent)
    (hxMantissa := hxMantissa) hxExponent31 hyExponent31 hproduct hproductNe hproductUpper
    hleading hleadingLower hleadingUpper hfracLeading hscale hposition hbias hsubnormal

/--
A successful two-word normal-product round agrees with the exact finite-product rounder.
-/
theorem roundNormalProduct_refines
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 31)
    (hfracLower : 32 ≤ fmt.fracWidth)
    (hfracUpper : fmt.fracWidth ≤ 62)
    (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : UInt64)
    (hxExponent :
      0 < xExponent.toNat ∧ xExponent.toNat < 2 ^ fmt.expWidth)
    (hyExponent :
      0 < yExponent.toNat ∧ yExponent.toNat < 2 ^ fmt.expWidth)
    (hxMantissa :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧
        xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧
        yMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (result : Model fmt)
    (hresult :
      roundNormalProductOption fmt sign
          xExponent yExponent xMantissa yMantissa =
        some result) :
    result =
      FiniteProductRound.round fmt sign
        (xMantissa.toNat * yMantissa.toNat)
        ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
  rw [roundNormalProduct_eq_spec fmt hwidth hexpWidth
    hfracLower hfracUpper sign xExponent yExponent xMantissa yMantissa
    hxExponent hyExponent hxMantissa hyMantissa] at hresult
  exact FiniteProductRound.normalSpec_refines_of_normalized
    fmt sign xExponent.toNat yExponent.toNat
      xMantissa.toNat yMantissa.toNat
      hxMantissa.1 hyMantissa.1 result hresult

/--
A successful two-word normal multiplication agrees with the compact finite kernel.

The native tier handles normal operands for one-storage-word IEEE formats with precisions 33
through 62. Exceptional operands and boundary results return `none` and retain the generic path.
-/
theorem mulNormal_refines {fmt : FloatFormat}
    (heligible : Eligible fmt) (x y result : Model fmt)
    (hresult : mulNormalOption x y = some result) :
    FiniteKernel.mulOption x y = some result := by
  rcases heligible with ⟨hieee, hwidth, hfracLower, hfracUpper⟩
  have hexpWidth : fmt.expWidth ≤ 31 := by
    unfold FloatFormat.bitWidth at hwidth
    omega
  refine NativeNormalPair.mul_refines
    hieee hwidth (roundNormalProductOption fmt) ?_ x y result ?_
  · intro sign xExponent yExponent xMantissa yMantissa candidate
      hxExponent hyExponent hxMantissa hyMantissa hround
    exact roundNormalProduct_refines fmt hwidth hexpWidth
      hfracLower hfracUpper sign
      xExponent yExponent xMantissa yMantissa
      hxExponent hyExponent hxMantissa hyMantissa candidate hround
  · simpa [mulNormalOption] using hresult

end Model.NativeTwoWordMul
end FloatLib.Floats.Formats.BinaryInterchange
