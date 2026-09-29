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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Fma.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Multiplication.Proof

/-!
# Correctness of two-word fused multiply-add

The specialized path accepts normal operands when the product and addend have the same sign and
the addend's scale is exactly the product scale plus `fracWidth`. Their sum fits in a `UInt256`
accumulator and is rounded once using the product rounder.

`fmaNormalSameSignAligned_refines` identifies accepted results with the generic finite kernel.
`fmaFinite_eq` extends the equality to the complete candidate chain, which uses the generic
implementation on all other inputs. Runtime clients can import `Fma.Runtime` separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Numerics.FixedWord

variable {fmt : FloatFormat}

/-! ## Fixed-limb representation lemmas -/

private theorem alignFmaAddend_toNat (h : Eligible fmt) (mantissa : UInt128) :
    (alignFmaAddend fmt mantissa).toNat = mantissa.toNat <<< fmt.fracWidth := by
  unfold alignFmaAddend
  exact UInt256.toNat_ofUInt128ShiftedLeft mantissa fmt.fracWidth h.frac_gt
    (by have := h.frac_le; omega)

/-- The scale offset of the addend fits a native word. -/
theorem addendOffset_toNat (h : Eligible fmt) :
    (UInt64.ofNat (fmt.bias + fmt.fracWidth - 1)).toNat = fmt.bias + fmt.fracWidth - 1 := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have hbias := h.bias_lt
  have hfrac := h.frac_le
  norm_num at hbias ⊢
  omega

/-! ## Normalization and nearest-even rounding -/

private theorem roundNormalFma_refines (h : Eligible fmt)
    (sign : Bool) (xExponent yExponent : UInt64)
    (xMantissa yMantissa zMantissa : UInt128)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < fmt.expAllOnesNat)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < fmt.expAllOnesNat)
    (hxMantissa :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hzMantissa :
      2 ^ fmt.fracWidth ≤ zMantissa.toNat ∧ zMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (result : Model fmt)
    (hcarry :
      (add256 (mul128 xMantissa yMantissa) (alignFmaAddend fmt zMantissa)).carry = 0)
    (hresult :
      roundNormalProductOption sign xExponent yExponent
          (add256 (mul128 xMantissa yMantissa) (alignFmaAddend fmt zMantissa)).value
          (UInt64.ofNat
            (add256 (mul128 xMantissa yMantissa) (alignFmaAddend fmt zMantissa)).value.log2) =
        some result) :
    result =
      FiniteProductRound.round fmt sign
        (xMantissa.toNat * yMantissa.toNat + (zMantissa.toNat <<< fmt.fracWidth))
        ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
  have hfracLe := h.frac_le
  let product := mul128 xMantissa yMantissa
  let aligned := alignFmaAddend fmt zMantissa
  let sum := add256 product aligned
  have hproduct : product.toNat = xMantissa.toNat * yMantissa.toNat := by
    simp [product]
  have haligned : aligned.toNat = zMantissa.toNat <<< fmt.fracWidth :=
    alignFmaAddend_toNat h zMantissa
  have hsum :
      sum.value.toNat =
        xMantissa.toNat * yMantissa.toNat + (zMantissa.toNat <<< fmt.fracWidth) := by
    rw [add256_value_toNat_of_carry_zero product aligned]
    · rw [hproduct, haligned]
    · simpa [sum, product, aligned] using hcarry
  have hsumLower : 2 ^ (2 * fmt.fracWidth) ≤ sum.value.toNat := by
    rw [hsum]
    calc
      2 ^ (2 * fmt.fracWidth) = 2 ^ fmt.fracWidth * 2 ^ fmt.fracWidth := by
        rw [two_mul, pow_add]
      _ ≤ xMantissa.toNat * yMantissa.toNat := Nat.mul_le_mul hxMantissa.1 hyMantissa.1
      _ ≤ _ := Nat.le_add_right _ _
  have hsumUpper : sum.value.toNat < 2 ^ (2 * fmt.fracWidth + 3) := by
    rw [hsum, Nat.shiftLeft_eq]
    have hproductLt :
        xMantissa.toNat * yMantissa.toNat < 2 ^ (fmt.fracWidth + 1) * 2 ^ (fmt.fracWidth + 1) :=
      Nat.mul_lt_mul'' hxMantissa.2 hyMantissa.2
    have haddendLt :
        zMantissa.toNat * 2 ^ fmt.fracWidth < 2 ^ (fmt.fracWidth + 1) * 2 ^ fmt.fracWidth :=
      Nat.mul_lt_mul_of_pos_right hzMantissa.2 (Nat.two_pow_pos _)
    have hpow1 : 2 ^ (fmt.fracWidth + 1) * 2 ^ (fmt.fracWidth + 1) = 2 ^ (2 * fmt.fracWidth + 2)
      := by
      rw [← pow_add]
      congr 1
      omega
    have hpow2 : 2 ^ (fmt.fracWidth + 1) * 2 ^ fmt.fracWidth = 2 ^ (2 * fmt.fracWidth + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hpow3 : 2 ^ (2 * fmt.fracWidth + 3) = 2 ^ (2 * fmt.fracWidth + 2) + 2 ^ (2 *
      fmt.fracWidth + 2) := by
      rw [pow_succ]
      ring
    have hpow4 : 2 ^ (2 * fmt.fracWidth + 1) ≤ 2 ^ (2 * fmt.fracWidth + 2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [hpow1] at hproductLt
    rw [hpow2] at haddendLt
    omega
  have hsumNe : sum.value.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hsumLower)
  have hlogLower : 2 * fmt.fracWidth ≤ sum.value.toNat.log2 :=
    (Nat.le_log2 hsumNe).2 hsumLower
  have hlogUpper : sum.value.toNat.log2 < 2 * fmt.fracWidth + 3 :=
    (Nat.log2_lt hsumNe).2 hsumUpper
  have hleading : (UInt64.ofNat sum.value.log2).toNat = sum.value.toNat.log2 := by
    rw [UInt256.log2_toNat, UInt64.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    omega
  rw [← hsum]
  exact roundNormalProduct_refines h sign xExponent yExponent sum.value
    (UInt64.ofNat sum.value.log2) hxExponent hyExponent hleading
    (by rw [hleading]; omega) hsumLower result
    (by simpa [sum, product, aligned] using hresult)

/-! ## Equal-sign aligned fast path -/

/-- Every result accepted by the aligned pair FMA kernel equals the exact finite kernel. -/
theorem fmaNormalSameSignAligned_refines (h : Eligible fmt)
    (x y z result : Model fmt)
    (hresult : fmaNormalSameSignAlignedOption x y z = some result) :
    FiniteKernel.fmaOption x y z = some result := by
  have hbias := h.bias_lt
  have hfracLe := h.frac_le
  have hallOnes := fmt.expAllOnesNat_eq_two_mul_bias_add_one
  have hoffsetWord := addendOffset_toNat h
  have hfracWord := fracWidth_toNat h
  let xWords := toWords x
  let yWords := toWords y
  let zWords := toWords z
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  let zExponent := expField fmt zWords.hi
  let xHigh := fracHigh fmt xWords.hi
  let yHigh := fracHigh fmt yWords.hi
  let zHigh := fracHigh fmt zWords.hi
  let xMantissa := normalMantissa fmt xHigh xWords.lo
  let yMantissa := normalMantissa fmt yHigh yWords.lo
  let zMantissa := normalMantissa fmt zHigh zWords.lo
  let productScale := (xExponent - 1) + (yExponent - 1)
  let zProductScale := (zExponent - 1) + UInt64.ofNat (fmt.bias + fmt.fracWidth - 1)
  let productSign := Bool.xor x.bits.msb y.bits.msb
  let zSign := z.bits.msb
  let product := mul128 xMantissa yMantissa
  let aligned := alignFmaAddend fmt zMantissa
  let sum := add256 product aligned
  by_cases hxZero : xExponent = 0
  · simp [fmaNormalSameSignAlignedOption, xWords, xExponent, hxZero] at hresult
  by_cases hxExceptional : xExponent = expAllOnes fmt
  · simp [fmaNormalSameSignAlignedOption, xWords, xExponent, hxExceptional] at hresult
  by_cases hyZero : yExponent = 0
  · simp [fmaNormalSameSignAlignedOption, yWords, yExponent, hyZero] at hresult
  by_cases hyExceptional : yExponent = expAllOnes fmt
  · simp [fmaNormalSameSignAlignedOption, yWords, yExponent, hyExceptional] at hresult
  by_cases hzZero : zExponent = 0
  · simp [fmaNormalSameSignAlignedOption, zWords, zExponent, hzZero] at hresult
  by_cases hzExceptional : zExponent = expAllOnes fmt
  · simp [fmaNormalSameSignAlignedOption, zWords, zExponent, hzExceptional] at hresult
  have haccepted := hresult
  simp only [fmaNormalSameSignAlignedOption, Bool.bne_assoc, bne_iff_ne, ne_eq, Bool.or_eq_true,
    beq_iff_eq, hxZero,
    hxExceptional, or_self, hyZero, hyExceptional, hzZero, hzExceptional, ↓reduceIte,
      UInt256.log2_toNat, ite_not,
    Option.ite_none_right_eq_some, zWords, zExponent, yWords, yExponent, xExponent,
    xWords] at haccepted
  rcases haccepted with
    ⟨hsignRaw, halignedRaw, hcarryRaw, hroundRaw⟩
  have hsign : productSign = zSign := by
    have hsignRaw' :
        x.bits.msb = (y.bits.msb != z.bits.msb) := by
      simpa using hsignRaw
    dsimp [productSign, zSign]
    cases hxSign : x.bits.msb <;>
      cases hySign : y.bits.msb <;>
      cases hzSign : z.bits.msb <;>
      simp [hxSign, hySign, hzSign] at hsignRaw' ⊢
  have haligned : productScale + UInt64.ofNat fmt.fracWidth = zProductScale := by
    simpa [productScale, zProductScale] using halignedRaw
  have hcarry : sum.carry = 0 := by
    simpa [sum, product, aligned, xMantissa, yMantissa, zMantissa,
      xHigh, yHigh, zHigh] using hcarryRaw
  have hround :
      roundNormalProductOption productSign xExponent yExponent sum.value
          (UInt64.ofNat sum.value.log2) =
        some result := by
    simpa [productSign, sum, product, aligned, xMantissa, yMantissa,
      zMantissa, xHigh, yHigh, zHigh] using hroundRaw
  have hxExponentBounds : 0 < xExponent.toNat ∧ xExponent.toNat < fmt.expAllOnesNat :=
    normalExponent_bounds h x hxZero hxExceptional
  have hyExponentBounds : 0 < yExponent.toNat ∧ yExponent.toNat < fmt.expAllOnesNat :=
    normalExponent_bounds h y hyZero hyExceptional
  have hzExponentBounds : 0 < zExponent.toNat ∧ zExponent.toNat < fmt.expAllOnesNat :=
    normalExponent_bounds h z hzZero hzExceptional
  have hxMantissaBounds :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h xHigh xWords.lo (fracHigh_lt h xWords.hi)
  have hyMantissaBounds :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h yHigh yWords.lo (fracHigh_lt h yWords.hi)
  have hzMantissaBounds :
      2 ^ fmt.fracWidth ≤ zMantissa.toNat ∧ zMantissa.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h zHigh zWords.lo (fracHigh_lt h zWords.hi)
  have hrefines :=
    roundNormalFma_refines h productSign xExponent yExponent
      xMantissa yMantissa zMantissa hxExponentBounds hyExponentBounds
      hxMantissaBounds hyMantissaBounds hzMantissaBounds result
      (by simpa [sum, product, aligned] using hcarry)
      (by simpa [sum] using hround)
  have hxOne : (1 : UInt64) ≤ xExponent :=
    UInt64.le_iff_toNat_le.mpr (by
      rw [show UInt64.toNat 1 = 1 by decide]
      omega)
  have hyOne : (1 : UInt64) ≤ yExponent :=
    UInt64.le_iff_toNat_le.mpr (by
      rw [show UInt64.toNat 1 = 1 by decide]
      omega)
  have hzOne : (1 : UInt64) ≤ zExponent :=
    UInt64.le_iff_toNat_le.mpr (by
      rw [show UInt64.toNat 1 = 1 by decide]
      omega)
  have hxScale : (xExponent - 1).toNat = xExponent.toNat - 1 :=
    UInt64.toNat_sub_of_le xExponent 1 hxOne
  have hyScale : (yExponent - 1).toNat = yExponent.toNat - 1 :=
    UInt64.toNat_sub_of_le yExponent 1 hyOne
  have hzScale : (zExponent - 1).toNat = zExponent.toNat - 1 :=
    UInt64.toNat_sub_of_le zExponent 1 hzOne
  have hproductScale :
      productScale.toNat = (xExponent.toNat - 1) + (yExponent.toNat - 1) := by
    unfold productScale
    rw [UInt64.toNat_add, hxScale, hyScale]
    apply Nat.mod_eq_of_lt
    norm_num at hbias ⊢
    omega
  have hzProductScale :
      zProductScale.toNat = (zExponent.toNat - 1) + (fmt.bias + fmt.fracWidth - 1) := by
    unfold zProductScale
    rw [UInt64.toNat_add, hzScale, hoffsetWord]
    apply Nat.mod_eq_of_lt
    norm_num at hbias ⊢
    omega
  have hproductScaleAligned :
      (productScale + UInt64.ofNat fmt.fracWidth).toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) + fmt.fracWidth := by
    rw [UInt64.toNat_add, hproductScale, hfracWord]
    apply Nat.mod_eq_of_lt
    norm_num at hbias ⊢
    omega
  have halignedNat :
      (xExponent.toNat - 1) + (yExponent.toNat - 1) + fmt.fracWidth =
        (zExponent.toNat - 1) + FiniteKernel.finiteScaleOffset fmt := by
    have hword := congrArg UInt64.toNat haligned
    rw [hproductScaleAligned, hzProductScale] at hword
    unfold FiniteKernel.finiteScaleOffset
    rw [h.exponentBias_eq]
    exact hword
  have hxSign : signBit fmt xWords.hi = x.bits.msb := by
    rw [signBit_eq h x, Model.signBit_eq_msb]
  have hySign : signBit fmt yWords.hi = y.bits.msb := by
    rw [signBit_eq h y, Model.signBit_eq_msb]
  have hzSign : signBit fmt zWords.hi = zSign := by
    rw [signBit_eq h z, Model.signBit_eq_msb]
  have hproductSign :
      Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi) = productSign := by
    simp [hxSign, hySign, productSign]
  have hxMantissaNe : xMantissa.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hxMantissaBounds.1)
  have hyMantissaNe : yMantissa.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hyMantissaBounds.1)
  have hzMantissaNe : zMantissa.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hzMantissaBounds.1)
  have hcomponents :
      FiniteKernel.fmaComponents fmt
          { sign := signBit fmt xWords.hi
            exponent := xExponent.toNat
            mantissa := xMantissa.toNat }
          { sign := signBit fmt yWords.hi
            exponent := yExponent.toNat
            mantissa := yMantissa.toNat }
          { sign := signBit fmt zWords.hi
            exponent := zExponent.toNat
            mantissa := zMantissa.toNat } =
        result := by
    calc
      _ = FiniteProductRound.round fmt productSign
            (xMantissa.toNat * yMantissa.toNat +
              (zMantissa.toNat <<< fmt.fracWidth))
            ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
          simpa [hproductSign, hzSign, hsign] using
            FiniteKernel.fmaComponents_sameSign_aligned
              fmt h.isIEEE fmt.fracWidth
              (signBit fmt xWords.hi) (signBit fmt yWords.hi)
              xExponent.toNat yExponent.toNat zExponent.toNat
              xMantissa.toNat yMantissa.toNat zMantissa.toNat
              (Nat.ne_of_gt hxExponentBounds.1)
              (Nat.ne_of_gt hyExponentBounds.1)
              (Nat.ne_of_gt hzExponentBounds.1)
              hxMantissaNe hyMantissaNe hzMantissaNe halignedNat
      _ = result := hrefines.symm
  unfold FiniteKernel.fmaOption
  rw [decode_of_normalExponent h x hxZero hxExceptional,
    decode_of_normalExponent h y hyZero hyExceptional,
    decode_of_normalExponent h z hzZero hzExceptional]
  simp only [Option.some.injEq]
  simpa [xWords, yWords, zWords, xExponent, yExponent, zExponent,
    xHigh, yHigh, zHigh, xMantissa, yMantissa, zMantissa] using hcomponents

/-! ## Complete finite dispatcher -/

/-- The two-word finite FMA chain equals the width-generic exact finite kernel. -/
theorem fmaFinite_eq (h : Eligible fmt) (x y z : Model fmt) :
    fmaFiniteOption x y z = FiniteKernel.fmaOption x y z := by
  unfold fmaFiniteOption
  cases hfast : fmaNormalSameSignAlignedOption x y z with
  | none =>
      exact (FiniteKernel.fmaRuntimeFlat_eq x y z).trans
        (FiniteKernel.fmaRuntime_eq x y z)
  | some result =>
      rw [fmaNormalSameSignAligned_refines h x y z result hfast]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
