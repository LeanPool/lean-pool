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
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Difference.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Fma.Runtime

/-!
# Verified scale-aligned binary64 fused multiply-add

For the accepted normal inputs, shifting the addend significand by the binary64 fraction width
places it at the product's scale. Their sum or difference needs at most 107 bits, so two native
words hold the exact intermediate value before one nearest-even rounding.

Exact zero, deep cancellation, different scale alignments, and results outside the normal
rounder's range use the generic finite kernel. Non-finite operands are handled by the outer
arithmetic dispatcher.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord

/-! ## Two-word exact arithmetic -/

private theorem alignFmaAddend_toNat (mantissa : UInt64)
    (hmantissa : mantissa.toNat < 2 ^ 53) :
    (alignFmaAddend mantissa).toNat = mantissa.toNat <<< 52 := by
  unfold alignFmaAddend
  have hfit :
      ({ hi := 0, lo := mantissa } : FloatLib.Numerics.FixedWord.UInt128).toNat <<< 52 <
        2 ^ 128 := by
    unfold FloatLib.Numerics.FixedWord.UInt128.toNat
    norm_num at hmantissa ⊢
    rw [Nat.shiftLeft_eq]
    nlinarith
  rw [FloatLib.Numerics.FixedWord.UInt128.shiftLeft_toNat _ 52 (by omega) hfit]
  simp [FloatLib.Numerics.FixedWord.UInt128.toNat]

private theorem fmaLeading_toNat (magnitude : FloatLib.Numerics.FixedWord.UInt128)
    (hmagnitude : magnitude.toNat ≠ 0)
    (hupper : magnitude.toNat < 2 ^ 107) :
    (fmaLeading magnitude).toNat = magnitude.toNat.log2 := by
  unfold fmaLeading
  rw [UInt64.toNat_ofNat', FloatLib.Numerics.FixedWord.UInt128.log2_toNat]
  apply Nat.mod_eq_of_lt
  have hlog : magnitude.toNat.log2 < 107 := by
    rw [Nat.log2_lt hmagnitude]
    exact hupper
  omega

/-! ## Scale-aligned component semantics -/

private theorem fmaComponents_opposite_aligned_addend_larger
    (xSign ySign zSign : Bool)
    (xExponent yExponent zExponent xMantissa yMantissa zMantissa : Nat)
    (hxExponent : xExponent ≠ 0)
    (hyExponent : yExponent ≠ 0)
    (hzExponent : zExponent ≠ 0)
    (hxMantissa : xMantissa ≠ 0)
    (hyMantissa : yMantissa ≠ 0)
    (hzMantissa : zMantissa ≠ 0)
    (hsign : Bool.xor xSign ySign ≠ zSign)
    (haligned :
      (xExponent - 1) + (yExponent - 1) + 52 =
        (zExponent - 1) + 1074)
    (hlt : xMantissa * yMantissa < zMantissa <<< 52) :
    FiniteKernel.fmaComponents FloatFormat.binary64
        { sign := xSign
          exponent := xExponent
          mantissa := xMantissa }
        { sign := ySign
          exponent := yExponent
          mantissa := yMantissa }
        { sign := zSign
          exponent := zExponent
          mantissa := zMantissa } =
      FiniteProductRound.round FloatFormat.binary64 zSign
        ((zMantissa <<< 52) - xMantissa * yMantissa)
        ((xExponent - 1) + (yExponent - 1)) := by
  rw [← FiniteKernel.fmaComponentsImpl_eq]
  unfold FiniteKernel.fmaComponentsImpl
  rw [ite_eq_left (by decide : FloatFormat.binary64.isIEEE = true)]
  unfold FiniteScaleAdd.roundSum
  simp only [FiniteKernel.scale, hxExponent, hyExponent, hzExponent,
    ite_false, hxMantissa, hyMantissa, hzMantissa, mul_eq_zero,
    beq_iff_eq]
  have hproduct : xMantissa * yMantissa ≠ 0 :=
    Nat.mul_ne_zero hxMantissa hyMantissa
  have hscale :
      (xExponent - 1) + (yExponent - 1) ≤
        (zExponent - 1) + FiniteKernel.finiteScaleOffset FloatFormat.binary64 := by
    change
      (xExponent - 1) + (yExponent - 1) ≤
        (zExponent - 1) + 1074
    omega
  simp only [or_self, ite_false]
  rw [ite_eq_left hscale]
  unfold FiniteScaleAdd.roundMagnitudes
  rw [ite_eq_right (by simpa only [beq_iff_eq] using hsign)]
  have hne :
      xMantissa * yMantissa ≠
        zMantissa <<<
          ((zExponent - 1) +
            FiniteKernel.finiteScaleOffset FloatFormat.binary64 -
            ((xExponent - 1) + (yExponent - 1))) := by
    intro heq
    have hoffset :
        FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 := by
      decide
    rw [hoffset] at heq
    have hshift :
        (zExponent - 1) + 1074 -
            ((xExponent - 1) + (yExponent - 1)) =
          52 := by
      omega
    rw [hshift] at heq
    omega
  rw [ite_eq_right (by simpa only [beq_iff_eq] using hne)]
  have hoffset :
      FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 := by
    decide
  rw [hoffset]
  have hshift :
      (zExponent - 1) + 1074 -
          ((xExponent - 1) + (yExponent - 1)) =
        52 := by
    omega
  rw [hshift, ite_eq_left hlt]
  rfl

private theorem fmaComponents_opposite_aligned_product_larger
    (xSign ySign zSign : Bool)
    (xExponent yExponent zExponent xMantissa yMantissa zMantissa : Nat)
    (hxExponent : xExponent ≠ 0)
    (hyExponent : yExponent ≠ 0)
    (hzExponent : zExponent ≠ 0)
    (hxMantissa : xMantissa ≠ 0)
    (hyMantissa : yMantissa ≠ 0)
    (hzMantissa : zMantissa ≠ 0)
    (hsign : Bool.xor xSign ySign ≠ zSign)
    (haligned :
      (xExponent - 1) + (yExponent - 1) + 52 =
        (zExponent - 1) + 1074)
    (hlt : zMantissa <<< 52 < xMantissa * yMantissa) :
    FiniteKernel.fmaComponents FloatFormat.binary64
        { sign := xSign
          exponent := xExponent
          mantissa := xMantissa }
        { sign := ySign
          exponent := yExponent
          mantissa := yMantissa }
        { sign := zSign
          exponent := zExponent
          mantissa := zMantissa } =
      FiniteProductRound.round FloatFormat.binary64
        (Bool.xor xSign ySign)
        (xMantissa * yMantissa - (zMantissa <<< 52))
        ((xExponent - 1) + (yExponent - 1)) := by
  rw [← FiniteKernel.fmaComponentsImpl_eq]
  unfold FiniteKernel.fmaComponentsImpl
  rw [ite_eq_left (by decide : FloatFormat.binary64.isIEEE = true)]
  unfold FiniteScaleAdd.roundSum
  simp only [FiniteKernel.scale, hxExponent, hyExponent, hzExponent,
    ite_false, hxMantissa, hyMantissa, hzMantissa, mul_eq_zero,
    beq_iff_eq]
  have hproduct : xMantissa * yMantissa ≠ 0 :=
    Nat.mul_ne_zero hxMantissa hyMantissa
  have hscale :
      (xExponent - 1) + (yExponent - 1) ≤
        (zExponent - 1) + FiniteKernel.finiteScaleOffset FloatFormat.binary64 := by
    change
      (xExponent - 1) + (yExponent - 1) ≤
        (zExponent - 1) + 1074
    omega
  simp only [or_self, ite_false]
  rw [ite_eq_left hscale]
  unfold FiniteScaleAdd.roundMagnitudes
  rw [ite_eq_right (by simpa only [beq_iff_eq] using hsign)]
  have hne :
      xMantissa * yMantissa ≠
        zMantissa <<<
          ((zExponent - 1) +
            FiniteKernel.finiteScaleOffset FloatFormat.binary64 -
            ((xExponent - 1) + (yExponent - 1))) := by
    intro heq
    have hoffset :
        FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 := by
      decide
    rw [hoffset] at heq
    have hshift :
        (zExponent - 1) + 1074 -
            ((xExponent - 1) + (yExponent - 1)) =
          52 := by
      omega
    rw [hshift] at heq
    omega
  rw [ite_eq_right (by simpa only [beq_iff_eq] using hne)]
  have hoffset :
      FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 := by
    decide
  rw [hoffset]
  have hshift :
      (zExponent - 1) + 1074 -
          ((xExponent - 1) + (yExponent - 1)) =
        52 := by
    omega
  rw [hshift, ite_eq_right (Nat.not_lt_of_ge hlt.le)]
  rfl

/-! ## Refinement of native product rounding -/

private theorem roundNormalFma_refines
    (sign : Bool) (xExponent yExponent : UInt64)
    (xMantissa yMantissa zMantissa : UInt64)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < 2047)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < 2047)
    (hxMantissa :
      2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53)
    (hyMantissa :
      2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53)
    (hzMantissa :
      2 ^ 52 ≤ zMantissa.toNat ∧ zMantissa.toNat < 2 ^ 53)
    (result : Value)
    (hcarry :
      (FloatLib.Numerics.FixedWord.add128
        (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa)
        (alignFmaAddend zMantissa)).carry = 0)
    (hresult :
      roundNormalProductOption sign xExponent yExponent
          (FloatLib.Numerics.FixedWord.add128
            (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa)
            (alignFmaAddend zMantissa)).value
          (fmaLeading
            (FloatLib.Numerics.FixedWord.add128
              (FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa)
              (alignFmaAddend zMantissa)).value) =
        some result) :
    result =
      FiniteProductRound.round FloatFormat.binary64 sign
        (xMantissa.toNat * yMantissa.toNat + (zMantissa.toNat <<< 52))
        ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let aligned := alignFmaAddend zMantissa
  let sum := FloatLib.Numerics.FixedWord.add128 product aligned
  have hproduct :
      product.toNat = xMantissa.toNat * yMantissa.toNat := by
    simp [product]
  have haligned :
      aligned.toNat = zMantissa.toNat <<< 52 := by
    exact alignFmaAddend_toNat zMantissa hzMantissa.2
  have hsum :
      sum.value.toNat =
        xMantissa.toNat * yMantissa.toNat + (zMantissa.toNat <<< 52) := by
    rw [FloatLib.Numerics.FixedWord.add128_value_toNat_of_carry_zero product aligned]
    · rw [hproduct, haligned]
    · simpa [sum, product, aligned] using hcarry
  have hsumLower : 2 ^ 104 ≤ sum.value.toNat := by
    rw [hsum]
    nlinarith
  have hsumUpper : sum.value.toNat < 2 ^ 107 := by
    rw [hsum, Nat.shiftLeft_eq]
    norm_num at hxMantissa hyMantissa hzMantissa ⊢
    nlinarith
  have hsumNe : sum.value.toNat ≠ 0 := by omega
  have hleading :
      (fmaLeading sum.value).toNat = sum.value.toNat.log2 :=
    fmaLeading_toNat sum.value hsumNe hsumUpper
  have hleadingRange :
      104 ≤ (fmaLeading sum.value).toNat ∧
        (fmaLeading sum.value).toNat ≤ 106 := by
    rw [hleading]
    constructor
    · rw [Nat.le_log2 hsumNe]
      exact hsumLower
    · have hlogLt : sum.value.toNat.log2 < 107 := by
        rw [Nat.log2_lt hsumNe]
        exact hsumUpper
      omega
  rw [← hsum]
  apply roundNormalProduct_refines sign xExponent yExponent sum.value
    (fmaLeading sum.value) hxExponent hyExponent hleading (by omega)
    (by omega) hsumUpper result
  simpa [sum, product, aligned] using hresult

private theorem roundNormalFmaDifference_refines
    (sign : Bool) (xExponent yExponent : UInt64)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < 2047)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < 2047)
    (hordered : right.toNat < left.toNat)
    (hleftUpper : left.toNat < 2 ^ 107)
    (hleadingMin :
      53 ≤ (fmaLeading (FloatLib.Numerics.FixedWord.UInt128.sub left right)).toNat)
    (result : Value)
    (hresult :
      roundNormalProductOption sign xExponent yExponent
          (FloatLib.Numerics.FixedWord.UInt128.sub left right)
          (fmaLeading (FloatLib.Numerics.FixedWord.UInt128.sub left right)) =
        some result) :
    result =
      FiniteProductRound.round FloatFormat.binary64 sign
        (left.toNat - right.toNat)
        ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
  let magnitude := FloatLib.Numerics.FixedWord.UInt128.sub left right
  have hmagnitude :
      magnitude.toNat = left.toNat - right.toNat := by
    exact FloatLib.Numerics.FixedWord.UInt128.sub_toNat left right hordered.le
  have hmagnitudeNe : magnitude.toNat ≠ 0 := by
    rw [hmagnitude]
    omega
  have hmagnitudeUpper : magnitude.toNat < 2 ^ 107 := by
    rw [hmagnitude]
    omega
  have hleading :
      (fmaLeading magnitude).toNat = magnitude.toNat.log2 :=
    fmaLeading_toNat magnitude hmagnitudeNe hmagnitudeUpper
  have hleadingRange :
      53 ≤ (fmaLeading magnitude).toNat ∧
        (fmaLeading magnitude).toNat ≤ 106 := by
    constructor
    · simpa [magnitude] using hleadingMin
    · rw [hleading]
      have hlogLt : magnitude.toNat.log2 < 107 := by
        rw [Nat.log2_lt hmagnitudeNe]
        exact hmagnitudeUpper
      omega
  have hmagnitudeLower : 2 ^ 52 ≤ magnitude.toNat := by
    have hpow :
        2 ^ magnitude.toNat.log2 ≤ magnitude.toNat :=
      (Nat.le_log2 hmagnitudeNe).mp (le_refl _)
    rw [← hleading] at hpow
    exact le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hpow
  rw [← hmagnitude]
  apply roundNormalProduct_refines sign xExponent yExponent magnitude
    (fmaLeading magnitude) hxExponent hyExponent hleading hleadingRange
    hmagnitudeLower hmagnitudeUpper result
  simpa [magnitude] using hresult

/-! ## Native fast-path refinements -/

private theorem fmaFiniteImplOption_eq_some_of_components (x y z result : Value)
    (hx : expField (toUInt64 x) ≠ 0x7ff)
    (hy : expField (toUInt64 y) ≠ 0x7ff)
    (hz : expField (toUInt64 z) ≠ 0x7ff)
    (hcomponents :
      FiniteKernel.fmaComponents FloatFormat.binary64
          { sign := signBit (toUInt64 x)
            exponent := (expField (toUInt64 x)).toNat
            mantissa :=
              (finiteMantissa (expField (toUInt64 x)) (fracField (toUInt64 x))).toNat }
          { sign := signBit (toUInt64 y)
            exponent := (expField (toUInt64 y)).toNat
            mantissa :=
              (finiteMantissa (expField (toUInt64 y)) (fracField (toUInt64 y))).toNat }
          { sign := signBit (toUInt64 z)
            exponent := (expField (toUInt64 z)).toNat
            mantissa :=
              (finiteMantissa (expField (toUInt64 z)) (fracField (toUInt64 z))).toNat } =
        result) :
    fmaFiniteImplOption x y z = some result := by
  unfold fmaFiniteImplOption
  rw [decode_of_finiteExponent x hx, decode_of_finiteExponent y hy,
    decode_of_finiteExponent z hz]
  simpa only [FiniteKernel.fmaComponentsImpl_eq, Option.some.injEq] using hcomponents

private theorem fmaNormalSameSignAligned_refines
    (x y z result : Value)
    (hresult : fmaNormalSameSignAlignedOption x y z = some result) :
    fmaFiniteImplOption x y z = some result := by
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let zBits := toUInt64 z
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  let xFraction := fracField xBits
  let yFraction := fracField yBits
  let zFraction := fracField zBits
  let xMantissa := finiteMantissa xExponent xFraction
  let yMantissa := finiteMantissa yExponent yFraction
  let zMantissa := finiteMantissa zExponent zFraction
  let productScale := finiteScale xExponent + finiteScale yExponent
  let zProductScale := finiteScale zExponent + 1074
  let productSign := Bool.xor (signBit xBits) (signBit yBits)
  let zSign := signBit zBits
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let aligned := alignFmaAddend zMantissa
  let sum := FloatLib.Numerics.FixedWord.add128 product aligned
  by_cases hxZero : xExponent = 0
  · simp [fmaNormalSameSignAlignedOption, xBits, xExponent, hxZero] at hresult
  by_cases hxExceptional : xExponent = 0x7ff
  · simp [fmaNormalSameSignAlignedOption, xBits, xExponent, hxExceptional] at hresult
  by_cases hyZero : yExponent = 0
  · simp [fmaNormalSameSignAlignedOption, yBits, yExponent, hyZero] at hresult
  by_cases hyExceptional : yExponent = 0x7ff
  · simp [fmaNormalSameSignAlignedOption, yBits, yExponent, hyExceptional] at hresult
  by_cases hzZero : zExponent = 0
  · simp [fmaNormalSameSignAlignedOption, zBits, zExponent, hzZero] at hresult
  by_cases hzExceptional : zExponent = 0x7ff
  · simp [fmaNormalSameSignAlignedOption, zBits, zExponent, hzExceptional] at hresult
  have haccepted := hresult
  simp only [fmaNormalSameSignAlignedOption, Bool.or_eq_true, beq_iff_eq, hxZero, hxExceptional,
    or_self, hyZero,
    hyExceptional, hzZero, hzExceptional, ↓reduceIte, Bool.bne_assoc, bne_iff_ne, ne_eq, ite_not,
    Option.ite_none_left_eq_some, not_or, Decidable.not_not, Option.ite_none_right_eq_some,
      zExponent, yBits, xBits,
    xExponent, yExponent, zBits] at haccepted
  rcases haccepted with
    ⟨⟨hsignRaw, halignedRaw⟩, hcarryRaw, hroundRaw⟩
  have hsign : productSign = zSign := by
    have hsignRaw' :
        signBit xBits = (signBit yBits != signBit zBits) := by
      simpa [xBits, yBits, zBits] using hsignRaw
    dsimp [productSign, zSign]
    cases hxSign : signBit xBits <;>
      cases hySign : signBit yBits <;>
      cases hzSign : signBit zBits <;>
      simp [hxSign, hySign, hzSign] at hsignRaw' ⊢
  have haligned : productScale + 52 = zProductScale := by
    simpa [productScale, zProductScale] using halignedRaw
  have hcarry : sum.carry = 0 := by
    simpa [sum, product, aligned, xMantissa, yMantissa, zMantissa,
      xFraction, yFraction, zFraction] using hcarryRaw
  have hround :
      roundNormalProductOption productSign xExponent yExponent sum.value
          (fmaLeading sum.value) =
        some result := by
    simpa [productSign, sum, product, aligned, xMantissa, yMantissa,
      zMantissa, xFraction, yFraction, zFraction] using hroundRaw
  have hxExponentBounds :
      0 < xExponent.toNat ∧ xExponent.toNat < 2047 := by
    simpa [xExponent, xBits] using
      normalExponent_bounds x hxZero hxExceptional
  have hyExponentBounds :
      0 < yExponent.toNat ∧ yExponent.toNat < 2047 := by
    simpa [yExponent, yBits] using
      normalExponent_bounds y hyZero hyExceptional
  have hzExponentBounds :
      0 < zExponent.toNat ∧ zExponent.toNat < 2047 := by
    simpa [zExponent, zBits] using
      normalExponent_bounds z hzZero hzExceptional
  have hxFractionBound : xFraction.toNat < 2 ^ 52 := by
    simpa [xFraction, xBits] using fracField_lt x
  have hyFractionBound : yFraction.toNat < 2 ^ 52 := by
    simpa [yFraction, yBits] using fracField_lt y
  have hzFractionBound : zFraction.toNat < 2 ^ 52 := by
    simpa [zFraction, zBits] using fracField_lt z
  have hxMantissaBounds :
      2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53 := by
    simpa [xMantissa] using
      finiteMantissa_bounds xExponent xFraction hxZero hxFractionBound
  have hyMantissaBounds :
      2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53 := by
    simpa [yMantissa] using
      finiteMantissa_bounds yExponent yFraction hyZero hyFractionBound
  have hzMantissaBounds :
      2 ^ 52 ≤ zMantissa.toNat ∧ zMantissa.toNat < 2 ^ 53 := by
    simpa [zMantissa] using
      finiteMantissa_bounds zExponent zFraction hzZero hzFractionBound
  have hrefines :=
    roundNormalFma_refines productSign xExponent yExponent
      xMantissa yMantissa zMantissa hxExponentBounds hyExponentBounds
      hxMantissaBounds hyMantissaBounds hzMantissaBounds result
      (by simpa [sum, product, aligned] using hcarry)
      (by simpa [sum] using hround)
  have hxScale :
      (finiteScale xExponent).toNat = xExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hxZero]
  have hyScale :
      (finiteScale yExponent).toNat = yExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hyZero]
  have hzScale :
      (finiteScale zExponent).toNat = zExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hzZero]
  have hproductScale :
      productScale.toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) := by
    unfold productScale
    rw [UInt64.toNat_add, hxScale, hyScale]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have hzProductScale :
      zProductScale.toNat = (zExponent.toNat - 1) + 1074 := by
    unfold zProductScale
    rw [UInt64.toNat_add, hzScale]
    apply Nat.mod_eq_of_lt
    change zExponent.toNat - 1 + 1074 < 18446744073709551616
    omega
  have hproductScaleAligned :
      (productScale + 52).toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) + 52 := by
    rw [UInt64.toNat_add, hproductScale]
    apply Nat.mod_eq_of_lt
    change
      (xExponent.toNat - 1) + (yExponent.toNat - 1) + 52 <
        18446744073709551616
    omega
  have halignedNat :
      (xExponent.toNat - 1) + (yExponent.toNat - 1) + 52 =
        (zExponent.toNat - 1) + 1074 := by
    have h := congrArg UInt64.toNat haligned
    simpa [hproductScaleAligned, hzProductScale] using h
  have hxMantissaNe : xMantissa.toNat ≠ 0 := by omega
  have hyMantissaNe : yMantissa.toNat ≠ 0 := by omega
  have hzMantissaNe : zMantissa.toNat ≠ 0 := by omega
  have hcomponents :
      FiniteKernel.fmaComponents FloatFormat.binary64
          { sign := signBit xBits
            exponent := xExponent.toNat
            mantissa := xMantissa.toNat }
          { sign := signBit yBits
            exponent := yExponent.toNat
            mantissa := yMantissa.toNat }
          { sign := zSign
            exponent := zExponent.toNat
            mantissa := zMantissa.toNat } =
        result := by
    calc
      _ = FiniteProductRound.round FloatFormat.binary64 productSign
            (xMantissa.toNat * yMantissa.toNat +
              (zMantissa.toNat <<< 52))
            ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
          simpa [productSign, zSign, hsign] using
            FiniteKernel.fmaComponents_sameSign_aligned
              FloatFormat.binary64 (by decide) 52
              (signBit xBits) (signBit yBits)
              xExponent.toNat yExponent.toNat zExponent.toNat
              xMantissa.toNat yMantissa.toNat zMantissa.toNat
              (Nat.ne_of_gt hxExponentBounds.1)
              (Nat.ne_of_gt hyExponentBounds.1)
              (Nat.ne_of_gt hzExponentBounds.1)
              hxMantissaNe hyMantissaNe hzMantissaNe halignedNat
      _ = result := hrefines.symm
  exact fmaFiniteImplOption_eq_some_of_components x y z result
    hxExceptional hyExceptional hzExceptional hcomponents

private theorem fmaAlignedDifferenceCases (x y z result : Value)
  (hresult : fmaNormalOppositeSignAlignedOption x y z = some result) :
  let xBits := toUInt64 x;
  let yBits := toUInt64 y;
  let zBits := toUInt64 z;
  let xExponent := expField xBits;
  let yExponent := expField yBits;
  let zExponent := expField zBits;
  let xFraction := fracField xBits;
  let yFraction := fracField yBits;
  let zFraction := fracField zBits;
  let xMantissa := finiteMantissa xExponent xFraction;
  let yMantissa := finiteMantissa yExponent yFraction;
  let zMantissa := finiteMantissa zExponent zFraction;
  let productScale := finiteScale xExponent + finiteScale yExponent;
  let zProductScale := finiteScale zExponent + 1074;
  let productSign := signBit xBits ^^ signBit yBits;
  let zSign := signBit zBits;
  let product := mul64 xMantissa yMantissa;
  let aligned := alignFmaAddend zMantissa;
  ¬xExponent = 0 →
    ¬xExponent = 2047 →
      ¬yExponent = 0 →
        ¬yExponent = 2047 →
          ¬zExponent = 0 →
            ¬zExponent = 2047 →
              productSign ≠ zSign →
                productScale + 52 = zProductScale →
                  product ≠ aligned →
                    0 < xExponent.toNat ∧ xExponent.toNat < 2047 →
                      0 < yExponent.toNat ∧ yExponent.toNat < 2047 →
                        0 < zExponent.toNat ∧ zExponent.toNat < 2047 →
                          product.toNat = xMantissa.toNat * yMantissa.toNat →
                            aligned.toNat = zMantissa.toNat <<< 52 →
                              product.toNat < 2 ^ 107 →
                                aligned.toNat < 2 ^ 107 →
                                  xExponent.toNat - 1 + (yExponent.toNat - 1) + 52 =
                                    zExponent.toNat - 1 + 1074 →
                                    xMantissa.toNat ≠ 0 →
                                      yMantissa.toNat ≠ 0 →
                                        zMantissa.toNat ≠ 0 → fmaFiniteImplOption x y z = some
                                          result
                                          := by
  intro xBits yBits zBits xExponent yExponent zExponent xFraction yFraction zFraction xMantissa
    yMantissa zMantissa productScale zProductScale productSign zSign product aligned hxZero
    hxExceptional hyZero hyExceptional hzZero hzExceptional hsign haligned hproductNe
    hxExponentBounds hyExponentBounds hzExponentBounds hproduct halignedValue hproductUpper
    halignedUpper halignedNat hxMantissaNe hyMantissaNe hzMantissaNe
  simp only [fmaNormalOppositeSignAlignedOption, Bool.or_eq_true, beq_iff_eq, hxZero, hxExceptional,
    or_self, hyZero,
    hyExceptional, hzZero, hzExceptional, ↓reduceIte, haligned, bne_self_eq_false, Bool.or_false,
      hsign, hproductNe,
    Option.ite_none_left_eq_some, UInt64.not_lt, zProductScale, zExponent, zBits, yFraction,
      product, productSign,
    productScale, xExponent, xBits, zFraction, xMantissa, aligned, zSign, yExponent, yMantissa,
      zMantissa, xFraction,
    yBits] at hresult
  let difference :=
    if UInt128.less product aligned then
      UInt128.sub aligned product
    else
      UInt128.sub product aligned
  change 53 ≤ fmaLeading difference ∧
    roundNormalProductOption (if UInt128.less product aligned then zSign else productSign)
      xExponent yExponent difference (fmaLeading difference) = some result at hresult
  by_cases hless : FloatLib.Numerics.FixedWord.UInt128.less product aligned = true
  · have hordered : product.toNat < aligned.toNat :=
      (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff product aligned).mp hless
    let magnitude := FloatLib.Numerics.FixedWord.UInt128.sub aligned product
    have haccepted := hresult
    simp only [difference, hless, ite_true] at haccepted
    rcases haccepted with ⟨hleading, hround⟩
    have hleadingWord :
        (53 : UInt64) ≤ fmaLeading magnitude := by
      apply UInt64.not_lt.mp
      simpa [magnitude] using hleading
    have hleadingMin :
        53 ≤ (fmaLeading magnitude).toNat := by
      simpa using UInt64.le_iff_toNat_le.mp hleadingWord
    have hrefines :=
      roundNormalFmaDifference_refines zSign xExponent yExponent
        aligned product hxExponentBounds hyExponentBounds hordered
        halignedUpper hleadingMin result
        (by simpa [magnitude] using hround)
    have hcomponents :
        FiniteKernel.fmaComponents FloatFormat.binary64
            { sign := signBit xBits
              exponent := xExponent.toNat
              mantissa := xMantissa.toNat }
            { sign := signBit yBits
              exponent := yExponent.toNat
              mantissa := yMantissa.toNat }
            { sign := zSign
              exponent := zExponent.toNat
              mantissa := zMantissa.toNat } =
          result := by
      calc
        _ = FiniteProductRound.round FloatFormat.binary64 zSign
              ((zMantissa.toNat <<< 52) -
                xMantissa.toNat * yMantissa.toNat)
              ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
            exact fmaComponents_opposite_aligned_addend_larger
              (signBit xBits) (signBit yBits) zSign
              xExponent.toNat yExponent.toNat zExponent.toNat
              xMantissa.toNat yMantissa.toNat zMantissa.toNat
              (Nat.ne_of_gt hxExponentBounds.1)
              (Nat.ne_of_gt hyExponentBounds.1)
              (Nat.ne_of_gt hzExponentBounds.1)
              hxMantissaNe hyMantissaNe hzMantissaNe
              (by simpa [productSign] using hsign) halignedNat
              (by simpa [hproduct, halignedValue] using hordered)
        _ = result := by
          rw [← halignedValue, ← hproduct]
          exact hrefines.symm
    exact fmaFiniteImplOption_eq_some_of_components x y z result
      hxExceptional hyExceptional hzExceptional hcomponents
  · have hnotLt : ¬product.toNat < aligned.toNat := by
      intro hordered
      exact hless
        ((FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff product aligned).mpr hordered)
    have hnatNe : product.toNat ≠ aligned.toNat := by
      intro heq
      exact hproductNe (FloatLib.Numerics.FixedWord.UInt128.toNat_injective heq)
    have hordered : aligned.toNat < product.toNat := by omega
    let magnitude := FloatLib.Numerics.FixedWord.UInt128.sub product aligned
    have haccepted := hresult
    simp only [difference, hless] at haccepted
    rcases haccepted with ⟨hleading, hround⟩
    have hleadingWord :
        (53 : UInt64) ≤ fmaLeading magnitude := by
      apply UInt64.not_lt.mp
      simpa [magnitude] using hleading
    have hleadingMin :
        53 ≤ (fmaLeading magnitude).toNat := by
      simpa using UInt64.le_iff_toNat_le.mp hleadingWord
    have hrefines :=
      roundNormalFmaDifference_refines productSign xExponent yExponent
        product aligned hxExponentBounds hyExponentBounds hordered
        hproductUpper hleadingMin result
        (by simpa [magnitude] using hround)
    have hcomponents :
        FiniteKernel.fmaComponents FloatFormat.binary64
            { sign := signBit xBits
              exponent := xExponent.toNat
              mantissa := xMantissa.toNat }
            { sign := signBit yBits
              exponent := yExponent.toNat
              mantissa := yMantissa.toNat }
            { sign := zSign
              exponent := zExponent.toNat
              mantissa := zMantissa.toNat } =
          result := by
      calc
        _ = FiniteProductRound.round FloatFormat.binary64 productSign
              (xMantissa.toNat * yMantissa.toNat -
                (zMantissa.toNat <<< 52))
              ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
            exact fmaComponents_opposite_aligned_product_larger
              (signBit xBits) (signBit yBits) zSign
              xExponent.toNat yExponent.toNat zExponent.toNat
              xMantissa.toNat yMantissa.toNat zMantissa.toNat
              (Nat.ne_of_gt hxExponentBounds.1)
              (Nat.ne_of_gt hyExponentBounds.1)
              (Nat.ne_of_gt hzExponentBounds.1)
              hxMantissaNe hyMantissaNe hzMantissaNe
              (by simpa [productSign] using hsign) halignedNat
              (by simpa [hproduct, halignedValue] using hordered)
        _ = result := by
          rw [← hproduct, ← halignedValue]
          exact hrefines.symm
    exact fmaFiniteImplOption_eq_some_of_components x y z result
      hxExceptional hyExceptional hzExceptional hcomponents

private theorem fmaNormalOppositeSignAligned_refines
    (x y z result : Value)
    (hresult : fmaNormalOppositeSignAlignedOption x y z = some result) :
    fmaFiniteImplOption x y z = some result := by
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let zBits := toUInt64 z
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  let xFraction := fracField xBits
  let yFraction := fracField yBits
  let zFraction := fracField zBits
  let xMantissa := finiteMantissa xExponent xFraction
  let yMantissa := finiteMantissa yExponent yFraction
  let zMantissa := finiteMantissa zExponent zFraction
  let productScale := finiteScale xExponent + finiteScale yExponent
  let zProductScale := finiteScale zExponent + 1074
  let productSign := Bool.xor (signBit xBits) (signBit yBits)
  let zSign := signBit zBits
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let aligned := alignFmaAddend zMantissa
  by_cases hxZero : xExponent = 0
  · simp [fmaNormalOppositeSignAlignedOption, xBits, xExponent, hxZero] at hresult
  by_cases hxExceptional : xExponent = 0x7ff
  · simp [fmaNormalOppositeSignAlignedOption, xBits, xExponent,
      hxExceptional] at hresult
  by_cases hyZero : yExponent = 0
  · simp [fmaNormalOppositeSignAlignedOption, yBits, yExponent, hyZero] at hresult
  by_cases hyExceptional : yExponent = 0x7ff
  · simp [fmaNormalOppositeSignAlignedOption, yBits, yExponent,
      hyExceptional] at hresult
  by_cases hzZero : zExponent = 0
  · simp [fmaNormalOppositeSignAlignedOption, zBits, zExponent, hzZero] at hresult
  by_cases hzExceptional : zExponent = 0x7ff
  · simp [fmaNormalOppositeSignAlignedOption, zBits, zExponent,
      hzExceptional] at hresult
  have hsign : productSign ≠ zSign := by
    intro heq
    simp [fmaNormalOppositeSignAlignedOption, xBits, yBits, zBits, xExponent,
      yExponent, zExponent, hxZero, hxExceptional, hyZero, hyExceptional,
      hzZero, hzExceptional, productSign, zSign, heq] at hresult
  have haligned : productScale + 52 = zProductScale := by
    by_contra hne
    simp [fmaNormalOppositeSignAlignedOption, xBits, yBits, zBits, xExponent,
      yExponent, zExponent, hxZero, hxExceptional, hyZero, hyExceptional,
      hzZero, hzExceptional, productScale, zProductScale, productSign,
      zSign, hsign, hne] at hresult
  have hproductNe : product ≠ aligned := by
    intro heq
    simp [fmaNormalOppositeSignAlignedOption, xBits, yBits, zBits, xExponent,
      yExponent, zExponent, hxZero, hxExceptional, hyZero, hyExceptional,
      hzZero, hzExceptional, productScale, zProductScale, productSign,
      zSign, hsign, haligned, product, aligned, xMantissa, yMantissa,
      zMantissa, xFraction, yFraction, zFraction, heq] at hresult
  have hxExponentBounds :
      0 < xExponent.toNat ∧ xExponent.toNat < 2047 := by
    simpa [xExponent, xBits] using
      normalExponent_bounds x hxZero hxExceptional
  have hyExponentBounds :
      0 < yExponent.toNat ∧ yExponent.toNat < 2047 := by
    simpa [yExponent, yBits] using
      normalExponent_bounds y hyZero hyExceptional
  have hzExponentBounds :
      0 < zExponent.toNat ∧ zExponent.toNat < 2047 := by
    simpa [zExponent, zBits] using
      normalExponent_bounds z hzZero hzExceptional
  have hxFractionBound : xFraction.toNat < 2 ^ 52 := by
    simpa [xFraction, xBits] using fracField_lt x
  have hyFractionBound : yFraction.toNat < 2 ^ 52 := by
    simpa [yFraction, yBits] using fracField_lt y
  have hzFractionBound : zFraction.toNat < 2 ^ 52 := by
    simpa [zFraction, zBits] using fracField_lt z
  have hxMantissaBounds :
      2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53 := by
    simpa [xMantissa] using
      finiteMantissa_bounds xExponent xFraction hxZero hxFractionBound
  have hyMantissaBounds :
      2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53 := by
    simpa [yMantissa] using
      finiteMantissa_bounds yExponent yFraction hyZero hyFractionBound
  have hzMantissaBounds :
      2 ^ 52 ≤ zMantissa.toNat ∧ zMantissa.toNat < 2 ^ 53 := by
    simpa [zMantissa] using
      finiteMantissa_bounds zExponent zFraction hzZero hzFractionBound
  have hproduct :
      product.toNat = xMantissa.toNat * yMantissa.toNat := by
    simp [product]
  have halignedValue :
      aligned.toNat = zMantissa.toNat <<< 52 := by
    exact alignFmaAddend_toNat zMantissa hzMantissaBounds.2
  have hproductUpper : product.toNat < 2 ^ 107 := by
    rw [hproduct]
    nlinarith
  have halignedUpper : aligned.toNat < 2 ^ 107 := by
    rw [halignedValue, Nat.shiftLeft_eq]
    norm_num at hzMantissaBounds ⊢
    nlinarith
  have hxScale :
      (finiteScale xExponent).toNat = xExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hxZero]
  have hyScale :
      (finiteScale yExponent).toNat = yExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hyZero]
  have hzScale :
      (finiteScale zExponent).toNat = zExponent.toNat - 1 := by
    rw [finiteScale_toNat]
    simp [hzZero]
  have hproductScale :
      productScale.toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) := by
    unfold productScale
    rw [UInt64.toNat_add, hxScale, hyScale]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have hzProductScale :
      zProductScale.toNat = (zExponent.toNat - 1) + 1074 := by
    unfold zProductScale
    rw [UInt64.toNat_add, hzScale]
    apply Nat.mod_eq_of_lt
    change zExponent.toNat - 1 + 1074 < 18446744073709551616
    omega
  have hproductScaleAligned :
      (productScale + 52).toNat =
        (xExponent.toNat - 1) + (yExponent.toNat - 1) + 52 := by
    rw [UInt64.toNat_add, hproductScale]
    apply Nat.mod_eq_of_lt
    change
      (xExponent.toNat - 1) + (yExponent.toNat - 1) + 52 <
        18446744073709551616
    omega
  have halignedNat :
      (xExponent.toNat - 1) + (yExponent.toNat - 1) + 52 =
        (zExponent.toNat - 1) + 1074 := by
    have h := congrArg UInt64.toNat haligned
    simpa [hproductScaleAligned, hzProductScale] using h
  have hxMantissaNe : xMantissa.toNat ≠ 0 := by omega
  have hyMantissaNe : yMantissa.toNat ≠ 0 := by omega
  have hzMantissaNe : zMantissa.toNat ≠ 0 := by omega
  exact fmaAlignedDifferenceCases (x := x) (y := y) (z := z) (result := result)
    (hresult := hresult) hxZero hxExceptional hyZero hyExceptional hzZero hzExceptional hsign
    haligned hproductNe hxExponentBounds hyExponentBounds hzExponentBounds hproduct
    halignedValue hproductUpper halignedUpper halignedNat hxMantissaNe hyMantissaNe
    hzMantissaNe

/-- The native aligned binary64 FMA path refines the existing exact finite kernel. -/
theorem fmaFiniteFastImpl_eq (x y z : Value) :
    fmaFiniteFastImplOption x y z = FiniteKernel.fmaOption x y z := by
  unfold fmaFiniteFastImplOption
  cases hfast : fmaNormalSameSignAlignedOption x y z with
  | none =>
      cases hopposite : fmaNormalOppositeSignAlignedOption x y z with
      | none => exact fmaFiniteImpl_eq x y z
      | some result =>
          simp only
          rw [← fmaFiniteImpl_eq]
          exact
            (fmaNormalOppositeSignAligned_refines
              x y z result hopposite).symm
  | some result =>
      simp only
      rw [← fmaFiniteImpl_eq]
      exact (fmaNormalSameSignAligned_refines x y z result hfast).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
