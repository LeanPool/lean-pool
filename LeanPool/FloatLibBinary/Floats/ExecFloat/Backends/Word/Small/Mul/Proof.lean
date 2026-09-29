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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Mul.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.NormalPair.Proof
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.ProductRound.Proof
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.ModelRounding.Proof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Correctness of native one-word finite multiplication

The one-word kernel uses a high-bit sentinel to decline cases outside its guarded normal-result
region. The sentinel proof rules out collisions with valid packed results, and the main refinement
identifies every successful proposal with the format-generic finite multiplication kernel.

`Mul.Runtime` contains the word-valued and optional entry points. Their agreement theorem allows
the dispatcher to use the sentinel interface and continue to the generic implementation on a
decline.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordMul

open NativeSmallWord

/-- Natural-number value of the one-word decline sentinel. -/
@[simp] theorem declineWord_toNat :
    declineWord.toNat = 2 ^ 63 := by
  decide

/--
Decode the word-valued normal-product result to the optional result.

The high decline bit is outside every eligible storage word, so successful packed results cannot
collide with the sentinel.
-/
theorem roundNormalProductWord_decode
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hstorage : fmt.bitWidth ≤ 63)
    (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : UInt64) :
    (if roundNormalProductWord fmt sign
          xExponent yExponent xMantissa yMantissa == declineWord then
        none
      else
        some <| NativeSmallWord.ofWord <|
          roundNormalProductWord fmt sign
            xExponent yExponent xMantissa yMantissa) =
      roundNormalProductOption fmt sign
        xExponent yExponent xMantissa yMantissa := by
  let product := xMantissa * yMantissa
  let leading := product.log2
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  let normalThreshold :=
    (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1)
  by_cases hsubnormal : position < normalThreshold
  · simp [roundNormalProductWord, roundNormalProductOption, product, leading,
      scale, position, normalThreshold, hsubnormal]
  let rounded :=
    FloatLib.Numerics.FixedWord.roundShiftRightEven product
      (leading - UInt64.ofNat fmt.fracWidth).toNat
  have hdecline :
      2 ^ fmt.bitWidth ≤ declineWord.toNat := by
    rw [declineWord_toNat]
    exact Nat.pow_le_pow_right (by decide) hstorage
  simpa [roundNormalProductWord, roundNormalProductOption, product, leading,
    scale, position, normalThreshold, rounded, hsubnormal] using
    NativeWordProduct.finishWord_decode
      fmt hwidth declineWord hdecline sign position rounded

private theorem roundNormalProduct_eq_spec
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 31)
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
      FiniteProductRound.normalSpecOption fmt sign xExponent.toNat yExponent.toNat
        xMantissa.toNat yMantissa.toNat := by
  let product := xMantissa * yMantissa
  let productNat := xMantissa.toNat * yMantissa.toNat
  have hpowExp :
      2 ^ fmt.expWidth ≤ 2 ^ 30 :=
    Nat.pow_le_pow_right (by decide) hexpWidth
  have hxExponent30 : xExponent.toNat < 2 ^ 30 :=
    hxExponent.2.trans_le hpowExp
  have hyExponent30 : yExponent.toNat < 2 ^ 30 :=
    hyExponent.2.trans_le hpowExp
  have hpowFrac :
      2 ^ (fmt.fracWidth + 1) ≤ 2 ^ 32 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hxMantissa32 : xMantissa.toNat < 2 ^ 32 :=
    hxMantissa.2.trans_le hpowFrac
  have hyMantissa32 : yMantissa.toNat < 2 ^ 32 :=
    hyMantissa.2.trans_le hpowFrac
  have hproductFit : productNat < 2 ^ 64 := by
    dsimp only [productNat]
    nlinarith [hxMantissa32, hyMantissa32]
  have hproduct :
      product.toNat = productNat := by
    unfold product productNat
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hproductFit]
  have hproductNe : productNat ≠ 0 := by
    have hxPositive : 0 < xMantissa.toNat :=
      lt_of_lt_of_le (Nat.two_pow_pos _) hxMantissa.1
    have hyPositive : 0 < yMantissa.toNat :=
      lt_of_lt_of_le (Nat.two_pow_pos _) hyMantissa.1
    dsimp only [productNat]
    positivity
  let leading := product.log2
  have hleading :
      leading.toNat = productNat.log2 := by
    unfold leading
    rw [FloatLib.Numerics.FixedWord.log2_toNat, hproduct]
  have hleadingUpper : leading.toNat < 64 := by
    rw [hleading]
    exact (Nat.log2_lt hproductNe).2 hproductFit
  have hproductLower :
      2 ^ (2 * fmt.fracWidth) ≤ productNat := by
    dsimp only [productNat]
    have hmul := Nat.mul_le_mul hxMantissa.1 hyMantissa.1
    simpa [← pow_add, two_mul] using hmul
  have hleadingLower :
      2 * fmt.fracWidth ≤ leading.toNat := by
    rw [hleading]
    exact (Nat.le_log2 hproductNe).2 hproductLower
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
    omega
  have hbias :
      fmt.bias < 2 ^ 30 :=
    (FloatFormat.bias_lt_pow_expWidth fmt).trans_le hpowExp
  have hnormalThreshold :
      (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1).toNat =
        fmt.bias + 2 * fmt.fracWidth - 1 :=
    normalThreshold_toNat hwidth
  unfold roundNormalProductOption FiniteProductRound.normalSpecOption
  dsimp only
  rw [show xMantissa * yMantissa = product by rfl]
  rw [show xMantissa.toNat * yMantissa.toNat = productNat by rfl]
  rw [show product.log2 = leading by rfl]
  rw [show xExponent - 1 + (yExponent - 1) = scale by rfl]
  rw [show leading + scale = position by rfl]
  by_cases hsubnormal :
      productNat.log2 +
          ((xExponent.toNat - 1) + (yExponent.toNat - 1)) <
        fmt.bias + 2 * fmt.fracWidth - 1
  · have hsubnormalWord :
        position < (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1) := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [hposition, hnormalThreshold]
      exact hsubnormal
    rw [ite_eq_left hsubnormalWord, ite_eq_left hsubnormal]
  have hsubnormalWord :
      ¬position < (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1) := by
    intro h
    apply hsubnormal
    have hnat := UInt64.lt_iff_toNat_lt.mp h
    rwa [hposition, hnormalThreshold] at hnat
  rw [ite_eq_right hsubnormalWord, ite_eq_right hsubnormal]
  let rounded :=
    FloatLib.Numerics.FixedWord.roundShiftRightEven product
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
  have hrounded :
      rounded.toNat = roundedNat := by
    unfold rounded roundedNat
    rw [FloatLib.Numerics.FixedWord.roundShiftRightEven_toNat, hproduct, hshift]
  have hhidden :
      (hiddenBit fmt).toNat = 2 ^ fmt.fracWidth :=
    hiddenBit_toNat_of_width fmt hwidth
  have hcarryBit :
      (carryBit fmt).toNat = 2 ^ (fmt.fracWidth + 1) :=
    carryBit_toNat_of_width fmt hwidth (by omega)
  have hroundedDef :
      FloatLib.Numerics.FixedWord.roundShiftRightEven product
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
    simpa [roundMantissaToLeadingBitEven, hfracLog, pow2_eq_two_pow] using
      pow2_le_roundMantissaToLeadingBitEven productNat fmt.fracWidth hproductNe
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

/--
A successful native normal-product round agrees with the exact finite-product rounder.

The hypotheses state only the machine-capacity and normalized-input bounds needed by the
`UInt64` implementation.
-/
theorem roundNormalProduct_refines
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 31)
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
  rw [roundNormalProduct_eq_spec fmt hwidth hexpWidth hfracWidth
    sign xExponent yExponent xMantissa yMantissa
    hxExponent hyExponent hxMantissa hyMantissa] at hresult
  exact FiniteProductRound.normalSpec_refines_of_normalized
    fmt sign xExponent.toNat yExponent.toNat
      xMantissa.toNat yMantissa.toNat
      hxMantissa.1 hyMantissa.1 result hresult

/-- Decode the flat tagged execution result back to the proof-facing optional result. -/
theorem mulNormalWord_decode {fmt : FloatFormat}
    (heligible : Eligible fmt) (x y : Model fmt) :
    (if mulNormalWord x y == declineWord then
        none
      else
        some (NativeSmallWord.ofWord (mulNormalWord x y))) =
      mulNormalOption x y := by
  rcases heligible with ⟨hieee, hwidth, hexpWidth, hfracWidth⟩
  have hstorage : fmt.bitWidth ≤ 63 := by
    unfold FloatFormat.bitWidth
    omega
  let xBits := NativeSmallWord.toWord x
  let yBits := NativeSmallWord.toWord y
  let xExponent := NativeSmallWord.exponentField fmt xBits
  let yExponent := NativeSmallWord.exponentField fmt yBits
  let allOnes := NativeSmallWord.exponentMask fmt
  let xMantissa :=
    NativeSmallWord.fractionField fmt xBits ||| hiddenBit fmt
  let yMantissa :=
    NativeSmallWord.fractionField fmt yBits ||| hiddenBit fmt
  let sign :=
    Bool.xor
      (NativeSmallWord.signField fmt xBits)
      (NativeSmallWord.signField fmt yBits)
  by_cases hinvalid :
      (xExponent == 0 || xExponent == allOnes ||
        yExponent == 0 || yExponent == allOnes) = true
  · simp [mulNormalWord, mulNormalOption, NativeSmallWord.withNormalPairOption,
      xBits, yBits, xExponent,
      yExponent, allOnes, hinvalid]
  · simpa [mulNormalWord, mulNormalOption, NativeSmallWord.withNormalPairOption,
      xBits, yBits, xExponent,
      yExponent, allOnes, xMantissa, yMantissa, sign, hinvalid] using
      roundNormalProductWord_decode fmt hwidth hstorage sign
        xExponent yExponent xMantissa yMantissa

/--
A successful one-word normal multiplication agrees with the compact finite kernel.

The native path deliberately handles only normal IEEE operands whose intermediate fields fit in
one word. Every other input returns `none`, so callers can retain the exact baseline.
-/
theorem mulNormal_refines {fmt : FloatFormat}
    (heligible : Eligible fmt) (x y result : Model fmt)
    (hresult : mulNormalOption x y = some result) :
    FiniteKernel.mulOption x y = some result := by
  rcases heligible with ⟨hieee, hwidth, hexpWidth, hfracWidth⟩
  refine NativeNormalPair.mul_refines
    hieee hwidth (roundNormalProductOption fmt) ?_ x y result ?_
  · intro sign xExponent yExponent xMantissa yMantissa candidate
      hxExponent hyExponent hxMantissa hyMantissa hround
    exact roundNormalProduct_refines fmt hwidth hexpWidth hfracWidth
      sign xExponent yExponent xMantissa yMantissa
      hxExponent hyExponent hxMantissa hyMantissa candidate hround
  · simpa [mulNormalOption] using hresult

end Model.NativeSmallWordMul
end FloatLib.Floats.Formats.BinaryInterchange
