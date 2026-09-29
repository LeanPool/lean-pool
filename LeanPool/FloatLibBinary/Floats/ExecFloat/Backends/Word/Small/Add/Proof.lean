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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Add.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ScaleAdd.Runtime
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Core.Proof
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Finite.Proof
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.ProductRound.Proof
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.ModelRounding.Proof
import Mathlib.Tactic.NormNum

/-!
# Correctness of native one-word finite addition

Under `Eligible`, every accepted result of `Add.Runtime` agrees with the exact finite kernel.
`addFinite_refines` also covers subtraction by identifying the toggled right sign with `neg y`.
A declined input is handled by the dispatcher's generic fallback.

`normalSpecOption` describes the normal branch of `FiniteProductRound.round`. The proof transfers
native rounding to this specification using the shared carry and packing theorem
`NativeWordProduct.finish_eq`, then treats signed magnitudes, exponent alignment, and decoding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordAdd

open NativeSmallWord

/-! ## Natural-number specification of the normal rounding path -/

/--
The normal branch of `FiniteProductRound.round`, declining instead of producing a subnormal or an
infinite result.

For a nonzero magnitude, this rounds the value with sign `sign` and magnitude
`magnitude * 2 ^ (scale - 2 * ieeeSubnormalAlignExp fmt)`, interpreting subtraction in `Int`.
`normalSpec_refines` identifies each accepted answer with the total product rounder.
-/
def normalSpecOption (fmt : FloatFormat) (sign : Bool) (magnitude scale : Nat) :
    Option (Model fmt) :=
  let leading := magnitude.log2
  let position := leading + scale
  let normalThreshold := fmt.bias + 2 * fmt.fracWidth - 1
  if position < normalThreshold then
    none
  else
    let rounded :=
      if fmt.fracWidth ≤ leading then
        Numerics.roundShiftRightEven magnitude (leading - fmt.fracWidth)
      else
        magnitude <<< (fmt.fracWidth - leading)
    let carry := rounded = pow2 (fmt.fracWidth + 1)
    let normalizedPosition := if carry then position + 1 else position
    let overflowThreshold := 3 * fmt.bias + 2 * fmt.fracWidth - 2
    if overflowThreshold < normalizedPosition then
      none
    else
      let normalizedMantissa := if carry then pow2 fmt.fracWidth else rounded
      let exponentOffset := fmt.bias + 2 * fmt.fracWidth - 2
      some <| ofFields fmt sign
        (normalizedPosition - exponentOffset)
        (normalizedMantissa - pow2 fmt.fracWidth)

/-- A `some` answer of the normal specification is the arbitrary-precision rounder's result. -/
theorem normalSpec_refines
    (fmt : FloatFormat) (sign : Bool) (magnitude scale : Nat)
    (hmagnitude : magnitude ≠ 0)
    (result : Model fmt)
    (hresult : normalSpecOption fmt sign magnitude scale = some result) :
    result = FiniteProductRound.round fmt sign magnitude scale := by
  unfold normalSpecOption at hresult
  let leading := magnitude.log2
  let position := leading + scale
  let normalThreshold := fmt.bias + 2 * fmt.fracWidth - 1
  by_cases hsubnormal : position < normalThreshold
  · simp [leading, position, normalThreshold, hsubnormal] at hresult
  let rounded :=
    if fmt.fracWidth ≤ leading then
      Numerics.roundShiftRightEven magnitude (leading - fmt.fracWidth)
    else
      magnitude <<< (fmt.fracWidth - leading)
  let carry := rounded = pow2 (fmt.fracWidth + 1)
  let normalizedPosition := if carry then position + 1 else position
  let overflowThreshold := 3 * fmt.bias + 2 * fmt.fracWidth - 2
  by_cases hoverflow : overflowThreshold < normalizedPosition
  · simp [leading, position, normalThreshold, hsubnormal, rounded, carry,
      normalizedPosition, overflowThreshold, hoverflow] at hresult
  have hresultEq :
      ofFields fmt sign
          (normalizedPosition - (fmt.bias + 2 * fmt.fracWidth - 2))
          ((if carry then pow2 fmt.fracWidth else rounded) - pow2 fmt.fracWidth) =
        result := by
    simpa [leading, position, normalThreshold, hsubnormal, rounded, carry,
      normalizedPosition, overflowThreshold, hoverflow] using hresult
  rw [← hresultEq]
  unfold FiniteProductRound.round
  simp only [beq_iff_eq, hmagnitude, ite_false]
  rw [ite_eq_right hsubnormal, ite_eq_right hoverflow]

/-! ## Machine-word rounding -/

private theorem bias_lt (fmt : FloatFormat) (hexpWidth : fmt.expWidth ≤ 30) :
    fmt.bias < 2 ^ 30 :=
  (FloatFormat.bias_lt_pow_expWidth fmt).trans_le
    (Nat.pow_le_pow_right (by decide) hexpWidth)

private theorem exponentBias_lt (fmt : FloatFormat) (hexpWidth : fmt.expWidth ≤ 30) :
    fmt.exponentBias < 2 ^ 30 :=
  (FloatFormat.exponentBias_lt_two_pow fmt).trans_le
    (Nat.pow_le_pow_right (by decide) hexpWidth)

/-- The alignment offset is exact when `expWidth ≤ 30` and `fracWidth ≤ 61`. -/
theorem alignOffset_toNat (fmt : FloatFormat)
    (hexpWidth : fmt.expWidth ≤ 30) (hfracWidth : fmt.fracWidth ≤ 61) :
    (alignOffset fmt).toNat = fmt.exponentBias + fmt.fracWidth - 1 := by
  have hbias := exponentBias_lt fmt hexpWidth
  unfold alignOffset
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
  norm_num at hbias ⊢
  omega

/-- The alignment shift limit is exact when `fracWidth ≤ 61`. -/
theorem shiftLimit_toNat (fmt : FloatFormat) (hfracWidth : fmt.fracWidth ≤ 61) :
    (shiftLimit fmt).toNat = 62 - fmt.fracWidth := by
  have hfrac : (UInt64.ofNat fmt.fracWidth).toNat = fmt.fracWidth := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    omega
  unfold shiftLimit
  rw [UInt64.toNat_sub_of_le]
  · rw [hfrac]
    rfl
  · apply UInt64.le_iff_toNat_le.mpr
    rw [hfrac]
    change fmt.fracWidth ≤ 62
    omega

/--
The machine-word rounder computes the natural-number normal specification.

The magnitude is nonzero and the scale is bounded by the exponent range, so no intermediate
position, shift, or increment wraps around the word.
-/
theorem roundMagnitude_eq_normalSpec
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 61)
    (sign : Bool) (magnitude scale : UInt64)
    (hmagnitude : magnitude ≠ 0)
    (hscale : scale.toNat < 2 ^ 31) :
    roundMagnitudeOption fmt sign magnitude scale =
      normalSpecOption fmt sign magnitude.toNat
        (scale.toNat + (fmt.exponentBias + fmt.fracWidth - 1)) := by
  let magnitudeNat := magnitude.toNat
  have hmagnitudeNe : magnitudeNat ≠ 0 := by
    simpa [magnitudeNat, ← UInt64.toNat_inj] using hmagnitude
  have hmagnitudeFit : magnitudeNat < 2 ^ 64 := UInt64.toNat_lt_size magnitude
  have hbias := bias_lt fmt hexpWidth
  have hexponentBias := exponentBias_lt fmt hexpWidth
  have hoffset := alignOffset_toNat fmt hexpWidth hfracWidth
  let leading := magnitude.log2
  have hleading : leading.toNat = magnitudeNat.log2 :=
    FloatLib.Numerics.FixedWord.log2_toNat magnitude
  have hleadingUpper : leading.toNat < 64 := by
    rw [hleading]
    exact (Nat.log2_lt hmagnitudeNe).2 hmagnitudeFit
  let positionNat := magnitudeNat.log2 + (scale.toNat + (fmt.exponentBias + fmt.fracWidth - 1))
  let position := leading + scale + alignOffset fmt
  have hposition : position.toNat = positionNat := by
    unfold position positionNat
    rw [UInt64.toNat_add, UInt64.toNat_add, hleading, hoffset]
    have hinner : magnitudeNat.log2 + scale.toNat < 2 ^ 64 := by
      norm_num at hscale ⊢
      omega
    rw [Nat.mod_eq_of_lt hinner, Nat.mod_eq_of_lt]
    · omega
    · norm_num at hscale hexponentBias ⊢
      omega
  have hpositionAdd : (position + 1).toNat = positionNat + 1 := by
    rw [UInt64.toNat_add, hposition, UInt64.toNat_one]
    apply Nat.mod_eq_of_lt
    unfold positionNat
    have hlog : magnitudeNat.log2 < 64 := by
      rwa [← hleading]
    norm_num at hscale hexponentBias ⊢
    omega
  have hnormalThreshold :
      (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1).toNat =
        fmt.bias + 2 * fmt.fracWidth - 1 :=
    normalThreshold_toNat hwidth
  unfold roundMagnitudeOption normalSpecOption
  dsimp only
  rw [show magnitude.log2 = leading by rfl,
    show leading + scale + alignOffset fmt = position by rfl,
    show magnitude.toNat = magnitudeNat by rfl,
    show magnitudeNat.log2 + (scale.toNat + (fmt.exponentBias + fmt.fracWidth - 1)) =
      positionNat by rfl]
  by_cases hsubnormal : positionNat < fmt.bias + 2 * fmt.fracWidth - 1
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
  let fracWidthWord := UInt64.ofNat fmt.fracWidth
  have hfracWord : fracWidthWord.toNat = fmt.fracWidth := by
    unfold fracWidthWord
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    omega
  let rounded :=
    if fracWidthWord ≤ leading then
      FloatLib.Numerics.FixedWord.roundShiftRightEven magnitude
        (leading - fracWidthWord).toNat
    else
      magnitude <<< (fracWidthWord - leading)
  let roundedNat :=
    if fmt.fracWidth ≤ magnitudeNat.log2 then
      Numerics.roundShiftRightEven magnitudeNat (magnitudeNat.log2 - fmt.fracWidth)
    else
      magnitudeNat <<< (fmt.fracWidth - magnitudeNat.log2)
  have hrounded : rounded.toNat = roundedNat := by
    unfold rounded roundedNat
    by_cases hle : fmt.fracWidth ≤ magnitudeNat.log2
    · have hleWord : fracWidthWord ≤ leading := by
        apply UInt64.le_iff_toNat_le.mpr
        rw [hfracWord, hleading]
        exact hle
      rw [ite_eq_left hleWord, ite_eq_left hle,
        FloatLib.Numerics.FixedWord.roundShiftRightEven_toNat,
        UInt64.toNat_sub_of_le _ _ hleWord, hleading, hfracWord]
    · have hleWord : ¬fracWidthWord ≤ leading := by
        intro h
        apply hle
        have hnat := UInt64.le_iff_toNat_le.mp h
        rwa [hfracWord, hleading] at hnat
      rw [ite_eq_right hleWord, ite_eq_right hle]
      have hshiftLe : leading ≤ fracWidthWord := by
        apply UInt64.le_iff_toNat_le.mpr
        rw [hfracWord, hleading]
        omega
      have hshiftNat :
          (fracWidthWord - leading).toNat = fmt.fracWidth - magnitudeNat.log2 := by
        rw [UInt64.toNat_sub_of_le _ _ hshiftLe, hfracWord, hleading]
      have hshiftLt : fmt.fracWidth - magnitudeNat.log2 < 64 := by
        omega
      have hfit :
          magnitudeNat <<< (fmt.fracWidth - magnitudeNat.log2) < 2 ^ 64 := by
        have hshifted :=
          Nat.shiftLeft_lt (m := fmt.fracWidth - magnitudeNat.log2)
            (Nat.lt_log2_self (n := magnitudeNat))
        have hexponent :
            magnitudeNat.log2 + 1 + (fmt.fracWidth - magnitudeNat.log2) =
              fmt.fracWidth + 1 := by
          omega
        rw [hexponent] at hshifted
        exact hshifted.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      rw [← UInt64.ofNat_toNat (x := fracWidthWord - leading), hshiftNat,
        FloatLib.Numerics.FixedWord.shiftLeft_toNat magnitude _ hshiftLt hfit]
  have hroundedDef :
      (if fracWidthWord ≤ leading then
          FloatLib.Numerics.FixedWord.roundShiftRightEven magnitude
            (leading - fracWidthWord).toNat
        else
          magnitude <<< (fracWidthWord - leading)) = rounded := rfl
  have hroundedNatDef :
      (if fmt.fracWidth ≤ magnitudeNat.log2 then
          Numerics.roundShiftRightEven magnitudeNat (magnitudeNat.log2 - fmt.fracWidth)
        else
          magnitudeNat <<< (fmt.fracWidth - magnitudeNat.log2)) = roundedNat := rfl
  rw [hroundedDef, hroundedNatDef]
  have hroundedLower : 2 ^ fmt.fracWidth ≤ roundedNat := by
    have hbound :=
      pow2_le_roundMantissaToLeadingBitEven magnitudeNat fmt.fracWidth hmagnitudeNe
    simpa [roundMantissaToLeadingBitEven, roundedNat, pow2_eq_two_pow] using hbound
  have hnormal : fmt.bias + 2 * fmt.fracWidth - 1 ≤ positionNat := by
    omega
  exact NativeWordProduct.finish_eq fmt hwidth sign position rounded
    positionNat roundedNat hposition hpositionAdd hrounded hnormal
    (hiddenBit_toNat_of_width fmt hwidth) (carryBit_toNat_of_width fmt hwidth (by omega))
    hroundedLower

/-- An accepted machine-word rounding is the unsigned-scale rounding of the exact kernel. -/
theorem roundMagnitude_refines
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 61)
    (sign : Bool) (magnitude scale : UInt64)
    (hmagnitude : magnitude ≠ 0)
    (hscale : scale.toNat < 2 ^ 31)
    (result : Model fmt)
    (hresult : roundMagnitudeOption fmt sign magnitude scale = some result) :
    result =
      FiniteScaleAdd.roundMagnitude fmt (FiniteKernel.finiteScaleOffset fmt)
        sign magnitude.toNat scale.toNat := by
  rw [roundMagnitude_eq_normalSpec fmt hwidth hexpWidth hfracWidth
    sign magnitude scale hmagnitude hscale] at hresult
  have hmagnitudeNe : magnitude.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hmagnitude
  unfold FiniteScaleAdd.roundMagnitude FiniteKernel.finiteScaleOffset
  exact normalSpec_refines fmt sign magnitude.toNat _ hmagnitudeNe result hresult

/-! ## Signed magnitudes and alignment -/

private theorem toNat_ne_zero_of_ne_zero {value : UInt64} (h : value ≠ 0) :
    value.toNat ≠ 0 := by
  simpa [← UInt64.toNat_inj] using h

/-- An accepted aligned combination is the exact kernel's signed-magnitude combination. -/
theorem roundAligned_refines
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 61)
    (leftSign rightSign : Bool) (left right scale : UInt64)
    (hleft : left ≠ 0) (hright : right ≠ 0)
    (hsum : left.toNat + right.toNat < 2 ^ 64)
    (hscale : scale.toNat < 2 ^ 31)
    (result : Model fmt)
    (hresult : roundAlignedOption fmt leftSign rightSign left right scale = some result) :
    result =
      FiniteScaleAdd.roundMagnitudes fmt (FiniteKernel.finiteScaleOffset fmt)
        leftSign rightSign left.toNat right.toNat scale.toNat := by
  have hleftNat := toNat_ne_zero_of_ne_zero hleft
  have hrightNat := toNat_ne_zero_of_ne_zero hright
  unfold roundAlignedOption at hresult
  unfold FiniteScaleAdd.roundMagnitudes
  by_cases hsign : leftSign = rightSign
  · rw [ite_eq_left (by simp [hsign])] at hresult
    rw [ite_eq_left (by simp [hsign])]
    have hadd : (left + right).toNat = left.toNat + right.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum]
    have haddNe : left + right ≠ 0 := by
      intro h
      have hnat := congrArg UInt64.toNat h
      rw [hadd, UInt64.toNat_zero] at hnat
      omega
    rw [roundMagnitude_refines fmt hwidth hexpWidth hfracWidth leftSign (left + right) scale
      haddNe hscale result hresult, hadd]
  · rw [ite_eq_right (by simpa using hsign)] at hresult
    rw [ite_eq_right (by simpa using hsign)]
    by_cases heq : left = right
    · subst heq
      simp only [beq_self_eq_true, ite_true, Option.some.injEq] at hresult
      simp only [beq_self_eq_true, ite_true]
      exact hresult.symm
    · have heqNat : left.toNat ≠ right.toNat := by
        intro h
        exact heq (UInt64.toNat_inj.mp h)
      rw [ite_eq_right (by simpa using heq)] at hresult
      rw [ite_eq_right (by simpa using heqNat)]
      by_cases hlt : left < right
      · have hltNat : left.toNat < right.toNat := UInt64.lt_iff_toNat_lt.mp hlt
        rw [ite_eq_left hlt] at hresult
        rw [ite_eq_left hltNat]
        have hsub : (right - left).toNat = right.toNat - left.toNat :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt)
        have hsubNe : right - left ≠ 0 := by
          intro h
          have hnat := congrArg UInt64.toNat h
          rw [hsub, UInt64.toNat_zero] at hnat
          omega
        rw [roundMagnitude_refines fmt hwidth hexpWidth hfracWidth rightSign (right - left)
          scale hsubNe hscale result hresult, hsub]
      · have hltNat : ¬left.toNat < right.toNat := by
          intro h
          exact hlt (UInt64.lt_iff_toNat_lt.mpr h)
        have hgt : right < left := by
          apply UInt64.lt_iff_toNat_lt.mpr
          omega
        rw [ite_eq_right hlt] at hresult
        rw [ite_eq_right hltNat]
        have hsub : (left - right).toNat = left.toNat - right.toNat :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hgt)
        have hsubNe : left - right ≠ 0 := by
          intro h
          have hnat := congrArg UInt64.toNat h
          rw [hsub, UInt64.toNat_zero] at hnat
          omega
        rw [roundMagnitude_refines fmt hwidth hexpWidth hfracWidth leftSign (left - right)
          scale hsubNe hscale result hresult, hsub]

/-- The machine-word finite scale is the compact finite scale of the exact kernel. -/
theorem finiteScale_toNat_eq_scale (exponent : UInt64) :
    (FloatLib.Numerics.FixedWord.finiteScale exponent).toNat =
      FiniteKernel.scale exponent.toNat := by
  rw [FloatLib.Numerics.FixedWord.finiteScale_toNat]
  unfold FiniteKernel.scale
  by_cases hzero : exponent = 0
  · subst hzero
    simp
  · have hzeroNat : exponent.toNat ≠ 0 := toNat_ne_zero_of_ne_zero hzero
    simp [hzero, hzeroNat]

private theorem finiteScale_toNat_lt (fmt : FloatFormat)
    (hexpWidth : fmt.expWidth ≤ 30) (exponent : UInt64)
    (hexponent : exponent.toNat < 2 ^ fmt.expWidth) :
    (FloatLib.Numerics.FixedWord.finiteScale exponent).toNat < 2 ^ 31 := by
  have hpow : 2 ^ fmt.expWidth ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hexpWidth
  rw [FloatLib.Numerics.FixedWord.finiteScale_toNat]
  split
  · exact Nat.two_pow_pos _
  · norm_num at hpow ⊢
    omega

private theorem shifted_toNat (fmt : FloatFormat) (hfracWidth : fmt.fracWidth ≤ 61)
    (mantissa shift : UInt64)
    (hmantissa : mantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hshift : shift.toNat + fmt.fracWidth ≤ 62) :
    (mantissa <<< shift).toNat = mantissa.toNat <<< shift.toNat ∧
      mantissa.toNat <<< shift.toNat < 2 ^ 63 := by
  have hfit : mantissa.toNat <<< shift.toNat < 2 ^ 63 := by
    have hshifted := Nat.shiftLeft_lt (m := shift.toNat) hmantissa
    exact hshifted.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨?_, hfit⟩
  have hshiftNat :=
    FloatLib.Numerics.FixedWord.shiftLeft_toNat mantissa shift.toNat (by omega)
      (hfit.trans (by norm_num))
  rwa [UInt64.ofNat_toNat] at hshiftNat

/--
An accepted field addition is the exact unsigned-scale sum of the same fields.

The exponent bounds keep every scale below `2 ^ 31` and the significand bounds keep the aligned
same-sign sum below `2 ^ 64`, which is all the machine-word transfer needs.
-/
theorem addFields_refines
    (fmt : FloatFormat)
    (hieee : fmt.isIEEE = true)
    (hwidth : fmt.bitWidth ≤ 64)
    (hexpWidth : fmt.expWidth ≤ 30)
    (hfracWidth : fmt.fracWidth ≤ 61)
    (xSign : Bool) (xExponent xMantissa : UInt64)
    (ySign : Bool) (yExponent yMantissa : UInt64)
    (hxExponent : xExponent.toNat < 2 ^ fmt.expWidth)
    (hyExponent : yExponent.toNat < 2 ^ fmt.expWidth)
    (hxMantissa : xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa : yMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (result : Model fmt)
    (hresult :
      addFieldsOption fmt xSign xExponent xMantissa ySign yExponent yMantissa = some result) :
    result =
      FiniteKernel.addFields fmt
        xSign xExponent.toNat xMantissa.toNat ySign yExponent.toNat yMantissa.toNat := by
  have hpowFrac : 2 ^ (fmt.fracWidth + 1) ≤ 2 ^ 62 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hxMantissa62 : xMantissa.toNat < 2 ^ 62 := hxMantissa.trans_le hpowFrac
  have hyMantissa62 : yMantissa.toNat < 2 ^ 62 := hyMantissa.trans_le hpowFrac
  unfold addFieldsOption at hresult
  by_cases hzero : (xMantissa == 0 || yMantissa == 0) = true
  · simp [hzero] at hresult
  rw [ite_eq_right hzero] at hresult
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hzero
  obtain ⟨hxNe, hyNe⟩ := hzero
  have hxNeNat := toNat_ne_zero_of_ne_zero hxNe
  have hyNeNat := toNat_ne_zero_of_ne_zero hyNe
  have hxScale := finiteScale_toNat_eq_scale xExponent
  have hyScale := finiteScale_toNat_eq_scale yExponent
  have hxScaleLt := finiteScale_toNat_lt fmt hexpWidth xExponent hxExponent
  have hyScaleLt := finiteScale_toNat_lt fmt hexpWidth yExponent hyExponent
  have hlimit := shiftLimit_toNat fmt hfracWidth
  unfold FiniteKernel.addFields
  rw [ite_eq_left hieee]
  unfold FiniteScaleAdd.roundSum
  rw [ite_eq_right (by simpa using hxNeNat), ite_eq_right (by simpa using hyNeNat)]
  set xScale := FloatLib.Numerics.FixedWord.finiteScale xExponent with hxScaleDef
  set yScale := FloatLib.Numerics.FixedWord.finiteScale yExponent with hyScaleDef
  by_cases hle : xScale ≤ yScale
  · have hleNat : FiniteKernel.scale xExponent.toNat ≤ FiniteKernel.scale yExponent.toNat := by
      rw [← hxScale, ← hyScale]
      exact UInt64.le_iff_toNat_le.mp hle
    rw [ite_eq_left hle] at hresult
    rw [ite_eq_left hleNat]
    by_cases hshift : yScale - xScale ≤ shiftLimit fmt
    · rw [ite_eq_left hshift] at hresult
      have hshiftNat :
          (yScale - xScale).toNat =
            FiniteKernel.scale yExponent.toNat - FiniteKernel.scale xExponent.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ hle, hxScale, hyScale]
      have hshiftBound : (yScale - xScale).toNat + fmt.fracWidth ≤ 62 := by
        have hnat := UInt64.le_iff_toNat_le.mp hshift
        rw [hlimit] at hnat
        omega
      obtain ⟨hshifted, hshiftedLt⟩ :=
        shifted_toNat fmt hfracWidth yMantissa (yScale - xScale) hyMantissa hshiftBound
      have hshiftedNe : yMantissa <<< (yScale - xScale) ≠ 0 := by
        intro h
        have hnat := congrArg UInt64.toNat h
        rw [hshifted, UInt64.toNat_zero, Nat.shiftLeft_eq] at hnat
        exact absurd hnat (Nat.mul_ne_zero hyNeNat (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))
      have hsum : xMantissa.toNat + (yMantissa <<< (yScale - xScale)).toNat < 2 ^ 64 := by
        rw [hshifted]
        norm_num at hxMantissa62 hshiftedLt ⊢
        omega
      rw [roundAligned_refines fmt hwidth hexpWidth hfracWidth xSign ySign xMantissa
        (yMantissa <<< (yScale - xScale)) xScale hxNe hshiftedNe hsum hxScaleLt result hresult,
        hshifted, hshiftNat, hxScale]
    · rw [ite_eq_right hshift] at hresult
      exact absurd hresult (by simp)
  · have hleNat :
        ¬FiniteKernel.scale xExponent.toNat ≤ FiniteKernel.scale yExponent.toNat := by
      intro h
      apply hle
      apply UInt64.le_iff_toNat_le.mpr
      rwa [hxScale, hyScale]
    have hlt : yScale ≤ xScale := by
      apply UInt64.le_iff_toNat_le.mpr
      have hnat : ¬xScale.toNat ≤ yScale.toNat := fun h => hle (UInt64.le_iff_toNat_le.mpr h)
      omega
    rw [ite_eq_right hle] at hresult
    rw [ite_eq_right hleNat]
    by_cases hshift : xScale - yScale ≤ shiftLimit fmt
    · rw [ite_eq_left hshift] at hresult
      have hshiftNat :
          (xScale - yScale).toNat =
            FiniteKernel.scale xExponent.toNat - FiniteKernel.scale yExponent.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ hlt, hxScale, hyScale]
      have hshiftBound : (xScale - yScale).toNat + fmt.fracWidth ≤ 62 := by
        have hnat := UInt64.le_iff_toNat_le.mp hshift
        rw [hlimit] at hnat
        omega
      obtain ⟨hshifted, hshiftedLt⟩ :=
        shifted_toNat fmt hfracWidth xMantissa (xScale - yScale) hxMantissa hshiftBound
      have hshiftedNe : xMantissa <<< (xScale - yScale) ≠ 0 := by
        intro h
        have hnat := congrArg UInt64.toNat h
        rw [hshifted, UInt64.toNat_zero, Nat.shiftLeft_eq] at hnat
        exact absurd hnat (Nat.mul_ne_zero hxNeNat (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))
      have hsum : (xMantissa <<< (xScale - yScale)).toNat + yMantissa.toNat < 2 ^ 64 := by
        rw [hshifted]
        norm_num at hyMantissa62 hshiftedLt ⊢
        omega
      rw [roundAligned_refines fmt hwidth hexpWidth hfracWidth xSign ySign
        (xMantissa <<< (xScale - yScale)) yMantissa yScale hshiftedNe hyNe hsum hyScaleLt
        result hresult, hshifted, hshiftNat, hyScale]
    · rw [ite_eq_right hshift] at hresult
      exact absurd hresult (by simp)

/-! ## Storage-word decoding -/

/-- The generic finite decoder sees the fields the one-word kernel extracts from a finite word. -/
theorem decode_of_finite {fmt : FloatFormat}
    (hieee : fmt.isIEEE = true) (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt)
    (hfinite : exponentField fmt (toWord x) ≠ exponentMask fmt) :
    FiniteKernel.decodeOption x =
      some {
        sign := signField fmt (toWord x)
        exponent := (exponentField fmt (toWord x)).toNat
        mantissa :=
          (NativeSmallWordFinite.finiteMantissa fmt (exponentField fmt (toWord x))
            (fractionField fmt (toWord x))).toNat } := by
  rw [← NativeSmallWordFinite.decode_eq ⟨hieee, hwidth⟩ x]
  unfold NativeSmallWordFinite.decodeOption
  simp only [beq_iff_eq, hfinite, ite_false]

/-- Negating a finite word keeps its exponent and fraction fields and toggles its sign. -/
theorem decode_neg_of_finite {fmt : FloatFormat}
    (hieee : fmt.isIEEE = true) (hwidth : fmt.bitWidth ≤ 64)
    (y : Model fmt)
    (hfinite : exponentField fmt (toWord y) ≠ exponentMask fmt) :
    FiniteKernel.decodeOption (neg y) =
      some {
        sign := !signField fmt (toWord y)
        exponent := (exponentField fmt (toWord y)).toNat
        mantissa :=
          (NativeSmallWordFinite.finiteMantissa fmt (exponentField fmt (toWord y))
            (fractionField fmt (toWord y))).toNat } := by
  have hexponent : exponentField fmt (toWord (neg y)) = exponentField fmt (toWord y) := by
    apply UInt64.toNat_inj.mp
    rw [exponentField_toNat hwidth, exponentField_toNat hwidth, expField_neg]
  have hfraction : fractionField fmt (toWord (neg y)) = fractionField fmt (toWord y) := by
    apply UInt64.toNat_inj.mp
    rw [fractionField_toNat hwidth, fractionField_toNat hwidth, fracField_neg]
  have hsign : signField fmt (toWord (neg y)) = !signField fmt (toWord y) := by
    rw [signField_eq hwidth, signField_eq hwidth, signBit_neg,
      ite_eq_left (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hieee)]
  rw [decode_of_finite hieee hwidth (neg y) (by rwa [hexponent]), hexponent, hfraction, hsign]

/-- The exponent field of a one-word value is a stored exponent. -/
theorem exponentField_toNat_lt {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt) :
    (exponentField fmt (toWord x)).toNat < 2 ^ fmt.expWidth := by
  rw [exponentField_toNat hwidth]
  exact Model.expField_lt_pow2 x

/-- The finite significand of a one-word value has at most `fracWidth + 1` bits. -/
theorem finiteMantissa_toNat_lt {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt) :
    (NativeSmallWordFinite.finiteMantissa fmt (exponentField fmt (toWord x))
      (fractionField fmt (toWord x))).toNat < 2 ^ (fmt.fracWidth + 1) := by
  unfold NativeSmallWordFinite.finiteMantissa
  split
  · rw [fractionField_toNat hwidth]
    exact (Model.fracField_lt_pow2 x).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  · exact (normalMantissa_bounds_of_width hwidth x).2

/--
An accepted one-word addition, or subtraction, is the exact compact finite kernel's answer.

`negateRight` selects subtraction: the kernel toggled the right sign in machine words, and the
theorem states the corresponding claim about `neg y`. Every decline is outside the statement; the
dispatcher uses the exact implementation for it. The hypothesis is the kernel's own capacity
contract `Eligible`: IEEE encoding, at most 64 total bits, at most 30 exponent bits, and at most
61 fraction bits.
-/
theorem addFinite_refines {fmt : FloatFormat}
    (heligible : Eligible fmt)
    (x y result : Model fmt) (negateRight : Bool)
    (hresult : addFiniteOption x y negateRight = some result) :
    FiniteKernel.addOption x (if negateRight then neg y else y) = some result := by
  rcases heligible with ⟨hieee, hwidth, hexpWidth, hfracWidth⟩
  unfold addFiniteOption at hresult
  by_cases hexceptional :
      (exponentField fmt (toWord x) == exponentMask fmt ||
        exponentField fmt (toWord y) == exponentMask fmt) = true
  · simp [hexceptional] at hresult
  rw [ite_eq_right hexceptional] at hresult
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hexceptional
  obtain ⟨hxFinite, hyFinite⟩ := hexceptional
  have hxExponent := exponentField_toNat_lt hwidth x
  have hyExponent := exponentField_toNat_lt hwidth y
  have hxMantissa := finiteMantissa_toNat_lt hwidth x
  have hyMantissa := finiteMantissa_toNat_lt hwidth y
  unfold FiniteKernel.addOption
  rw [decode_of_finite hieee hwidth x hxFinite]
  cases negateRight
  · simp only [Bool.false_eq_true, ite_false, Bool.xor_false] at hresult ⊢
    rw [decode_of_finite hieee hwidth y hyFinite]
    simp only
    rw [← FiniteKernel.addFields_eq]
    exact congrArg some
      (addFields_refines fmt hieee hwidth hexpWidth hfracWidth _ _ _ _ _ _
        hxExponent hyExponent hxMantissa hyMantissa result hresult).symm
  · simp only [ite_true, Bool.xor_true] at hresult ⊢
    rw [decode_neg_of_finite hieee hwidth y hyFinite]
    simp only
    rw [← FiniteKernel.addFields_eq]
    exact congrArg some
      (addFields_refines fmt hieee hwidth hexpWidth hfracWidth _ _ _ _ _ _
        hxExponent hyExponent hxMantissa hyMantissa result hresult).symm

end Model.NativeSmallWordAdd
end FloatLib.Floats.Formats.BinaryInterchange
