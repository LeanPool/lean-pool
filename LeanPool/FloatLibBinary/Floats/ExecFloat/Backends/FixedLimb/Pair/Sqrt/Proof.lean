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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Sqrt.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.RestoringSqrt.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.SqrtArithmetic
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.SqrtNormalRounding
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Spec.SquareRoot

/-!
# Correctness of two-word square root for normal inputs

The normal path aligns a `fracWidth + 1`-bit significand in a `UInt256`, computes a restoring
integer square root with `fracWidth + 1` base-four digits, and rounds from exact remainder
information. `sqrtNormal_refines` identifies each accepted result with the public format-level
square-root specification.

The kernel accepts only eligible layouts with `fracWidth ≤ 124` and `fracWidth + 1 ≤ bias`. The
first bound keeps the doubled remainder inside the two-word restoring state; the second is the
hypothesis under which `SqrtArithmetic.target_exponent` identifies the model's target exponent
with the kernel's affine exponent formula. Exceptional, subnormal, and unsupported inputs are
left to the operation dispatcher. Runtime clients can import `Sqrt.Runtime` separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic
open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord.RestoringSquareRoot

variable {fmt : FloatFormat}

private theorem alignSqrtRadicand_toNat
    (mantissa : UInt128) (shift : Nat) (hlower : 64 < shift) (hupper : shift < 128) :
    (alignSqrtRadicand mantissa shift).toNat = mantissa.toNat <<< shift :=
  UInt256.toNat_ofUInt128ShiftedLeft mantissa shift hlower hupper

private theorem toModel_of_positive_normal (h : Eligible fmt)
    (x : Model fmt)
    (hsign : signBit fmt (toWords x).hi = false)
    (hexponentZero : expField fmt (toWords x).hi ≠ 0)
    (hexponentFinite : expField fmt (toWords x).hi ≠ expAllOnes fmt) :
    Model.toModel x =
      .finite .positive
        (normalMantissa fmt (fracHigh fmt (toWords x).hi) (toWords x).lo).toNat
        (Int.ofNat (expField fmt (toWords x).hi).toNat - Int.ofNat (fmt.bias + fmt.fracWidth))
        (Nat.pos_of_ne_zero
          (by
            have hbounds :=
              normalMantissa_bounds h (fracHigh fmt (toWords x).hi)
                (toWords x).lo (fracHigh_lt h (toWords x).hi)
            exact Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hbounds.1))) := by
  let mantissa := (normalMantissa fmt (fracHigh fmt (toWords x).hi) (toWords x).lo).toNat
  have hmantissa : mantissa ≠ 0 := by
    have hbounds :=
      normalMantissa_bounds h (fracHigh fmt (toWords x).hi)
        (toWords x).lo (fracHigh_lt h (toWords x).hi)
    dsimp only [mantissa]
    exact Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hbounds.1)
  have hexponentBounds := normalExponent_bounds h x hexponentZero hexponentFinite
  have hexponentNat : (expField fmt (toWords x).hi).toNat ≠ 0 := hexponentBounds.1.ne'
  have hdecode := decode_of_normalExponent h x hexponentZero hexponentFinite
  have hdyadic :
      Model.toDyadicOption x =
        some
          ({ negative := false
             significand := mantissa
             exponent :=
              Int.ofNat (expField fmt (toWords x).hi).toNat -
                Int.ofNat (fmt.bias + fmt.fracWidth) } :
            Numerics.Dyadic) := by
    rw [FiniteKernel.toDyadic_eq_decode, hdecode]
    simp only [Option.map_some, hsign]
    rw [normalComponents_toDyadic h false (expField fmt (toWords x).hi).toNat mantissa
      hexponentNat hmantissa]
  have hieeeDecode :
      Model.ieeeToDyadicOption x =
        some
          ({ negative := false
             significand := mantissa
             exponent :=
              Int.ofNat (expField fmt (toWords x).hi).toNat -
                Int.ofNat (fmt.bias + fmt.fracWidth) } :
            Numerics.Dyadic) := by
    simpa [Model.toDyadicOption, h.isIEEE] using hdyadic
  simpa [mantissa, Model.modelSign] using
    Model.toModel_eq_finite_of_ieeeToDyadicOption_eq_some
      x false mantissa
      (Int.ofNat (expField fmt (toWords x).hi).toNat - Int.ofNat (fmt.bias + fmt.fracWidth))
      hmantissa hieeeDecode

/-- The model's smallest exponent is the negated subnormal alignment shift. -/
private theorem model_minExponent (h : Eligible fmt) :
    (FloatFormat.toModel fmt).minExponent = -Int.ofNat (fmt.bias + fmt.fracWidth - 1) := by
  have hfrac := h.frac_gt
  have hbiasInt : (fmt.bias : Int) = 2 ^ (fmt.expWidth - 1) - 1 := by
    unfold FloatFormat.bias
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  unfold Float.Model.Format.minExponent Float.Model.Format.mantissaBits FloatFormat.toModel
  simp only [Int.ofNat_eq_natCast]
  push_cast
  omega

/-- The model's significand width, including the implicit bit. -/
private theorem model_mantissaBits :
    ((FloatFormat.toModel fmt).mantissaBits : Int) = Int.ofNat (fmt.fracWidth + 1) := by
  simp [Float.Model.Format.mantissaBits, FloatFormat.toModel, Nat.add_comm]

private theorem sqrt_target_exponent (h : Eligible fmt)
    (hbiasGe : fmt.fracWidth + 1 ≤ fmt.bias)
    (m scale : Nat) (hleading : m.log2 < fmt.fracWidth + 1) :
    let inputExponent := Int.ofNat scale - Int.ofNat (fmt.bias + fmt.fracWidth - 1)
    let position := m.log2 + scale
    let rootExponent :=
      Int.ofNat ((position + (fmt.bias - fmt.fracWidth + 1)) / 2) - Int.ofNat fmt.bias
    min (inputExponent.ediv 2)
        ((FloatFormat.toModel fmt).targetExponent
          ((Float.Model.totalExponent m inputExponent + 1).ediv 2)) =
      rootExponent - Int.ofNat fmt.fracWidth := by
  dsimp only
  have hfrac := h.frac_gt
  rw [Float.Model.Format.targetExponent, model_minExponent h, model_mantissaBits]
  unfold Float.Model.totalExponent
  exact target_exponent m.log2 scale (fmt.bias + fmt.fracWidth - 1)
    (fmt.bias - fmt.fracWidth + 1) fmt.bias fmt.fracWidth
    (by omega) (by omega) fmt.bias_pos (by omega) (by omega)

private theorem sqrt_shift_amount (h : Eligible fmt)
    (hbiasGe : fmt.fracWidth + 1 ≤ fmt.bias)
    (m scale : Nat) (hleading : m.log2 < fmt.fracWidth + 1) :
    let inputExponent := Int.ofNat scale - Int.ofNat (fmt.bias + fmt.fracWidth - 1)
    let position := m.log2 + scale
    let rootExponent :=
      Int.ofNat ((position + (fmt.bias - fmt.fracWidth + 1)) / 2) - Int.ofNat fmt.bias
    (inputExponent - 2 * (rootExponent - Int.ofNat fmt.fracWidth)).toNat =
      (position + (fmt.bias - fmt.fracWidth + 1)) % 2 + 2 * fmt.fracWidth - m.log2 := by
  dsimp only
  have hfrac := h.frac_gt
  exact shift_amount m.log2 scale (fmt.bias + fmt.fracWidth - 1)
    (fmt.bias - fmt.fracWidth + 1) fmt.bias fmt.fracWidth (by omega) (by omega)

private def sqrtNormalSpec (fmt : FloatFormat) (exponent mantissa : Nat) : Model fmt :=
  let scale := exponent - 1
  let leading := mantissa.log2
  let position := leading + scale
  let shift := (position + (fmt.bias - fmt.fracWidth + 1)) % 2 + 2 * fmt.fracWidth - leading
  let scaled := mantissa <<< shift
  let root := Nat.sqrt scaled
  let remainder := scaled - root * root
  let rounded := if remainder ≤ root then root else root + 1
  let carry := rounded = pow2 (fmt.fracWidth + 1)
  let encodedExponent :=
    (position + (fmt.bias - fmt.fracWidth + 1)) / 2 + if carry then 1 else 0
  let normalized := if carry then pow2 fmt.fracWidth else rounded
  ofFields fmt false encodedExponent (normalized - pow2 fmt.fracWidth)

private theorem sqrtNormalSpec_eq_model (h : Eligible fmt)
    (hbiasGe : fmt.fracWidth + 1 ≤ fmt.bias)
    (exponent mantissa : Nat)
    (hexponentPositive : 0 < exponent)
    (hexponentFinite : exponent < fmt.expAllOnesNat)
    (hmantissaLower : 2 ^ fmt.fracWidth ≤ mantissa)
    (hmantissaUpper : mantissa < 2 ^ (fmt.fracWidth + 1)) :
    sqrtNormalSpec fmt exponent mantissa =
      ofModel fmt
        (Float.Model.UnpackedFloat.sqrt
          (FloatFormat.toModel fmt)
          (.finite .positive mantissa
            (Int.ofNat exponent - Int.ofNat (fmt.bias + fmt.fracWidth))
            (Nat.pos_of_ne_zero
              (Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hmantissaLower))))) := by
  have hfrac := h.frac_gt
  have hallOnes := fmt.expAllOnesNat_eq_two_mul_bias_add_one
  have hmantissaNonzero : mantissa ≠ 0 :=
    Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hmantissaLower)
  have hleading : mantissa.log2 < fmt.fracWidth + 1 := by
    rw [Nat.log2_lt hmantissaNonzero]
    exact hmantissaUpper
  have hleadingEq : mantissa.log2 = fmt.fracWidth :=
    (Nat.log2_eq_iff hmantissaNonzero).2 ⟨hmantissaLower, hmantissaUpper⟩
  have hinput :
      Int.ofNat exponent - Int.ofNat (fmt.bias + fmt.fracWidth) =
        Int.ofNat (exponent - 1) - Int.ofNat (fmt.bias + fmt.fracWidth - 1) := by
    simp only [Int.ofNat_eq_natCast]
    omega
  rw [hinput, ofModel_sqrt_finite_positive_eq_ofFields fmt mantissa
    ((mantissa.log2 + (exponent - 1) + (fmt.bias - fmt.fracWidth + 1)) % 2 +
      2 * fmt.fracWidth - mantissa.log2)
    ((mantissa.log2 + (exponent - 1) + (fmt.bias - fmt.fracWidth + 1)) / 2)
    (Int.ofNat (exponent - 1) - Int.ofNat (fmt.bias + fmt.fracWidth - 1))
    (Nat.pos_of_ne_zero hmantissaNonzero)
    (by omega) (by omega)
    (by rw [hleadingEq]; omega) (by rw [hleadingEq]; omega)
    (sqrt_target_exponent h hbiasGe mantissa (exponent - 1) hleading)
    (sqrt_shift_amount h hbiasGe mantissa (exponent - 1) hleading)]
  simp only [sqrtNormalSpec]

private theorem exponentShift_eq_modelShift
    (hbiasGe : fmt.fracWidth + 1 ≤ fmt.bias)
    (exponent : UInt64) (hexponentPositive : 0 < exponent.toNat) :
    (if (exponent &&& 1) == 1 then fmt.fracWidth else fmt.fracWidth + 1) =
      (fmt.fracWidth + (exponent.toNat - 1) + (fmt.bias - fmt.fracWidth + 1)) % 2 +
        2 * fmt.fracWidth - fmt.fracWidth := by
  have hand : (exponent &&& 1).toNat = exponent.toNat % 2 := by
    rw [UInt64.toNat_and]
    simp only [show (1 : UInt64).toNat = 1 by decide, Nat.and_one_is_mod]
  have hbiasOdd : fmt.bias % 2 = 1 := by
    have hexp := fmt.expWidth_ge_two
    have hpow : 2 ^ (fmt.expWidth - 1) = 2 * 2 ^ (fmt.expWidth - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    have hpos : 0 < 2 ^ (fmt.expWidth - 2) := Nat.two_pow_pos _
    unfold FloatFormat.bias
    rw [hpow]
    omega
  by_cases hodd : (exponent &&& 1) == 1
  · have hoddEq : exponent &&& 1 = 1 := beq_iff_eq.mp hodd
    have hmod : exponent.toNat % 2 = 1 := by
      rw [← hand, hoddEq]
      decide
    rw [ite_eq_left hodd]
    omega
  · have hmod : exponent.toNat % 2 = 0 := by
      have hnotOne : exponent.toNat % 2 ≠ 1 := by
        intro hone
        apply hodd
        apply beq_iff_eq.mpr
        apply UInt64.toNat_inj.mp
        rw [hand, hone]
        decide
      omega
    rw [ite_eq_right hodd]
    omega

private theorem shiftedMantissa_lt (mantissa width shift : Nat)
    (hmantissa : mantissa < 2 ^ (width + 1))
    (hshift : shift = width ∨ shift = width + 1) :
    mantissa <<< shift < 2 ^ (2 * width + 2) := by
  rw [Nat.shiftLeft_eq]
  rcases hshift with hs | hs <;> rw [hs]
  · calc
      mantissa * 2 ^ width < 2 ^ (width + 1) * 2 ^ width :=
        Nat.mul_lt_mul_of_pos_right hmantissa (Nat.two_pow_pos _)
      _ ≤ 2 ^ (2 * width + 2) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by decide) (by omega)
  · calc
      mantissa * 2 ^ (width + 1) < 2 ^ (width + 1) * 2 ^ (width + 1) :=
        Nat.mul_lt_mul_of_pos_right hmantissa (Nat.two_pow_pos _)
      _ = 2 ^ (2 * width + 2) := by
        rw [← pow_add]
        congr 1
        omega

private theorem sqrtNormalOption_eq_sqrtNormalSpec (h : Eligible fmt)
    (hbiasGe : fmt.fracWidth + 1 ≤ fmt.bias) (hfracLe : fmt.fracWidth ≤ 124)
    (x result : Model fmt) (hfast : sqrtNormalOption x = some result) :
    result =
      sqrtNormalSpec fmt
        (expField fmt (toWords x).hi).toNat
        (normalMantissa fmt (fracHigh fmt (toWords x).hi) (toWords x).lo).toNat := by
  have hfrac := h.frac_gt
  have hallOnes := fmt.expAllOnesNat_eq_two_mul_bias_add_one
  have hbias := h.bias_lt
  have hexpWidth := fmt.two_pow_expWidth_eq_two_mul_bias_add_two
  have hnotBias : ¬fmt.bias < fmt.fracWidth + 1 := not_lt.mpr hbiasGe
  have hnotFrac : ¬124 < fmt.fracWidth := not_lt.mpr hfracLe
  let words := toWords x
  let exponent := expField fmt words.hi
  let mantissa := normalMantissa fmt (fracHigh fmt words.hi) words.lo
  let shift := if (exponent &&& 1) == 1 then fmt.fracWidth else fmt.fracWidth + 1
  let radicand := alignSqrtRadicand mantissa shift
  let state := rootAndRemainder radicand (fmt.fracWidth + 1)
  let rounded := roundRoot state
  let carry := isCarry fmt rounded
  let normalized := normalizeCarry fmt carry rounded
  let resultExponent := (exponent + UInt64.ofNat fmt.bias) / 2 + if carry then 1 else 0
  change result = sqrtNormalSpec fmt exponent.toNat mantissa.toNat
  by_cases hsign : x.bits.msb = true
  · simp [sqrtNormalOption, hsign] at hfast
  have hsignFalse : x.bits.msb = false := Bool.eq_false_of_not_eq_true hsign
  by_cases hexponentZero : exponent = 0
  · simp [sqrtNormalOption, hsignFalse, hnotBias, hnotFrac, words, exponent, hexponentZero] at hfast
  by_cases hexponentAll : exponent = expAllOnes fmt
  · simp [sqrtNormalOption, hsignFalse, hnotBias, hnotFrac, words, exponent, hexponentAll] at hfast
  have hresult : result = packNormal fmt false resultExponent normalized := by
    simpa [sqrtNormalOption, hsignFalse, hnotBias, hnotFrac, words, exponent, hexponentZero,
      hexponentAll, mantissa, shift, radicand, state, rounded, carry, normalized,
      resultExponent] using hfast.symm
  have hexponentBounds : 0 < exponent.toNat ∧ exponent.toNat < fmt.expAllOnesNat :=
    normalExponent_bounds h x hexponentZero hexponentAll
  have hexponentPositive : 0 < exponent.toNat := hexponentBounds.1
  have hexponentFinite : exponent.toNat < fmt.expAllOnesNat := hexponentBounds.2
  have hmantissaBounds :
      2 ^ fmt.fracWidth ≤ mantissa.toNat ∧ mantissa.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h (fracHigh fmt words.hi) words.lo (fracHigh_lt h words.hi)
  have hmantissaNe : mantissa.toNat ≠ 0 :=
    Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hmantissaBounds.1)
  have hleading : mantissa.toNat.log2 = fmt.fracWidth :=
    (Nat.log2_eq_iff hmantissaNe).2 hmantissaBounds
  let scale := exponent.toNat - 1
  let position := mantissa.toNat.log2 + scale
  let modelShift :=
    (position + (fmt.bias - fmt.fracWidth + 1)) % 2 + 2 * fmt.fracWidth - mantissa.toNat.log2
  let scaled := mantissa.toNat <<< modelShift
  let root := Nat.sqrt scaled
  let remainder := scaled - root * root
  let genericRounded := if remainder ≤ root then root else root + 1
  let genericCarry := genericRounded = pow2 (fmt.fracWidth + 1)
  let encodedExponent :=
    (position + (fmt.bias - fmt.fracWidth + 1)) / 2 + if genericCarry then 1 else 0
  let genericNormalized := if genericCarry then pow2 fmt.fracWidth else genericRounded
  have hshift : shift = modelShift := by
    have hnative := exponentShift_eq_modelShift hbiasGe exponent hexponentPositive
    dsimp only [shift, modelShift, position, scale]
    rw [hnative, hleading]
  have hshiftCases : shift = fmt.fracWidth ∨ shift = fmt.fracWidth + 1 := by
    dsimp only [shift]
    split <;> simp
  have hshiftLower : 64 < shift := by
    rcases hshiftCases with hs | hs <;> omega
  have hshiftUpper : shift < 128 := by
    rcases hshiftCases with hs | hs <;> omega
  have hradicand : radicand.toNat = scaled := by
    rw [show radicand = alignSqrtRadicand mantissa shift by rfl,
      alignSqrtRadicand_toNat mantissa shift hshiftLower hshiftUpper]
    simp only [scaled, hshift]
  have hscaledUpper : scaled < 2 ^ (2 * fmt.fracWidth + 2) := by
    exact shiftedMantissa_lt _ _ _ hmantissaBounds.2 (hshift ▸ hshiftCases)
  have hscaledLower : 2 ^ (2 * fmt.fracWidth) ≤ scaled := by
    dsimp only [scaled]
    rw [← hshift, Nat.shiftLeft_eq]
    rcases hshiftCases with hs | hs <;> rw [hs]
    · calc
        2 ^ (2 * fmt.fracWidth) = 2 ^ fmt.fracWidth * 2 ^ fmt.fracWidth := by
          rw [← pow_add, two_mul]
        _ ≤ mantissa.toNat * 2 ^ fmt.fracWidth :=
          Nat.mul_le_mul_right _ hmantissaBounds.1
    · calc
        2 ^ (2 * fmt.fracWidth) ≤ 2 ^ fmt.fracWidth * 2 ^ (fmt.fracWidth + 1) := by
          rw [← pow_add]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        _ ≤ mantissa.toNat * 2 ^ (fmt.fracWidth + 1) :=
          Nat.mul_le_mul_right _ hmantissaBounds.1
  have hradicandFit : radicand.toNat < 2 ^ (2 * (fmt.fracWidth + 1)) := by
    rw [hradicand, show 2 * (fmt.fracWidth + 1) = 2 * fmt.fracWidth + 2 by omega]
    exact hscaledUpper
  have hrounded : rounded.toNat = genericRounded := by
    have hnative :=
      roundRoot_toNat radicand (fmt.fracWidth + 1) (by omega) (by omega) hradicandFit
    simpa only [rounded, state, root, remainder, genericRounded, hradicand] using hnative
  have hcarry : carry = true ↔ genericCarry := by
    rw [show carry = isCarry fmt rounded by rfl, isCarry_iff h rounded, hrounded]
  have hrootLower : 2 ^ fmt.fracWidth ≤ root := by
    dsimp only [root]
    rw [Nat.le_sqrt, ← pow_add, ← two_mul]
    exact hscaledLower
  have hrootUpper : root < 2 ^ (fmt.fracWidth + 1) := by
    dsimp only [root]
    rw [Nat.sqrt_lt, ← pow_add, show fmt.fracWidth + 1 + (fmt.fracWidth + 1) =
      2 * fmt.fracWidth + 2 by omega]
    exact hscaledUpper
  have hgenericRoundedLower : 2 ^ fmt.fracWidth ≤ genericRounded := by
    dsimp only [genericRounded]
    split <;> omega
  have hgenericRoundedUpper : genericRounded ≤ 2 ^ (fmt.fracWidth + 1) := by
    dsimp only [genericRounded]
    split <;> omega
  have hnormalized : normalized.toNat = genericNormalized := by
    dsimp only [normalized, genericNormalized]
    rw [normalizeCarry_toNat h]
    by_cases hnativeCarry : carry = true
    · have hgenericCarry : genericCarry := hcarry.mp hnativeCarry
      simp [hnativeCarry, hgenericCarry]
    · have hnativeCarryFalse : carry = false := Bool.eq_false_of_not_eq_true hnativeCarry
      have hgenericCarry : ¬genericCarry := fun hg => hnativeCarry (hcarry.mpr hg)
      simp [hnativeCarryFalse, hgenericCarry, hrounded]
  have hgenericNormalizedLower : 2 ^ fmt.fracWidth ≤ genericNormalized := by
    dsimp only [genericNormalized]
    split
    · simp [pow2_eq_two_pow]
    · exact hgenericRoundedLower
  have hgenericNormalizedUpper : genericNormalized < 2 ^ (fmt.fracWidth + 1) := by
    dsimp only [genericNormalized]
    by_cases hgenericCarry : genericCarry
    · simp only [hgenericCarry, ite_true, pow2_eq_two_pow]
      exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
    · simp only [hgenericCarry, ite_false]
      exact lt_of_le_of_ne hgenericRoundedUpper
        (by
          intro heq
          apply hgenericCarry
          simpa [genericCarry, pow2_eq_two_pow] using heq)
  have hbiasWord : (UInt64.ofNat fmt.bias).toNat = fmt.bias := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    norm_num at hbias ⊢
    omega
  have hexponentAdd :
      (exponent + UInt64.ofNat fmt.bias).toNat = exponent.toNat + fmt.bias := by
    rw [UInt64.toNat_add, hbiasWord]
    apply Nat.mod_eq_of_lt
    norm_num at hbias ⊢
    omega
  have hexponentHalf :
      ((exponent + UInt64.ofNat fmt.bias) / 2).toNat = (exponent.toNat + fmt.bias) / 2 := by
    rw [UInt64.toNat_div, hexponentAdd]
    rfl
  have hpositionHalf :
      (position + (fmt.bias - fmt.fracWidth + 1)) / 2 = (exponent.toNat + fmt.bias) / 2 := by
    dsimp only [position, scale]
    rw [hleading]
    congr 1
    omega
  have hresultExponentNative :
      resultExponent.toNat = (exponent.toNat + fmt.bias) / 2 + if carry then 1 else 0 := by
    by_cases hnativeCarry : carry = true
    · dsimp only [resultExponent]
      simp only [hnativeCarry, ite_true]
      rw [UInt64.toNat_add, hexponentHalf]
      rw [show (1 : UInt64).toNat = 1 by decide]
      apply Nat.mod_eq_of_lt
      norm_num at hbias ⊢
      omega
    · have hnativeCarryFalse : carry = false := Bool.eq_false_of_not_eq_true hnativeCarry
      simp [resultExponent, hnativeCarryFalse, hexponentHalf]
  have hresultExponent : resultExponent.toNat = encodedExponent := by
    rw [hresultExponentNative]
    dsimp only [encodedExponent]
    rw [hpositionHalf]
    by_cases hnativeCarry : carry = true
    · have hgenericCarry : genericCarry := hcarry.mp hnativeCarry
      simp [hnativeCarry, hgenericCarry]
    · have hnativeCarryFalse : carry = false := Bool.eq_false_of_not_eq_true hnativeCarry
      have hgenericCarry : ¬genericCarry := fun hg => hnativeCarry (hcarry.mpr hg)
      simp [hnativeCarryFalse, hgenericCarry]
  have hresultExponentUpper : resultExponent.toNat < 2 ^ fmt.expWidth := by
    rw [hresultExponent, hexpWidth]
    dsimp only [encodedExponent]
    rw [hpositionHalf]
    split <;> omega
  rw [hresult, packNormal_eq_ofFields h false resultExponent normalized hresultExponentUpper
    (by rw [hnormalized]; exact hgenericNormalizedLower)
    (by rw [hnormalized]; exact hgenericNormalizedUpper)]
  rw [hresultExponent, hnormalized]
  simp only [sqrtNormalSpec, scale, position, modelShift, scaled, root, remainder,
    genericRounded, genericCarry, encodedExponent, genericNormalized]

/-- Every accepted two-word square root agrees with the exact specification. -/
theorem sqrtNormal_refines (h : Eligible fmt)
    (x result : Model fmt) (hfast : sqrtNormalOption x = some result) :
    result = Model.Spec.sqrt x := by
  let exponent := expField fmt (toWords x).hi
  let mantissa := normalMantissa fmt (fracHigh fmt (toWords x).hi) (toWords x).lo
  have hsignFalse : x.bits.msb = false := by
    by_cases hsign : x.bits.msb = true
    · simp [sqrtNormalOption, hsign] at hfast
    · exact Bool.eq_false_of_not_eq_true hsign
  by_cases hbiasGe : fmt.fracWidth + 1 ≤ fmt.bias
  swap
  · have hlt : fmt.bias < fmt.fracWidth + 1 := not_le.mp hbiasGe
    simp [sqrtNormalOption, hsignFalse, hlt] at hfast
  by_cases hfracLe : fmt.fracWidth ≤ 124
  swap
  · have hlt : 124 < fmt.fracWidth := not_le.mp hfracLe
    simp [sqrtNormalOption, hsignFalse, hlt] at hfast
  have hnotBias : ¬fmt.bias < fmt.fracWidth + 1 := not_lt.mpr hbiasGe
  have hnotFrac : ¬124 < fmt.fracWidth := not_lt.mpr hfracLe
  have hexponentZero : exponent ≠ 0 := by
    intro hzero
    simp [sqrtNormalOption, hsignFalse, hnotBias, hnotFrac, exponent, hzero] at hfast
  have hexponentFinite : exponent ≠ expAllOnes fmt := by
    intro hall
    simp [sqrtNormalOption, hsignFalse, hnotBias, hnotFrac, exponent, hall] at hfast
  have hsignNative : signBit fmt (toWords x).hi = false := by
    rw [signBit_eq h x, Model.signBit_eq_msb]
    exact hsignFalse
  have hsignPublic : Model.signBit x = false := by
    rw [Model.signBit_eq_msb]
    exact hsignFalse
  have hexponentBounds : 0 < exponent.toNat ∧ exponent.toNat < fmt.expAllOnesNat :=
    normalExponent_bounds h x hexponentZero hexponentFinite
  have hexponentZeroNat : exponent.toNat ≠ 0 := hexponentBounds.1.ne'
  have hexponentFiniteNat : exponent.toNat ≠ fmt.expAllOnesNat :=
    Nat.ne_of_lt hexponentBounds.2
  have hexponentPublic : Model.expField x = exponent.toNat := (expField_toNat h x).symm
  have hfinite : Model.isFinite x = true := by
    simp [Model.isFinite, h.encoding, Model.IEEE.isFinite, hexponentPublic, hexponentFiniteNat]
  have hnonzero : Model.isZero x = false := by
    simp [Model.isZero, h.encoding, Model.IEEE.isZero, hexponentPublic, hexponentZeroNat]
  have hbounds :
      2 ^ fmt.fracWidth ≤ mantissa.toNat ∧ mantissa.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h (fracHigh fmt (toWords x).hi) (toWords x).lo
      (fracHigh_lt h (toWords x).hi)
  have hnative := sqrtNormalOption_eq_sqrtNormalSpec h hbiasGe hfracLe x result hfast
  have hmodel :=
    sqrtNormalSpec_eq_model h hbiasGe exponent.toNat mantissa.toNat
      hexponentBounds.1 hexponentBounds.2 hbounds.1 hbounds.2
  have hpublic := Model.Spec.sqrt_eq_model h.isIEEE x hfinite hnonzero hsignPublic
  calc
    result = sqrtNormalSpec fmt exponent.toNat mantissa.toNat := hnative
    _ = ofModel fmt
        (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt) (toModel x)) := by
      rw [toModel_of_positive_normal h x hsignNative hexponentZero hexponentFinite]
      exact hmodel
    _ = Model.Spec.sqrt x := hpublic.symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
