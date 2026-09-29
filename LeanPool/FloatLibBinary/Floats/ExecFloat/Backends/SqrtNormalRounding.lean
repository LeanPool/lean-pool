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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.SqrtArithmetic
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.ModelRounding.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Proof
public import Init.Data.Float.Model.Unpacked.Operations.Sqrt
public import Mathlib.Data.Nat.Sqrt

/-!
# Model square root of a normalized positive value

The binary32, binary64 and binary128 square-root kernels compute the same recipe: shift the
significand so that its integer square root has exactly `fracWidth + 1` bits, take the integer
root, round it by comparing the remainder with the root, and pack the result with a possible
carry into the exponent field. This module proves once, for every IEEE format, that the recipe
agrees with `Float.Model.UnpackedFloat.sqrt` on the proof model.

Each kernel proves that its word arithmetic computes this recipe, that the scaled radicand and
encoded exponent satisfy the stated bounds, and that its scaling constants satisfy `htarget`
and `hshift`. `Backends.SqrtArithmetic` supplies the shared affine exponent identities.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic

/--
Rounding a normalized square-root core result back to packed fields.

The input is the positive finite value `m * 2 ^ inputExponent`. The root exponent is `q - bias`,
and `shift` scales the significand so that the integer root of `m <<< shift` has exactly
`fracWidth + 1` bits. Under these conditions the model square root is the packed encoding of the
remainder-rounded root, with a carry into the exponent field when rounding reaches
`2 ^ (fracWidth + 1)`.
-/
theorem ofModel_sqrt_finite_positive_eq_ofFields (fmt : FloatFormat)
    (m shift q : Nat) (inputExponent : Int) (hm : 0 < m)
    (hshiftLower : 2 * fmt.fracWidth ≤ m.log2 + shift)
    (hshiftUpper : m.log2 + 1 + shift ≤ 2 * fmt.fracWidth + 2)
    (hq : 1 ≤ q) (hqCarry : q + 1 ≤ 2 * fmt.bias)
    (htarget : min (inputExponent.ediv 2)
        ((FloatFormat.toModel fmt).targetExponent
          ((Float.Model.totalExponent m inputExponent + 1).ediv 2)) =
      Int.ofNat q - Int.ofNat fmt.bias - fmt.fracWidth)
    (hshift : (inputExponent - 2 * (Int.ofNat q - Int.ofNat fmt.bias - fmt.fracWidth)).toNat =
      shift) :
    let root := Nat.sqrt (m <<< shift)
    let remainder := m <<< shift - root * root
    let rounded := if remainder ≤ root then root else root + 1
    ofModel fmt
        (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
          (.finite .positive m inputExponent hm)) =
      ofFields fmt false
        (q + if rounded = pow2 (fmt.fracWidth + 1) then 1 else 0)
        ((if rounded = pow2 (fmt.fracWidth + 1) then pow2 fmt.fracWidth else rounded) -
          pow2 fmt.fracWidth) := by
  intro root remainder rounded
  set rootExponent : Int := Int.ofNat q - Int.ofNat fmt.bias with hrootExponent
  set accuracy : Float.Model.UnpackedFloat.Accuracy :=
    if remainder = 0 then .exact else .inexact (if remainder ≤ root then .lt else .gt)
    with haccuracy
  have hrounded : rounded = if remainder ≤ root then root else root + 1 := rfl
  have hcore :
      Float.Model.UnpackedFloat.sqrtCore (FloatFormat.toModel fmt) m inputExponent =
        (root, rootExponent - fmt.fracWidth, accuracy) := by
    unfold Float.Model.UnpackedFloat.sqrtCore
    rw [htarget]
    dsimp only
    rw [hshift]
  simp only [Float.Model.UnpackedFloat.sqrt]
  change
    ofModel fmt
      (Float.Model.UnpackedFloat.roundWithAccuracy (FloatFormat.toModel fmt) .positive
        (Float.Model.UnpackedFloat.sqrtCore (FloatFormat.toModel fmt) m inputExponent).1
        (Float.Model.UnpackedFloat.sqrtCore (FloatFormat.toModel fmt) m inputExponent).2.1
        (Float.Model.UnpackedFloat.sqrtCore (FloatFormat.toModel fmt) m inputExponent).2.2) = _
  rw [hcore]
  dsimp only [Prod.fst, Prod.snd]
  have hleading : 2 ^ m.log2 ≤ m := (Nat.le_log2 hm.ne').mp le_rfl
  have hscaledLower : 2 ^ (2 * fmt.fracWidth) ≤ m <<< shift := by
    rw [Nat.shiftLeft_eq]
    calc 2 ^ (2 * fmt.fracWidth) ≤ 2 ^ (m.log2 + shift) :=
          Nat.pow_le_pow_right (by decide) hshiftLower
      _ = 2 ^ m.log2 * 2 ^ shift := Nat.pow_add ..
      _ ≤ m * 2 ^ shift := Nat.mul_le_mul_right _ hleading
  have hscaledUpper : m <<< shift < 2 ^ (2 * fmt.fracWidth + 2) :=
    lt_of_lt_of_le (Nat.shiftLeft_lt Nat.lt_log2_self)
      (Nat.pow_le_pow_right (by decide) hshiftUpper)
  have hrootLower : pow2 fmt.fracWidth ≤ root := by
    change pow2 fmt.fracWidth ≤ Nat.sqrt (m <<< shift)
    rw [pow2_eq_two_pow, Nat.le_sqrt, ← Nat.pow_add, ← two_mul]
    exact hscaledLower
  have hrootUpper : root < pow2 (fmt.fracWidth + 1) := by
    change Nat.sqrt (m <<< shift) < pow2 (fmt.fracWidth + 1)
    rw [pow2_eq_two_pow, Nat.sqrt_lt, ← Nat.pow_add]
    exact lt_of_lt_of_le hscaledUpper (Nat.pow_le_pow_right (by decide) (by omega))
  have hroundedLower : pow2 fmt.fracWidth ≤ rounded := by
    rw [hrounded]
    split <;> omega
  have hroundedUpper : rounded ≤ pow2 (fmt.fracWidth + 1) := by
    rw [hrounded]
    split <;> omega
  simp only [Int.ofNat_eq_natCast] at hrootExponent
  have hminNormal : FloatFormat.ieeeMinNormalExponent fmt ≤ rootExponent := by
    unfold FloatFormat.ieeeMinNormalExponent
    simp only [Int.ofNat_eq_natCast]
    omega
  have hmaxNormalCarry :
      rootExponent + 1 ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
    unfold FloatFormat.ieeeMaxNormalExponent
    simp only [Int.ofNat_eq_natCast]
    omega
  have hmaxNormal : rootExponent ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
    omega
  have hminNormalCarry : FloatFormat.ieeeMinNormalExponent fmt ≤ rootExponent + 1 := by
    omega
  have hfirst := shiftToTargetExponent_normalized fmt root rootExponent accuracy
    hrootLower hrootUpper hminNormal
  have hroundedMantissa :
      (Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        root accuracy).roundedMantissa = rounded := by
    rw [haccuracy, hrounded]
    exact roundedMantissa_of_sqrtRemainder root remainder
  rw [roundWithAccuracy_eq_finishRoundedMantissa, hfirst]
  simp only [hroundedMantissa]
  have hpow : 0 < pow2 fmt.fracWidth := by simp [pow2_eq_two_pow]
  by_cases hcarry : rounded = pow2 (fmt.fracWidth + 1)
  · have hfinish :
        finishRoundedMantissa (FloatFormat.toModel fmt) .positive
            (rounded, rootExponent - fmt.fracWidth) =
          .finite .positive (pow2 fmt.fracWidth) (rootExponent + 1 - fmt.fracWidth)
            (Nat.pos_of_ne_zero (by simp [pow2_eq_two_pow])) := by
      rw [hcarry]
      exact finishRoundedMantissa_normalized_carry fmt .positive rootExponent hminNormal
    have hpowLt : pow2 fmt.fracWidth < pow2 (fmt.fracWidth + 1) := by
      rw [pow2_eq_two_pow, pow2_eq_two_pow]
      exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
    have hpack :
        ofModel fmt
            (.finite .positive (pow2 fmt.fracWidth) (rootExponent + 1 - fmt.fracWidth)
              (Nat.pos_of_ne_zero (by simp [pow2_eq_two_pow]))) =
          ofFields fmt false (Int.toNat (rootExponent + 1 + Int.ofNat fmt.bias))
            (pow2 fmt.fracWidth - pow2 fmt.fracWidth) := by
      simpa [modelSign] using
        ofModel_finite_normalized_eq_ofFields fmt false (pow2 fmt.fracWidth)
          (rootExponent + 1) le_rfl hpowLt hminNormalCarry hmaxNormalCarry
    have hencoded : Int.toNat (rootExponent + 1 + Int.ofNat fmt.bias) = q + 1 := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hfinish, hpack, hencoded, ite_eq_left hcarry, ite_eq_left hcarry]
  · have hroundedHigh : rounded < pow2 (fmt.fracWidth + 1) :=
      lt_of_le_of_ne hroundedUpper hcarry
    have hfinish :
        finishRoundedMantissa (FloatFormat.toModel fmt) .positive
            (rounded, rootExponent - fmt.fracWidth) =
          .finite .positive rounded (rootExponent - fmt.fracWidth)
            (Nat.pos_of_ne_zero (Nat.ne_of_gt (hpow.trans_le hroundedLower))) :=
      finishRoundedMantissa_normalized fmt .positive rounded rootExponent
        hroundedLower hroundedHigh hminNormal
    have hpack :
        ofModel fmt
            (.finite .positive rounded (rootExponent - fmt.fracWidth)
              (Nat.pos_of_ne_zero (Nat.ne_of_gt (hpow.trans_le hroundedLower)))) =
          ofFields fmt false (Int.toNat (rootExponent + Int.ofNat fmt.bias))
            (rounded - pow2 fmt.fracWidth) := by
      simpa [modelSign] using
        ofModel_finite_normalized_eq_ofFields fmt false rounded rootExponent
          hroundedLower hroundedHigh hminNormal hmaxNormal
    have hencoded : Int.toNat (rootExponent + Int.ofNat fmt.bias) = q := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hfinish, hpack, hencoded, ite_eq_right hcarry, ite_eq_right hcarry, Nat.add_zero]

end FloatLib.Floats.Formats.BinaryInterchange.Model
