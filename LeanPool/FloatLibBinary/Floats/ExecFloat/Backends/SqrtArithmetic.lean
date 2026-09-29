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

public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.DivMod

/-!
# Shared arithmetic for fixed-width square-root refinements

The binary32, binary64, and binary128 square-root kernels use the same affine exponent
calculation with different format constants. This module records that calculation once so each
backend proof only supplies its descriptor-specific constants.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic

/--
The unpacked-model accuracy used by integer square root rounds up exactly when the square
remainder is larger than the lower root.

For `n = root² + remainder`, comparison with `(root + 1 / 2)²` reduces to comparing the integer
remainder with `root`: `remainder ≤ root` is below the midpoint, while the next integer remainder
is above it. Thus an integer radicand cannot produce a square-root midpoint tie.
-/
theorem roundedMantissa_of_sqrtRemainder (root remainder : Nat) :
    let accuracy : Float.Model.UnpackedFloat.Accuracy :=
      if remainder = 0 then
        .exact
      else
        .inexact (if remainder ≤ root then .lt else .gt)
    (Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
      root accuracy).roundedMantissa =
        if remainder ≤ root then root else root + 1 := by
  dsimp only
  by_cases hremainderZero : remainder = 0
  · simp [hremainderZero,
      Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
      Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
      Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy,
      Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]
  · by_cases hremainderLe : remainder ≤ root
    · simp [hremainderZero, hremainderLe,
        Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
        Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
        Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy,
        Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]
    · simp [hremainderZero, hremainderLe,
        Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
        Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
        Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy,
        Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]

/--
Move an even affine offset through Euclidean division by two.

The balance equation says that `inputShift` and `outputOffset` describe the same exponent origin
on opposite sides of the radix point.
-/
theorem half_sub_eq
    (position inputShift outputOffset outputBias : Nat)
    (hbalance : inputShift + outputOffset = 2 * outputBias) :
    (Int.ofNat position - Int.ofNat inputShift).ediv 2 =
      Int.ofNat ((position + outputOffset) / 2) -
        Int.ofNat outputBias := by
  change (Int.ofNat position - Int.ofNat inputShift) / 2 =
    Int.ofNat ((position + outputOffset) / 2) - Int.ofNat outputBias
  have hnumerator :
      Int.ofNat position - Int.ofNat inputShift =
        Int.ofNat (position + outputOffset) -
          Int.ofNat outputBias * 2 := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    omega
  rw [hnumerator, Int.sub_mul_ediv_right]
  · exact congrArg (fun value : Int => value - Int.ofNat outputBias) <|
      (Int.natCast_ediv (position + outputOffset) 2).symm
  · decide

/--
Normalize the total-exponent numerator used by square-root target-exponent calculations.
-/
theorem sum_half_sub_eq
    (leading scale inputShift outputOffset outputBias : Nat)
    (hinput : 2 ≤ inputShift)
    (hbalance : inputShift - 2 + outputOffset = 2 * outputBias) :
    (Int.ofNat leading + 1 + (Int.ofNat scale - Int.ofNat inputShift) + 1).ediv 2 =
      Int.ofNat ((leading + scale + outputOffset) / 2) -
        Int.ofNat outputBias := by
  have hnumerator :
      Int.ofNat leading + 1 + (Int.ofNat scale - Int.ofNat inputShift) + 1 =
        Int.ofNat (leading + scale) - Int.ofNat (inputShift - 2) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hinput]
    omega
  rw [hnumerator]
  exact half_sub_eq (leading + scale) (inputShift - 2)
    outputOffset outputBias hbalance

/-- Cast a natural affine numerator before or after division by two. -/
theorem sum_natCast_ediv_two (left right offset : Nat) :
    (Int.ofNat left + Int.ofNat right + Int.ofNat offset).ediv 2 =
      Int.ofNat ((left + right + offset) / 2) := by
  have hnumerator :
      Int.ofNat left + Int.ofNat right + Int.ofNat offset =
        Int.ofNat (left + right + offset) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
  rw [hnumerator]
  exact (Int.natCast_ediv (left + right + offset) 2).symm

/--
Normalize the target exponent selected for a square-root result.

The hypotheses express the format-independent relationships among the encoded exponent origin,
the result bias, and the fraction width. In particular, the affine offset must leave enough room
for the normalized result significand, and the input leading bit must lie within that significand.
-/
theorem target_exponent
    (leading scale inputShift outputOffset outputBias fractionBits : Nat)
    (hleading : leading ≤ fractionBits)
    (hinput : 2 ≤ inputShift)
    (hbias : 1 ≤ outputBias)
    (hnormal :
      outputBias + fractionBits ≤ inputShift + outputOffset / 2)
    (hbalance : inputShift + outputOffset = 2 * outputBias) :
    min ((Int.ofNat scale - Int.ofNat inputShift).ediv 2)
        (max
          ((Int.ofNat leading + 1 +
                (Int.ofNat scale - Int.ofNat inputShift) + 1).ediv 2 -
            Int.ofNat (fractionBits + 1))
          (-Int.ofNat inputShift)) =
      (Int.ofNat leading + Int.ofNat scale +
          Int.ofNat outputOffset).ediv 2 -
        Int.ofNat outputBias - Int.ofNat fractionBits := by
  let position := leading + scale
  let rootExponent :=
    Int.ofNat ((position + outputOffset) / 2) -
      Int.ofNat outputBias
  have htotalBalance :
      inputShift - 2 + outputOffset = 2 * (outputBias - 1) := by
    omega
  have htotal :
      (Int.ofNat leading + 1 +
          (Int.ofNat scale - Int.ofNat inputShift) + 1).ediv 2 =
        rootExponent + 1 := by
    dsimp only [rootExponent, position]
    rw [sum_half_sub_eq leading scale inputShift outputOffset
      (outputBias - 1) hinput htotalBalance]
    simp only [Int.ofNat_eq_natCast, Nat.cast_sub hbias]
    omega
  have hrhs :
      (Int.ofNat leading + Int.ofNat scale +
          Int.ofNat outputOffset).ediv 2 -
          Int.ofNat outputBias - Int.ofNat fractionBits =
        rootExponent - Int.ofNat fractionBits := by
    dsimp only [rootExponent, position]
    rw [sum_natCast_ediv_two]
  have hrootNormal :
      -Int.ofNat inputShift ≤ rootExponent - Int.ofNat fractionBits := by
    have hquotient :
        outputOffset / 2 ≤ (position + outputOffset) / 2 := by
      dsimp only [position]
      omega
    have hquotientInt :
        Int.ofNat (outputOffset / 2) ≤
          Int.ofNat ((position + outputOffset) / 2) :=
      Int.ofNat_le.mpr hquotient
    have hnormalInt :
        Int.ofNat (outputBias + fractionBits) ≤
          Int.ofNat (inputShift + outputOffset / 2) :=
      Int.ofNat_le.mpr hnormal
    dsimp only [rootExponent]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hnormalInt ⊢
    omega
  have htargetLe :
      rootExponent - Int.ofNat fractionBits ≤
        (Int.ofNat scale - Int.ofNat inputShift).ediv 2 := by
    have htarget :
        rootExponent - Int.ofNat fractionBits =
          (Int.ofNat position - Int.ofNat inputShift -
              Int.ofNat fractionBits * 2) / 2 := by
      dsimp only [rootExponent]
      rw [← half_sub_eq position inputShift outputOffset outputBias hbalance]
      exact
        (Int.sub_mul_ediv_right
          (Int.ofNat position - Int.ofNat inputShift)
          (Int.ofNat fractionBits) (by decide)).symm
    rw [htarget]
    apply Int.ediv_le_ediv (by decide)
    dsimp only [position]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    omega
  have hrootTarget :
      rootExponent + 1 - Int.ofNat (fractionBits + 1) =
        rootExponent - Int.ofNat fractionBits := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    omega
  have hmax :
      max (rootExponent - Int.ofNat fractionBits)
          (-Int.ofNat inputShift) =
        rootExponent - Int.ofNat fractionBits :=
    Int.max_eq_left hrootNormal
  have hmin :
      min ((Int.ofNat scale - Int.ofNat inputShift).ediv 2)
          (rootExponent - Int.ofNat fractionBits) =
        rootExponent - Int.ofNat fractionBits :=
    Int.min_eq_right htargetLe
  rw [htotal, hrootTarget, hmax, hmin, hrhs]

/--
Compute the nonnegative integer shift required to align a square-root radicand.

After the exponent origins cancel, only the parity of the affine position remains. The result is
therefore twice the destination fraction width, minus the input's leading-bit position, plus one
when the affine position is odd.
-/
theorem shift_amount
    (leading scale inputShift outputOffset outputBias fractionBits : Nat)
    (hleading : leading ≤ fractionBits)
    (hbalance : inputShift + outputOffset = 2 * outputBias) :
    let position := leading + scale
    let rootExponent :=
      Int.ofNat ((position + outputOffset) / 2) - Int.ofNat outputBias
    (Int.ofNat scale - Int.ofNat inputShift -
        2 * (rootExponent - Int.ofNat fractionBits)).toNat =
      (position + outputOffset) % 2 + 2 * fractionBits - leading := by
  dsimp only
  let position := leading + scale
  let numerator := position + outputOffset
  have hdecompose :
      numerator % 2 + 2 * (numerator / 2) = numerator := by
    simpa [Nat.mul_comm] using Nat.mod_add_div numerator 2
  have hnonnegative :
      leading ≤ numerator % 2 + 2 * fractionBits := by
    omega
  have hvalue :
      Int.ofNat scale - Int.ofNat inputShift -
          2 *
            (Int.ofNat (numerator / 2) -
              Int.ofNat outputBias - Int.ofNat fractionBits) =
        Int.ofNat (numerator % 2 + 2 * fractionBits - leading) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_sub hnonnegative, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat]
    dsimp only [numerator, position] at hdecompose ⊢
    omega
  rw [show leading + scale + outputOffset = numerator by rfl, hvalue]
  simp

/--
Express the square-root shift directly in terms of the input position when the affine offset is
even.
-/
theorem shift_amount_of_even_offset
    (leading scale inputShift outputOffset outputBias fractionBits : Nat)
    (hleading : leading ≤ fractionBits)
    (hbalance : inputShift + outputOffset = 2 * outputBias)
    (hoffset : outputOffset % 2 = 0) :
    let position := leading + scale
    let rootExponent :=
      Int.ofNat ((position + outputOffset) / 2) - Int.ofNat outputBias
    (Int.ofNat scale - Int.ofNat inputShift -
        2 * (rootExponent - Int.ofNat fractionBits)).toNat =
      if position % 2 = 0 then
        2 * fractionBits - leading
      else
        2 * fractionBits + 1 - leading := by
  dsimp only
  rw [shift_amount leading scale inputShift outputOffset outputBias
    fractionBits hleading hbalance]
  split <;> omega

/--
Express the square-root shift directly in terms of the input position when the affine offset is
odd.
-/
theorem shift_amount_of_odd_offset
    (leading scale inputShift outputOffset outputBias fractionBits : Nat)
    (hleading : leading ≤ fractionBits)
    (hbalance : inputShift + outputOffset = 2 * outputBias)
    (hoffset : outputOffset % 2 = 1) :
    let position := leading + scale
    let rootExponent :=
      Int.ofNat ((position + outputOffset) / 2) - Int.ofNat outputBias
    (Int.ofNat scale - Int.ofNat inputShift -
        2 * (rootExponent - Int.ofNat fractionBits)).toNat =
      if position % 2 = 0 then
        2 * fractionBits + 1 - leading
      else
        2 * fractionBits - leading := by
  dsimp only
  rw [shift_amount leading scale inputShift outputOffset outputBias
    fractionBits hleading hbalance]
  split <;> omega

end FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic
