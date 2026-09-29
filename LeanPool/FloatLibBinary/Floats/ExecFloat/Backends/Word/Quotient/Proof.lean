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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Quotient.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.NearestEven

/-!
# Shared bounds for native-word quotient kernels

The one-word and binary64 division backends use different packing code, but they normalize the
same exact rational quotient. This module proves the representation-independent facts once:

* the normalization shift is nonnegative,
* the rounded significand lies in `[2^fracWidth, 2^(fracWidth + 1)]`, and
* the restoring quotient and its carry bit fit in the `UInt64` kernel.

The shift and significand bounds precede the representation-specific estimates. A direct shifted
numerator fits below bit 63 when `2 * (fracWidth + 1) ≤ 63`; the quotient and a possible rounding
increment fit below bit 63 under the weaker condition `fracWidth ≤ 61`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeWordQuotient

open FloatLib.Numerics.FixedWord.RestoringQuotient

/-- The normalizing shift computed by the native kernel is the corresponding integer difference. -/
theorem normalShift_eq
    (fmt : FloatFormat) (num den : UInt64)
    (hnum : num ≠ 0)
    (hnumFit : num.toNat < 2 ^ (fmt.fracWidth + 1)) :
    let rationalExponent := floorLog2RatWord num den
    let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
    Int.ofNat shift =
      Int.ofNat fmt.fracWidth - rationalExponent := by
  have hnumLog :
      num.log2.toNat < fmt.fracWidth + 1 :=
    FloatLib.Numerics.FixedWord.log2_toNat_lt_of_toNat_lt_two_pow
      num (fmt.fracWidth + 1) hnum hnumFit
  have hrange := floorLog2RatWord_log_bounds num den
  simp only [Int.ofNat_eq_natCast] at hrange
  have hnumLogLe :
      (num.log2.toNat : Int) ≤ Int.ofNat fmt.fracWidth := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hnonnegative :
      0 ≤ Int.ofNat fmt.fracWidth -
        floorLog2RatWord num den := by
    have hfloorLe := hrange.2
    omega
  exact Int.toNat_of_nonneg hnonnegative

/--
The normalized numerator and its shift fit the signed-width budget used by the `UInt64` quotient
kernel.

The condition `2 * (fracWidth + 1) ≤ 63` is the representation boundary for this direct shifted
numerator path. It is satisfied by binary32 and other narrow formats; wider one-word formats use
the restoring loop without first materializing the whole shifted numerator.
-/
theorem normalShift_bounds
    (fmt : FloatFormat) (num den : UInt64)
    (hnum : num ≠ 0) (hden : den ≠ 0)
    (hnumFit : num.toNat < 2 ^ (fmt.fracWidth + 1))
    (hdenFit : den.toNat < 2 ^ (fmt.fracWidth + 1))
    (hbudget : 2 * (fmt.fracWidth + 1) ≤ 63) :
    let rationalExponent := floorLog2RatWord num den
    let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
    shift < 64 ∧ num.toNat <<< shift < 2 ^ 63 := by
  let rationalExponent := floorLog2RatWord num den
  let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
  have hnumLog :
      num.log2.toNat < fmt.fracWidth + 1 :=
    FloatLib.Numerics.FixedWord.log2_toNat_lt_of_toNat_lt_two_pow
      num (fmt.fracWidth + 1) hnum hnumFit
  have hdenLog :
      den.log2.toNat < fmt.fracWidth + 1 :=
    FloatLib.Numerics.FixedWord.log2_toNat_lt_of_toNat_lt_two_pow
      den (fmt.fracWidth + 1) hden hdenFit
  have hrange := floorLog2RatWord_log_bounds num den
  simp only [Int.ofNat_eq_natCast] at hrange
  have hshiftInt :
      Int.ofNat shift =
        Int.ofNat fmt.fracWidth - rationalExponent :=
    normalShift_eq fmt num den hnum hnumFit
  simp only [Int.ofNat_eq_natCast] at hshiftInt
  have hshiftLt : shift < 64 := by
    dsimp only [rationalExponent] at hshiftInt
    omega
  have hexponent :
      num.log2.toNat + 1 + shift ≤ 63 := by
    dsimp only [rationalExponent] at hshiftInt
    omega
  have hbound :
      num.toNat <<< shift <
        2 ^ (num.toNat.log2 + 1 + shift) :=
    Nat.shiftLeft_lt Nat.lt_log2_self
  rw [← FloatLib.Numerics.FixedWord.log2_toNat] at hbound
  exact ⟨hshiftLt, lt_of_lt_of_le hbound <|
    Nat.pow_le_pow_right (by decide) hexponent⟩

/-- Normalized nearest-even quotient rounding stays within the expected significand interval. -/
theorem roundedMantissa_bounds
    (fmt : FloatFormat) (num den : UInt64)
    (hnum : num ≠ 0) (hden : den ≠ 0)
    (hnumFit : num.toNat < 2 ^ (fmt.fracWidth + 1)) :
    let rationalExponent := floorLog2RatWord num den
    let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
    2 ^ fmt.fracWidth ≤
        Numerics.roundQuotientEven
          (num.toNat <<< shift) den.toNat ∧
      Numerics.roundQuotientEven
          (num.toNat <<< shift) den.toNat ≤
        2 ^ (fmt.fracWidth + 1) := by
  let rationalExponent := floorLog2RatWord num den
  let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
  have hnumNat : num.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hnum
  have hdenNat : den.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hden
  have hfloor := floorLog2RatWord_eq num den hnum hden
  have hshift := normalShift_eq fmt num den hnum hnumFit
  have hscaled :
      Numerics.RationalBinary.scaleByPowerOfTwo num.toNat den.toNat
          (Int.ofNat fmt.fracWidth -
            Numerics.RationalBinary.floorLog2 num.toNat den.toNat) =
        (num.toNat <<< shift, den.toNat) := by
    rw [← hfloor, ← hshift]
    rfl
  have hrounded :=
    Model.roundQuotientEven_normal_bounds
      fmt num.toNat den.toNat hnumNat hdenNat
  dsimp only at hrounded
  rw [hscaled] at hrounded
  simpa only [Model.pow2_eq_two_pow] using hrounded

/--
The restoring quotient and a possible rounding increment fit below bit 63.

The bound `fracWidth ≤ 61` leaves room for a significand carry and a possible rounding increment
without using bit 63.
-/
theorem quotient_lt_two_pow_63
    (fmt : FloatFormat) (num den : UInt64)
    (hnum : num ≠ 0) (hden : den ≠ 0)
    (hnumFit : num.toNat < 2 ^ (fmt.fracWidth + 1))
    (hfracWidth : fmt.fracWidth ≤ 61) :
    let rationalExponent := floorLog2RatWord num den
    let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
    (num.toNat <<< shift) / den.toNat + 1 < 2 ^ 63 := by
  let rationalExponent := floorLog2RatWord num den
  let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
  have hdenNat : den.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hden
  have hroundedUpper :
      Numerics.roundQuotientEven
          (num.toNat <<< shift) den.toNat ≤
        2 ^ (fmt.fracWidth + 1) :=
    (roundedMantissa_bounds fmt num den hnum hden hnumFit).2
  have hfloorLe :
      (num.toNat <<< shift) / den.toNat ≤
        Numerics.roundQuotientEven
          (num.toNat <<< shift) den.toNat := by
    have hsandwich :=
      Model.roundQuotDirected_false_le_roundQuotientEven_le_true
        (num.toNat <<< shift) den.toNat hdenNat
    simpa [Model.roundQuotDirected] using hsandwich.1
  change
    (num.toNat <<< shift) / den.toNat + 1 < 2 ^ 63
  have hpow : 2 ^ (fmt.fracWidth + 1) < 2 ^ 63 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  omega

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeWordQuotient
