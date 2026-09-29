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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Basic
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Proof
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Quotient

/-!
# Positive directed rounding for arbitrary executable float formats

The shift-based directed rounders used by `Model` are related to the independent Flocq-style
real semantics at the scaled-mantissa boundary, before subnormal and normal values are packed
into interchange fields.

All definitions are uniform in `FloatFormat`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/-! ## Independent directed semantics -/

/-- Round a real downward on the gradual-underflow grid of `fmt`, before overflow handling. -/
noncomputable abbrev roundAtDown (fmt : FloatFormat) (x : ℝ) : ℝ :=
  round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) floorRound x

/-- Round a real upward on the gradual-underflow grid of `fmt`, before overflow handling. -/
noncomputable abbrev roundAtUp (fmt : FloatFormat) (x : ℝ) : ℝ :=
  round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) ceilRound x

/-- Downward rounding fixes zero. -/
theorem roundAtDown_zero (fmt : FloatFormat) :
    roundAtDown fmt 0 = 0 := by
  exact round_preserves_generic floorRound 0 generic_format_zero

/-- Upward rounding fixes zero. -/
theorem roundAtUp_zero (fmt : FloatFormat) :
    roundAtUp fmt 0 = 0 := by
  exact round_preserves_generic ceilRound 0 generic_format_zero

/-! ## Executable scaled-mantissa rounding -/

/-- Floor a natural mantissa after expressing it at `targetExponent`. -/
def roundMantissaAtExponentDown
    (mantissa : Nat) (exponent targetExponent : Int) : Nat :=
  if exponent ≤ targetExponent then
    Nat.shiftRight mantissa (targetExponent - exponent).toNat
  else
    Nat.shiftLeft mantissa (exponent - targetExponent).toNat

/-- Ceil a natural mantissa after expressing it at `targetExponent`. -/
def roundMantissaAtExponentUp
    (mantissa : Nat) (exponent targetExponent : Int) : Nat :=
  if exponent ≤ targetExponent then
    shiftRightCeilPow2 mantissa (targetExponent - exponent).toNat
  else
    Nat.shiftLeft mantissa (exponent - targetExponent).toNat

/-- Ceiling alignment preserves nonzeroness of a positive mantissa. -/
theorem roundMantissaAtExponentUp_ne_zero
    (mantissa : Nat) (exponent targetExponent : Int) (hm : mantissa ≠ 0) :
    roundMantissaAtExponentUp mantissa exponent targetExponent ≠ 0 := by
  by_cases hle : exponent ≤ targetExponent
  · let shift := (targetExponent - exponent).toNat
    have hcover := le_shiftRightCeilPow2_mul_pow2 mantissa shift
    simp only [roundMantissaAtExponentUp, hle, ite_true]
    intro hzero
    rw [hzero] at hcover
    simp only [zero_mul, nonpos_iff_eq_zero] at hcover
    exact hm hcover
  · simp [roundMantissaAtExponentUp, hle, Nat.shiftLeft_eq, hm]

/-- Floor alignment never exceeds ceiling alignment at the same exponent. -/
theorem roundMantissaAtExponentDown_le_up
    (mantissa : Nat) (exponent targetExponent : Int) :
    roundMantissaAtExponentDown mantissa exponent targetExponent ≤
      roundMantissaAtExponentUp mantissa exponent targetExponent := by
  by_cases hle : exponent ≤ targetExponent
  · simp only [roundMantissaAtExponentDown, roundMantissaAtExponentUp, hle, ite_true]
    exact shiftRight_le_shiftRightCeilPow2 _ _
  · simp [roundMantissaAtExponentDown, roundMantissaAtExponentUp, hle]

/-- Ceiling alignment is at most one unit above floor alignment. -/
theorem roundMantissaAtExponentUp_le_down_add_one
    (mantissa : Nat) (exponent targetExponent : Int) :
    roundMantissaAtExponentUp mantissa exponent targetExponent ≤
      roundMantissaAtExponentDown mantissa exponent targetExponent + 1 := by
  by_cases hle : exponent ≤ targetExponent
  · simp only [roundMantissaAtExponentDown, roundMantissaAtExponentUp, hle, ite_true]
    exact shiftRightCeilPow2_le_shiftRight_add_one _ _
  · simp [roundMantissaAtExponentDown, roundMantissaAtExponentUp, hle]

private theorem shiftRightCeilPow2_eq_div_add_one
    (numerator shift : Nat) :
    shiftRightCeilPow2 numerator shift =
      if numerator % pow2 shift = 0 then
        numerator / pow2 shift
      else
        numerator / pow2 shift + 1 := by
  cases shift with
  | zero =>
      simp [shiftRightCeilPow2, pow2_eq_two_pow, Nat.mod_one]
  | succ shift =>
      let distance := Nat.succ shift
      let denominator := pow2 distance
      let quotient := numerator / denominator
      let remainder := numerator % denominator
      have hshift :
          Nat.shiftRight numerator distance = quotient := by
        simp [quotient, denominator, Nat.shiftRight_eq_div_pow, pow2_eq_two_pow]
      have hleft :
          Nat.shiftLeft quotient distance = quotient * denominator := by
        simp [Nat.shiftLeft_eq, denominator, pow2_eq_two_pow]
      have hn :
          numerator = quotient * denominator + remainder := by
        simpa [quotient, remainder, Nat.mul_comm, Nat.mul_left_comm,
          Nat.mul_assoc] using (Nat.div_add_mod numerator denominator).symm
      have hsub :
          numerator - Nat.shiftLeft quotient distance = remainder := by
        rw [hleft, hn]
        simp
      have hshift' : numerator >>> (shift + 1) = quotient := by
        simpa [distance, Nat.succ_eq_add_one] using hshift
      have hsub' : numerator - quotient <<< (shift + 1) = remainder := by
        simpa [distance, Nat.succ_eq_add_one] using hsub
      have hmod : numerator % pow2 (shift + 1) = remainder := by
        simp [remainder, denominator, distance, Nat.succ_eq_add_one]
      have hdiv : numerator / pow2 (shift + 1) = quotient := by
        simp [quotient, denominator, distance, Nat.succ_eq_add_one]
      by_cases hzero : remainder = 0
      · have hceil : shiftRightCeilPow2 numerator (shift + 1) = quotient := by
          simp (config := { zeta := true }) only [shiftRightCeilPow2, Nat.reduceBeqDiff,
            Bool.false_eq_true, ↓reduceIte,
            Nat.shiftRight_eq', Nat.shiftLeft_eq', beq_iff_eq]
          rw [hshift', hsub']
          simp [hzero]
        rw [hceil, hmod, hdiv, hzero]
        simp
      · have hceil : shiftRightCeilPow2 numerator (shift + 1) = quotient + 1 := by
          simp (config := { zeta := true }) only [shiftRightCeilPow2, Nat.reduceBeqDiff,
            Bool.false_eq_true, ↓reduceIte,
            Nat.shiftRight_eq', Nat.shiftLeft_eq', beq_iff_eq]
          rw [hshift', hsub']
          simp [hzero]
        rw [hceil, hmod, hdiv]
        simp [hzero]

/-- Downward shifting computes the integer floor of a scaled positive dyadic. -/
theorem floor_scaledMagnitude
    (mantissa : Nat) (exponent targetExponent : Int) :
    floorRound
        ((mantissa : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (exponent - targetExponent)) =
      Int.ofNat
        (roundMantissaAtExponentDown mantissa exponent targetExponent) := by
  by_cases hle : exponent ≤ targetExponent
  · let shift := (targetExponent - exponent).toNat
    have hshiftInt : (shift : Int) = targetExponent - exponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hle)
    have hvalue :
        (mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent) =
          (mantissa : ℝ) / (pow2 shift : ℝ) := by
      rw [show exponent - targetExponent = -(shift : Int) by omega]
      simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal,
        pow2_eq_two_pow, div_eq_mul_inv]
    rw [hvalue]
    simpa [floorRound, roundMantissaAtExponentDown, hle, shift,
      Nat.shiftRight_eq_div_pow, pow2_eq_two_pow] using
      floor_real_nat_div mantissa (pow2 shift)
  · let shift := (exponent - targetExponent).toNat
    have hshiftInt : (shift : Int) = exponent - targetExponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))
    have hvalue :
        (mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent) =
          (Nat.shiftLeft mantissa shift : Nat) := by
      rw [← hshiftInt]
      simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal,
        Nat.shiftLeft_eq]
    rw [hvalue]
    simp [floorRound, roundMantissaAtExponentDown, hle, shift]

/-- Upward shifting computes the integer ceiling of a scaled positive dyadic. -/
theorem ceil_scaledMagnitude
    (mantissa : Nat) (exponent targetExponent : Int) :
    ceilRound
        ((mantissa : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (exponent - targetExponent)) =
      Int.ofNat
        (roundMantissaAtExponentUp mantissa exponent targetExponent) := by
  by_cases hle : exponent ≤ targetExponent
  · let shift := (targetExponent - exponent).toNat
    have hshiftInt : (shift : Int) = targetExponent - exponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hle)
    have hvalue :
        (mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent) =
          (mantissa : ℝ) / (pow2 shift : ℝ) := by
      rw [show exponent - targetExponent = -(shift : Int) by omega]
      simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal,
        pow2_eq_two_pow, div_eq_mul_inv]
    rw [hvalue]
    simp only [roundMantissaAtExponentUp, ite_eq_left hle]
    rw [shiftRightCeilPow2_eq_div_add_one]
    have hpow2 : pow2 shift ≠ 0 := Nat.ne_of_gt (pow2_pos shift)
    simpa [ceilRound, shift, quotCeil, hpow2] using
      ceil_real_nat_div_eq_quotCeil mantissa (pow2 shift) hpow2
  · let shift := (exponent - targetExponent).toNat
    have hshiftInt : (shift : Int) = exponent - targetExponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))
    have hvalue :
        (mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent) =
          (Nat.shiftLeft mantissa shift : Nat) := by
      rw [← hshiftInt]
      simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal,
        Nat.shiftLeft_eq]
    rw [hvalue]
    simp [ceilRound, roundMantissaAtExponentUp, hle, shift]

/-- Floor alignment at any target exponent is a lower bound for the exact dyadic magnitude. -/
theorem roundMantissaAtExponentDown_mul_bpow_le
    (mantissa : Nat) (exponent targetExponent : Int) :
    (roundMantissaAtExponentDown mantissa exponent targetExponent : ℝ) *
        bpow targetExponent ≤
      (mantissa : ℝ) * bpow exponent := by
  have hfloor :
      ((floorRound ((mantissa : ℝ) * bpow (exponent - targetExponent)) : Int) : ℝ) ≤
        (mantissa : ℝ) * bpow (exponent - targetExponent) :=
    Int.floor_le _
  rw [floor_scaledMagnitude] at hfloor
  change (roundMantissaAtExponentDown mantissa exponent targetExponent : ℝ) ≤
    (mantissa : ℝ) * bpow (exponent - targetExponent) at hfloor
  have hscale := mul_le_mul_of_nonneg_right hfloor (bpow_nonneg targetExponent)
  simpa only [mul_assoc, ← bpow_add, sub_add_cancel] using hscale

/-- Ceiling alignment at any target exponent is an upper bound for the exact dyadic magnitude. -/
theorem le_roundMantissaAtExponentUp_mul_bpow
    (mantissa : Nat) (exponent targetExponent : Int) :
    (mantissa : ℝ) * bpow exponent ≤
      (roundMantissaAtExponentUp mantissa exponent targetExponent : ℝ) *
        bpow targetExponent := by
  have hceil :
      (mantissa : ℝ) * bpow (exponent - targetExponent) ≤
        ((ceilRound ((mantissa : ℝ) * bpow (exponent - targetExponent)) : Int) : ℝ) :=
    Int.le_ceil _
  rw [ceil_scaledMagnitude] at hceil
  change (mantissa : ℝ) * bpow (exponent - targetExponent) ≤
    (roundMantissaAtExponentUp mantissa exponent targetExponent : ℝ) at hceil
  have hscale := mul_le_mul_of_nonneg_right hceil (bpow_nonneg targetExponent)
  simpa only [mul_assoc, ← bpow_add, sub_add_cancel] using hscale

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
