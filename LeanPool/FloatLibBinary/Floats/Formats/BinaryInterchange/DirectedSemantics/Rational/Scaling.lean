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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Power
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.RealSemantics

/-!
# Exact real semantics of scaled natural rationals

Scaled natural rationals provide the exact algebraic representation used by directed rational
rounding. A rational is represented by natural numerator and denominator together with an
external binary exponent. The shared exact `Numerics.RationalBinary.scaleByPowerOfTwo` operation
moves that exponent into one side of the quotient; the main theorem proves that this
transformation preserves the exact real value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/-- Exact nonnegative real value represented by a scaled natural rational. -/
noncomputable def scaledRatToReal (numerator denominator : Nat) (exponent : Int) : Real :=
  (numerator : Real) / (denominator : Real) * bpow exponent

/-- Apply a stored sign bit to the exact value of a scaled natural rational. -/
noncomputable def signedScaledRatToReal (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) : Real :=
  if sign then
    -scaledRatToReal numerator denominator exponent
  else
    scaledRatToReal numerator denominator exponent

/--
The signed scaled rational formed from two dyadics is their exact real quotient.

The equality also covers a zero denominator because division in `ℝ` is totalized at zero.
-/
theorem signedScaledRatToReal_eq_div_toReal (dx dy : Numerics.Dyadic) :
    signedScaledRatToReal
        (Bool.xor dx.negative dy.negative) dx.significand dy.significand (dx.exponent -
          dy.exponent) =
      dx.toReal / dy.toReal := by
  cases hxSign : dx.negative <;> cases hySign : dy.negative <;>
    simp [signedScaledRatToReal, scaledRatToReal, Numerics.Dyadic.toReal,
      Numerics.Dyadic.signedSignificand, hxSign, hySign, Bool.xor, bpow,
      Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal,
      zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)] <;>
    ring

/-- Shifting the numerator realizes multiplication by a nonnegative binary power. -/
theorem div_mul_bpow_ofNat (numerator denominator shift : Nat) :
    (numerator : Real) / (denominator : Real) * bpow (Int.ofNat shift) =
      (Nat.shiftLeft numerator shift : Nat) / (denominator : Real) := by
  rw [bpow_ofNat]
  simp only [pow2_eq_two_pow, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_mul_eq_mul_div]
  congr 1
  simp [Nat.shiftLeft_eq]

/-- Shifting the denominator realizes multiplication by a negative binary power. -/
theorem div_mul_bpow_negSucc (numerator denominator shift : Nat) :
    (numerator : Real) / (denominator : Real) * bpow (Int.negSucc shift) =
      (numerator : Real) / (Nat.shiftLeft denominator (shift + 1) : Nat) := by
  rw [bpow_negSucc]
  simp only [pow2_eq_two_pow, Nat.cast_pow, Nat.cast_ofNat]
  calc
    (numerator : Real) / denominator * ((2 : Real) ^ (shift + 1))⁻¹ =
        numerator / (denominator * (2 : Real) ^ (shift + 1)) := by
      field_simp
    _ = numerator / (Nat.shiftLeft denominator (shift + 1) : Nat) := by
      congr 1
      simp [Nat.shiftLeft_eq]

/--
Moving a binary exponent into the numerator or denominator preserves the represented real ratio.
-/
theorem scaleByPowerOfTwo_real (numerator denominator : Nat) (exponent : Int) :
    ((Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator exponent).1 : Real) /
        ((Numerics.RationalBinary.scaleByPowerOfTwo
          numerator denominator exponent).2 : Real) =
      scaledRatToReal numerator denominator exponent := by
  cases exponent with
  | ofNat shift =>
      simpa [scaledRatToReal, Numerics.RationalBinary.scaleByPowerOfTwo] using
        (div_mul_bpow_ofNat numerator denominator shift).symm
  | negSucc shift =>
      simpa [scaledRatToReal, Numerics.RationalBinary.scaleByPowerOfTwo] using
        (div_mul_bpow_negSucc numerator denominator shift).symm

/-- The unsigned scaled rational is nonnegative. -/
theorem scaledRatToReal_nonneg
    (numerator denominator : Nat) (exponent : Int) :
    0 ≤ scaledRatToReal numerator denominator exponent := by
  unfold scaledRatToReal
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg numerator) (Nat.cast_nonneg denominator))
    (le_of_lt (bpow_pos exponent))

/-- The unsigned scaled rational is positive when both natural components are nonzero. -/
theorem scaledRatToReal_pos
    (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    0 < scaledRatToReal numerator denominator exponent := by
  unfold scaledRatToReal
  have hnumeratorPos : (0 : Real) < numerator := by
    exact_mod_cast Nat.pos_of_ne_zero hnumerator
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  exact mul_pos (div_pos hnumeratorPos hdenominatorPos) (bpow_pos exponent)

/-- Combining two external binary scales adds their exponents. -/
theorem scaledRatToReal_mul_bpow
    (numerator denominator : Nat) (left right : Int) :
    scaledRatToReal numerator denominator left * bpow right =
      scaledRatToReal numerator denominator (left + right) := by
  unfold scaledRatToReal
  rw [bpow_add]
  ring

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
