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

public import Mathlib.Data.Nat.Log
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Fields.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Packing.Bounds
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Power
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Directed.Dyadic

/-!
# Basic lemmas for format-parameterized directed rounding

Shared arithmetic facts support both directed dyadic and rational rounding proofs. Further
lemmas give closed forms for the smallest positive subnormal and a strict power-of-two bound for
the largest finite value. All statements are uniform in `FloatFormat`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats

section

/-- Increasing a natural exponent by one does not decrease its power of two. -/
theorem pow2_le_pow2_succ (exponent : Nat) :
    pow2 exponent ≤ pow2 (exponent + 1) := by
  simp [pow2, Nat.shiftLeft_succ]

/-- Natural powers of two are positive. -/
theorem pow2_pos (exponent : Nat) : 0 < pow2 exponent := by
  simp [pow2_eq_two_pow]

/-- Natural powers of two grow strictly with the exponent. -/
theorem pow2_lt_pow2_succ (exponent : Nat) :
    pow2 exponent < pow2 (exponent + 1) := by
  simpa only [pow2_eq_two_pow] using
    Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) (Nat.lt_succ_self exponent)

/-- Split a natural power of two across an exponent sum. -/
theorem pow2_add (left right : Nat) :
    pow2 (left + right) = pow2 left * pow2 right := by
  simp [pow2_eq_two_pow, Nat.pow_add]

/-- Multiplicative form of `pow2_add`. -/
theorem pow2_mul (left right : Nat) :
    pow2 left * pow2 right = pow2 (left + right) :=
  (pow2_add left right).symm

/-! ## Floor and ceiling shifts -/

/-- Shifting right and restoring the removed power of two cannot exceed the original number. -/
theorem shiftRight_mul_pow2_le (n shift : Nat) :
    Nat.shiftRight n shift * pow2 shift ≤ n := by
  have h := Nat.div_mul_le_self n (2 ^ shift)
  simpa [Nat.shiftRight_eq_div_pow, pow2_eq_two_pow, Nat.mul_comm] using h

/-- A ceiling right shift, followed by restoration of its scale, covers the original number. -/
theorem le_shiftRightCeilPow2_mul_pow2 (n shift : Nat) :
    n ≤ shiftRightCeilPow2 n shift * pow2 shift := by
  classical
  cases shift with
  | zero =>
      simp [shiftRightCeilPow2, pow2_eq_two_pow]
  | succ shift =>
      set divisor : Nat := pow2 (Nat.succ shift)
      have hdivisor : 0 < divisor := pow2_pos (Nat.succ shift)
      set quotient : Nat := n / divisor
      set remainder : Nat := n % divisor
      have hn : n = quotient * divisor + remainder := by
        simpa [quotient, remainder, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.div_add_mod n divisor).symm
      have hremainder : remainder < divisor := Nat.mod_lt n hdivisor
      have hshift : Nat.shiftRight n (Nat.succ shift) = quotient := by
        simp [quotient, divisor, Nat.shiftRight_eq_div_pow, pow2_eq_two_pow]
      have hrem : n - Nat.shiftLeft quotient (Nat.succ shift) = remainder := by
        have hleft : Nat.shiftLeft quotient (Nat.succ shift) = quotient * divisor := by
          simp [Nat.shiftLeft_eq, divisor, pow2_eq_two_pow]
        rw [hleft, hn]
        simp
      have hshift' : n >>> (shift + 1) = quotient := by
        simpa [Nat.succ_eq_add_one] using hshift
      have hrem' : n - quotient <<< (shift + 1) = remainder := by
        simpa [Nat.succ_eq_add_one] using hrem
      by_cases hzero : remainder = 0
      · have hn' : n = quotient * divisor := by
          simp [hn, hzero]
        have hceil : shiftRightCeilPow2 n (Nat.succ shift) = quotient := by
          have hshiftNonzero : (Nat.succ shift == 0) = false := by
            simp
          simp (config := { zeta := true }) only [shiftRightCeilPow2, Nat.succ_eq_add_one,
            hshiftNonzero,
            Bool.false_eq_true, ↓reduceIte, Nat.shiftRight_eq', Nat.shiftLeft_eq', beq_iff_eq]
          rw [hshift', hrem']
          simp [hzero]
        have hceil' :
            shiftRightCeilPow2 (quotient * divisor) (Nat.succ shift) = quotient := by
          simpa [hn'] using hceil
        simp [hn', hceil', divisor]
      · have hnle : n ≤ (quotient + 1) * divisor := by
          have hsum :
              quotient * divisor + remainder ≤ quotient * divisor + divisor :=
            Nat.add_le_add_left (Nat.le_of_lt hremainder) (quotient * divisor)
          have hmul : (quotient + 1) * divisor = quotient * divisor + divisor := by
            simp [Nat.add_mul]
          have : n ≤ quotient * divisor + divisor := by
            simpa [hn] using hsum
          simpa [hmul] using this
        have hceil : shiftRightCeilPow2 n (Nat.succ shift) = quotient + 1 := by
          have hshiftNonzero : (Nat.succ shift == 0) = false := by
            simp
          simp (config := { zeta := true }) only [shiftRightCeilPow2, Nat.succ_eq_add_one,
            hshiftNonzero,
            Bool.false_eq_true, ↓reduceIte, Nat.shiftRight_eq', Nat.shiftLeft_eq', beq_iff_eq]
          rw [hshift', hrem']
          simp [hzero]
        simp [hceil, hnle, divisor]

/-- A ceiling shift is at most one larger than the corresponding floor shift. -/
theorem shiftRightCeilPow2_le_shiftRight_add_one (n shift : Nat) :
    shiftRightCeilPow2 n shift ≤ Nat.shiftRight n shift + 1 := by
  cases shift with
  | zero =>
      simp [shiftRightCeilPow2]
  | succ shift =>
      simp (config := { zeta := true }) [shiftRightCeilPow2]
      split <;> omega

/-- A floor right shift never exceeds the corresponding ceiling right shift. -/
theorem shiftRight_le_shiftRightCeilPow2 (n shift : Nat) :
    Nat.shiftRight n shift ≤ shiftRightCeilPow2 n shift := by
  cases shift with
  | zero =>
      simp [shiftRightCeilPow2]
  | succ shift =>
      simp (config := { zeta := true }) [shiftRightCeilPow2]
      split <;> omega

/-- The leading power of two does not exceed a nonzero natural number. -/
theorem pow2_log2_le {n : Nat} (hn : n ≠ 0) :
    pow2 (Nat.log2 n) ≤ n := by
  have h : 2 ^ Nat.log2 n ≤ n := (Nat.le_log2 hn).1 le_rfl
  simpa [pow2_eq_two_pow] using h

/-- A nonzero natural number is below the next power after its leading bit. -/
theorem lt_pow2_log2_add_one {n : Nat} (hn : n ≠ 0) :
    n < pow2 (Nat.log2 n + 1) := by
  have hlog : n.log2 < n.log2 + 1 := Nat.lt_succ_self _
  have h : n < 2 ^ (n.log2 + 1) := (Nat.log2_lt hn).1 hlog
  simpa [pow2_eq_two_pow] using h

/-! ## Format constants -/

/-- The subnormal grid starts strictly below the smallest normal exponent. -/
theorem minSubnormalExponent_lt_minNormalExponent (fmt : FloatFormat) :
    fmt.minSubnormalExponent < fmt.minNormalExponent := by
  unfold FloatFormat.minSubnormalExponent
  have hfrac : (0 : Int) < Int.ofNat fmt.fracWidth :=
    Int.natCast_pos.mpr fmt.fracWidth_pos
  omega

/-- The subnormal exponent plus the explicit fraction width is the minimum normal exponent. -/
theorem minSubnormalExponent_add_fracWidth (fmt : FloatFormat) :
    fmt.minSubnormalExponent + Int.ofNat fmt.fracWidth =
      fmt.minNormalExponent := by
  unfold FloatFormat.minSubnormalExponent
  omega

/-- The smallest positive subnormal is explicit field packing with fraction one. -/
theorem posMinSubnormal_eq_ofFields (fmt : FloatFormat) :
    posMinSubnormal fmt = ofFields fmt false 0 1 := by
  apply congrArg ofBits
  apply BitVec.eq_of_toNat_eq
  simp only [FloatFormat.ofWordNat, BitVec.toNat_ofNat, mkBits, Bool.false_eq_true, ↓reduceIte,
    BitVec.ofNat_eq_ofNat, BitVec.zero_and, BitVec.zero_shiftLeft, BitVec.or_self,
      FloatFormat.fracMask,
    FloatFormat.fracMaskNat, BitVec.zero_or, BitVec.toNat_and]
  have hbitWidthPos : 0 < fmt.bitWidth := by
    unfold FloatFormat.bitWidth
    omega
  have hfracWidthLe : fmt.fracWidth ≤ fmt.bitWidth := by
    unfold FloatFormat.bitWidth
    omega
  have honeBitWidth : 1 < 2 ^ fmt.bitWidth :=
    Nat.one_lt_two_pow (Nat.ne_of_gt hbitWidthPos)
  have hpowLe : 2 ^ fmt.fracWidth ≤ 2 ^ fmt.bitWidth :=
    Nat.pow_le_pow_right (by decide) hfracWidthLe
  have hmaskLt : 2 ^ fmt.fracWidth - 1 < 2 ^ fmt.bitWidth := by
    have hfracPowPos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos fmt.fracWidth
    omega
  rw [Nat.mod_eq_of_lt honeBitWidth, Nat.mod_eq_of_lt hmaskLt]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt fmt.fracWidth_pos))]

/-- The smallest positive subnormal denotes one unit at the minimum subnormal exponent. -/
@[simp] theorem toReal_posMinSubnormal (fmt : FloatFormat) :
    toReal (posMinSubnormal fmt) = bpow fmt.minSubnormalExponent := by
  rw [posMinSubnormal_eq_ofFields]
  have hfit : 1 < 2 ^ fmt.fracWidth :=
    Nat.one_lt_two_pow (Nat.ne_of_gt fmt.fracWidth_pos)
  simpa [bpow] using
    toReal_ofFields_subnormal fmt false 1 (by decide) hfit

/-- Closed form for the largest finite positive value of an arbitrary format. -/
theorem toReal_posMaxFinite (fmt : FloatFormat) :
    toReal (posMaxFinite fmt) =
      ((pow2 fmt.fracWidth + fmt.maxFiniteFracField : Nat) : ℝ) *
        bpow (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) := by
  rw [show posMaxFinite fmt =
      ofFields fmt false fmt.maxFiniteExpField fmt.maxFiniteFracField by rfl]
  rw [toReal_ofFields_normal_of_isFinite fmt false fmt.maxFiniteExpField
    fmt.maxFiniteFracField (Nat.ne_of_gt fmt.maxFiniteExpField_pos)
    fmt.maxFiniteExpField_lt_two_pow fmt.maxFiniteFracField_lt_two_pow
    (by simpa [posMaxFinite, maxFinite] using isFinite_posMaxFinite fmt)]
  simp only [Bool.false_eq_true, ite_false, one_mul]
  congr 1

/--
A signed magnitude whose mantissa and exponent do not exceed those of the largest finite value is
bounded by that value.
-/
theorem abs_signed_mul_bpow_le_toReal_posMaxFinite
    (fmt : FloatFormat) (sign : Bool) (mantissa : Nat) (exponent : Int)
    (hmantissa : mantissa ≤ pow2 fmt.fracWidth + fmt.maxFiniteFracField)
    (hexponent : exponent ≤ fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) :
    |(if sign then (-1 : ℝ) else 1) * (mantissa : ℝ) * bpow exponent| ≤
      toReal (posMaxFinite fmt) := by
  have hsign : |(if sign then (-1 : ℝ) else 1)| = 1 := by
    cases sign <;> norm_num
  rw [toReal_posMaxFinite, abs_mul, abs_mul, hsign, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (bpow_nonneg _)]
  exact mul_le_mul (by exact_mod_cast hmantissa) (bpow_le_bpow_of_le hexponent)
    (bpow_nonneg _) (Nat.cast_nonneg _)

/--
Every finite IEEE value lies between the two largest-finite endpoints.

The finiteness hypothesis excludes infinities and NaNs; the bound follows from the descriptor's
exponent and fraction fields.
-/
theorem abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite
    {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true) (hfinite : isFinite x = true) :
    |toReal x| ≤ toReal (posMaxFinite fmt) := by
  have hencoding : fmt.encoding = .ieee :=
    FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt
  have hexponentNe : expField x ≠ fmt.expAllOnesNat := by
    have hfiniteIEEE : IEEE.isFinite x = true := by
      simpa [isFinite, hencoding] using hfinite
    exact (bne_iff_ne).mp hfiniteIEEE
  have hexponentLt := expField_lt_pow2 x
  have hfractionLt := fracField_lt_pow2 x
  have hexponentLe : expField x ≤ fmt.maxFiniteExpField := by
    simp only [FloatFormat.maxFiniteExpField,
      FloatFormat.Encoding.maxFiniteExponent, hencoding]
    unfold FloatFormat.expAllOnesNat at hexponentNe
    omega
  have hfractionLe : fracField x ≤ fmt.maxFiniteFracField := by
    simp only [FloatFormat.maxFiniteFracField, hencoding,
      FloatFormat.fracMaskNat]
    omega
  have hfieldsFinite :
      isFinite
          (ofFields fmt (signBit x) (expField x) (fracField x)) =
        true := by
    simpa only [ofFields_signBit_expField_fracField] using hfinite
  rw [← ofFields_signBit_expField_fracField x]
  by_cases hexponentZero : expField x = 0
  · by_cases hfractionZero : fracField x = 0
    · have hmaximumNonneg : 0 ≤ toReal (posMaxFinite fmt) := by
        rw [toReal_posMaxFinite]
        exact mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _)
      cases hsign : signBit x <;>
        simp [hexponentZero, hfractionZero, toReal_posZero fmt hfmt,
          toReal_negZero fmt hfmt, hmaximumNonneg]
    · rw [hexponentZero,
        toReal_ofFields_subnormal fmt (signBit x) (fracField x)
          hfractionZero hfractionLt]
      apply abs_signed_mul_bpow_le_toReal_posMaxFinite
      · omega
      · have := fmt.maxFiniteExpField_pos
        unfold FloatFormat.minSubnormalExponent FloatFormat.minNormalExponent
          FloatFormat.maxNormalExponent
        simp only [Int.ofNat_eq_natCast]
        omega
  · rw [toReal_ofFields_normal_of_isFinite fmt (signBit x)
        (expField x) (fracField x) hexponentZero hexponentLt hfractionLt hfieldsFinite]
    apply abs_signed_mul_bpow_le_toReal_posMaxFinite
    · omega
    · unfold FloatFormat.maxNormalExponent
      simp only [Int.ofNat_eq_natCast]
      omega

/-- The largest finite value is strictly below the next normal power of two. -/
theorem toReal_posMaxFinite_lt_bpow (fmt : FloatFormat) :
    toReal (posMaxFinite fmt) <
      bpow (fmt.maxNormalExponent + 1) := by
  rw [toReal_posMaxFinite]
  have hmantissa :
      ((pow2 fmt.fracWidth + fmt.maxFiniteFracField : Nat) : ℝ) <
        (pow2 (fmt.fracWidth + 1) : ℝ) := by
    exact_mod_cast show
      pow2 fmt.fracWidth + fmt.maxFiniteFracField <
        pow2 (fmt.fracWidth + 1) by
      have hfraction := fmt.maxFiniteFracField_lt_two_pow
      simp only [pow2_eq_two_pow, pow_succ]
      omega
  have hscale :
      0 < bpow (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) :=
    bpow_pos _
  refine (mul_lt_mul_of_pos_right hmantissa hscale).trans_eq ?_
  calc
    (pow2 (fmt.fracWidth + 1) : ℝ) *
          bpow (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) =
        bpow (Int.ofNat (fmt.fracWidth + 1)) *
          bpow (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) := by
      rw [bpow_ofNat]
    _ = bpow
          (Int.ofNat (fmt.fracWidth + 1) +
            (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth)) := by
      rw [← bpow_add]
    _ = bpow (fmt.maxNormalExponent + 1) := by
      congr 1
      have hfrac :
          Int.ofNat (fmt.fracWidth + 1) =
            Int.ofNat fmt.fracWidth + 1 := by
        simp
      rw [hfrac]
      ring

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
