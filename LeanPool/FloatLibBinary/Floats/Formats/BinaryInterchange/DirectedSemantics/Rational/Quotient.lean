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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Scaling
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.NearestEven

/-!
# Directed integer rounding of nonnegative rational quotients

The quotient operations used by directed rational rounding satisfy format-independent order
bounds. Floor rounding lies below the exact real quotient, ceiling rounding lies above it, and
integer lower and upper thresholds are preserved in the expected directions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats.Formats.Flocq

section

/-! ## Natural quotient bounds -/

/-- The floor quotient is no larger than the ceiling quotient. -/
theorem div_le_quotCeil (numerator denominator : Nat) :
    numerator / denominator ≤ quotCeil numerator denominator := by
  by_cases hdenominator : denominator = 0
  · simp [hdenominator, quotCeil]
  · by_cases hremainder : numerator % denominator = 0
    · simp [quotCeil, hdenominator, hremainder]
    · simp [quotCeil, hdenominator, hremainder]

/-- The ceiling quotient is at most one larger than the floor quotient. -/
theorem quotCeil_le_div_add_one (numerator denominator : Nat) :
    quotCeil numerator denominator ≤ numerator / denominator + 1 := by
  by_cases hdenominator : denominator = 0
  · simp [hdenominator, quotCeil]
  · by_cases hremainder : numerator % denominator = 0
    · simp [quotCeil, hdenominator, hremainder]
    · simp [quotCeil, hdenominator, hremainder]

/-- Multiplying the floor quotient back by its denominator does not exceed the numerator. -/
theorem div_mul_le_numerator (numerator denominator : Nat) :
    numerator / denominator * denominator ≤ numerator :=
  Nat.div_mul_le_self numerator denominator

/-- Multiplying the ceiling quotient back by a nonzero denominator covers the numerator. -/
theorem numerator_le_quotCeil_mul
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    numerator ≤ quotCeil numerator denominator * denominator := by
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  have hnumerator : numerator = quotient * denominator + remainder := by
    simpa [quotient, remainder, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.div_add_mod numerator denominator).symm
  have hremainderLt : remainder < denominator :=
    Nat.mod_lt numerator (Nat.pos_of_ne_zero hdenominator)
  by_cases hremainderZero : remainder = 0
  · have hceil : quotCeil numerator denominator = quotient := by
      simp [quotCeil, hdenominator, quotient, remainder, hremainderZero]
    calc
      numerator = quotient * denominator := by
        simpa [hremainderZero] using hnumerator
      _ ≤ quotCeil numerator denominator * denominator := by simp [hceil]
  · have hceil : quotCeil numerator denominator = quotient + 1 := by
      simp [quotCeil, hdenominator, quotient, remainder, hremainderZero]
    calc
      numerator = quotient * denominator + remainder := hnumerator
      _ ≤ quotient * denominator + denominator :=
        Nat.add_le_add_left hremainderLt.le _
      _ ≤ quotCeil numerator denominator * denominator := by
        simp [hceil, Nat.add_mul]

/-! ## Exact real enclosure -/

/-- The executable natural ceiling is the exact integer ceiling of the represented real quotient. -/
theorem ceil_real_nat_div_eq_quotCeil
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    (⌈(numerator : Real) / (denominator : Real)⌉ : Int) =
      Int.ofNat (quotCeil numerator denominator) := by
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  have hdivision :
      denominator * quotient + remainder = numerator := by
    simpa [quotient, remainder] using Nat.div_add_mod numerator denominator
  have hdivisionReal :
      ((denominator * quotient : Nat) : Real) + (remainder : Real) =
        (numerator : Real) := by
    exact_mod_cast hdivision
  have hdenominatorReal : (denominator : Real) ≠ 0 := by
    exact_mod_cast hdenominator
  have hsplit :
      (numerator : Real) / (denominator : Real) =
        (quotient : Real) + (remainder : Real) / (denominator : Real) := by
    have h :=
      congrArg (fun value : Real => value / (denominator : Real)) hdivisionReal
    simp [add_div, hdenominatorReal] at h
    simpa [Nat.cast_div] using h.symm
  by_cases hremainder : remainder = 0
  · rw [hsplit, hremainder]
    simp [quotCeil, hdenominator, quotient, remainder, hremainder]
  · have hdenominatorPos : (0 : Real) < denominator := by
      exact_mod_cast Nat.pos_of_ne_zero hdenominator
    have hremainderPos : (0 : Real) < remainder := by
      exact_mod_cast Nat.pos_of_ne_zero hremainder
    have hremainderLt : (remainder : Real) < denominator := by
      exact_mod_cast Nat.mod_lt numerator (Nat.pos_of_ne_zero hdenominator)
    have hfractionPos :
        0 < (remainder : Real) / (denominator : Real) :=
      div_pos hremainderPos hdenominatorPos
    have hfractionLe :
        (remainder : Real) / (denominator : Real) ≤ 1 :=
      (div_le_one hdenominatorPos).2 hremainderLt.le
    have hquotCeil :
        quotCeil numerator denominator = quotient + 1 := by
      simp [quotCeil, hdenominator, quotient, remainder, hremainder]
    rw [hsplit, hquotCeil, Int.ceil_eq_iff]
    constructor <;> norm_num <;> linarith

/-- The natural floor quotient lies below the exact real quotient. -/
theorem natCast_div_le_div
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    ((numerator / denominator : Nat) : Real) ≤
      (numerator : Real) / (denominator : Real) := by
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  rw [le_div_iff₀ hdenominatorPos]
  exact_mod_cast div_mul_le_numerator numerator denominator

/-- The exact real quotient lies below its natural ceiling quotient. -/
theorem div_le_natCast_quotCeil
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    (numerator : Real) / (denominator : Real) ≤
      (quotCeil numerator denominator : Real) := by
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  rw [div_le_iff₀ hdenominatorPos]
  exact_mod_cast numerator_le_quotCeil_mul numerator denominator hdenominator

/-- Downward quotient rounding is a lower bound on the exact real quotient. -/
theorem natCast_roundQuotDirected_false_le
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    (roundQuotDirected false numerator denominator : Real) ≤
      (numerator : Real) / (denominator : Real) := by
  simpa [roundQuotDirected] using
    natCast_div_le_div numerator denominator hdenominator

/-- Upward quotient rounding is an upper bound on the exact real quotient. -/
theorem le_natCast_roundQuotDirected_true
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    (numerator : Real) / (denominator : Real) ≤
      (roundQuotDirected true numerator denominator : Real) := by
  simpa [roundQuotDirected] using
    div_le_natCast_quotCeil numerator denominator hdenominator

/-! ## Exact rational invariance -/

/-- Directed quotient rounding depends only on the represented nonnegative rational. -/
theorem roundQuotDirected_eq_of_rat_eq
    (roundUp : Bool)
    (numerator denominator numerator' denominator' : Nat)
    (hdenominator : denominator ≠ 0) (hdenominator' : denominator' ≠ 0)
    (hvalue :
      (numerator : Real) / (denominator : Real) =
        (numerator' : Real) / (denominator' : Real)) :
    roundQuotDirected roundUp numerator denominator =
      roundQuotDirected roundUp numerator' denominator' := by
  cases roundUp
  · simp only [roundQuotDirected, Bool.false_eq_true, ite_false]
    apply Int.ofNat_inj.mp
    calc
      Int.ofNat (numerator / denominator) =
          ⌊(numerator : Real) / (denominator : Real)⌋ :=
        (floor_real_nat_div numerator denominator).symm
      _ = ⌊(numerator' : Real) / (denominator' : Real)⌋ :=
        congrArg Int.floor hvalue
      _ = Int.ofNat (numerator' / denominator') :=
        floor_real_nat_div numerator' denominator'
  · simp only [roundQuotDirected, ite_true]
    apply Int.ofNat_inj.mp
    calc
      Int.ofNat (quotCeil numerator denominator) =
          ⌈(numerator : Real) / (denominator : Real)⌉ :=
        (ceil_real_nat_div_eq_quotCeil numerator denominator hdenominator).symm
      _ = ⌈(numerator' : Real) / (denominator' : Real)⌉ :=
        congrArg Int.ceil hvalue
      _ = Int.ofNat (quotCeil numerator' denominator') :=
        ceil_real_nat_div_eq_quotCeil numerator' denominator' hdenominator'

/-- Successive exact binary scalings may be combined before directed quotient rounding. -/
theorem roundQuotDirected_scaleByPowerOfTwo_add
    (roundUp : Bool) (numerator denominator : Nat)
    (firstExponent secondExponent : Int) (hdenominator : denominator ≠ 0) :
    let first :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        numerator denominator firstExponent
    let second :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        first.1 first.2 secondExponent
    let combined :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        numerator denominator (firstExponent + secondExponent)
    roundQuotDirected roundUp second.1 second.2 =
      roundQuotDirected roundUp combined.1 combined.2 := by
  dsimp only
  apply roundQuotDirected_eq_of_rat_eq
  · exact Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero _ _ _
      (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
        numerator denominator firstExponent hdenominator)
  · exact Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
      numerator denominator (firstExponent + secondExponent) hdenominator
  · rw [scaleByPowerOfTwo_real, scaleByPowerOfTwo_real]
    change
      ((Numerics.RationalBinary.scaleByPowerOfTwo
          numerator denominator firstExponent).1 : Real) /
            ((Numerics.RationalBinary.scaleByPowerOfTwo
              numerator denominator firstExponent).2 : Real) *
          bpow secondExponent =
        scaledRatToReal numerator denominator (firstExponent + secondExponent)
    rw [scaleByPowerOfTwo_real]
    exact scaledRatToReal_mul_bpow
      numerator denominator firstExponent secondExponent

/-! ## Preservation of integer thresholds -/

/-- An integer lower bound on a quotient survives either directed integer rounding. -/
theorem le_roundQuotDirected_of_mul_le
    (roundUp : Bool) (numerator denominator lower : Nat)
    (hdenominator : denominator ≠ 0)
    (hlower : lower * denominator ≤ numerator) :
    lower ≤ roundQuotDirected roundUp numerator denominator := by
  have hfloor :
      lower ≤ numerator / denominator :=
    (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hdenominator)).2 hlower
  cases roundUp with
  | false => simpa [roundQuotDirected] using hfloor
  | true =>
      simpa [roundQuotDirected] using
        hfloor.trans (div_le_quotCeil numerator denominator)

/-- A strict integer upper bound on a quotient bounds either directed integer rounding. -/
theorem roundQuotDirected_le_of_lt_mul
    (roundUp : Bool) (numerator denominator upper : Nat)
    (hdenominator : denominator ≠ 0)
    (hupper : numerator < upper * denominator) :
    roundQuotDirected roundUp numerator denominator ≤ upper := by
  have hfloor :
      numerator / denominator < upper :=
    (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hdenominator)).2 hupper
  cases roundUp with
  | false =>
      simpa [roundQuotDirected] using hfloor.le
  | true =>
      simp only [roundQuotDirected, ite_true]
      exact (quotCeil_le_div_add_one numerator denominator).trans (by omega)

/-- A real power-of-two lower bound survives either directed integer rounding. -/
theorem pow2_le_roundQuotDirected_of_le_div
    (roundUp : Bool) (numerator denominator exponent : Nat)
    (hdenominator : denominator ≠ 0)
    (hlower :
      ((pow2 exponent : Nat) : Real) ≤
        (numerator : Real) / (denominator : Real)) :
    pow2 exponent ≤ roundQuotDirected roundUp numerator denominator := by
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  have hmulReal :
      ((pow2 exponent : Nat) : Real) * denominator ≤ numerator :=
    (le_div_iff₀ hdenominatorPos).mp hlower
  have hmulNat : pow2 exponent * denominator ≤ numerator := by
    exact_mod_cast hmulReal
  exact le_roundQuotDirected_of_mul_le roundUp numerator denominator
    (pow2 exponent) hdenominator hmulNat

/-- A strict real power-of-two upper bound weakly bounds either directed integer rounding. -/
theorem roundQuotDirected_le_pow2_of_div_lt
    (roundUp : Bool) (numerator denominator exponent : Nat)
    (hdenominator : denominator ≠ 0)
    (hupper :
      (numerator : Real) / (denominator : Real) <
        ((pow2 exponent : Nat) : Real)) :
    roundQuotDirected roundUp numerator denominator ≤ pow2 exponent := by
  have hdenominatorPos : (0 : Real) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  have hmulReal :
      (numerator : Real) < ((pow2 exponent : Nat) : Real) * denominator :=
    (div_lt_iff₀ hdenominatorPos).mp hupper
  have hmulNat : numerator < pow2 exponent * denominator := by
    exact_mod_cast hmulReal
  exact roundQuotDirected_le_of_lt_mul roundUp numerator denominator
    (pow2 exponent) hdenominator hmulNat

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
