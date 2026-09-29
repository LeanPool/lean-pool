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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.ModelRounding.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Quotient

/-!
# Nearest-even rounding of positive rational numbers

Lean's logical floating-point model represents an inexact quotient by its integer quotient and an
`Accuracy` value computed from the remainder. `Model.roundRatScaled` rounds the same rational
after moving a binary exponent into its numerator or denominator. This module proves that those
representations remain equivalent through model normalization.

All results are independent of a particular floating-point format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Numerics

/-! ## Quotient bounds -/

/--
Nearest-even quotient rounding lies between the directed floor and ceiling rounders.

The nonzero-denominator premise is essential: at denominator zero and positive numerator, both
directed rounders return zero but nearest-even quotient rounding returns one.
-/
theorem roundQuotDirected_false_le_roundQuotientEven_le_true
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    roundQuotDirected false numerator denominator ≤
        roundQuotientEven numerator denominator ∧
      roundQuotientEven numerator denominator ≤
        roundQuotDirected true numerator denominator := by
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  have hdenominatorPos : 0 < denominator :=
    Nat.pos_of_ne_zero hdenominator
  by_cases hremainder : remainder = 0
  · simp [roundQuotDirected, roundQuotientEven, quotCeil, hdenominator,
      remainder, hremainder, hdenominatorPos]
  · have hceil : quotCeil numerator denominator = quotient + 1 := by
      simp [quotCeil, hdenominator, quotient, remainder, hremainder]
    have hnearest :
        roundQuotientEven numerator denominator = quotient ∨
          roundQuotientEven numerator denominator = quotient + 1 := by
      unfold roundQuotientEven
      dsimp only
      split
      · exact Or.inl rfl
      · split
        · exact Or.inr rfl
        · split
          · exact Or.inl rfl
          · exact Or.inr rfl
    constructor
    · simp only [roundQuotDirected]
      rcases hnearest with hnearest | hnearest <;>
        simp [hnearest, quotient]
    · simp only [roundQuotDirected, ite_true, hceil]
      rcases hnearest with hnearest | hnearest <;>
        simp [hnearest, quotient]

/-- Nearest-even normal-path rounding stays within the normalized mantissa interval. -/
theorem roundQuotientEven_normal_bounds
    (fmt : FloatFormat) (numerator denominator : Nat)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (Int.ofNat fmt.fracWidth - rationalExponent)
    pow2 fmt.fracWidth ≤ roundQuotientEven scaled.1 scaled.2 ∧
      roundQuotientEven scaled.1 scaled.2 ≤ pow2 (fmt.fracWidth + 1) := by
  dsimp only
  let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
  let scaled :=
    Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
      (Int.ofNat fmt.fracWidth - rationalExponent)
  have hscaledDenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator
      (Int.ofNat fmt.fracWidth - rationalExponent) hdenominator
  have hscaledBounds :=
    scaleByPowerOfTwo_floorLog2_bounds numerator denominator
      (Int.ofNat fmt.fracWidth - rationalExponent)
      hnumerator hdenominator
  have hlowerReal :
      ((pow2 fmt.fracWidth : Nat) : Real) ≤
        (scaled.1 : Real) / (scaled.2 : Real) := by
    have hexponent :
        Numerics.RationalBinary.floorLog2 numerator denominator +
            (Int.ofNat fmt.fracWidth - rationalExponent) =
          Int.ofNat fmt.fracWidth := by
      simp only [rationalExponent]
      ring
    rw [hexponent] at hscaledBounds
    rw [bpow_ofNat] at hscaledBounds
    simpa [scaled] using hscaledBounds.1
  have hupperReal :
      (scaled.1 : Real) / (scaled.2 : Real) <
        ((pow2 (fmt.fracWidth + 1) : Nat) : Real) := by
    have hexponent :
        Numerics.RationalBinary.floorLog2 numerator denominator +
              (Int.ofNat fmt.fracWidth - rationalExponent) + 1 =
          Int.ofNat (fmt.fracWidth + 1) := by
      simp only [rationalExponent]
      ring_nf
      simp
    rw [hexponent] at hscaledBounds
    rw [bpow_ofNat] at hscaledBounds
    simpa [scaled] using hscaledBounds.2
  have hsandwich :=
    roundQuotDirected_false_le_roundQuotientEven_le_true
      scaled.1 scaled.2 hscaledDenominator
  constructor
  · exact
      (pow2_le_roundQuotDirected_of_le_div false
        scaled.1 scaled.2 fmt.fracWidth
        hscaledDenominator hlowerReal).trans hsandwich.1
  · exact
      hsandwich.2.trans <|
        roundQuotDirected_le_pow2_of_div_lt true
          scaled.1 scaled.2 (fmt.fracWidth + 1)
          hscaledDenominator hupperReal

/-- The integer quotient and remainder accuracy used to round `numerator / denominator`. -/
def quotientExtendedMantissa (numerator denominator : Nat) : ExtendedMantissa :=
  ExtendedMantissa.ofMantissaAndAccuracy (numerator / denominator)
    (accuracyOfFraction (numerator % denominator) denominator)

/-- Multiplying the remainder and denominator by a common nonzero factor preserves accuracy. -/
theorem accuracyOfFraction_mul_right
    (remainder denominator factor : Nat) (hfactor : factor ≠ 0) :
    accuracyOfFraction (remainder * factor) (denominator * factor) =
      accuracyOfFraction remainder denominator := by
  have hfactorPos : 0 < factor := Nat.pos_of_ne_zero hfactor
  unfold accuracyOfFraction
  simp only [Nat.mul_eq_zero, hfactor, or_false]
  split <;> rename_i hrem
  · rfl
  · congr 1
    cases hcompare : Ord.compare (2 * remainder) denominator with
    | lt =>
        rw [Nat.compare_eq_lt] at hcompare ⊢
        rw [show 2 * (remainder * factor) = (2 * remainder) * factor by ac_rfl]
        exact (Nat.mul_lt_mul_right hfactorPos).2 hcompare
    | eq =>
        rw [Nat.compare_eq_eq] at hcompare ⊢
        rw [show 2 * (remainder * factor) = (2 * remainder) * factor by ac_rfl]
        exact congrArg (· * factor) hcompare
    | gt =>
        rw [Nat.compare_eq_gt] at hcompare ⊢
        rw [show 2 * (remainder * factor) = (2 * remainder) * factor by ac_rfl]
        exact (Nat.mul_lt_mul_right hfactorPos).2 hcompare

/-- A common nonzero scale factor does not change a quotient's extended mantissa. -/
theorem quotientExtendedMantissa_mul_right
    (numerator denominator factor : Nat) (hfactor : factor ≠ 0) :
    quotientExtendedMantissa (numerator * factor) (denominator * factor) =
      quotientExtendedMantissa numerator denominator := by
  have hfactorPos : 0 < factor := Nat.pos_of_ne_zero hfactor
  unfold quotientExtendedMantissa
  rw [Nat.mul_div_mul_right numerator denominator hfactorPos]
  rw [Nat.mul_mod_mul_right]
  rw [accuracyOfFraction_mul_right (numerator % denominator) denominator factor hfactor]

/-- Nearest-even quotient rounding depends only on the represented nonnegative rational. -/
theorem roundQuotientEven_eq_of_rat_eq
    (numerator denominator numerator' denominator' : Nat)
    (hdenominator : denominator ≠ 0) (hdenominator' : denominator' ≠ 0)
    (hvalue :
      (numerator : Real) / (denominator : Real) =
        (numerator' : Real) / (denominator' : Real)) :
    roundQuotientEven numerator denominator =
      roundQuotientEven numerator' denominator' := by
  have hleft :=
    nearestEven_div_eq_roundQuotientEven numerator denominator hdenominator
  have hright :=
    nearestEven_div_eq_roundQuotientEven numerator' denominator' hdenominator'
  apply Int.ofNat_inj.mp
  calc
    Int.ofNat (roundQuotientEven numerator denominator) =
        FloatLib.Floats.Formats.Flocq.nearestEven
          ((numerator : Real) / (denominator : Real)) := hleft.symm
    _ = FloatLib.Floats.Formats.Flocq.nearestEven
          ((numerator' : Real) / (denominator' : Real)) :=
      congrArg FloatLib.Floats.Formats.Flocq.nearestEven hvalue
    _ = Int.ofNat (roundQuotientEven numerator' denominator') := hright

/-- Successive exact binary scalings may be combined before nearest-even rounding. -/
theorem roundQuotientEven_scaleByPowerOfTwo_add
    (numerator denominator : Nat) (firstExponent secondExponent : Int)
    (hdenominator : denominator ≠ 0) :
    let first := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator firstExponent
    let second := Numerics.RationalBinary.scaleByPowerOfTwo first.1 first.2 secondExponent
    let combined :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (firstExponent +
        secondExponent)
    roundQuotientEven second.1 second.2 =
      roundQuotientEven combined.1 combined.2 := by
  dsimp only
  apply roundQuotientEven_eq_of_rat_eq
  · exact Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero _ _ _
      (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator firstExponent
        hdenominator)
  · exact Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
      numerator denominator (firstExponent + secondExponent) hdenominator
  · rw [scaleByPowerOfTwo_real, scaleByPowerOfTwo_real]
    change
      ((Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator firstExponent).1 : Real) /
          ((Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator firstExponent).2 :
            Real) *
          bpow secondExponent =
        scaledRatToReal numerator denominator (firstExponent + secondExponent)
    rw [scaleByPowerOfTwo_real]
    exact scaledRatToReal_mul_bpow
      numerator denominator firstExponent secondExponent

/-- Scaling a denominator by `2 ^ shift` is exact binary scaling by `2 ^ (-shift)`. -/
theorem roundQuotientEven_mul_pow2_den (numerator denominator shift : Nat) :
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (-Int.ofNat shift)
  roundQuotientEven numerator (denominator * 2 ^ shift) =
      roundQuotientEven scaled.1 scaled.2 := by
  cases shift with
  | zero => simp [Numerics.RationalBinary.scaleByPowerOfTwo]
  | succ shift =>
      rw [show -Int.ofNat (Nat.succ shift) = Int.negSucc shift by rfl]
      simp [Numerics.RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq]

/--
Round a quotient at a chosen binary exponent either directly or by first restoring the quotient's
exact external exponent.
-/
theorem roundQuotientEven_shift_to_exponent
    (numerator denominator : Nat) (exponent targetExponent : Int)
    (hdenominator : denominator ≠ 0) (hexponent : exponent ≤ targetExponent) :
    let shift := (targetExponent - exponent).toNat
    let exact := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator exponent
    let normalized := Numerics.RationalBinary.scaleByPowerOfTwo exact.1 exact.2 (-targetExponent)
    roundQuotientEven numerator (denominator * 2 ^ shift) =
      roundQuotientEven normalized.1 normalized.2 := by
  dsimp only
  let shift := (targetExponent - exponent).toNat
  have hshift : (shift : Int) = targetExponent - exponent := by
    exact Int.toNat_of_nonneg (by grind)
  calc
    roundQuotientEven numerator (denominator * 2 ^ shift) =
        roundQuotientEven
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (-Int.ofNat shift)).1
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (-Int.ofNat shift)).2 :=
      roundQuotientEven_mul_pow2_den numerator denominator shift
    _ = roundQuotientEven
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (exponent +
            -targetExponent)).1
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (exponent +
            -targetExponent)).2 := by
      congr 2 <;> congr 1 <;> grind
    _ = roundQuotientEven
          (Numerics.RationalBinary.scaleByPowerOfTwo
            (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator exponent).1
            (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator exponent).2
            (-targetExponent)).1
          (Numerics.RationalBinary.scaleByPowerOfTwo
            (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator exponent).1
            (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator exponent).2
            (-targetExponent)).2 :=
      (roundQuotientEven_scaleByPowerOfTwo_add
        numerator denominator exponent (-targetExponent) hdenominator).symm

@[simp] private theorem ofMantissaAndAccuracy_mantissa
    (mantissa : Nat) (accuracy : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy).mantissa = mantissa := by
  cases accuracy with
  | exact => rfl
  | inexact ordering => cases ordering <;> rfl

@[simp] private theorem ofMantissaAndAccuracy_accuracy
    (mantissa : Nat) (accuracy : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy).accuracy = accuracy := by
  cases accuracy with
  | exact => rfl
  | inexact ordering => cases ordering <;> rfl

/--
Shifting a quotient's extended mantissa right once is equivalent to doubling its denominator.

When the quotient is odd, its low bit becomes the new round bit and any existing nonzero remainder
becomes sticky information.
-/
private theorem quotientExtendedMantissa_shiftRightOne
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    ExtendedMantissa.shiftRightOne
        (quotientExtendedMantissa numerator denominator) =
      quotientExtendedMantissa numerator (denominator * 2) := by
  have hdenominatorPos : 0 < denominator := Nat.pos_of_ne_zero hdenominator
  have hremainderLt : numerator % denominator < denominator :=
    Nat.mod_lt numerator hdenominatorPos
  have hmantissa :
      numerator / denominator / 2 = numerator / (denominator * 2) :=
    Nat.div_div_eq_div_mul numerator denominator 2
  rcases Nat.mod_two_eq_zero_or_one (numerator / denominator) with hbit | hbit
  · have hremainder :
        numerator % (denominator * 2) = numerator % denominator := by
      have hdecomp := Nat.div_add_mod (numerator % (denominator * 2)) denominator
      rw [Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod, hbit] at hdecomp
      simpa using hdecomp.symm
    by_cases hzero : numerator % denominator = 0
    · simp [quotientExtendedMantissa, ExtendedMantissa.shiftRightOne,
        ExtendedMantissa.ofMantissaAndAccuracy, accuracyOfFraction, hzero, hremainder,
        hbit, hmantissa]
    · have hcompare :
          compare (2 * (numerator % (denominator * 2))) (denominator * 2) = .lt := by
        apply Nat.compare_eq_lt.mpr
        rw [hremainder]
        grind
      have hcompare' :
          compare (2 * (numerator % denominator)) (denominator * 2) = .lt := by
        simpa [hremainder] using hcompare
      cases haccuracy : compare (2 * (numerator % denominator)) denominator <;>
        simp [quotientExtendedMantissa, ExtendedMantissa.shiftRightOne,
          ExtendedMantissa.ofMantissaAndAccuracy, accuracyOfFraction, hzero, hremainder,
          hbit, hcompare', haccuracy, hmantissa]
  · have hremainder :
        numerator % (denominator * 2) = denominator + numerator % denominator := by
      have hdecomp := Nat.div_add_mod (numerator % (denominator * 2)) denominator
      rw [Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod, hbit] at hdecomp
      simpa [Nat.add_comm] using hdecomp.symm
    by_cases hzero : numerator % denominator = 0
    · have hcompare' :
          Ord.compare (2 * denominator) (denominator * 2) = Ordering.eq :=
        Nat.compare_eq_eq.mpr (Nat.mul_comm 2 denominator)
      simp [quotientExtendedMantissa, ExtendedMantissa.shiftRightOne,
        ExtendedMantissa.ofMantissaAndAccuracy, accuracyOfFraction, hzero, hremainder,
        hbit, hcompare', hmantissa, hdenominator]
    · have hcompare :
          compare (2 * (numerator % (denominator * 2))) (denominator * 2) = .gt := by
        apply Nat.compare_eq_gt.mpr
        rw [hremainder]
        grind
      have hcompare' :
          compare (2 * (denominator + numerator % denominator)) (denominator * 2) = .gt := by
        simpa [hremainder] using hcompare
      cases haccuracy : compare (2 * (numerator % denominator)) denominator <;>
        simp [quotientExtendedMantissa, ExtendedMantissa.shiftRightOne,
          ExtendedMantissa.ofMantissaAndAccuracy, accuracyOfFraction, hzero, hremainder,
          hbit, hcompare', haccuracy, hmantissa]

/-- Shifting a quotient right by `shift` bits scales its denominator by `2 ^ shift`. -/
theorem quotientExtendedMantissa_shift
    (numerator denominator shift : Nat) (hdenominator : denominator ≠ 0) :
    quotientExtendedMantissa numerator denominator >>> shift =
      quotientExtendedMantissa numerator (denominator * 2 ^ shift) := by
  induction shift with
  | zero => simp [HShiftRight.hShiftRight, Nat.repeat]
  | succ shift ih =>
      rw [show quotientExtendedMantissa numerator denominator >>> (shift + 1) =
          ExtendedMantissa.shiftRightOne
            (quotientExtendedMantissa numerator denominator >>> shift) by rfl]
      rw [ih]
      have hpower :
          denominator * 2 ^ (shift + 1) = (denominator * 2 ^ shift) * 2 := by
        rw [pow_succ]
        ac_rfl
      rw [hpower]
      apply quotientExtendedMantissa_shiftRightOne
      exact mul_ne_zero hdenominator (pow_ne_zero _ (by decide))

/-- Adding quotient bits by shifting left is undone by the matching right shift. -/
theorem quotientExtendedMantissa_shiftLeft_shiftRight
    (numerator denominator shift : Nat) (hdenominator : denominator ≠ 0) :
    quotientExtendedMantissa (numerator <<< shift) denominator >>> shift =
      quotientExtendedMantissa numerator denominator := by
  rw [quotientExtendedMantissa_shift
    (numerator <<< shift) denominator shift hdenominator]
  rw [Nat.shiftLeft_eq]
  exact quotientExtendedMantissa_mul_right numerator denominator (2 ^ shift)
    (pow_ne_zero _ (by decide))

/--
Nearest-even rounding after shifting a quotient agrees with rounding the rational number whose
denominator has been scaled by the same power of two.
-/
theorem roundedMantissa_shift_quotient
    (numerator denominator shift : Nat) (hdenominator : denominator ≠ 0) :
    (ExtendedMantissa.ofMantissaAndAccuracy (numerator / denominator)
        (accuracyOfFraction (numerator % denominator) denominator) >>>
      shift).roundedMantissa =
      roundQuotientEven numerator (denominator * 2 ^ shift) := by
  change
    (quotientExtendedMantissa numerator denominator >>> shift).roundedMantissa = _
  rw [quotientExtendedMantissa_shift
    numerator denominator shift hdenominator]
  unfold quotientExtendedMantissa ExtendedMantissa.roundedMantissa
  simpa using roundToNearestEven_accuracyOfFraction_mod
    numerator (denominator * 2 ^ shift)
    (mul_ne_zero hdenominator (pow_ne_zero _ (by decide)))

/--
After choosing the format's target exponent, model quotient rounding reduces to one
`roundQuotientEven` call on the correspondingly scaled denominator.
-/
theorem roundWithAccuracy_quotient_eq_finishRoundedMantissa
    (spec : Float.Model.Format) (sign : Sign)
    (numerator denominator : Nat) (exponent : Int)
    (hdenominator : denominator ≠ 0) :
    Float.Model.UnpackedFloat.roundWithAccuracy spec sign
        (numerator / denominator) exponent
        (accuracyOfFraction (numerator % denominator) denominator) =
      let shift :=
        (spec.targetExponent
          (Float.Model.totalExponent (numerator / denominator) exponent) -
            exponent).toNat
      finishRoundedMantissa spec sign
        (roundQuotientEven numerator (denominator * 2 ^ shift),
          exponent + shift) := by
  unfold Float.Model.UnpackedFloat.roundWithAccuracy
    Float.Model.UnpackedFloat.shiftToTargetExponent
    Float.Model.UnpackedFloat.shiftToExponent
  simp only
  rw [roundedMantissa_shift_quotient
    numerator denominator _ hdenominator]
  rfl

end Model
end FloatLib.Floats.Formats.BinaryInterchange
