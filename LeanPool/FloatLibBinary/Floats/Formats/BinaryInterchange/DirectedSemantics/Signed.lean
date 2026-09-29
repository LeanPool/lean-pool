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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Positive

/-!
# Signed directed rounding for arbitrary executable float formats

Signed floor and ceiling semantics follow from the positive scaled-mantissa results. For
negative inputs, downward rounding uses the upward-rounded magnitude and upward rounding uses
the downward-rounded magnitude. The final theorems lift these integer identities through `round`
to exact real equations for nonzero dyadics when `fmt.isIEEE = true`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/-! ## Signed scaled mantissas -/

/-- Signed mantissa selected by rounding a dyadic toward negative infinity. -/
def roundSignedMantissaAtExponentDown
    (sign : Bool) (mantissa : Nat) (exponent targetExponent : Int) : Int :=
  if sign then
    -Int.ofNat (roundMantissaAtExponentUp mantissa exponent targetExponent)
  else
    Int.ofNat (roundMantissaAtExponentDown mantissa exponent targetExponent)

/-- Signed mantissa selected by rounding a dyadic toward positive infinity. -/
def roundSignedMantissaAtExponentUp
    (sign : Bool) (mantissa : Nat) (exponent targetExponent : Int) : Int :=
  if sign then
    -Int.ofNat (roundMantissaAtExponentDown mantissa exponent targetExponent)
  else
    Int.ofNat (roundMantissaAtExponentUp mantissa exponent targetExponent)

/-- Signed floor rounding swaps to ceiling on the magnitude of a negative dyadic. -/
theorem floor_scaledDyadic
    (sign : Bool) (mantissa : Nat) (exponent targetExponent : Int) :
    floorRound
        ((if sign then (-1 : ℝ) else 1) * (mantissa : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (exponent - targetExponent)) =
      roundSignedMantissaAtExponentDown sign mantissa exponent targetExponent := by
  cases sign with
  | false =>
      simpa [roundSignedMantissaAtExponentDown] using
        floor_scaledMagnitude mantissa exponent targetExponent
  | true =>
      simp only [roundSignedMantissaAtExponentDown, ite_true]
      rw [show
        (-1 : ℝ) * (mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent) =
          -((mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent)) by ring]
      unfold floorRound
      rw [Int.floor_neg]
      exact congrArg Neg.neg
        (ceil_scaledMagnitude mantissa exponent targetExponent)

/-- Signed ceiling rounding swaps to floor on the magnitude of a negative dyadic. -/
theorem ceil_scaledDyadic
    (sign : Bool) (mantissa : Nat) (exponent targetExponent : Int) :
    ceilRound
        ((if sign then (-1 : ℝ) else 1) * (mantissa : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (exponent - targetExponent)) =
      roundSignedMantissaAtExponentUp sign mantissa exponent targetExponent := by
  cases sign with
  | false =>
      simpa [roundSignedMantissaAtExponentUp] using
        ceil_scaledMagnitude mantissa exponent targetExponent
  | true =>
      simp only [roundSignedMantissaAtExponentUp, ite_true]
      rw [show
        (-1 : ℝ) * (mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent) =
          -((mantissa : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (exponent - targetExponent)) by ring]
      unfold ceilRound
      rw [Int.ceil_neg]
      exact congrArg Neg.neg
        (floor_scaledMagnitude mantissa exponent targetExponent)

/-! ## Numerics.Dyadic rounded-real semantics -/

private theorem round_dyadic_eq_of_scaled_round_eq
    (fmt : FloatFormat) (d : Numerics.Dyadic) (hfmt : fmt.isIEEE = true) (hm : d.significand ≠ 0)
    (rnd : ℝ → Int) (roundedMantissa : Int)
    (hscaled :
      rnd
          ((if d.negative then (-1 : ℝ) else 1) * (d.significand : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (d.exponent -
                (FloatFormat.toModel fmt).targetExponent
                  (Float.Model.totalExponent d.significand d.exponent))) =
        roundedMantissa) :
    round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) rnd d.toReal =
      (roundedMantissa : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          ((FloatFormat.toModel fmt).targetExponent
            (Float.Model.totalExponent d.significand d.exponent)) := by
  have hscaled' :
      rnd (scaledMantissa Numerics.binaryRadix (fexpOf fmt) d.toReal) =
        roundedMantissa := by
    rw [scaledMantissa_toReal fmt d hfmt hm]
    exact hscaled
  calc
    round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) rnd d.toReal =
        FloatLib.Floats.Formats.Flocq.toReal (β := Numerics.binaryRadix) {
          mantissa := roundedMantissa
          exponent := cexp Numerics.binaryRadix (fexpOf fmt) d.toReal } :=
      round_eq_toReal_of_scaled_round_eq rnd d.toReal roundedMantissa hscaled'
    _ = (roundedMantissa : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            ((FloatFormat.toModel fmt).targetExponent
              (Float.Model.totalExponent d.significand d.exponent)) := by
      rw [cexp_toReal_eq_targetExponent fmt d hfmt hm]
      rfl

/-- Rounded-real semantics of downward rounding for a nonzero signed dyadic. -/
theorem roundAtDown_dyadic_eq (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hfmt : fmt.isIEEE = true) (hm : d.significand ≠ 0) :
    let target :=
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent d.significand d.exponent)
    roundAtDown fmt d.toReal =
      (roundSignedMantissaAtExponentDown d.negative d.significand d.exponent target : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix target := by
  dsimp only
  apply round_dyadic_eq_of_scaled_round_eq fmt d hfmt hm floorRound
  exact floor_scaledDyadic d.negative d.significand d.exponent _

/-- Rounded-real semantics of upward rounding for a nonzero signed dyadic. -/
theorem roundAtUp_dyadic_eq (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hfmt : fmt.isIEEE = true) (hm : d.significand ≠ 0) :
    let target :=
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent d.significand d.exponent)
    roundAtUp fmt d.toReal =
      (roundSignedMantissaAtExponentUp d.negative d.significand d.exponent target : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix target := by
  dsimp only
  apply round_dyadic_eq_of_scaled_round_eq fmt d hfmt hm ceilRound
  exact ceil_scaledDyadic d.negative d.significand d.exponent _

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
