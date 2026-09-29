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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ScaleAdd.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.AddDyadic.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Packing.Special

/-!
# Correctness of unsigned-scale exact addition

For conventional IEEE descriptors, `roundSum_eq` identifies unsigned-scale alignment and rounding
with exact dyadic addition followed by `roundDyadic`. The proof includes zero operands and the
signed-zero result of cancellation. The `roundOffset` parameter accommodates both addition scales
and the product scales used by FMA.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteScaleAdd

/-- Unsigned-scale rounding is the corresponding exact dyadic rounding. -/
theorem roundMagnitude_eq
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (roundOffset : Nat) (sign : Bool) (mantissa scale : Nat) :
    roundMagnitude fmt roundOffset sign mantissa scale =
      roundDyadic fmt {
        negative := sign
        significand := mantissa
        exponent := exponent fmt scale roundOffset } := by
  exact FiniteProductRound.round_eq_roundDyadic
    fmt hfmt sign mantissa (scale + roundOffset)

private theorem roundDyadic_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (exp : Int) :
    roundDyadic fmt {
      negative := sign
      significand := 0
      exponent := exp } = zero fmt sign := by
  have hencoding : fmt.encoding = .ieee :=
    ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  cases sign <;>
    simp [roundDyadic, hfmt, ieeeRoundDyadic, zero,
      FloatFormat.supportsSignedZero, hencoding,
      posZero_eq_ofModel_zero, negZero_eq_ofModel_zero]

private theorem exponent_le_iff
    (fmt : FloatFormat) (roundOffset leftScale rightScale : Nat) :
    exponent fmt leftScale roundOffset ≤ exponent fmt rightScale roundOffset ↔
      leftScale ≤ rightScale := by
  unfold exponent
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

private theorem exponent_sub_toNat
    (fmt : FloatFormat) (roundOffset leftScale rightScale : Nat)
    (hscale : leftScale ≤ rightScale) :
    Int.toNat
        (exponent fmt rightScale roundOffset -
          exponent fmt leftScale roundOffset) =
      rightScale - leftScale := by
  unfold exponent
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- The signed-magnitude helper rounds the exact dyadic magnitude sum. -/
theorem roundMagnitudes_eq
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (roundOffset : Nat) (leftSign rightSign : Bool)
    (left right scale : Nat) :
    roundMagnitudes fmt roundOffset leftSign rightSign left right scale =
      roundDyadic fmt
        (addDyadicMagnitudes leftSign rightSign left right
          (exponent fmt scale roundOffset)) := by
  unfold roundMagnitudes addDyadicMagnitudes
  by_cases hsign : leftSign = rightSign
  · simp [hsign, roundMagnitude_eq fmt hfmt]
  · by_cases heq : left = right
    · simp [hsign, heq, roundDyadic_zero fmt hfmt]
    · by_cases hlt : left < right
      · simp [hsign, heq, hlt, roundMagnitude_eq fmt hfmt]
      · simp [hsign, heq, hlt, roundMagnitude_eq fmt hfmt]

/-- `roundSum` is exactly dyadic addition followed by one IEEE rounding step. -/
theorem roundSum_eq
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (roundOffset : Nat) (leftSign rightSign : Bool)
    (leftMantissa leftScale rightMantissa rightScale : Nat) :
    roundSum fmt roundOffset leftSign rightSign
        leftMantissa leftScale rightMantissa rightScale =
      roundDyadic fmt
        (addDyadic
          { negative := leftSign
            significand := leftMantissa
            exponent := exponent fmt leftScale roundOffset }
          { negative := rightSign
            significand := rightMantissa
            exponent := exponent fmt rightScale roundOffset }) := by
  rw [← addDyadicImpl_eq]
  unfold roundSum addDyadicImpl
  by_cases hleft : leftMantissa = 0
  · by_cases hright : rightMantissa = 0
    · simp [hleft, hright, roundDyadic_zero fmt hfmt]
    · simp [hleft, hright, roundMagnitude_eq fmt hfmt]
  · by_cases hright : rightMantissa = 0
    · simp [hleft, hright, roundMagnitude_eq fmt hfmt]
    · by_cases hscale : leftScale ≤ rightScale
      · have hexponent :
            exponent fmt leftScale roundOffset ≤
              exponent fmt rightScale roundOffset := by
          exact (exponent_le_iff fmt roundOffset leftScale rightScale).2 hscale
        have hshift :
            Int.toNat
                (exponent fmt rightScale roundOffset -
                  exponent fmt leftScale roundOffset) =
              rightScale - leftScale := by
          exact exponent_sub_toNat fmt roundOffset leftScale rightScale hscale
        simp only [hleft, hright, beq_iff_eq, ite_false, hexponent, ite_true,
          hscale, hshift]
        exact roundMagnitudes_eq fmt hfmt roundOffset leftSign rightSign
          leftMantissa (rightMantissa <<< (rightScale - leftScale))
          leftScale
      · have hexponent :
            ¬exponent fmt leftScale roundOffset ≤
              exponent fmt rightScale roundOffset := by
          simpa only [exponent_le_iff] using hscale
        have hrightScale : rightScale ≤ leftScale := by omega
        have hshift :
            Int.toNat
                (exponent fmt leftScale roundOffset -
                  exponent fmt rightScale roundOffset) =
              leftScale - rightScale := by
          exact exponent_sub_toNat fmt roundOffset rightScale leftScale
            hrightScale
        simp only [hleft, hright, beq_iff_eq, ite_false, hscale, hexponent,
          hshift]
        exact roundMagnitudes_eq fmt hfmt roundOffset leftSign rightSign
          (leftMantissa <<< (leftScale - rightScale)) rightMantissa
          rightScale

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteScaleAdd
