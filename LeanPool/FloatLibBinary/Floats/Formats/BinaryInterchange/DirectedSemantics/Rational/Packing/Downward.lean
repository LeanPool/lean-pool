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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Packing.Branches
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Packing.Internal
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.ERealSemantics

/-!
# Downward bounds for directed rational packing

For a positive exact rational and a descriptor with `fmt.isIEEE = true`, the executable downward
rounder returns a finite value no greater than the input.

The proof follows the same branch partition as the runtime packer (overflow saturation,
below-minimum underflow, subnormal, and normal), using the equations from `Packing.Branches` and the
shared grid inequalities from `Packing.Grid`. The final `EReal` theorem packages the result in the
order used by the generic directed-rounding semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq
open Packing.Internal

section

/-! ## Positive downward bounds -/

private theorem roundRatMagnitudeDirectedScaled_pos_down_overflow_finite_le
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hoverflow :
      fmt.maxNormalExponent <
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent) :
    isFinite
        (roundRatMagnitudeDirectedScaled
          fmt false false numerator denominator exponent) = true ∧
      toReal
          (roundRatMagnitudeDirectedScaled
            fmt false false numerator denominator exponent) ≤
        scaledRatToReal numerator denominator exponent := by
  have hround :
      roundRatMagnitudeDirectedScaled
          fmt false false numerator denominator exponent =
        posMaxFinite fmt := by
    simpa [directedOverflow, posMaxFinite] using
      roundRatMagnitudeDirectedScaled_pos_eq_overflow
        fmt false numerator denominator exponent
        hnumerator hdenominator hoverflow
  have hbounds :=
    scaledRatToReal_floorLog2_bounds
      numerator denominator exponent hnumerator hdenominator
  have hpower :
      bpow
          (fmt.maxNormalExponent + 1) ≤
        bpow (Numerics.RationalBinary.floorLog2 numerator denominator + exponent) := by
    apply bpow_le_bpow_of_le
    omega
  constructor
  · exact (congrArg isFinite hround).trans (isFinite_posMaxFinite fmt)
  · calc
      toReal
          (roundRatMagnitudeDirectedScaled
            fmt false false numerator denominator exponent) =
          toReal (posMaxFinite fmt) := by simpa using congrArg toReal hround
      _ ≤ bpow
            (fmt.maxNormalExponent + 1) :=
        (toReal_posMaxFinite_lt_bpow fmt).le
      _ ≤ bpow (Numerics.RationalBinary.floorLog2 numerator denominator + exponent) := hpower
      _ ≤ scaledRatToReal numerator denominator exponent := hbounds.1

private theorem roundRatMagnitudeDirectedScaled_pos_down_underflow_finite_le
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hunderflow :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minSubnormalExponent) :
    isFinite
        (roundRatMagnitudeDirectedScaled
          fmt false false numerator denominator exponent) = true ∧
      toReal
          (roundRatMagnitudeDirectedScaled
            fmt false false numerator denominator exponent) ≤
        scaledRatToReal numerator denominator exponent := by
  have hround :
      roundRatMagnitudeDirectedScaled
          fmt false false numerator denominator exponent =
        zero fmt false := by
    simpa using
      roundRatMagnitudeDirectedScaled_pos_eq_underflow
        fmt false numerator denominator exponent
        hnumerator hdenominator hmax hunderflow
  constructor
  · exact (congrArg isFinite hround).trans
      (isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt false))
  · calc
      toReal
          (roundRatMagnitudeDirectedScaled
            fmt false false numerator denominator exponent) =
          0 := (congrArg toReal hround).trans (toReal_zero fmt false)
      _ ≤ scaledRatToReal numerator denominator exponent :=
        scaledRatToReal_nonneg numerator denominator exponent

private theorem roundRatMagnitudeDirectedScaled_pos_down_subnormal_finite_le
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hlow :
      fmt.minSubnormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hhigh :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minNormalExponent) :
    isFinite
        (roundRatMagnitudeDirectedScaled
          fmt false false numerator denominator exponent) = true ∧
      toReal
          (roundRatMagnitudeDirectedScaled
            fmt false false numerator denominator exponent) ≤
        scaledRatToReal numerator denominator exponent := by
  have hpos :=
    (roundQuotDirected_subnormal_bounds fmt false numerator denominator exponent
      hnumerator hdenominator hlow hhigh).1
  have hlt :=
    roundQuotDirected_false_subnormal_lt_pow2
      fmt numerator denominator exponent hnumerator hdenominator hlow hhigh
  have hround :=
    roundRatMagnitudeDirectedScaled_pos_eq_subnormal_down
      fmt numerator denominator exponent hnumerator hdenominator hmax hlow hhigh
  dsimp only at hpos hlt hround
  have hvalue := toReal_roundSubnormalDown fmt _ hlt
  rw [ite_eq_right (Nat.one_le_iff_ne_zero.mp hpos)] at hvalue
  rw [hround]
  refine ⟨isFinite_ofFields_subnormal fmt hfmt _ (by simpa [pow2_eq_two_pow] using hlt), ?_⟩
  rw [hvalue]
  exact roundQuotDirected_false_subnormal_value_le fmt numerator denominator exponent hdenominator

private theorem roundRatMagnitudeDirectedScaled_pos_down_normal_finite_le
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hnormal :
      fmt.minNormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent) :
    isFinite
        (roundRatMagnitudeDirectedScaled
          fmt false false numerator denominator exponent) = true ∧
      toReal
          (roundRatMagnitudeDirectedScaled
            fmt false false numerator denominator exponent) ≤
        scaledRatToReal numerator denominator exponent := by
  have hbounds :=
    roundQuotDirected_normal_bounds fmt false numerator denominator hnumerator hdenominator
  have hlt :=
    roundQuotDirected_false_normal_lt_pow2_succ fmt numerator denominator hnumerator hdenominator
  have hround :=
    roundRatMagnitudeDirectedScaled_pos_eq_normal_down
      fmt numerator denominator exponent hfmt hnumerator hdenominator hnormal hmax
  dsimp only at hbounds hlt hround
  rw [hround]
  refine ⟨Directed.Internal.isFinite_ofFields_normalized fmt hfmt _ _ hnormal hmax, ?_⟩
  rw [toReal_ofFields_normalized fmt _ _ hbounds.1 hlt hnormal hmax
    (Directed.Internal.isFinite_ofFields_normalized fmt hfmt _ _ hnormal hmax)]
  exact roundQuotDirected_false_normal_value_le fmt numerator denominator exponent hdenominator

/--
Positive downward rational rounding is finite and never exceeds the exact scaled rational.
-/
theorem roundRatMagnitudeDirectedScaled_pos_down_finite_le
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    isFinite
        (roundRatMagnitudeDirectedScaled
          fmt false false numerator denominator exponent) = true ∧
      toReal
          (roundRatMagnitudeDirectedScaled
            fmt false false numerator denominator exponent) ≤
        scaledRatToReal numerator denominator exponent := by
  by_cases hoverflow :
      fmt.maxNormalExponent <
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent
  · exact roundRatMagnitudeDirectedScaled_pos_down_overflow_finite_le
      fmt numerator denominator exponent
      hnumerator hdenominator hoverflow
  · have hmax :
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
          fmt.maxNormalExponent :=
      le_of_not_gt hoverflow
    by_cases hunderflow :
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
          fmt.minSubnormalExponent
    · exact roundRatMagnitudeDirectedScaled_pos_down_underflow_finite_le
        fmt numerator denominator exponent
        hnumerator hdenominator hmax hunderflow
    · have hlow :
          fmt.minSubnormalExponent ≤
            Numerics.RationalBinary.floorLog2 numerator denominator + exponent :=
        le_of_not_gt hunderflow
      by_cases hsubnormal :
          Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
            fmt.minNormalExponent
      · exact roundRatMagnitudeDirectedScaled_pos_down_subnormal_finite_le
          fmt numerator denominator exponent hfmt
          hnumerator hdenominator hmax hlow hsubnormal
      · have hnormal :
            fmt.minNormalExponent ≤
              Numerics.RationalBinary.floorLog2 numerator denominator + exponent :=
          le_of_not_gt hsubnormal
        exact roundRatMagnitudeDirectedScaled_pos_down_normal_finite_le
          fmt numerator denominator exponent hfmt
          hnumerator hdenominator hnormal hmax

/-- Positive downward rational rounding is never classified as NaN. -/
theorem isNaN_roundRatMagnitudeDirectedScaled_pos_down_eq_false
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    isNaN
        (roundRatMagnitudeDirectedScaled
          fmt false false numerator denominator exponent) = false :=
  isNaN_eq_false_of_isFinite_eq_true _
    (roundRatMagnitudeDirectedScaled_pos_down_finite_le
      fmt numerator denominator exponent hfmt hnumerator hdenominator).1

/-- Positive downward rational rounding is a lower bound in the extended reals. -/
theorem toEReal_roundRatMagnitudeDirectedScaled_pos_down_le
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    toEReal
        (roundRatMagnitudeDirectedScaled
          fmt false false numerator denominator exponent) ≤
      (scaledRatToReal numerator denominator exponent : EReal) := by
  have hresult :=
    roundRatMagnitudeDirectedScaled_pos_down_finite_le
      fmt numerator denominator exponent hfmt hnumerator hdenominator
  rw [toEReal_eq_coe_toReal_of_isFinite _ hresult.1]
  exact EReal.coe_le_coe_iff.mpr hresult.2


end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
