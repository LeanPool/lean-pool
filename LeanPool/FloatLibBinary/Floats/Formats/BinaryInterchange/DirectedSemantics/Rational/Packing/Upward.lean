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
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core

/-!
# Upward bounds for directed rational packing

For a positive exact rational and a descriptor with `fmt.isIEEE = true`, the executable upward
rounder returns positive infinity or a finite value no smaller than the input.

Upward normal rounding may carry into a new exponent and may overflow. The branch lemmas cover
both cases. The final `EReal` inequality includes positive infinity and supplies the upper bound
used by the directed-rounding semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq
open Packing.Internal

section

/-! ## Positive upward bounds -/

private theorem roundRatMagnitudeDirectedScaled_pos_up_underflow_finite_ge
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
          fmt true false numerator denominator exponent) = true ∧
      scaledRatToReal numerator denominator exponent ≤
        toReal
          (roundRatMagnitudeDirectedScaled
            fmt true false numerator denominator exponent) := by
  have hround :
      roundRatMagnitudeDirectedScaled
          fmt true false numerator denominator exponent =
        posMinSubnormal fmt := by
    simpa using
      roundRatMagnitudeDirectedScaled_pos_eq_underflow
        fmt true numerator denominator exponent
        hnumerator hdenominator hmax hunderflow
  have hbounds :=
    scaledRatToReal_floorLog2_bounds
      numerator denominator exponent hnumerator hdenominator
  have hpower :
      bpow (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1) ≤
        bpow (fmt.minSubnormalExponent) := by
    apply bpow_le_bpow_of_le
    omega
  constructor
  · exact (congrArg isFinite hround).trans
      (Model.isFinite_posMinSubnormal fmt)
  · calc
      scaledRatToReal numerator denominator exponent ≤
          bpow (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1) :=
        hbounds.2.le
      _ ≤ bpow (fmt.minSubnormalExponent) := hpower
      _ = toReal (posMinSubnormal fmt) :=
        (toReal_posMinSubnormal fmt).symm
      _ = toReal
          (roundRatMagnitudeDirectedScaled
            fmt true false numerator denominator exponent) :=
        congrArg toReal hround.symm

private theorem roundRatMagnitudeDirectedScaled_pos_up_subnormal_finite_ge
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
          fmt true false numerator denominator exponent) = true ∧
      scaledRatToReal numerator denominator exponent ≤
        toReal
          (roundRatMagnitudeDirectedScaled
            fmt true false numerator denominator exponent) := by
  let shift :=
    exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt)
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  let rounded := roundQuotDirected true scaled.1 scaled.2
  have hbounds :=
    roundQuotDirected_subnormal_bounds
      fmt true numerator denominator exponent
      hnumerator hdenominator hlow hhigh
  have hroundedNe : rounded ≠ 0 := by
    have hone : 1 ≤ rounded := by
      simpa [rounded, scaled, shift] using hbounds.1
    omega
  have hroundedHigh : rounded ≤ pow2 fmt.fracWidth := by
    simpa [rounded, scaled, shift] using hbounds.2
  have hround :
      roundRatMagnitudeDirectedScaled
          fmt true false numerator denominator exponent =
        if pow2 fmt.fracWidth ≤ rounded then
          ofFields fmt false 1 0
        else
          ofFields fmt false 0 rounded := by
    simpa [rounded, scaled, shift] using
      roundRatMagnitudeDirectedScaled_pos_eq_subnormal_up
        fmt numerator denominator exponent
        hnumerator hdenominator hmax hlow hhigh
  have hvalue :
      toReal
          (if pow2 fmt.fracWidth ≤ rounded then
            ofFields fmt false 1 0
          else
            ofFields fmt false 0 rounded) =
        (rounded : Real) *
          bpow (fmt.minSubnormalExponent) := by
    simpa [hroundedNe] using
      toReal_roundSubnormalUp fmt rounded hroundedNe hroundedHigh
  constructor
  · rw [hround]
    by_cases hnormal : pow2 fmt.fracWidth ≤ rounded
    · rw [ite_eq_left hnormal]
      exact isFinite_ofFields_minNormal fmt hfmt
    · rw [ite_eq_right hnormal]
      exact isFinite_ofFields_subnormal fmt hfmt rounded
        (by
          simpa [pow2_eq_two_pow] using lt_of_not_ge hnormal)
  · rw [hround, hvalue]
    simpa [rounded, scaled, shift] using
      le_roundQuotDirected_true_subnormal_value
        fmt numerator denominator exponent hdenominator

private theorem roundRatMagnitudeDirectedScaled_pos_up_normal_no_carry_finite_ge
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hnormal :
      fmt.minNormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (Int.ofNat fmt.fracWidth - rationalExponent)
      roundQuotDirected true scaled.1 scaled.2 ≠
        pow2 (fmt.fracWidth + 1)) :
    isFinite
        (roundRatMagnitudeDirectedScaled
          fmt true false numerator denominator exponent) = true ∧
      scaledRatToReal numerator denominator exponent ≤
        toReal
          (roundRatMagnitudeDirectedScaled
            fmt true false numerator denominator exponent) := by
  dsimp only at hcarry
  have hbounds :=
    roundQuotDirected_normal_bounds fmt true numerator denominator hnumerator hdenominator
  dsimp only at hbounds
  have hround :=
    roundRatMagnitudeDirectedScaled_pos_eq_normal_up_no_carry
      fmt numerator denominator exponent hfmt hnumerator hdenominator hnormal hmax hcarry
  dsimp only at hround
  rw [hround]
  refine ⟨Directed.Internal.isFinite_ofFields_normalized fmt hfmt _ _ hnormal hmax, ?_⟩
  rw [toReal_ofFields_normalized fmt _ _ hbounds.1 (lt_of_le_of_ne hbounds.2 hcarry) hnormal hmax
    (Directed.Internal.isFinite_ofFields_normalized fmt hfmt _ _ hnormal hmax)]
  exact le_roundQuotDirected_true_normal_value fmt numerator denominator exponent hdenominator

private theorem roundRatMagnitudeDirectedScaled_pos_up_normal_carry_finite_ge
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hnormal :
      fmt.minNormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hmax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (Int.ofNat fmt.fracWidth - rationalExponent)
      roundQuotDirected true scaled.1 scaled.2 =
        pow2 (fmt.fracWidth + 1))
    (hcarryMax :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1 ≤
        fmt.maxNormalExponent) :
    isFinite
        (roundRatMagnitudeDirectedScaled
          fmt true false numerator denominator exponent) = true ∧
      scaledRatToReal numerator denominator exponent ≤
        toReal
          (roundRatMagnitudeDirectedScaled
            fmt true false numerator denominator exponent) := by
  dsimp only at hcarry
  have hnormalCarry :
      fmt.minNormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1 := by
    omega
  have hfinite :=
    Directed.Internal.isFinite_ofFields_normalized fmt hfmt (pow2 fmt.fracWidth) _ hnormalCarry
      hcarryMax
  have hvalue :=
    toReal_ofFields_normalized fmt (pow2 fmt.fracWidth) _ le_rfl (pow2_lt_pow2_succ fmt.fracWidth)
      hnormalCarry hcarryMax hfinite
  rw [Nat.sub_self] at hfinite hvalue
  rw [roundRatMagnitudeDirectedScaled_pos_eq_normal_up_carry
    fmt numerator denominator exponent hnumerator hdenominator hnormal hmax hcarry hcarryMax]
  refine ⟨hfinite, ?_⟩
  rw [hvalue, Directed.Internal.normalizationCarry_value fmt, ← hcarry]
  exact le_roundQuotDirected_true_normal_value fmt numerator denominator exponent hdenominator

/--
Positive upward rational rounding is either positive infinity or a finite value no smaller than
the exact scaled rational.
-/
theorem roundRatMagnitudeDirectedScaled_pos_up_eq_posInf_or_finite_ge
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    roundRatMagnitudeDirectedScaled
        fmt true false numerator denominator exponent = posInf fmt ∨
      (isFinite
          (roundRatMagnitudeDirectedScaled
            fmt true false numerator denominator exponent) = true ∧
        scaledRatToReal numerator denominator exponent ≤
          toReal
            (roundRatMagnitudeDirectedScaled
              fmt true false numerator denominator exponent)) := by
  by_cases hoverflow :
      fmt.maxNormalExponent <
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent
  · exact Or.inl <| by
      calc
        roundRatMagnitudeDirectedScaled
            fmt true false numerator denominator exponent =
            directedOverflow fmt false true :=
          roundRatMagnitudeDirectedScaled_pos_eq_overflow
            fmt true numerator denominator exponent
            hnumerator hdenominator hoverflow
        _ = posInf fmt := directedOverflow_false_true_eq_posInf fmt hfmt
  · have hmax :
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent ≤
          fmt.maxNormalExponent :=
      le_of_not_gt hoverflow
    by_cases hunderflow :
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
          fmt.minSubnormalExponent
    · exact Or.inr
        (roundRatMagnitudeDirectedScaled_pos_up_underflow_finite_ge
          fmt numerator denominator exponent
          hnumerator hdenominator hmax hunderflow)
    · have hlow :
          fmt.minSubnormalExponent ≤
            Numerics.RationalBinary.floorLog2 numerator denominator + exponent :=
        le_of_not_gt hunderflow
      by_cases hsubnormal :
          Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
            fmt.minNormalExponent
      · exact Or.inr
          (roundRatMagnitudeDirectedScaled_pos_up_subnormal_finite_ge
            fmt numerator denominator exponent hfmt
            hnumerator hdenominator hmax hlow hsubnormal)
      · have hnormal :
            fmt.minNormalExponent ≤
              Numerics.RationalBinary.floorLog2 numerator denominator + exponent :=
          le_of_not_gt hsubnormal
        by_cases hcarry :
            let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
            let scaled :=
              Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
                (Int.ofNat fmt.fracWidth - rationalExponent)
            roundQuotDirected true scaled.1 scaled.2 =
              pow2 (fmt.fracWidth + 1)
        · by_cases hcarryOverflow :
              fmt.maxNormalExponent <
                Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1
          · exact Or.inl <| by
              calc
                roundRatMagnitudeDirectedScaled
                    fmt true false numerator denominator exponent =
                    directedOverflow fmt false true :=
                  roundRatMagnitudeDirectedScaled_pos_eq_normal_up_carry_overflow
                    fmt numerator denominator exponent
                    hnumerator hdenominator hnormal hmax hcarry hcarryOverflow
                _ = posInf fmt :=
                  directedOverflow_false_true_eq_posInf fmt hfmt
          · have hcarryMax :
                Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1 ≤
                  fmt.maxNormalExponent :=
              le_of_not_gt hcarryOverflow
            exact Or.inr
              (roundRatMagnitudeDirectedScaled_pos_up_normal_carry_finite_ge
                fmt numerator denominator exponent hfmt
                hnumerator hdenominator hnormal hmax hcarry hcarryMax)
        · exact Or.inr
            (roundRatMagnitudeDirectedScaled_pos_up_normal_no_carry_finite_ge
              fmt numerator denominator exponent hfmt
              hnumerator hdenominator hnormal hmax hcarry)

/-- Positive upward rational rounding is never classified as NaN. -/
theorem isNaN_roundRatMagnitudeDirectedScaled_pos_up_eq_false
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    isNaN
        (roundRatMagnitudeDirectedScaled
          fmt true false numerator denominator exponent) = false := by
  rcases roundRatMagnitudeDirectedScaled_pos_up_eq_posInf_or_finite_ge
      fmt numerator denominator exponent
      hfmt hnumerator hdenominator with hinf | ⟨hfinite, _⟩
  · rw [hinf]
    exact isNaN_posInf fmt <|
      FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt
  · exact isNaN_eq_false_of_isFinite_eq_true _ hfinite

/-- Positive upward rational rounding is an upper bound in the extended reals. -/
theorem le_toEReal_roundRatMagnitudeDirectedScaled_pos_up
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    (scaledRatToReal numerator denominator exponent : EReal) ≤
      toEReal
        (roundRatMagnitudeDirectedScaled
          fmt true false numerator denominator exponent) := by
  rcases roundRatMagnitudeDirectedScaled_pos_up_eq_posInf_or_finite_ge
      fmt numerator denominator exponent
      hfmt hnumerator hdenominator with hinf | ⟨hfinite, hbound⟩
  · rw [hinf, toEReal_posInf fmt hfmt]
    exact le_top
  · rw [toEReal_eq_coe_toReal_of_isFinite _ hfinite]
    exact EReal.coe_le_coe_iff.mpr hbound

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
