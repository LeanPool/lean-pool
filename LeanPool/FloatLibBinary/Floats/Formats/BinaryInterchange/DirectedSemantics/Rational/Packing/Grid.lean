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
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Basic
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Quotient

/-!
# Grid bounds for directed rational packing

The executable packer rescales a rational to the subnormal or normal grid, then rounds its
quotient to an integer. Rescaling by a power of two and restoring that scale preserves the exact
value. The bounds below describe the scaled quotient and its floor and ceiling.

`Packing.Branches` identifies the corresponding executable branches. `Packing.Downward` and
`Packing.Upward` use these inequalities to bound the packed results.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/-! ## Exact scale changes and integer bounds -/

/-- The subnormal alignment shift is the negation of the smallest subnormal exponent. -/
theorem subnormalAlignExp_add_minSubnormalExponent (fmt : FloatFormat) :
    Int.ofNat (FloatFormat.subnormalAlignExp fmt) +
        fmt.minSubnormalExponent = 0 := by
  have hone : 1 ≤ fmt.exponentBias + fmt.fracWidth := by
    have hbias := fmt.exponentBias_pos
    omega
  have hcast :
      Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1) =
        Int.ofNat (fmt.exponentBias + fmt.fracWidth) - 1 := by
    simpa only [Int.ofNat_eq_natCast, Int.natCast_one] using
      (Int.ofNat_sub hone)
  unfold FloatFormat.subnormalAlignExp FloatFormat.minSubnormalExponent
    FloatFormat.minNormalExponent
  rw [hcast]
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  ring

/-- Rescaling onto the subnormal grid and back is the identity on the exact rational value. -/
theorem scaledRatToReal_subnormal_grid
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int) :
    scaledRatToReal numerator denominator
          (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt)) *
        bpow (fmt.minSubnormalExponent) =
      scaledRatToReal numerator denominator exponent := by
  rw [scaledRatToReal_mul_bpow]
  congr 1
  have halign := subnormalAlignExp_add_minSubnormalExponent fmt
  omega

/--
Rescaling onto the normal grid at a leading exponent and back is the identity on the exact
rational value.
-/
theorem scaledRatToReal_normal_grid
    (fmt : FloatFormat) (numerator denominator : Nat)
    (rationalExponent exponent : Int) :
    scaledRatToReal numerator denominator
          (Int.ofNat fmt.fracWidth - rationalExponent) *
        bpow
          (rationalExponent + exponent - Int.ofNat fmt.fracWidth) =
      scaledRatToReal numerator denominator exponent := by
  rw [scaledRatToReal_mul_bpow]
  congr 1
  ring

/-- The quotient scaled to the normal grid lies in the normalized mantissa interval. -/
theorem scaleByPowerOfTwo_normal_bounds
    (fmt : FloatFormat) (numerator denominator : Nat)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (Int.ofNat fmt.fracWidth - rationalExponent)
    ((pow2 fmt.fracWidth : Nat) : Real) ≤
        (scaled.1 : Real) / (scaled.2 : Real) ∧
      (scaled.1 : Real) / (scaled.2 : Real) <
        ((pow2 (fmt.fracWidth + 1) : Nat) : Real) := by
  let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
  let shift := Int.ofNat fmt.fracWidth - rationalExponent
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  have hbounds :=
    scaleByPowerOfTwo_floorLog2_bounds
      numerator denominator shift hnumerator hdenominator
  have hlowerExponent :
      Numerics.RationalBinary.floorLog2 numerator denominator + shift =
        Int.ofNat fmt.fracWidth := by
    simp only [shift, rationalExponent]
    ring
  have hupperExponent :
      Numerics.RationalBinary.floorLog2 numerator denominator + shift + 1 =
        Int.ofNat (fmt.fracWidth + 1) := by
    rw [hlowerExponent]
    simp
  rw [hupperExponent, hlowerExponent, bpow_ofNat fmt.fracWidth,
    bpow_ofNat (fmt.fracWidth + 1)] at hbounds
  simpa [scaled, shift, rationalExponent] using hbounds

/-- In the subnormal range, the quotient scaled to the subnormal grid lies in `[1, 2 ^
  fracWidth)`. -/
theorem scaleByPowerOfTwo_subnormal_bounds
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hlow :
      fmt.minSubnormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hhigh :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minNormalExponent) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))
    (1 : Real) ≤ (scaled.1 : Real) / (scaled.2 : Real) ∧
      (scaled.1 : Real) / (scaled.2 : Real) <
        ((pow2 fmt.fracWidth : Nat) : Real) := by
  let shift :=
    exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt)
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  let scaledExponent := Numerics.RationalBinary.floorLog2 numerator denominator + shift
  have hbounds :=
    scaleByPowerOfTwo_floorLog2_bounds
      numerator denominator shift hnumerator hdenominator
  have halign := subnormalAlignExp_add_minSubnormalExponent fmt
  have hnormal := minSubnormalExponent_add_fracWidth fmt
  have hscaledExponent :
      scaledExponent =
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent +
          Int.ofNat (FloatFormat.subnormalAlignExp fmt) := by
    simp only [scaledExponent, shift]
    ring
  have hscaledNonneg : 0 ≤ scaledExponent := by
    rw [hscaledExponent]
    omega
  have hscaledSuccLe : scaledExponent + 1 ≤ Int.ofNat fmt.fracWidth := by
    rw [hscaledExponent]
    omega
  constructor
  · calc
      (1 : Real) = bpow 0 := by
        simp
      _ ≤ bpow scaledExponent := bpow_le_bpow_of_le hscaledNonneg
      _ ≤ (scaled.1 : Real) / (scaled.2 : Real) := by
        simpa [scaledExponent] using hbounds.1
  · calc
      (scaled.1 : Real) / (scaled.2 : Real) <
          bpow (scaledExponent + 1) := by
        simpa [scaledExponent] using hbounds.2
      _ ≤ bpow (Int.ofNat fmt.fracWidth) :=
        bpow_le_bpow_of_le hscaledSuccLe
      _ = ((pow2 fmt.fracWidth : Nat) : Real) :=
        bpow_ofNat fmt.fracWidth

/-- Directed rounding on the normal grid stays within the closed normalized mantissa interval. -/
theorem roundQuotDirected_normal_bounds
    (fmt : FloatFormat) (roundUp : Bool) (numerator denominator : Nat)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (Int.ofNat fmt.fracWidth - rationalExponent)
    pow2 fmt.fracWidth ≤
        roundQuotDirected roundUp scaled.1 scaled.2 ∧
      roundQuotDirected roundUp scaled.1 scaled.2 ≤
        pow2 (fmt.fracWidth + 1) := by
  let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
  let shift := Int.ofNat fmt.fracWidth - rationalExponent
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  have hscaledDenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator shift hdenominator
  have hbounds :=
    scaleByPowerOfTwo_normal_bounds
      fmt numerator denominator hnumerator hdenominator
  constructor
  · exact pow2_le_roundQuotDirected_of_le_div
      roundUp scaled.1 scaled.2 fmt.fracWidth hscaledDenominator
      (by simpa [scaled, shift, rationalExponent] using hbounds.1)
  · exact roundQuotDirected_le_pow2_of_div_lt
      roundUp scaled.1 scaled.2 (fmt.fracWidth + 1) hscaledDenominator
      (by simpa [scaled, shift, rationalExponent] using hbounds.2)

/-- In the subnormal range, directed rounding on the subnormal grid lies in `[1, 2 ^ fracWidth]`. -/
theorem roundQuotDirected_subnormal_bounds
    (fmt : FloatFormat) (roundUp : Bool) (numerator denominator : Nat)
    (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hlow :
      fmt.minSubnormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hhigh :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minNormalExponent) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))
    1 ≤ roundQuotDirected roundUp scaled.1 scaled.2 ∧
      roundQuotDirected roundUp scaled.1 scaled.2 ≤
        pow2 fmt.fracWidth := by
  let shift :=
    exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt)
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  have hscaledDenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator shift hdenominator
  have hbounds :=
    scaleByPowerOfTwo_subnormal_bounds
      fmt numerator denominator exponent hnumerator hdenominator hlow hhigh
  have hlower :
      pow2 0 ≤ roundQuotDirected roundUp scaled.1 scaled.2 :=
    pow2_le_roundQuotDirected_of_le_div
      roundUp scaled.1 scaled.2 0 hscaledDenominator
      (by simpa [pow2_eq_two_pow, scaled, shift] using hbounds.1)
  constructor
  · simpa [pow2_eq_two_pow, scaled, shift] using hlower
  · exact roundQuotDirected_le_pow2_of_div_lt
      roundUp scaled.1 scaled.2 fmt.fracWidth hscaledDenominator
      (by simpa [scaled, shift] using hbounds.2)

/-- Downward rounding on the subnormal grid stays strictly below the smallest normal mantissa. -/
theorem roundQuotDirected_false_subnormal_lt_pow2
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hlow :
      fmt.minSubnormalExponent ≤
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
    (hhigh :
      Numerics.RationalBinary.floorLog2 numerator denominator + exponent <
        fmt.minNormalExponent) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))
    roundQuotDirected false scaled.1 scaled.2 < pow2 fmt.fracWidth := by
  let shift :=
    exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt)
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  have hscaledDenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator shift hdenominator
  have hbounds :=
    scaleByPowerOfTwo_subnormal_bounds
      fmt numerator denominator exponent hnumerator hdenominator hlow hhigh
  have hround :=
    natCast_roundQuotDirected_false_le
      scaled.1 scaled.2 hscaledDenominator
  have hreal :
      (roundQuotDirected false scaled.1 scaled.2 : Real) <
        (pow2 fmt.fracWidth : Nat) :=
    hround.trans_lt (by simpa [scaled, shift] using hbounds.2)
  exact_mod_cast hreal

/-- Downward rounding on the normal grid never carries out of the normalized mantissa interval. -/
theorem roundQuotDirected_false_normal_lt_pow2_succ
    (fmt : FloatFormat) (numerator denominator : Nat)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0) :
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (Int.ofNat fmt.fracWidth - rationalExponent)
    roundQuotDirected false scaled.1 scaled.2 <
      pow2 (fmt.fracWidth + 1) := by
  let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
  let shift := Int.ofNat fmt.fracWidth - rationalExponent
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  have hscaledDenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator shift hdenominator
  have hbounds :=
    scaleByPowerOfTwo_normal_bounds
      fmt numerator denominator hnumerator hdenominator
  have hround :=
    natCast_roundQuotDirected_false_le
      scaled.1 scaled.2 hscaledDenominator
  have hreal :
      (roundQuotDirected false scaled.1 scaled.2 : Real) <
        (pow2 (fmt.fracWidth + 1) : Nat) :=
    hround.trans_lt
      (by simpa [scaled, shift, rationalExponent] using hbounds.2)
  exact_mod_cast hreal

/-! ## Exact real bounds on the packing grids -/

/-- Downward quotient rounding on the subnormal grid lies below the exact scaled rational. -/
theorem roundQuotDirected_false_subnormal_value_le
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hdenominator : denominator ≠ 0) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))
    (roundQuotDirected false scaled.1 scaled.2 : Real) *
        bpow (fmt.minSubnormalExponent) ≤
      scaledRatToReal numerator denominator exponent := by
  rw [← scaledRatToReal_subnormal_grid fmt numerator denominator exponent,
    ← scaleByPowerOfTwo_real]
  exact mul_le_mul_of_nonneg_right
    (natCast_roundQuotDirected_false_le _ _
      (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator _ hdenominator))
    (bpow_nonneg _)

/-- The exact scaled rational lies below upward quotient rounding on the subnormal grid. -/
theorem le_roundQuotDirected_true_subnormal_value
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hdenominator : denominator ≠ 0) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))
    scaledRatToReal numerator denominator exponent ≤
      (roundQuotDirected true scaled.1 scaled.2 : Real) *
        bpow (fmt.minSubnormalExponent) := by
  rw [← scaledRatToReal_subnormal_grid fmt numerator denominator exponent,
    ← scaleByPowerOfTwo_real]
  exact mul_le_mul_of_nonneg_right
    (le_natCast_roundQuotDirected_true _ _
      (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator _ hdenominator))
    (bpow_nonneg _)

/-- Downward quotient rounding on the normal grid lies below the exact scaled rational. -/
theorem roundQuotDirected_false_normal_value_le
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hdenominator : denominator ≠ 0) :
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (Int.ofNat fmt.fracWidth - rationalExponent)
    (roundQuotDirected false scaled.1 scaled.2 : Real) *
        bpow
          (rationalExponent + exponent - Int.ofNat fmt.fracWidth) ≤
      scaledRatToReal numerator denominator exponent := by
  rw [← scaledRatToReal_normal_grid fmt numerator denominator
    (Numerics.RationalBinary.floorLog2 numerator denominator) exponent, ← scaleByPowerOfTwo_real]
  exact mul_le_mul_of_nonneg_right
    (natCast_roundQuotDirected_false_le _ _
      (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator _ hdenominator))
    (bpow_nonneg _)

/-- The exact scaled rational lies below upward quotient rounding on the normal grid. -/
theorem le_roundQuotDirected_true_normal_value
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hdenominator : denominator ≠ 0) :
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
        (Int.ofNat fmt.fracWidth - rationalExponent)
    scaledRatToReal numerator denominator exponent ≤
      (roundQuotDirected true scaled.1 scaled.2 : Real) *
        bpow
          (rationalExponent + exponent - Int.ofNat fmt.fracWidth) := by
  rw [← scaledRatToReal_normal_grid fmt numerator denominator
    (Numerics.RationalBinary.floorLog2 numerator denominator) exponent, ← scaleByPowerOfTwo_real]
  exact mul_le_mul_of_nonneg_right
    (le_natCast_roundQuotDirected_true _ _
      (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator _ hdenominator))
    (bpow_nonneg _)

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
