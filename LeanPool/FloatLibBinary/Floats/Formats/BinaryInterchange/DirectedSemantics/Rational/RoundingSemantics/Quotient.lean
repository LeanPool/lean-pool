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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.NearestEven
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Packing.Downward
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Packing.Upward
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Proof

/-!
# Quotient and exponent semantics

Exact rational rounding reduces to an integer quotient after a power-of-two rescaling. This
module proves bounds for small quotients and relates the scaled leading exponent to the order of
the numerator and denominator. It also identifies the subnormal and normal grid exponents used
by `roundAt`.

These lemmas supply the bounds and exponent identities used by the nearest-even packing proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
open Directed.Internal

section

/-- A quotient at or below one half rounds to the even integer zero. -/
theorem roundQuotientEven_eq_zero_of_two_mul_le
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0)
    (hhalf : 2 * numerator ≤ denominator) :
    roundQuotientEven numerator denominator = 0 := by
  have hnumeratorLt : numerator < denominator := by
    have hdenominatorPos := Nat.pos_of_ne_zero hdenominator
    omega
  have hquotient : numerator / denominator = 0 :=
    Nat.div_eq_of_lt hnumeratorLt
  have hremainder : numerator % denominator = numerator :=
    Nat.mod_eq_of_lt hnumeratorLt
  unfold roundQuotientEven
  simp only [hquotient, hremainder, Nat.zero_mod, beq_self_eq_true]
  by_cases hstrict : 2 * numerator < denominator
  · simp [hstrict]
  · have hequal : denominator = 2 * numerator := by omega
    simp [hequal]

/-- A positive proper fraction rounds to either zero or one. -/
theorem roundQuotientEven_le_one_of_lt
    (numerator denominator : Nat) (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0) (hlt : numerator < denominator) :
    roundQuotientEven numerator denominator ≤ 1 := by
  have hsandwich :=
    roundQuotDirected_false_le_roundQuotientEven_le_true
      numerator denominator hdenominator
  have hceil : roundQuotDirected true numerator denominator = 1 := by
    simp [roundQuotDirected, quotCeil, hdenominator,
      Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, hnumerator]
  exact hsandwich.2.trans_eq hceil

/--
If a scaled rational's leading exponent is negative, its scaled numerator is strictly smaller
than its denominator.
-/
theorem scaleByPowerOfTwo_fst_lt_snd_of_neg_log
    (numerator denominator : Nat) (shift : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hnegative : Numerics.RationalBinary.floorLog2 numerator denominator + shift < 0) :
    (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift).1 <
      (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift).2 := by
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  have hbounds :=
    scaleByPowerOfTwo_floorLog2_bounds
      numerator denominator shift hnumerator hdenominator
  have hpower :
      bpow (Numerics.RationalBinary.floorLog2 numerator denominator + shift + 1) ≤ 1 := by
    calc
      bpow (Numerics.RationalBinary.floorLog2 numerator denominator + shift + 1) ≤ bpow 0 := by
        apply bpow_le_bpow_of_le
        omega
      _ = 1 := bpow_zero
  have hratio : (scaled.1 : Real) / (scaled.2 : Real) < 1 :=
    hbounds.2.trans_le hpower
  have hscaledDenominator : 0 < (scaled.2 : Real) := by
    exact_mod_cast
      (Nat.pos_of_ne_zero
        (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator shift
          hdenominator))
  have hcast : (scaled.1 : Real) < scaled.2 :=
    (div_lt_one hscaledDenominator).mp hratio
  exact_mod_cast hcast

/--
Values whose scaled leading exponent is below `-1` are strictly below one half of a grid unit and
therefore round to zero under nearest-even.
-/
theorem roundQuotientEven_scaled_eq_zero
    (numerator denominator : Nat) (shift : Int)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hsmall : Numerics.RationalBinary.floorLog2 numerator denominator + shift < -1) :
    roundQuotientEven
        (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift).1
        (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift).2 = 0 := by
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  have hbounds :=
    scaleByPowerOfTwo_floorLog2_bounds
      numerator denominator shift hnumerator hdenominator
  have hpower :
      bpow (Numerics.RationalBinary.floorLog2 numerator denominator + shift + 1) ≤ (2 : Real)⁻¹
        := by
    calc
      bpow (Numerics.RationalBinary.floorLog2 numerator denominator + shift + 1) ≤ bpow (-1) := by
        apply bpow_le_bpow_of_le
        omega
      _ = (2 : Real)⁻¹ := bpow_neg_one
  have hratio :
      (scaled.1 : Real) / (scaled.2 : Real) < (2 : Real)⁻¹ :=
    hbounds.2.trans_le hpower
  have hscaledDenominator : 0 < (scaled.2 : Real) := by
    exact_mod_cast
      (Nat.pos_of_ne_zero
        (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator shift
          hdenominator))
  have hcast : (2 : Real) * scaled.1 < scaled.2 := by
    rw [div_lt_iff₀ hscaledDenominator] at hratio
    nlinarith
  have hhalf : 2 * scaled.1 ≤ scaled.2 := by
    exact_mod_cast hcast.le
  exact roundQuotientEven_eq_zero_of_two_mul_le
    scaled.1 scaled.2
    (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator shift hdenominator)
    hhalf

/-- Nearest-even subnormal-path rounding is at most the smallest normal mantissa. -/
theorem roundQuotientEven_subnormal_le
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
    roundQuotientEven scaled.1 scaled.2 ≤ pow2 fmt.fracWidth := by
  dsimp only
  let shift :=
    exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt)
  let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
  have hscaledDenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero numerator denominator shift hdenominator
  have hsandwich :=
    roundQuotDirected_false_le_roundQuotientEven_le_true
      scaled.1 scaled.2 hscaledDenominator
  have hupper :=
    (roundQuotDirected_subnormal_bounds
      fmt true numerator denominator exponent
      hnumerator hdenominator hlow hhigh).2
  exact hsandwich.2.trans (by simpa [scaled, shift] using hupper)

/-! ## Format exponent selection -/

/-- The nearest-even implementation's half-min-subnormal cutoff in semantic form. -/
theorem neg_normalMantissaExpOffset_eq_minSubnormalExponent_sub_one
    (fmt : FloatFormat) :
    -Int.ofNat (FloatFormat.normalMantissaExpOffset fmt) =
      fmt.minSubnormalExponent - 1 := by
  unfold FloatFormat.normalMantissaExpOffset FloatFormat.minSubnormalExponent
    FloatFormat.minNormalExponent
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  ring

/-- Values below the normal range use the descriptor's minimum-subnormal grid. -/
theorem fexpOf_total_eq_minSubnormal
    (fmt : FloatFormat) (totalExponent : Int)
    (hsubnormal : totalExponent < fmt.minNormalExponent) :
    fexpOf fmt (totalExponent + 1) = fmt.minSubnormalExponent := by
  simp only [fexpOf, fltExp, FloatFormat.minSubnormalExponent,
    Int.ofNat_eq_natCast]
  apply max_eq_right
  omega

/-- Normal values use the descriptor's precision-shifted rounded-real grid. -/
theorem fexpOf_total_eq_normal
    (fmt : FloatFormat) (totalExponent : Int)
    (hnormal : fmt.minNormalExponent ≤ totalExponent) :
    fexpOf fmt (totalExponent + 1) = totalExponent - Int.ofNat fmt.fracWidth := by
  simp only [fexpOf, fltExp, FloatFormat.minSubnormalExponent,
    Int.ofNat_eq_natCast]
  omega


end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
