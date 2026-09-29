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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Rounding.Core

/-!
# Nearest-even rounding lemmas

Format-independent integer primitives in `Numerics` agree with FloatLib's rounded-real
nearest-even operation under the stated bounds.

Generic shift-rounding equations and floor bounds live in
`Numerics.Quantization.Deterministic.ShiftRight`, where fixed-point and other binary
quantizations can reuse them. This module adds normalized-significand bounds, oddness of
`nearestEven`, and its agreement with executable rounding of nonnegative rationals.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics

/--
Nearest-even averaging preserves the normalized interval for every significand precision.
-/
theorem roundShiftRightEven_add_normalized_bounds
    (precision left right : Nat)
    (hleft : 2 ^ precision ≤ left ∧ left < 2 ^ (precision + 1))
    (hright : 2 ^ precision ≤ right ∧ right < 2 ^ (precision + 1)) :
    2 ^ precision ≤ roundShiftRightEven (left + right) 1 ∧
      roundShiftRightEven (left + right) 1 < 2 ^ (precision + 1) := by
  have hpowUpper : 2 ^ (precision + 1) = 2 * 2 ^ precision := by
    rw [pow_succ]
    omega
  have hpowNext : 2 ^ (precision + 2) = 2 * 2 ^ (precision + 1) := by
    rw [show precision + 2 = (precision + 1) + 1 by omega, pow_succ]
    omega
  have hupperPositive : 0 < 2 ^ (precision + 1) := by
    positivity
  have hsumLower : 2 ^ (precision + 1) ≤ left + right := by
    rw [hpowUpper]
    omega
  have hsumUpper : left + right ≤ 2 ^ (precision + 2) - 2 := by
    rw [hpowNext]
    omega
  have hfloorLower : 2 ^ precision ≤ (left + right) >>> 1 := by
    rw [Nat.shiftRight_eq_div_pow]
    norm_num
    rw [hpowUpper] at hsumLower
    omega
  have hroundLower :=
    shiftRight_le_roundShiftRightEven (left + right) 1
  constructor
  · exact le_trans hfloorLower hroundLower
  by_cases hmax : left + right = 2 ^ (precision + 2) - 2
  · have hmaxForm :
        2 ^ (precision + 2) - 2 =
          2 * (2 ^ (precision + 1) - 1) := by
      rw [hpowNext]
      omega
    rw [hmax, hmaxForm, roundShiftRightEven_two_mul]
    omega
  · have hsumUpper' : left + right < 2 ^ (precision + 2) - 2 :=
      lt_of_le_of_ne hsumUpper hmax
    have hfloorUpper :
        (left + right) >>> 1 ≤ 2 ^ (precision + 1) - 2 := by
      rw [Nat.shiftRight_eq_div_pow]
      norm_num
      rw [hpowNext] at hsumUpper'
      omega
    have hroundUpper :=
      roundShiftRightEven_le_shiftRight_add1 (left + right) 1
    norm_num [Nat.shiftRight_eq_div_pow] at hroundUpper
    omega

/-- Nearest-even integer rounding commutes with negation. -/
theorem nearestEven_neg (x : ℝ) :
    nearestEven (-x) = -nearestEven x := by
  by_cases hint : x = (⌊x⌋ : ℝ)
  · have hceil : ⌈x⌉ = ⌊x⌋ := Int.ceil_eq_iff.2 ⟨by linarith, hint.le⟩
    have hfloorNeg : ⌊-x⌋ = -⌊x⌋ := by rw [Int.floor_neg, hceil]
    have hx : x - (⌊x⌋ : ℝ) = 0 := by linarith
    have hnegx : -x - -(⌊x⌋ : ℝ) = 0 := by linarith
    simp [nearestEven, hfloorNeg, hx, hnegx]
  · have hnotMem : x ∉ Set.range ((↑·) : ℤ → ℝ) := by
      rintro ⟨n, rfl⟩
      exact hint (by simp)
    have hceil : ⌈x⌉ = ⌊x⌋ + 1 := (Int.ceil_eq_floor_add_one_iff_notMem x).2 hnotMem
    have hfloorNeg : ⌊-x⌋ = -⌊x⌋ - 1 := by
      rw [Int.floor_neg, hceil]
      ring
    have hlt : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (Ne.symm hint)
    have hgt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    have hparity : Even (-⌊x⌋ - 1) ↔ ¬Even ⌊x⌋ := by
      rw [show -⌊x⌋ - 1 = -(⌊x⌋ + 1) by ring, even_neg, Int.even_add_one]
    simp only [nearestEven, hfloorNeg, Int.cast_sub, Int.cast_neg, Int.cast_one, hparity]
    split_ifs <;> first | omega | linarith

/-- Nearest-even rounding never exceeds a natural upper bound of its argument. -/
theorem nearestEven_le_natCast_of_le {value : ℝ} {bound : Nat} (hvalue : value ≤ bound) :
    nearestEven value ≤ Int.ofNat bound := by
  have hbound : nearestEven (bound : ℝ) = Int.ofNat bound := by
    simpa using ValidRnd.id (rnd := nearestEven) (Int.ofNat bound)
  simpa [hbound] using ValidRnd.monotone (rnd := nearestEven) value bound hvalue

/-- Nearest-even rounding never drops below a natural lower bound of its argument. -/
theorem natCast_le_nearestEven_of_le {bound : Nat} {value : ℝ} (hvalue : (bound : ℝ) ≤ value) :
    Int.ofNat bound ≤ nearestEven value := by
  have hbound : nearestEven (bound : ℝ) = Int.ofNat bound := by
    simpa using ValidRnd.id (rnd := nearestEven) (Int.ofNat bound)
  simpa [hbound] using ValidRnd.monotone (rnd := nearestEven) bound value hvalue

/--
The floor of a quotient of natural numbers in `ℝ` is their natural-number quotient.
-/
theorem floor_real_nat_div (num den : Nat) :
    (⌊(num : ℝ) / (den : ℝ)⌋ : Int) = (num / den : Nat) := by
  simp [Int.floor_div_natCast]

private theorem div_lt_half_iff (remainder den : Nat) (hden : den ≠ 0) :
    ((remainder : ℝ) / (den : ℝ) < (2⁻¹ : ℝ)) ↔
      2 * remainder < den := by
  have hdenPos : (0 : ℝ) < den := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hden)
  rw [div_lt_iff₀ hdenPos, inv_mul_eq_div, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  norm_cast
  omega

private theorem half_lt_div_iff (remainder den : Nat) (hden : den ≠ 0) :
    ((2⁻¹ : ℝ) < (remainder : ℝ) / (den : ℝ)) ↔
      den < 2 * remainder := by
  have hdenPos : (0 : ℝ) < den := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hden)
  rw [lt_div_iff₀ hdenPos, inv_mul_eq_div, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  norm_cast
  omega

/-- Nearest-even rounding of a nonnegative rational agrees with `roundQuotientEven`. -/
theorem nearestEven_div_eq_roundQuotientEven
    (num den : Nat) (hden : den ≠ 0) :
    nearestEven ((num : ℝ) / (den : ℝ)) =
      Int.ofNat (roundQuotientEven num den) := by
  classical
  let quotient := num / den
  let remainder := num % den
  have hfloor :
      (⌊((num : ℝ) / (den : ℝ))⌋ : Int) = quotient := by
    simpa [quotient] using floor_real_nat_div num den
  have hfract :
      ((num : ℝ) / (den : ℝ)) - (quotient : ℝ) =
        (remainder : ℝ) / (den : ℝ) := by
    simpa only [Int.fract, floor_real_nat_div, Int.cast_natCast, quotient, remainder] using
      (Int.fract_div_natCast_eq_div_natCast_mod (m := num) (n := den) (k := ℝ))
  unfold nearestEven
  simp only [hfloor, Int.cast_natCast, one_div, gt_iff_lt, Int.even_coe_nat, Int.ofNat_eq_natCast]
  rw [hfract]
  simp only [Int.natCast_ediv, roundQuotientEven, beq_iff_eq, Nat.cast_ite, Nat.cast_add,
    Nat.cast_one,
    remainder, quotient]
  have hlt :
      (((num % den : Nat) : ℝ) / (den : ℝ) < (2⁻¹ : ℝ)) ↔
        2 * (num % den) < den := by
    simpa using div_lt_half_iff (num % den) den hden
  have hgt :
      ((2⁻¹ : ℝ) < ((num % den : Nat) : ℝ) / (den : ℝ)) ↔
        den < 2 * (num % den) := by
    simpa using half_lt_div_iff (num % den) den hden
  by_cases htwoLt : 2 * (num % den) < den
  · have hrLt :
        ((num % den : Nat) : ℝ) / (den : ℝ) < (2⁻¹ : ℝ) :=
      hlt.mpr htwoLt
    simp [htwoLt, hrLt]
  · have hrNotLt :
        ¬((num % den : Nat) : ℝ) / (den : ℝ) < (2⁻¹ : ℝ) := by
      exact fun h => htwoLt (hlt.mp h)
    by_cases htwoGt : den < 2 * (num % den)
    · have hrGt :
          (2⁻¹ : ℝ) < ((num % den : Nat) : ℝ) / (den : ℝ) :=
        hgt.mpr htwoGt
      simp [htwoLt, hrNotLt, htwoGt, hrGt]
    · have hrNotGt :
          ¬(2⁻¹ : ℝ) < ((num % den : Nat) : ℝ) / (den : ℝ) := by
        exact fun h => htwoGt (hgt.mp h)
      simp [htwoLt, hrNotLt, htwoGt, hrNotGt, Nat.even_iff]

/-- Nearest-even rounding after division by `2^shift` is executable shift rounding. -/
theorem nearestEven_div_pow2_eq_roundShiftRightEven (num shift : Nat) :
    nearestEven ((num : ℝ) / (pow2 shift : ℝ)) =
      Int.ofNat (roundShiftRightEven num shift) := by
  have hden : pow2 shift ≠ 0 := by
    simp [pow2_eq_two_pow]
  rw [nearestEven_div_eq_roundQuotientEven num (pow2 shift) hden]
  simp only [pow2_eq_two_pow, Numerics.roundShiftRightEven_eq_roundQuotientEven]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
