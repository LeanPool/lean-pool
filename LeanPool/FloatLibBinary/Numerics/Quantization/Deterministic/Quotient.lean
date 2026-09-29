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

public import Mathlib.Data.Nat.ModEq

/-!
# Deterministic nearest-even quotient rounding

Format-independent nearest-even rounding for a natural quotient and remainder. The executable
decision uses only quotient parity and the remainder, so optimized kernels can recover the same
result without constructing a large scaled numerator.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
Whether a quotient should increase when rounding a nonnegative quotient and remainder to nearest,
with an exact halfway case sent to the even integer.

Only the quotient's parity is needed. Keeping that fact explicit lets callers handle very large
scaled numerators through modular arithmetic without first constructing the full quotient.
-/
@[inline] def nearestEvenRoundsUp
    (quotientOdd : Bool) (remainder denominator : Nat) : Bool :=
  let twiceRemainder := 2 * remainder
  denominator < twiceRemainder ||
    (denominator == twiceRemainder && quotientOdd)

/--
Round `numerator / denominator` to the nearest natural number, breaking exact halfway cases toward
the even result.

The function is total. Callers that assign mathematical quotient semantics must establish that
`denominator` is nonzero: with `denominator = 0`, Lean's conventions `n / 0 = 0` and `n % 0 = n`
make the result `0` for `numerator = 0` and `1` otherwise. The native kernel
`FixedWord.roundQuotientEven` returns `0` for a zero denominator instead, so its refinement
theorem assumes a nonzero denominator.
-/
@[inline] def roundQuotientEven (numerator denominator : Nat) : Nat :=
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  let twice := 2 * remainder
  if twice < denominator then
    quotient
  else if denominator < twice then
    quotient + 1
  else if quotient % 2 == 0 then
    quotient
  else
    quotient + 1

/--
Nearest-even quotient rounding either retains the integer quotient or increases it by one.

The decision depends only on the remainder and quotient parity. This form is useful for optimized
algorithms that recover those two facts through modular arithmetic without constructing a very
large scaled numerator.
-/
theorem roundQuotientEven_eq_quotient_add (numerator denominator : Nat) :
    roundQuotientEven numerator denominator =
      numerator / denominator +
        if nearestEvenRoundsUp
            (numerator / denominator % 2 == 1)
            (numerator % denominator) denominator then
          1
        else
          0 := by
  by_cases hbelow : 2 * (numerator % denominator) < denominator
  · have hnotAbove : ¬ denominator < 2 * (numerator % denominator) := by
      omega
    have hnotEqual : denominator ≠ 2 * (numerator % denominator) := by
      omega
    simp [roundQuotientEven, nearestEvenRoundsUp, hbelow, hnotAbove,
      hnotEqual]
  · by_cases habove : denominator < 2 * (numerator % denominator)
    · simp [roundQuotientEven, nearestEvenRoundsUp, hbelow, habove]
    · have hequal : denominator = 2 * (numerator % denominator) := by
        omega
      by_cases heven : numerator / denominator % 2 = 0
      · have hresult :
            roundQuotientEven numerator denominator =
              numerator / denominator := by
          unfold roundQuotientEven
          rw [ite_eq_right hbelow, ite_eq_right habove,
            ite_eq_left (beq_iff_eq.mpr heven)]
        have hcompare :
            (decide (denominator < 2 * (numerator % denominator)) : Bool) =
              false := by
          simp [habove]
        have hequalBool :
            (denominator == 2 * (numerator % denominator)) = true :=
          beq_iff_eq.mpr hequal
        have hparity :
            (numerator / denominator % 2 == 1) = false := by
          simp [heven]
        have hrounds :
            nearestEvenRoundsUp
                (numerator / denominator % 2 == 1)
                (numerator % denominator) denominator =
              false := by
          simp only [nearestEvenRoundsUp, hcompare, Bool.false_or,
            hequalBool, Bool.true_and, hparity]
        rw [hresult, hrounds]
        simp
      · have hmodLt : numerator / denominator % 2 < 2 :=
          Nat.mod_lt _ (by decide)
        have hodd : numerator / denominator % 2 = 1 := by omega
        have hresult :
            roundQuotientEven numerator denominator =
              numerator / denominator + 1 := by
          unfold roundQuotientEven
          rw [ite_eq_right hbelow, ite_eq_right habove,
            ite_eq_right (by simpa only [beq_iff_eq] using heven)]
        have hcompare :
            (decide (denominator < 2 * (numerator % denominator)) : Bool) =
              false := by
          simp [habove]
        have hequalBool :
            (denominator == 2 * (numerator % denominator)) = true :=
          beq_iff_eq.mpr hequal
        have hparity :
            (numerator / denominator % 2 == 1) = true :=
          beq_iff_eq.mpr hodd
        have hrounds :
            nearestEvenRoundsUp
                (numerator / denominator % 2 == 1)
                (numerator % denominator) denominator =
              true := by
          simp only [nearestEvenRoundsUp, hcompare, Bool.false_or,
            hequalBool, Bool.true_and, hparity]
        rw [hresult, hrounds]
        simp

end FloatLib.Numerics
