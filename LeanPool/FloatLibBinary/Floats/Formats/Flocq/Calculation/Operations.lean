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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Digits

/-!
# Exact Operations on Mantissa/Exponent Values

These operations manipulate `FloatRep` representations without rounding.  Addition aligns both
operands to their smaller exponent; multiplication adds exponents.  Their correctness theorems are
radix-parametric counterparts of Flocq's `Calc.Operations` results.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- Integer radix powers agree with real radix powers at nonnegative exponents. -/
theorem intPower_cast_eq_bpow (β : Numerics.Radix) {e : ℤ} (he : 0 ≤ e) :
    (intPower β e : ℝ) = bpow β e := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le he
  simp [intPower, bpow, Numerics.Radix.toReal]

/-- Two integer mantissas expressed on a common exponent grid. -/
structure FloatAlignment where
  /-- First aligned mantissa. -/
  leftMantissa : ℤ
  /-- Second aligned mantissa. -/
  rightMantissa : ℤ
  /-- Common exponent, equal to the smaller input exponent. -/
  exponent : ℤ

namespace FloatRep

variable {β : Numerics.Radix}

/-- Align two representations to the smaller exponent without changing their real values. -/
def align (f g : FloatRep β) : FloatAlignment :=
  if f.exponent ≤ g.exponent then
    { leftMantissa := f.mantissa
      rightMantissa := g.mantissa * intPower β (g.exponent - f.exponent)
      exponent := f.exponent }
  else
    { leftMantissa := f.mantissa * intPower β (f.exponent - g.exponent)
      rightMantissa := g.mantissa
      exponent := g.exponent }

/-- Alignment preserves both represented real values. -/
theorem align_toReal (f g : FloatRep β) :
    toReal f = toReal (β := β) {
      mantissa := (align f g).leftMantissa
      exponent := (align f g).exponent } ∧
    toReal g = toReal (β := β) {
      mantissa := (align f g).rightMantissa
      exponent := (align f g).exponent } := by
  by_cases hfg : f.exponent ≤ g.exponent
  · constructor
    · simp [align, hfg]
    · simp only [align, ite_eq_left hfg, toReal, Int.cast_mul]
      rw [intPower_cast_eq_bpow β (sub_nonneg.mpr hfg),
        bpow.sub_exp, mul_assoc, div_mul_cancel₀ _ (bpow.ne_zero β _)]
  · constructor
    · simp only [align, ite_eq_right hfg, toReal, Int.cast_mul]
      rw [intPower_cast_eq_bpow β (sub_nonneg.mpr (le_of_not_ge hfg)),
        bpow.sub_exp, mul_assoc, div_mul_cancel₀ _ (bpow.ne_zero β _)]
    · simp [align, hfg]

/-- Alignment selects the minimum input exponent. -/
theorem align_exponent (f g : FloatRep β) :
    (align f g).exponent = min f.exponent g.exponent := by
  by_cases hfg : f.exponent ≤ g.exponent <;> simp [align, min_def, hfg]

/-- Exact negation of a mantissa/exponent representation. -/
@[inline] def negExact (f : FloatRep β) : FloatRep β :=
  { mantissa := -f.mantissa, exponent := f.exponent }

/-- Exact absolute value of a mantissa/exponent representation. -/
def absExact (f : FloatRep β) : FloatRep β :=
  { mantissa := |f.mantissa|, exponent := f.exponent }

/-- Exact addition after exponent alignment. -/
def addExact (f g : FloatRep β) : FloatRep β :=
  let aligned := align f g
  { mantissa := aligned.leftMantissa + aligned.rightMantissa
    exponent := aligned.exponent }

/-- Exact subtraction after exponent alignment. -/
def subExact (f g : FloatRep β) : FloatRep β :=
  addExact f (negExact g)

/-- Exact multiplication of mantissas with exponent addition. -/
@[inline] def mulExact (f g : FloatRep β) : FloatRep β :=
  { mantissa := f.mantissa * g.mantissa
    exponent := f.exponent + g.exponent }

/-- Exact representation negation denotes real negation. -/
@[simp] theorem toReal_negExact (f : FloatRep β) :
    toReal (negExact f) = -toReal f := by
  simp [negExact, toReal]

/-- Exact representation absolute value denotes real absolute value. -/
@[simp] theorem toReal_absExact (f : FloatRep β) :
    toReal (absExact f) = |toReal f| := by
  unfold absExact toReal
  rw [Int.cast_abs, abs_mul, abs_of_pos (bpow.pos β f.exponent)]

/-- Exact aligned addition denotes real addition. -/
@[simp] theorem toReal_addExact (f g : FloatRep β) :
    toReal (addExact f g) = toReal f + toReal g := by
  obtain ⟨hf, hg⟩ := align_toReal f g
  simpa only [toReal, addExact, Int.cast_add, add_mul] using
    congrArg₂ (· + ·) hf.symm hg.symm

/-- Exact aligned subtraction denotes real subtraction. -/
@[simp] theorem toReal_subExact (f g : FloatRep β) :
    toReal (subExact f g) = toReal f - toReal g := by
  simp [subExact, sub_eq_add_neg]

/-- Exact mantissa/exponent multiplication denotes real multiplication. -/
@[simp] theorem toReal_mulExact (f g : FloatRep β) :
    toReal (mulExact f g) = toReal f * toReal g := by
  unfold mulExact toReal
  rw [Int.cast_mul, bpow.add_exp]
  ring

end FloatRep
end FloatLib.Floats.Formats.Flocq
