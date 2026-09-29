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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Analysis.Sterbenz
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Error.Addition
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Error.Multiplication

/-!
# Sterbenz's Lemma for Gradual Underflow

Sterbenz exact subtraction extends from the unbounded-exponent family `FLX` to the
gradual-underflow family `FLT`. The latter is the format used by the rounded-real binary32
model.

The proof splits on the magnitude of the exact difference. Every `FLT` operand lies on the
minimum-exponent grid, so a sufficiently small difference is representable by closure of that
grid under subtraction. A larger difference follows from the `FLX` Sterbenz theorem and the
normal-range inclusion from `FLX` to `FLT`.

## Reference

- P. H. Sterbenz, *Floating-Point Computation*, Prentice-Hall, 1974.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/--
An `FLX` value in the normal range is representable in the corresponding `FLT` format.

This is the normal-range converse of `generic_format_FLT_to_FLX`.
-/
theorem generic_format_FLX_to_FLT_of_normal (emin prec : ℤ) (hprec : 0 < prec)
    {x : ℝ} (hxFLX : genericFormat β (flxExp prec) x)
    (hnorm : bpow β (emin + prec - 1) ≤ abs x) :
    genericFormat β (fltExp emin prec) x := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  obtain ⟨_, f, hxf, hmant⟩ := (generic_format_FLX_iff (β := β) prec hprec x).mp hxFLX
  refine (generic_format_FLT_iff (β := β) emin prec hprec x).mpr ⟨hprec, f, hxf, hmant, ?_⟩
  have hmabs : abs (f.mantissa : ℝ) = (f.mantissa.natAbs : ℝ) := by
    cases f.mantissa with
    | ofNat n => simp
    | negSucc n =>
        rw [Int.cast_negSucc, abs_of_neg]
        · norm_num
        · exact neg_neg_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ))
  have hmantR : abs (f.mantissa : ℝ) < bpow β prec := by
    rw [hmabs, bpow_eq_natPow (β := β) prec hprec.le]
    exact_mod_cast hmant
  have habsx : abs x < bpow β (f.exponent + prec) := by
    rw [hxf, toReal, abs_mul, abs_of_pos (bpow.pos β f.exponent)]
    calc
      abs (f.mantissa : ℝ) * bpow β f.exponent <
          bpow β prec * bpow β f.exponent :=
        mul_lt_mul_of_pos_right hmantR (bpow.pos β f.exponent)
      _ = bpow β (f.exponent + prec) := by
        rw [← bpow.add_exp]
        congr 1
        linarith
  have hlt : bpow β (emin + prec - 1) < bpow β (f.exponent + prec) :=
    lt_of_le_of_lt hnorm habsx
  have hexp : emin + prec - 1 < f.exponent + prec :=
    (bpow_lt_bpow_iff β _ _).mp hlt
  linarith

/--
Directed Sterbenz lemma for `FLT`: if `0 < y ≤ x ≤ 2y` and both operands are representable, then
their exact difference is representable.
-/
theorem generic_format_FLT_sub_of_le_two_mul (emin prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hx2y : x ≤ 2 * y)
    (hxFmt : genericFormat β (fltExp emin prec) x)
    (hyFmt : genericFormat β (fltExp emin prec) y) :
    genericFormat β (fltExp emin prec) (x - y) := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  by_cases hsmall : abs (x - y) ≤ bpow β (emin + prec - 1)
  · have hxFix := generic_format_FLT_to_FIX (β := β) emin prec hprec hxFmt
    have hyFix := generic_format_FLT_to_FIX (β := β) emin prec hprec hyFmt
    have hdFix := generic_format_FIX_sub (β := β) emin hxFix hyFix
    apply generic_format_FIX_to_FLT_of_abs_le (β := β) emin prec hprec hdFix
    exact hsmall.trans ((bpow_le_bpow_iff β _ _).2 (by linarith))
  · rw [not_le] at hsmall
    have hxFLX := generic_format_FLT_to_FLX (β := β) emin prec hprec hxFmt
    have hyFLX := generic_format_FLT_to_FLX (β := β) emin prec hprec hyFmt
    have hdFLX := generic_format_FLX_sub_of_le_two_mul (β := β) prec hprec
      hy hyx hx2y hxFLX hyFLX
    exact generic_format_FLX_to_FLT_of_normal (β := β) emin prec hprec
      hdFLX (le_of_lt hsmall)

/--
Sterbenz's lemma for `FLT`: if two positive representable values are within a factor of two, then
their exact difference is representable, including across the subnormal boundary.
-/
theorem generic_format_FLT_sterbenz (emin prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx2y : x ≤ 2 * y) (hy2x : y ≤ 2 * x)
    (hxFmt : genericFormat β (fltExp emin prec) x)
    (hyFmt : genericFormat β (fltExp emin prec) y) :
    genericFormat β (fltExp emin prec) (x - y) := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  rcases le_total y x with hyx | hxy
  · exact generic_format_FLT_sub_of_le_two_mul emin prec hprec hy hyx hx2y hxFmt hyFmt
  · have hdiff :=
      generic_format_FLT_sub_of_le_two_mul emin prec hprec hx hxy hy2x hyFmt hxFmt
    have hneg := generic_format_neg (β := β) (fexp := fltExp emin prec) (y - x) hdiff
    simpa only [neg_sub] using hneg

end FloatLib.Floats.Formats.Flocq
