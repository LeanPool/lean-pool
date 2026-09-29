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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Theorems

/-!
# Exact Subtraction

The fixed-point family is an additive lattice, so subtraction is exact without a ratio
restriction.  This is the fixed-grid foundation for the floating-point Sterbenz theorem, where
the ratio hypotheses are needed to align the operands' effective exponents.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/-- Values on a fixed grid are closed under negation. -/
theorem fixFormat_neg {emin : ℤ} {x : ℝ} (hx : FIXFormat (β := β) emin x) :
    FIXFormat (β := β) emin (-x) := by
  obtain ⟨f, hxf, hfe⟩ := hx
  refine ⟨{ mantissa := -f.mantissa, exponent := emin }, ?_, rfl⟩
  rw [hxf, toReal, hfe]
  simp [toReal]

/-- Values on a fixed grid are closed under addition. -/
theorem fixFormat_add {emin : ℤ} {x y : ℝ}
    (hx : FIXFormat (β := β) emin x) (hy : FIXFormat (β := β) emin y) :
    FIXFormat (β := β) emin (x + y) := by
  obtain ⟨fx, hxf, hxe⟩ := hx
  obtain ⟨fy, hyf, hye⟩ := hy
  refine ⟨{ mantissa := fx.mantissa + fy.mantissa, exponent := emin }, ?_, rfl⟩
  rw [hxf, hyf, toReal, toReal, hxe, hye]
  simp only [toReal]
  push_cast
  ring

/-- Values on a fixed grid are closed under subtraction. -/
theorem fixFormat_sub {emin : ℤ} {x y : ℝ}
    (hx : FIXFormat (β := β) emin x) (hy : FIXFormat (β := β) emin y) :
    FIXFormat (β := β) emin (x - y) := by
  rw [sub_eq_add_neg]
  exact fixFormat_add hx (fixFormat_neg hy)

/-- Generic FIX representability is closed under exact subtraction. -/
theorem generic_format_FIX_sub (emin : ℤ) {x y : ℝ}
    (hx : genericFormat β (fixExp emin) x)
    (hy : genericFormat β (fixExp emin) y) :
    genericFormat β (fixExp emin) (x - y) := by
  rw [generic_format_FIX_iff] at hx hy ⊢
  exact fixFormat_sub hx hy

/--
Sterbenz's lemma for the unbounded-exponent format: if two positive representable values differ by
at most a factor of two, then their subtraction is exactly representable at the same precision.

The proof does not appeal to rounding.  The ratio bound shows that the operands' magnitudes differ
by at most one radix bin.  Their integer scaled mantissas can therefore be aligned on the smaller
canonical exponent, and the exact integer difference is fine enough for the result's canonical
exponent.
-/
theorem generic_format_FLX_sub_of_le_two_mul (prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hx2y : x ≤ 2 * y)
    (hxFmt : genericFormat β (flxExp prec) x)
    (hyFmt : genericFormat β (flxExp prec) y) :
    genericFormat β (flxExp prec) (x - y) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  by_cases hxy : x = y
  · rw [hxy, sub_self]
    exact generic_format_zero
  have hx : 0 < x := hy.trans_le hyx
  have hdpos : 0 < x - y := sub_pos.mpr (lt_of_le_of_ne hyx (Ne.symm hxy))
  let ex := magnitude β x
  let ey := magnitude β y
  let e0 := ey - prec
  have heyex : ey ≤ ex := magnitude_mono_pos β hy hyx
  have hexb : ex ≤ ey + 1 := by
    have hxLower := bpow_magnitude_sub_one_le β x hx.ne'
    have hyUpper := abs_lt_bpow_magnitude β y hy.ne'
    have hbaseTwo : (2 : ℝ) ≤ β.toReal := by
      change (2 : ℝ) ≤ (β.base : ℝ)
      exact_mod_cast β.base_valid
    have hpow : bpow β (ex - 1) < bpow β (ey + 1) := by
      calc
        bpow β (ex - 1) ≤ x := by simpa [ex, abs_of_pos hx] using hxLower
        _ ≤ 2 * y := hx2y
        _ ≤ β.toReal * y := mul_le_mul_of_nonneg_right hbaseTwo hy.le
        _ < β.toReal * bpow β ey :=
          mul_lt_mul_of_pos_left (by simpa [ey, abs_of_pos hy] using hyUpper)
            (Numerics.Radix.pos β)
        _ = bpow β 1 * bpow β ey := by simp [bpow]
        _ = bpow β (1 + ey) := (bpow.add_exp β 1 ey).symm
        _ = bpow β (ey + 1) := by congr 1; linarith
    have : ex - 1 < ey + 1 := (bpow_lt_bpow_iff β _ _).mp hpow
    linarith
  let shift := ex - ey
  have hshift0 : 0 ≤ shift := sub_nonneg.mpr heyex
  have hshift1 : shift ≤ 1 := by simp [shift]; linarith
  obtain ⟨scale, hscale⟩ := bpow_eq_natCast_of_nonneg β shift hshift0
  obtain ⟨nx, hnx⟩ := scaled_mantissa_int_of_generic
    (β := β) (fexp := flxExp prec) x hxFmt
  obtain ⟨ny, hny⟩ := scaled_mantissa_int_of_generic
    (β := β) (fexp := flxExp prec) y hyFmt
  have hxRepr := scaled_mantissa_mul_bpow
    (β := β) (fexp := flxExp prec) x
  have hyRepr := scaled_mantissa_mul_bpow
    (β := β) (fexp := flxExp prec) y
  have hscaleReal : ((Int.ofNat scale : ℤ) : ℝ) = bpow β shift := by
    simpa using hscale.symm
  have hxAligned : x = ((nx * Int.ofNat scale : ℤ) : ℝ) * bpow β e0 := by
    rw [← hxRepr, hnx]
    rw [Int.cast_mul, hscaleReal]
    rw [mul_assoc, ← bpow.add_exp]
    congr 2
    simp [cexp, flxExp, shift, ex, ey, e0]
  have hyAligned : y = (ny : ℝ) * bpow β e0 := by
    rw [← hyRepr, hny]
    simp [cexp, flxExp, ey, e0]
  have hdUpper : x - y < bpow β ey := by
    calc
      x - y ≤ y := by linarith
      _ < bpow β ey := by simpa [ey, abs_of_pos hy] using
        (abs_lt_bpow_magnitude β y hy.ne')
  have hmagd : magnitude β (x - y) ≤ ey :=
    magnitude_le_of_abs_lt_bpow β (x - y) ey hdpos.ne'
      (by simpa [abs_of_pos hdpos] using hdUpper)
  apply generic_format_of_toReal_of_cexp_le
    ({ mantissa := nx * Int.ofNat scale - ny, exponent := e0 } : FloatRep β)
  · rw [hxAligned, hyAligned, toReal]
    push_cast
    ring
  · simp [cexp, flxExp, e0]
    linarith

/--
Symmetric Sterbenz lemma for FLX.  If two positive representable values are within a factor of two,
their exact difference is representable, whichever operand is larger.
-/
theorem generic_format_FLX_sterbenz (prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx2y : x ≤ 2 * y) (hy2x : y ≤ 2 * x)
    (hxFmt : genericFormat β (flxExp prec) x)
    (hyFmt : genericFormat β (flxExp prec) y) :
    genericFormat β (flxExp prec) (x - y) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  rcases le_total y x with hyx | hxy
  · exact generic_format_FLX_sub_of_le_two_mul
      prec hprec hy hyx hx2y hxFmt hyFmt
  · have hdiff := generic_format_FLX_sub_of_le_two_mul
      prec hprec hx hxy hy2x hyFmt hxFmt
    have hneg := generic_format_neg (β := β) (fexp := flxExp prec) (y - x) hdiff
    simpa only [neg_sub] using hneg

end FloatLib.Floats.Formats.Flocq
