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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Error.Bounds
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Formats
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Magnitude

/-!
# Relative Error in the FLX Format

The unbounded-exponent `flxExp prec` format has a uniform relative-error bound.  For a nonzero
input, its ULP is `β^(magnitude x - prec)`, while the magnitude lower bound gives
`β^(magnitude x - 1) ≤ |x|`.  Their ratio is therefore at most `β^(1 - prec)`.

Combining the ULP ratio with nearest rounding gives the unit-roundoff bound
`u = β^(1 - prec) / 2`. The same bound holds for FLT inputs in the normal range. The sharper
classical bound `u / (1 + u)` for nearest rounding is not proved here.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/-- The relative size of one FLX ULP is at most `β^(1-prec)`. -/
theorem ulp_div_abs_le_FLX (prec : ℤ) (hprec : 0 < prec) (x : ℝ) (hx : x ≠ 0) :
    ulp β (flxExp prec) x / abs x ≤
      bpow β (1 - prec) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  rw [div_le_iff₀ (abs_pos.mpr hx)]
  rw [ulp.of_ne_zero β (flxExp prec) x hx]
  have hlower := bpow_magnitude_sub_one_le β x hx
  calc
    bpow β (cexp β (flxExp prec) x) =
        bpow β (1 - prec) * bpow β (magnitude β x - 1) := by
      rw [← bpow.add_exp]
      congr 1
      simp [cexp, flxExp]
    _ ≤ bpow β (1 - prec) * abs x :=
      mul_le_mul_of_nonneg_left hlower (bpow.nonneg β _)

/-- Nearest FLX rounding has relative error at most the unit roundoff `u = β^(1 - prec) / 2`. -/
theorem relative_error_round_FLX (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) (hx : x ≠ 0) :
    ErrorBounds.relativeError x
        (@round β (flxExp prec) rnd x) hx ≤
      bpow β (1 - prec) / 2 := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  calc
    ErrorBounds.relativeError x (round (β := β) (fexp := flxExp prec) rnd x) hx ≤
        ulp β (flxExp prec) x / (2 * abs x) :=
      ErrorBounds.relative_error_round_ulp rnd x hx
    _ = (ulp β (flxExp prec) x / abs x) / 2 := by
      field_simp [abs_ne_zero.mpr hx]
    _ ≤ bpow β (1 - prec) / 2 :=
      div_le_div_of_nonneg_right (ulp_div_abs_le_FLX prec hprec x hx) (by norm_num)

/--
Nearest FLX rounding admits the usual multiplicative model
`round x = x * (1 + δ)` with `|δ| ≤ u`, where `u = β^(1 - prec) / 2` is the unit roundoff.
-/
theorem round_relative_error_FLX (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) (hx : x ≠ 0) :
    ∃ δ : ℝ,
      abs δ ≤ bpow β (1 - prec) / 2 ∧
      @round β (flxExp prec) rnd x = x * (1 + δ) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  obtain ⟨δ, hδ, hround⟩ :=
    ErrorBounds.round_relative_error_ulp
      (β := β) (fexp := flxExp prec) rnd x hx
  refine ⟨δ, hδ.trans ?_, hround⟩
  calc
    ulp β (flxExp prec) x / (2 * abs x) =
        (ulp β (flxExp prec) x / abs x) / 2 := by
      field_simp [abs_ne_zero.mpr hx]
    _ ≤ bpow β (1 - prec) / 2 :=
      div_le_div_of_nonneg_right (ulp_div_abs_le_FLX prec hprec x hx) (by norm_num)

/-- In the normal range, one FLT ULP has relative size at most `β^(1-prec)`. -/
theorem ulp_div_abs_le_FLT_normal (emin prec : ℤ) (hprec : 0 < prec)
    (x : ℝ) (hx : x ≠ 0)
    (hnormal : bpow β (emin + prec - 1) ≤ abs x) :
    ulp β (fltExp emin prec) x / abs x ≤
      bpow β (1 - prec) := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  have hupper := abs_lt_bpow_magnitude β x hx
  have hpowLt : bpow β (emin + prec - 1) <
      bpow β (magnitude β x) := hnormal.trans_lt hupper
  have hnormalExp : emin ≤ magnitude β x - prec := by
    have := (bpow_lt_bpow_iff β _ _).mp hpowLt
    linarith
  rw [div_le_iff₀ (abs_pos.mpr hx)]
  rw [ulp.of_ne_zero β (fltExp emin prec) x hx]
  have hlower := bpow_magnitude_sub_one_le β x hx
  calc
    bpow β (cexp β (fltExp emin prec) x) =
        bpow β (1 - prec) * bpow β (magnitude β x - 1) := by
      rw [← bpow.add_exp]
      congr 1
      simp [cexp, fltExp, max_eq_left hnormalExp]
    _ ≤ bpow β (1 - prec) * abs x :=
      mul_le_mul_of_nonneg_left hlower (bpow.nonneg β _)

/-- Nearest FLT rounding has relative error at most `u = β^(1 - prec) / 2` in the normal range. -/
theorem relative_error_round_FLT_normal (emin prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) (hx : x ≠ 0)
    (hnormal : bpow β (emin + prec - 1) ≤ abs x) :
    ErrorBounds.relativeError x
        (@round β (fltExp emin prec) rnd x) hx ≤
      bpow β (1 - prec) / 2 := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  calc
    ErrorBounds.relativeError x
        (round (β := β) (fexp := fltExp emin prec) rnd x) hx ≤
        ulp β (fltExp emin prec) x / (2 * abs x) :=
      ErrorBounds.relative_error_round_ulp rnd x hx
    _ = (ulp β (fltExp emin prec) x / abs x) / 2 := by
      field_simp [abs_ne_zero.mpr hx]
    _ ≤ bpow β (1 - prec) / 2 :=
      div_le_div_of_nonneg_right
        (ulp_div_abs_le_FLT_normal emin prec hprec x hx hnormal) (by norm_num)

end FloatLib.Floats.Formats.Flocq
