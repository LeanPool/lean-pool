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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Error.Exactness
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Theorems
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Rounding.Order

/-!
# Exactness of Addition Errors

For a valid, monotone exponent function and any nearest rounding rule, the error of adding two
representable values is itself representable. The proof aligns both operands on the smaller
canonical grid, represents the rounded result on that same grid, and uses nearestness to
control the canonical exponent of the error.

Nearestness is essential.  For directed rounding the statement fails: with radix `2` and three
digits of precision, rounding `1 - 2^(-10)` downward gives `7/8`, and the error `2^(-3) - 2^(-10)`
needs seven digits.

The representable error is the mathematical content of the TwoSum and FastTwoSum error-free
transformations: `x + y = round (x + y) + e` with `e` in the format.  The step-by-step exactness of
the floating-point operations that compute `e` in those algorithms is not formalized here.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ}
  [ValidExp fexp] [MonotoneExp fexp]

/-- Addition-error exactness when the first operand has the smaller canonical exponent. -/
private theorem add_round_error_generic_aux {rnd : ℝ → ℤ} [ValidRndToNearest rnd] {x y : ℝ}
    (hxy : cexp β fexp x ≤ cexp β fexp y)
    (hx : genericFormat β fexp x) (hy : genericFormat β fexp y) :
    genericFormat β fexp
      (round (β := β) (fexp := fexp) rnd (x + y) - (x + y)) := by
  let ex := cexp β fexp x
  let ey := cexp β fexp y
  obtain ⟨mx, hmx⟩ :=
    (generic_format_iff_scaled_mantissa_int (β := β) (fexp := fexp) x).mp hx
  obtain ⟨my, hmy⟩ :=
    (generic_format_iff_scaled_mantissa_int (β := β) (fexp := fexp) y).mp hy
  have hxrepr : x = (mx : ℝ) * bpow β ex := by
    have h := scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x
    rw [hmx] at h
    exact h.symm
  have hyrepr : y = (my : ℝ) * bpow β ey := by
    have h := scaled_mantissa_mul_bpow (β := β) (fexp := fexp) y
    rw [hmy] at h
    exact h.symm
  obtain ⟨scale, hscale⟩ := bpow_eq_natCast_of_nonneg β (ey - ex)
    (sub_nonneg.mpr hxy)
  let commonMantissa : ℤ := mx + my * Int.ofNat scale
  let common : FloatRep β := { mantissa := commonMantissa, exponent := ex }
  have hscaleCast : (((Int.ofNat scale : ℤ) : ℝ)) = (scale : ℝ) := by norm_num
  have hsum : x + y = toReal common := by
    rw [hxrepr, hyrepr]
    unfold common commonMantissa toReal
    rw [show ey = (ey - ex) + ex by ring, bpow.add_exp, hscale]
    simp only [Int.cast_add, Int.cast_mul, hscaleCast]
    ring
  obtain ⟨mr, hrounded⟩ :=
    round_toReal_exists_same_exponent
      (β := β) (fexp := fexp) rnd common
  let errorMantissa : ℤ := mr - commonMantissa
  let errorFloat : FloatRep β := { mantissa := errorMantissa, exponent := ex }
  let err := round (β := β) (fexp := fexp) rnd (x + y) - (x + y)
  have herr : err = toReal errorFloat := by
    unfold err errorFloat errorMantissa toReal
    rw [hsum, hrounded]
    unfold common
    simp only [toReal]
    push_cast
    ring
  by_cases herr0 : err = 0
  · change genericFormat β fexp err
    rw [herr0]
    exact generic_format_zero
  have hnear := (round_toNearest_point
    (β := β) (fexp := fexp) rnd (x + y)).2 y hy
  have herrLe : abs err ≤ abs x := by
    simpa [err] using hnear
  have hcexp : cexp β fexp err ≤ ex := by
    exact cexp_mono_abs β herr0 herrLe
  apply generic_format_of_toReal_of_cexp_le errorFloat err herr
  exact hcexp

/--
The addition error of two representable values under any nearest rounding rule is representable.

The rounding rule is implicit because it is determined by the conclusion; `nearestEven` is the
usual instance.  The statement needs a monotone exponent function and fails for directed rounding.
-/
theorem add_round_error_generic {rnd : ℝ → ℤ} [ValidRndToNearest rnd] {x y : ℝ}
    (hx : genericFormat β fexp x) (hy : genericFormat β fexp y) :
    genericFormat β fexp
      (round (β := β) (fexp := fexp) rnd (x + y) - (x + y)) := by
  rcases le_total (cexp β fexp x) (cexp β fexp y) with hxy | hyx
  · exact add_round_error_generic_aux hxy hx hy
  · simpa [add_comm] using
      (add_round_error_generic_aux (β := β) (fexp := fexp) (rnd := rnd) hyx hy hx)

/--
Error-free transformation of addition: the exact sum of two representable values is the rounded
sum plus a representable error term.

This is the specification met by the TwoSum and FastTwoSum algorithms.  The term `e` is
`x + y - round (x + y)`; its representability is `add_round_error_generic` up to sign.
-/
theorem add_round_exact_error {rnd : ℝ → ℤ} [ValidRndToNearest rnd] {x y : ℝ}
    (hx : genericFormat β fexp x) (hy : genericFormat β fexp y) :
    ∃ e : ℝ, genericFormat β fexp e ∧
      x + y = round (β := β) (fexp := fexp) rnd (x + y) + e := by
  refine ⟨x + y - round (β := β) (fexp := fexp) rnd (x + y), ?_, by ring⟩
  have herr := add_round_error_generic (β := β) (fexp := fexp) (rnd := rnd) hx hy
  simpa [neg_sub] using generic_format_neg (β := β) (fexp := fexp) _ herr

/-- Every FLT value lies on its minimum-exponent FIX grid. -/
theorem generic_format_FLT_to_FIX (emin prec : ℤ) (hprec : 0 < prec) {x : ℝ}
    (hx : genericFormat β (fltExp emin prec) x) :
    genericFormat β (fixExp emin) x := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  let : ValidExp (fixExp emin) := fixValidExp emin
  obtain ⟨m, hm⟩ :=
    (generic_format_iff_scaled_mantissa_int
      (β := β) (fexp := fltExp emin prec) x).mp hx
  let e := cexp β (fltExp emin prec) x
  have herepr : x = (m : ℝ) * bpow β e := by
    have h := scaled_mantissa_mul_bpow (β := β) (fexp := fltExp emin prec) x
    rw [hm] at h
    exact h.symm
  have hemin : emin ≤ e := by simp [e, cexp, fltExp]
  obtain ⟨scale, hscale⟩ := bpow_eq_natCast_of_nonneg β (e - emin)
    (sub_nonneg.mpr hemin)
  let f : FloatRep β := { mantissa := m * Int.ofNat scale, exponent := emin }
  have hxf : x = toReal f := by
    rw [herepr, show e = (e - emin) + emin by ring, bpow.add_exp, hscale]
    unfold f toReal
    have hcast : (((Int.ofNat scale : ℤ) : ℝ)) = (scale : ℝ) := by norm_num
    rw [Int.cast_mul, hcast]
    ring
  apply generic_format_of_toReal_of_cexp_le f x hxf
  simp [f, cexp, fixExp]

/-- A bounded FIX value is FLT-representable, including the radix-power boundary. -/
theorem generic_format_FIX_to_FLT_of_abs_le (emin prec : ℤ) (hprec : 0 < prec)
    {x : ℝ} (hx : genericFormat β (fixExp emin) x)
    (hbound : abs x ≤ bpow β (prec + emin)) :
    genericFormat β (fltExp emin prec) x := by
  let : ValidExp (fixExp emin) := fixValidExp emin
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  by_cases hx0 : x = 0
  · subst x
    exact generic_format_zero
  rcases hbound.eq_or_lt with heq | hlt
  · have habsFmt : genericFormat β (fltExp emin prec) (abs x) := by
      rw [heq]
      apply generic_format_bpow
      unfold fltExp
      rw [max_eq_left (by linarith)]
      linarith
    exact (generic_format_abs_iff (β := β) (fexp := fltExp emin prec) x).mp habsFmt
  · obtain ⟨f, hxf, hfe⟩ :=
      (generic_format_FIX_iff (β := β) emin x).mp hx
    apply generic_format_of_toReal_of_cexp_le f x hxf
    have hmag : magnitude β x ≤ prec + emin :=
      magnitude_le_of_abs_lt_bpow β x (prec + emin) hx0 hlt
    rw [hfe]
    simp [cexp, fltExp]
    linarith

/-- A sufficiently small sum of two FLT values is exactly FLT-representable. -/
theorem generic_format_FLT_add_small (emin prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ}
    (hx : genericFormat β (fltExp emin prec) x)
    (hy : genericFormat β (fltExp emin prec) y)
    (hbound : abs (x + y) ≤ bpow β (prec + emin)) :
    genericFormat β (fltExp emin prec) (x + y) := by
  let : ValidExp (fixExp emin) := fixValidExp emin
  have hxFix := generic_format_FLT_to_FIX (β := β) emin prec hprec hx
  have hyFix := generic_format_FLT_to_FIX (β := β) emin prec hprec hy
  obtain ⟨fx, hfx, ex⟩ := (generic_format_FIX_iff (β := β) emin x).mp hxFix
  obtain ⟨fy, hfy, ey⟩ := (generic_format_FIX_iff (β := β) emin y).mp hyFix
  let fsum : FloatRep β :=
    { mantissa := fx.mantissa + fy.mantissa, exponent := emin }
  have hsum : x + y = toReal fsum := by
    rw [hfx, hfy]
    unfold fsum toReal
    rw [ex, ey]
    push_cast
    ring
  have hsumFix : genericFormat β (fixExp emin) (x + y) := by
    apply (generic_format_FIX_iff (β := β) emin (x + y)).2
    exact ⟨fsum, hsum, rfl⟩
  exact generic_format_FIX_to_FLT_of_abs_le
    (β := β) emin prec hprec hsumFix hbound

end FloatLib.Floats.Formats.Flocq
