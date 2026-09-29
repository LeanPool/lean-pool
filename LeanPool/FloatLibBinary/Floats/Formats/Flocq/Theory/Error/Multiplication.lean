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
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Error.Directed

/-!
# Exactness of Multiplication Errors

In the unbounded-exponent FLX format, the residual of a rounded product of two representable
operands is itself representable. The rounding mode may be any valid monotone integer rounding.

Working in FLX isolates the precision argument from overflow and underflow. Later bounded-format
error theorems can combine this exact residual fact with their own range hypotheses rather than
reproving the algebra of rounded multiplication for each exponent policy.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/-- Multiplication by a radix power preserves FLX representability. -/
theorem generic_format_FLX_mul_bpow (prec : ℤ) (hprec : 0 < prec)
    {x : ℝ} (hx : genericFormat β (flxExp prec) x)
    (e : ℤ) :
    genericFormat β (flxExp prec)
      (x * bpow β e) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  by_cases hx0 : x = 0
  · subst x
    simp
  obtain ⟨f, hxf, hf⟩ := canonical_exists_of_generic hx
  let shifted : FloatRep β := { mantissa := f.mantissa, exponent := f.exponent + e }
  have hvalue : x * bpow β e = toReal shifted := by
    rw [hxf]
    simp [shifted, toReal, bpow.add_exp]
    ring
  apply generic_format_of_toReal_of_cexp_le shifted _ hvalue
  have hmag : magnitude β (x * bpow β e) = magnitude β x + e := by
    rw [magnitude_mul_bpow β x e hx0]
  have hfexp : f.exponent = cexp β (flxExp prec) x := by
    rw [hxf]
    exact hf
  change cexp β (flxExp prec) (x * bpow β e) ≤ f.exponent + e
  rw [hfexp]
  simp [cexp, flxExp, hmag]
  linarith

/--
A nonzero rounded-product residual has a representation at the sum of the operand canonical
exponents. This is the exponent-carrying form needed by FLT underflow proofs.
-/
theorem mul_round_error_FLX_exists_repr (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRnd rnd] {x y : ℝ}
    (hx : genericFormat β (flxExp prec) x)
    (hy : genericFormat β (flxExp prec) y)
    (herr0 : @round β (flxExp prec) rnd (x * y) - x * y ≠ 0) :
    ∃ f : FloatRep β,
      @round β (flxExp prec) rnd (x * y) - x * y =
        toReal f ∧
      cexp β (flxExp prec)
          (@round β (flxExp prec) rnd (x * y) - x * y) ≤
        f.exponent ∧
      f.exponent = cexp β (flxExp prec) x +
        cexp β (flxExp prec) y := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  let product := x * y
  let rounded := round (β := β) (fexp := flxExp prec) rnd product
  let err := rounded - product
  have herr0' : err ≠ 0 := herr0
  have hp0 : product ≠ 0 := by
    intro hp0
    have hr0 : rounded = 0 := by
      unfold rounded
      rw [hp0]
      exact round_preserves_generic rnd 0 generic_format_zero
    exact herr0' (by simp [err, hr0, hp0])
  have hx0 : x ≠ 0 := by
    intro h
    exact hp0 (by simp [product, h])
  have hy0 : y ≠ 0 := by
    intro h
    exact hp0 (by simp [product, h])
  let ex := cexp β (flxExp prec) x
  let ey := cexp β (flxExp prec) y
  obtain ⟨mx, hmx⟩ :=
    (generic_format_iff_scaled_mantissa_int
      (β := β) (fexp := flxExp prec) x).mp hx
  obtain ⟨my, hmy⟩ :=
    (generic_format_iff_scaled_mantissa_int
      (β := β) (fexp := flxExp prec) y).mp hy
  have hxrepr : x = (mx : ℝ) * bpow β ex := by
    have h := scaled_mantissa_mul_bpow (β := β) (fexp := flxExp prec) x
    rw [hmx] at h
    exact h.symm
  have hyrepr : y = (my : ℝ) * bpow β ey := by
    have h := scaled_mantissa_mul_bpow (β := β) (fexp := flxExp prec) y
    rw [hmy] at h
    exact h.symm
  let exactProduct : FloatRep β := { mantissa := mx * my, exponent := ex + ey }
  have hproduct : product = toReal exactProduct := by
    unfold product exactProduct toReal
    rw [hxrepr, hyrepr, bpow.add_exp]
    push_cast
    ring
  obtain ⟨mr, hrounded⟩ :=
    round_toReal_exists_same_exponent
      (β := β) (fexp := flxExp prec) rnd exactProduct
  let errorFloat : FloatRep β :=
    { mantissa := mr - exactProduct.mantissa, exponent := ex + ey }
  have herr : err = toReal errorFloat := by
    unfold err rounded errorFloat toReal
    rw [hproduct, hrounded]
    simp only [exactProduct]
    simp only [toReal]
    push_cast
    ring
  have hinexact : rounded ≠ product := sub_ne_zero.mp herr0'
  have herrUlp : abs err < ulp β (flxExp prec) product := by
    exact round_abs_error_lt_ulp_of_inexact rnd hinexact
  have herrBpow : abs err < bpow β (cexp β (flxExp prec) product) := by
    simpa [ulp, hp0] using herrUlp
  have hmagErr : magnitude β err ≤ cexp β (flxExp prec) product :=
    magnitude_le_of_abs_lt_bpow β err _ herr0' herrBpow
  have hmagProduct : magnitude β product ≤
      magnitude β x + magnitude β y := by
    simpa [product] using magnitude_mul_le_add β hx0 hy0
  have hcexp : cexp β (flxExp prec) err ≤ ex + ey := by
    change magnitude β err - prec ≤
      (magnitude β x - prec) + (magnitude β y - prec)
    simp [cexp, flxExp] at hmagErr
    linarith
  exact ⟨errorFloat, herr, hcexp, rfl⟩

/-- The residual of a valid rounded FLX product is exactly FLX-representable. -/
theorem mul_round_error_FLX (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRnd rnd] {x y : ℝ}
    (hx : genericFormat β (flxExp prec) x)
    (hy : genericFormat β (flxExp prec) y) :
    genericFormat β (flxExp prec)
      (@round β (flxExp prec) rnd (x * y) - x * y) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  let err := round (β := β) (fexp := flxExp prec) rnd (x * y) - x * y
  by_cases herr0 : err = 0
  · change genericFormat β (flxExp prec) err
    rw [herr0]
    exact generic_format_zero
  obtain ⟨f, herr, hcexp, _⟩ :=
    mul_round_error_FLX_exists_repr (β := β) prec hprec rnd hx hy herr0
  apply generic_format_of_toReal_of_cexp_le f err herr
  exact hcexp

/-- Every FLT value is representable in the corresponding unbounded FLX format. -/
theorem generic_format_FLT_to_FLX (emin prec : ℤ) (hprec : 0 < prec) {x : ℝ}
    (hx : genericFormat β (fltExp emin prec) x) :
    genericFormat β (flxExp prec) x := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  apply generic_inclusion (fexp₁ := fltExp emin prec) (fexp₂ := flxExp prec)
  · intro e
    simp [fltExp, flxExp]
  · exact hx

/--
The residual of an FLT rounded product is FLT-representable when the exact product is zero or
has magnitude at least `β^(emin + 2*prec - 1)`. This sufficient bound keeps the residual
representation's exponent at or above `emin`.
-/
theorem mul_round_error_FLT (emin prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRnd rnd] {x y : ℝ}
    (hx : genericFormat β (fltExp emin prec) x)
    (hy : genericFormat β (fltExp emin prec) y)
    (hproduct : x * y ≠ 0 →
      bpow β (emin + 2 * prec - 1) ≤ abs (x * y)) :
    genericFormat β (fltExp emin prec)
      (@round β (fltExp emin prec) rnd (x * y) - x * y) := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  let product := x * y
  let roundFLT := round (β := β) (fexp := fltExp emin prec) rnd product
  let roundFLX := round (β := β) (fexp := flxExp prec) rnd product
  let err := roundFLT - product
  by_cases hp0 : product = 0
  · have hr0 : roundFLT = 0 := by
      unfold roundFLT
      rw [hp0]
      exact round_preserves_generic rnd 0 generic_format_zero
    change genericFormat β (fltExp emin prec) err
    simp [err, hr0, hp0]
  have hx0 : x ≠ 0 := by
    intro h
    exact hp0 (by simp [product, h])
  have hy0 : y ≠ 0 := by
    intro h
    exact hp0 (by simp [product, h])
  have hmagProduct : emin + 2 * prec ≤ magnitude β product := by
    have hlower := hproduct hp0
    have hupper := abs_lt_bpow_magnitude β product hp0
    have hpowers : bpow β (emin + 2 * prec - 1) <
        bpow β (magnitude β product) := hlower.trans_lt hupper
    have hexp := (bpow_lt_bpow_iff β _ _).mp hpowers
    linarith
  have hcexpEq : cexp β (fltExp emin prec) product =
      cexp β (flxExp prec) product := by
    simp [cexp, fltExp, flxExp, max_eq_left (by linarith :
      emin ≤ magnitude β product - prec)]
  have hroundEq : roundFLT = roundFLX := by
    unfold roundFLT roundFLX round scaledMantissa
    rw [hcexpEq]
  have hxFLX := generic_format_FLT_to_FLX (β := β) emin prec hprec hx
  have hyFLX := generic_format_FLT_to_FLX (β := β) emin prec hprec hy
  by_cases herr0 : err = 0
  · change genericFormat β (fltExp emin prec) err
    rw [herr0]
    exact generic_format_zero
  have herrFLX0 : roundFLX - product ≠ 0 := by simpa [err, hroundEq] using herr0
  obtain ⟨f, herr, hcexpFLX, hfexp⟩ :=
    mul_round_error_FLX_exists_repr
      (β := β) prec hprec rnd hxFLX hyFLX herrFLX0
  have hmagMul := magnitude_mul_le_add β hx0 hy0
  have hemin : emin ≤ f.exponent := by
    rw [hfexp]
    simp only [cexp, flxExp]
    have : emin + 2 * prec ≤ magnitude β x + magnitude β y := by
      exact hmagProduct.trans (by simpa [product] using hmagMul)
    linarith
  have hcexpFLT : cexp β (fltExp emin prec) err ≤ f.exponent := by
    have herrEq : err = roundFLX - product := by simp [err, hroundEq]
    have hflx : cexp β (flxExp prec) err ≤ f.exponent := by
      simpa [herrEq] using hcexpFLX
    change max (magnitude β err - prec) emin ≤ f.exponent
    apply max_le
    · simpa [cexp, flxExp] using hflx
    · exact hemin
  apply generic_format_of_toReal_of_cexp_le f err
  · simpa [err, hroundEq] using herr
  · exact hcexpFLT

/--
Multiplying an FLT-representable value by a radix power preserves representability when
`emin + prec - magnitude β x ≤ e`.
-/
theorem generic_format_FLT_mul_bpow (emin prec : ℤ) (hprec : 0 < prec)
    {x : ℝ} (hx : genericFormat β (fltExp emin prec) x) (e : ℤ)
    (hshift : emin + prec - magnitude β x ≤ e) :
    genericFormat β (fltExp emin prec)
      (x * bpow β e) := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  by_cases hx0 : x = 0
  · subst x
    simp
  obtain ⟨f, hxf, hf⟩ := canonical_exists_of_generic hx
  let shifted : FloatRep β := { mantissa := f.mantissa, exponent := f.exponent + e }
  have hvalue : x * bpow β e = toReal shifted := by
    rw [hxf]
    simp [shifted, toReal, bpow.add_exp]
    ring
  apply generic_format_of_toReal_of_cexp_le shifted _ hvalue
  have hmag := magnitude_mul_bpow β x e hx0
  have hfexp : f.exponent = cexp β (fltExp emin prec) x := by
    rw [hxf]
    exact hf
  change max (magnitude β (x * bpow β e) - prec) emin ≤ f.exponent + e
  rw [hmag, hfexp]
  simp only [cexp, fltExp]
  apply max_le
  · have hleft := add_le_add_right
      (le_max_left (magnitude β x - prec) emin) e
    linarith
  · have hbase : magnitude β x - prec ≤
        max (magnitude β x - prec) emin := le_max_left _ _
    linarith

/-- Nonnegative radix shifts preserve every FLT-representable value. -/
theorem generic_format_FLT_mul_bpow_of_nonneg (emin prec : ℤ) (hprec : 0 < prec)
    {x : ℝ} (hx : genericFormat β (fltExp emin prec) x) (e : ℤ) (he : 0 ≤ e) :
    genericFormat β (fltExp emin prec)
      (x * bpow β e) := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  by_cases hx0 : x = 0
  · subst x
    simp
  obtain ⟨f, hxf, hf⟩ := canonical_exists_of_generic hx
  let shifted : FloatRep β := { mantissa := f.mantissa, exponent := f.exponent + e }
  have hvalue : x * bpow β e = toReal shifted := by
    rw [hxf]
    simp [shifted, toReal, bpow.add_exp]
    ring
  apply generic_format_of_toReal_of_cexp_le shifted _ hvalue
  have hmag := magnitude_mul_bpow β x e hx0
  have hfexp : f.exponent = cexp β (fltExp emin prec) x := by
    rw [hxf]
    exact hf
  change max (magnitude β (x * bpow β e) - prec) emin ≤ f.exponent + e
  rw [hmag, hfexp]
  simp only [cexp, fltExp]
  apply max_le
  · have hleft := add_le_add_right
      (le_max_left (magnitude β x - prec) emin) e
    linarith
  · exact (le_max_right _ _).trans (le_add_of_nonneg_right he)

end FloatLib.Floats.Formats.Flocq
