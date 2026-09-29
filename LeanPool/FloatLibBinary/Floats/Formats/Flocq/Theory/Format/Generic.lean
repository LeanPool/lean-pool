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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Magnitude
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Rounding.Core

/-!
# Generic format properties

The Flocq-style generic format describes representability through a radix and a canonical exponent
function, before choosing a concrete FIX, FLX, or FLT family. This module develops the closure and
representation facts needed by later rounding theory.

The layer is mathematical rather than executable: it gives binary-interchange and other format
implementations a common real-valued specification against which their exact integer algorithms
can be proved.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-- Magnitude is invariant under negation. -/
@[simp] theorem magnitude_neg (x : ℝ) : magnitude β (-x) = magnitude β x := by
  simp [magnitude]

omit [ValidExp fexp] in
/-- The canonical exponent is invariant under negation. -/
@[simp] theorem cexp_neg (x : ℝ) : cexp β fexp (-x) = cexp β fexp x := by
  simp [cexp]

omit [ValidExp fexp] in
/-- Negation negates the canonical scaled mantissa. -/
@[simp] theorem scaledMantissa_neg (x : ℝ) :
    scaledMantissa β fexp (-x) = -scaledMantissa β fexp x := by
  simp [scaledMantissa]

omit [ValidExp fexp] in
/-- Zero belongs to every valid generic format. -/
@[simp] theorem generic_format_zero : genericFormat β fexp 0 := by
  apply generic_format_of_scaled_mantissa_int (n := 0)
  simp [scaledMantissa]

omit [ValidExp fexp] in
/-- Generic formats are closed under negation. -/
theorem generic_format_neg (x : ℝ) (hx : genericFormat β fexp x) :
    genericFormat β fexp (-x) := by
  obtain ⟨n, hn⟩ :=
    (generic_format_iff_scaled_mantissa_int (β := β) (fexp := fexp) x).mp hx
  apply generic_format_of_scaled_mantissa_int (n := -n)
  simp [hn]

omit [ValidExp fexp] in
/-- A value is representable exactly when its negation is representable. -/
@[simp] theorem generic_format_neg_iff (x : ℝ) :
    genericFormat β fexp (-x) ↔ genericFormat β fexp x := by
  constructor
  · intro hx
    simpa using generic_format_neg (β := β) (fexp := fexp) (-x) hx
  · exact generic_format_neg (β := β) (fexp := fexp) x

omit [ValidExp fexp] in
/-- A value is representable exactly when its absolute value is representable. -/
theorem generic_format_abs_iff (x : ℝ) :
    genericFormat β fexp (abs x) ↔ genericFormat β fexp x := by
  rcases le_total 0 x with hx | hx
  · simp [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, generic_format_neg_iff]

omit [ValidExp fexp] in
/-- A radix power is representable whenever its canonical exponent is no larger than its
  exponent. -/
theorem generic_format_bpow (e : ℤ) (h : fexp (e + 1) ≤ e) :
    genericFormat β fexp (bpow β e) := by
  apply generic_format_of_scaled_mantissa_int
    (n := Int.ofNat (β.base ^ (e - fexp (e + 1)).toNat))
  have hd : 0 ≤ e - fexp (e + 1) := sub_nonneg.mpr h
  calc
    scaledMantissa β fexp (bpow β e) =
        bpow β e * bpow β (-fexp (e + 1)) := by
      simp [scaledMantissa, cexp]
    _ = bpow β (e - fexp (e + 1)) := by
      rw [← bpow.add_exp]
      congr 1
    _ = Int.ofNat (β.base ^ (e - fexp (e + 1)).toNat) := by
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hd
      rw [hk]
      simp [bpow, Numerics.Radix.toReal]

omit [ValidExp fexp] in
/--
A mantissa/exponent representation is generic when its stored exponent is at least the canonical
exponent selected for its value.
-/
theorem generic_format_of_toReal_of_cexp_le (f : FloatRep β) (x : ℝ)
    (hxf : x = toReal f) (he : cexp β fexp x ≤ f.exponent) :
    genericFormat β fexp x := by
  obtain ⟨n, hn⟩ := bpow_eq_natCast_of_nonneg β
    (f.exponent - cexp β fexp x) (sub_nonneg.mpr he)
  apply generic_format_of_scaled_mantissa_int (n := f.mantissa * Int.ofNat n)
  rw [scaledMantissa_eq_div]
  have hxfdiv : x / bpow β (cexp β fexp x) =
      toReal f / bpow β (cexp β fexp x) :=
    congrArg (fun y : ℝ => y / bpow β (cexp β fexp x)) hxf
  rw [hxfdiv, toReal]
  calc
    (f.mantissa : ℝ) * bpow β f.exponent /
        bpow β (cexp β fexp x) =
        (f.mantissa : ℝ) * bpow β (f.exponent - cexp β fexp x) := by
      rw [bpow.sub_exp]
      field_simp
    _ = (f.mantissa : ℝ) * n := by rw [hn]
    _ = (f.mantissa * Int.ofNat n : ℤ) := by norm_num

omit [ValidExp fexp] in
/-- A positive representable value uses a canonical exponent strictly below its magnitude. -/
theorem cexp_lt_magnitude_of_pos_generic {x : ℝ} (hx : 0 < x)
    (hfmt : genericFormat β fexp x) :
    cexp β fexp x < magnitude β x := by
  obtain ⟨n, hn⟩ := scaled_mantissa_int_of_generic
    (β := β) (fexp := fexp) x hfmt
  have hbpos := bpow.pos β (cexp β fexp x)
  have hspos : 0 < scaledMantissa β fexp x := by
    rw [scaledMantissa_eq_div]
    positivity
  have hnpos : 0 < n := by
    exact_mod_cast (show (0 : ℝ) < n by simpa [hn] using hspos)
  by_contra hnot
  have hmagle : magnitude β x ≤ cexp β fexp x := le_of_not_gt hnot
  have hxUpper : x < bpow β (magnitude β x) := by
    simpa [abs_of_pos hx] using (magnitude_spec β x hx.ne').2
  have hslt : scaledMantissa β fexp x < 1 := by
    rw [scaledMantissa_eq_div, div_lt_one hbpos]
    exact hxUpper.trans_le ((bpow_le_bpow_iff β _ _).2 hmagle)
  have hnlt : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by simpa [hn] using hslt)
  exact (not_lt_of_ge (Int.add_one_le_iff.mpr hnpos)) hnlt

omit [ValidExp fexp] in
/-- Representability of `β^e` forces its canonical exponent to be at most `e`. -/
theorem fexp_succ_le_of_generic_bpow (e : ℤ)
    (hfmt : genericFormat β fexp (bpow β e)) : fexp (e + 1) ≤ e := by
  have h := cexp_lt_magnitude_of_pos_generic
    (β := β) (fexp := fexp) (bpow.pos β e) hfmt
  simp [cexp] at h
  linarith

/-- If `β^e` is representable, the exponent selected for the bin below it is at most `e`. -/
theorem fexp_le_of_generic_bpow (e : ℤ)
    (hfmt : genericFormat β fexp (bpow β e)) : fexp e ≤ e := by
  have hnext := fexp_succ_le_of_generic_bpow (β := β) (fexp := fexp) e hfmt
  by_contra hnot
  have heLt : e < fexp e := lt_of_not_ge hnot
  have heSucc : e + 1 ≤ fexp e := Int.add_one_le_iff.mpr heLt
  have hconst := ((ValidExp.flocq_valid (fexp := fexp) e).2 heLt.le).2 (e + 1) heSucc
  linarith

/--
A value representable with `fexp₁` remains representable with `fexp₂` when the second canonical
exponent is no larger at that value's magnitude.  The condition is local because representability
of `x` only depends on the exponent selected at `magnitude x`.
-/
theorem generic_inclusion_mag {fexp₁ fexp₂ : ℤ → ℤ}
    {x : ℝ}
    (hexp : x ≠ 0 → fexp₂ (magnitude β x) ≤ fexp₁ (magnitude β x))
    (hx : genericFormat β fexp₁ x) : genericFormat β fexp₂ x := by
  by_cases hx0 : x = 0
  · subst x
    exact generic_format_zero
  obtain ⟨n, hn⟩ := scaled_mantissa_int_of_generic
    (β := β) (fexp := fexp₁) x hx
  let f : FloatRep β :=
    { mantissa := n, exponent := cexp β fexp₁ x }
  have hxf : x = toReal f := by
    have hrepr := scaled_mantissa_mul_bpow (β := β) (fexp := fexp₁) x
    rw [hn] at hrepr
    exact hrepr.symm
  apply generic_format_of_toReal_of_cexp_le f x hxf
  change fexp₂ (magnitude β x) ≤ fexp₁ (magnitude β x)
  exact hexp hx0

/-- Pointwise-smaller exponent selection defines a containing generic format. -/
theorem generic_inclusion {fexp₁ fexp₂ : ℤ → ℤ}
    (hexp : ∀ e, fexp₂ e ≤ fexp₁ e) {x : ℝ}
    (hx : genericFormat β fexp₁ x) : genericFormat β fexp₂ x :=
  generic_inclusion_mag (fun _ => hexp _) hx

omit [ValidExp fexp] in
/-- No generic-format value lies strictly between consecutive points on its canonical grid. -/
theorem generic_format_discrete (x : ℝ) (m : ℤ)
    (hlower : (m : ℝ) * bpow β (cexp β fexp x) < x)
    (hupper : x < ((m + 1 : ℤ) : ℝ) * bpow β (cexp β fexp x)) :
    ¬genericFormat β fexp x := by
  intro hx
  obtain ⟨n, hn⟩ := scaled_mantissa_int_of_generic
    (β := β) (fexp := fexp) x hx
  have hb : 0 < bpow β (cexp β fexp x) := bpow.pos β _
  have hrepr := scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x
  rw [hn] at hrepr
  have hlower' : (m : ℝ) * bpow β (cexp β fexp x) <
      (n : ℝ) * bpow β (cexp β fexp x) := hlower.trans_eq hrepr.symm
  have hupper' : (n : ℝ) * bpow β (cexp β fexp x) <
      ((m + 1 : ℤ) : ℝ) * bpow β (cexp β fexp x) := hrepr.trans_lt hupper
  have hmnR : (m : ℝ) < (n : ℝ) := by
    nlinarith [hlower']
  have hnmR : (n : ℝ) < ((m + 1 : ℤ) : ℝ) := by
    nlinarith [hupper']
  have hmn : m < n := by exact_mod_cast hmnR
  have hnm : n < m + 1 := by exact_mod_cast hnmR
  linarith

omit [ValidExp fexp] in
/-- Every generic-format value has a canonical mantissa/exponent representation. -/
theorem canonical_exists_of_generic {x : ℝ} (hx : genericFormat β fexp x) :
    ∃ f : FloatRep β, x = toReal f ∧ Canonical β fexp f := by
  let f : FloatRep β :=
    { mantissa := ⌊scaledMantissa β fexp x⌋
      exponent := cexp β fexp x }
  refine ⟨f, hx, ?_⟩
  unfold Canonical
  change cexp β fexp x = cexp β fexp (toReal f)
  rw [← hx]

omit [ValidExp fexp] in
/-- The real value of a canonical representation belongs to its generic format. -/
theorem generic_format_of_canonical (f : FloatRep β)
    (hf : Canonical β fexp f) :
    genericFormat β fexp (toReal f) := by
  apply generic_format_of_toReal_of_cexp_le f (toReal f) rfl
  exact hf.ge

omit [ValidExp fexp] in
/-- Canonical representations of the same real value are equal. -/
theorem canonical_unique {f g : FloatRep β}
    (hf : Canonical β fexp f) (hg : Canonical β fexp g)
    (hval : toReal f = toReal g) : f = g := by
  have hexp : f.exponent = g.exponent := by
    rw [hf, hg, hval]
  have hmant : f.mantissa = g.mantissa := by
    have hb : 0 < bpow β f.exponent := bpow.pos β _
    have hreal : (f.mantissa : ℝ) * bpow β f.exponent =
        (g.mantissa : ℝ) * bpow β f.exponent := by
      simpa [toReal, hexp] using hval
    have hcast : (f.mantissa : ℝ) = (g.mantissa : ℝ) := by nlinarith
    exact_mod_cast hcast
  cases f
  cases g
  simp_all

end FloatLib.Floats.Formats.Flocq
