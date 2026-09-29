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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Generic
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Rounding.Properties

/-!
# Rounding Into A Generic Format

Rounding any real with a valid integer-rounding rule produces a value in the selected generic
format. The proof separates inputs whose magnitude is at most the selected exponent from those
above it.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-- The `Valid_exp` consequence used when the input magnitude is below the selected exponent. -/
theorem validExp_small {e : ℤ} (h : e ≤ fexp e) : fexp (fexp e + 1) ≤ fexp e :=
  ((ValidExp.flocq_valid (fexp := fexp) e).2 h).1

/-- The `Valid_exp` consequence used when the selected exponent is below the input magnitude. -/
theorem validExp_large {e : ℤ} (h : fexp e < e) : fexp (e + 1) ≤ e :=
  (ValidExp.flocq_valid (fexp := fexp) e).1 h

omit [ValidExp fexp] in
/-- Positive inputs in the small-magnitude regime round either to zero or to one radix power. -/
theorem round_pos_small_cases (rnd : ℝ → ℤ) [ValidRnd rnd]
    (x : ℝ) (hx : 0 < x) (hsmall : magnitude β x ≤ fexp (magnitude β x)) :
    round (β := β) (fexp := fexp) rnd x = 0 ∨
      round (β := β) (fexp := fexp) rnd x =
        bpow β (fexp (magnitude β x)) := by
  let ex := magnitude β x
  let e := fexp ex
  let s := scaledMantissa β fexp x
  have hxne : x ≠ 0 := ne_of_gt hx
  have hbpowPos : 0 < bpow β e := bpow.pos β e
  have hcexp : cexp β fexp x = e := rfl
  have hsdiv : s = x / bpow β e := by
    simpa [s, hcexp] using scaledMantissa_eq_div (β := β) (fexp := fexp) x
  have hspos : 0 < s := by rw [hsdiv]; positivity
  have hxUpper : x < bpow β ex := by
    simpa [ex, abs_of_pos hx] using (magnitude_spec β x hxne).2
  have hbpowMono : bpow β ex ≤ bpow β e := by
    exact (bpow_le_bpow_iff β ex e).2 hsmall
  have hslt : s < 1 := by
    rw [hsdiv, div_lt_one hbpowPos]
    exact hxUpper.trans_le hbpowMono
  have hfloor : floorRound s = 0 := by
    unfold floorRound
    exact Int.floor_eq_iff.mpr ⟨by exact_mod_cast hspos.le, by simpa using hslt⟩
  have hceil : ceilRound s = 1 := by
    unfold ceilRound
    exact Int.ceil_eq_iff.mpr ⟨by simpa using hspos, by exact_mod_cast hslt.le⟩
  have hm0 : 0 ≤ rnd s := by
    simpa [hfloor] using floor_le_valid_round (rnd := rnd) s
  have hm1 : rnd s ≤ 1 := by
    simpa [hceil] using valid_round_le_ceil (rnd := rnd) s
  have hm : rnd s = 0 ∨ rnd s = 1 := by
    by_cases hzero : rnd s = 0
    · exact Or.inl hzero
    · right
      have hpos : 0 < rnd s := lt_of_le_of_ne hm0 (Ne.symm hzero)
      exact le_antisymm hm1 (by simpa using Int.add_one_le_iff.mpr hpos)
  rcases hm with hm | hm
  · have hy : round (β := β) (fexp := fexp) rnd x = 0 := by
      simp [round, toReal, s, hm]
    exact Or.inl hy
  · have hy : round (β := β) (fexp := fexp) rnd x = bpow β e := by
      simp [round, toReal, s, hm, hcexp]
    exact Or.inr (by simpa [e, ex] using hy)

/-- Rounding in the small-magnitude regime produces a generic-format value. -/
theorem generic_format_round_pos_small (rnd : ℝ → ℤ) [ValidRnd rnd]
    (x : ℝ) (hx : 0 < x) (hsmall : magnitude β x ≤ fexp (magnitude β x)) :
    genericFormat β fexp (round (β := β) (fexp := fexp) rnd x) := by
  rcases round_pos_small_cases (β := β) (fexp := fexp) rnd x hx hsmall with hy | hy
  · rw [hy]
    exact generic_format_zero
  · rw [hy]
    exact generic_format_bpow _ (validExp_small (fexp := fexp) hsmall)

/--
In the large-magnitude regime, the rounded value lies between the endpoints of the input
magnitude bin, including the upper endpoint, and belongs to the generic format.
-/
theorem round_pos_large_bounds_and_generic (rnd : ℝ → ℤ) [ValidRnd rnd]
    (x : ℝ) (hx : 0 < x) (hlarge : fexp (magnitude β x) < magnitude β x) :
    (bpow β (magnitude β x - 1) ≤
        round (β := β) (fexp := fexp) rnd x ∧
      round (β := β) (fexp := fexp) rnd x ≤
        bpow β (magnitude β x)) ∧
      genericFormat β fexp (round (β := β) (fexp := fexp) rnd x) := by
  set ex := magnitude β x with hex
  set e := fexp ex with he
  set s := scaledMantissa β fexp x with hs
  have hxne : x ≠ 0 := hx.ne'
  have hbpowPos : 0 < bpow β e := bpow.pos β e
  have hsdiv : s = x / bpow β e := scaledMantissa_eq_div (β := β) (fexp := fexp) x
  have hxLower : bpow β (ex - 1) ≤ x := by
    simpa [abs_of_pos hx] using (magnitude_spec β x hxne).1
  have hxUpper : x < bpow β ex := by
    simpa [abs_of_pos hx] using (magnitude_spec β x hxne).2
  obtain ⟨nLower, hnLower⟩ := bpow_eq_natCast_of_nonneg β (ex - 1 - e) (by linarith)
  obtain ⟨nUpper, hnUpper⟩ := bpow_eq_natCast_of_nonneg β (ex - e) (by linarith)
  have hsLower : (nLower : ℝ) ≤ s := by
    rw [← hnLower, bpow.sub_exp, hsdiv]
    exact div_le_div_of_nonneg_right hxLower hbpowPos.le
  have hsUpper : s < (nUpper : ℝ) := by
    rw [← hnUpper, bpow.sub_exp, hsdiv]
    exact div_lt_div_of_pos_right hxUpper hbpowPos
  have hmLower : (nLower : ℤ) ≤ rnd s := by
    have hid : rnd (nLower : ℝ) = (nLower : ℤ) := by
      simpa using ValidRnd.id (rnd := rnd) (nLower : ℤ)
    rw [← hid]
    exact ValidRnd.monotone (rnd := rnd) _ _ hsLower
  have hmUpper : rnd s ≤ (nUpper : ℤ) :=
    (valid_round_le_ceil (rnd := rnd) s).trans (Int.ceil_le.mpr (by simpa using hsUpper.le))
  have hnLowerOne : (1 : ℝ) ≤ nLower := by
    rw [← hnLower]
    exact one_le_zpow₀ (Numerics.Radix.gt_one β).le (by linarith)
  have hmPos : (0 : ℝ) < rnd s := by
    have hmLowerR : (nLower : ℝ) ≤ (rnd s : ℝ) := by exact_mod_cast hmLower
    linarith
  have hy : round (β := β) (fexp := fexp) rnd x = (rnd s : ℝ) * bpow β e := rfl
  have hyLower : bpow β (ex - 1) ≤ round (β := β) (fexp := fexp) rnd x := by
    rw [hy, show ex - 1 = (ex - 1 - e) + e by ring, bpow.add_exp, hnLower]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmLower) hbpowPos.le
  have hyUpper : round (β := β) (fexp := fexp) rnd x ≤ bpow β ex := by
    rw [hy, show ex = (ex - e) + e by ring, bpow.add_exp, hnUpper]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmUpper) hbpowPos.le
  refine ⟨⟨hyLower, hyUpper⟩, ?_⟩
  rcases hyUpper.eq_or_lt with hyEq | hyLt
  · rw [hyEq]
    exact generic_format_bpow ex (validExp_large (fexp := fexp) hlarge)
  · have hyPos : 0 < round (β := β) (fexp := fexp) rnd x := by
      rw [hy]
      exact mul_pos hmPos hbpowPos
    have hmagY : magnitude β (round (β := β) (fexp := fexp) rnd x) = ex :=
      magnitude_eq_of_bpow_bounds β _ ex hyPos.ne'
        (by simpa [abs_of_pos hyPos] using hyLower) (by simpa [abs_of_pos hyPos] using hyLt)
    apply generic_format_of_scaled_mantissa_int (n := rnd s)
    rw [scaledMantissa_eq_div, show cexp β fexp (round (β := β) (fexp := fexp) rnd x) = e by
      simp [cexp, hmagY, he], hy]
    exact mul_div_cancel_right₀ _ (bpow.ne_zero β e)

/-- Rounding in the large-magnitude regime produces a generic-format value. -/
theorem generic_format_round_pos_large (rnd : ℝ → ℤ) [ValidRnd rnd]
    (x : ℝ) (hx : 0 < x) (hlarge : fexp (magnitude β x) < magnitude β x) :
    genericFormat β fexp (round (β := β) (fexp := fexp) rnd x) :=
  (round_pos_large_bounds_and_generic
    (β := β) (fexp := fexp) rnd x hx hlarge).2

/-- Every positive real rounds into the selected generic format. -/
theorem generic_format_round_pos (rnd : ℝ → ℤ) [ValidRnd rnd]
    (x : ℝ) (hx : 0 < x) :
    genericFormat β fexp (round (β := β) (fexp := fexp) rnd x) := by
  by_cases hsmall : magnitude β x ≤ fexp (magnitude β x)
  · exact generic_format_round_pos_small rnd x hx hsmall
  · exact generic_format_round_pos_large rnd x hx (lt_of_not_ge hsmall)

/-- Conjugate a rounding rule by negation. -/
def negRound (rnd : ℝ → ℤ) : ℝ → ℤ := fun x => -rnd (-x)

instance negRoundValid (rnd : ℝ → ℤ) [ValidRnd rnd] :
    ValidRnd (negRound rnd) where
  monotone := by
    intro x y hxy
    exact neg_le_neg (ValidRnd.monotone (rnd := rnd) (-y) (-x) (neg_le_neg hxy))
  id := by
    intro n
    have h : rnd (-(n : ℝ)) = -n := by
      simpa using ValidRnd.id (rnd := rnd) (-n)
    simp [negRound, h]

omit [ValidExp fexp] in
/-- Rounding a negated input is negated rounding with the conjugate integer rule. -/
theorem round_neg (rnd : ℝ → ℤ) (x : ℝ) :
    round (β := β) (fexp := fexp) rnd (-x) =
      -round (β := β) (fexp := fexp) (negRound rnd) x := by
  simp [round, toReal, negRound]

/-- Rounding any real produces a value in the selected generic format. -/
theorem generic_format_round (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    genericFormat β fexp (round (β := β) (fexp := fexp) rnd x) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hpos : 0 < -x := neg_pos.mpr hx
    have hgeneric :=
      generic_format_round_pos (β := β) (fexp := fexp) (negRound rnd) (-x) hpos
    have hround := round_neg (β := β) (fexp := fexp) rnd (-x)
    simp only [neg_neg] at hround
    rw [hround]
    exact generic_format_neg _ hgeneric
  · subst x
    have hr0 : rnd 0 = 0 := by simpa using ValidRnd.id (rnd := rnd) (0 : ℤ)
    have hround : round (β := β) (fexp := fexp) rnd 0 = 0 := by
      simp [round, scaledMantissa, toReal, hr0]
    rw [hround]
    exact generic_format_zero
  · exact generic_format_round_pos rnd x hx

end FloatLib.Floats.Formats.Flocq
