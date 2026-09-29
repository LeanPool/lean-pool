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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Rounding.Generic
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Rounding.Predicates

/-!
# Order Theory for Generic Rounding

Monotonicity is subtle because two inputs may be scaled with different canonical exponents.  The
proof separates equal-grid inputs from inputs in different magnitude bins and uses the bounds from
`Rounding.Generic` in the latter case.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

omit [ValidExp fexp] in
/-- Rounding is monotone when both inputs use the same canonical exponent. -/
theorem round_le_of_cexp_eq (rnd : ℝ → ℤ) [ValidRnd rnd]
    {x y : ℝ} (hxy : x ≤ y) (he : cexp β fexp x = cexp β fexp y) :
    round (β := β) (fexp := fexp) rnd x ≤
      round (β := β) (fexp := fexp) rnd y := by
  have hs : scaledMantissa β fexp x ≤ scaledMantissa β fexp y := by
    rw [scaledMantissa_eq_div, scaledMantissa_eq_div, he]
    exact div_le_div_of_nonneg_right hxy (bpow.nonneg β _)
  have hm : rnd (scaledMantissa β fexp x) ≤
      rnd (scaledMantissa β fexp y) := ValidRnd.monotone _ _ hs
  have hmR : (rnd (scaledMantissa β fexp x) : ℝ) ≤
      (rnd (scaledMantissa β fexp y) : ℝ) := by exact_mod_cast hm
  unfold round toReal
  rw [he]
  exact mul_le_mul_of_nonneg_right hmR (bpow.nonneg β _)

/-- Positive generic rounding is monotone. -/
theorem round_mono_pos (rnd : ℝ → ℤ) [ValidRnd rnd]
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    round (β := β) (fexp := fexp) rnd x ≤
      round (β := β) (fexp := fexp) rnd y := by
  have hy : 0 < y := hx.trans_le hxy
  let ex := magnitude β x
  let ey := magnitude β y
  have hmag : ex ≤ ey := magnitude_mono_pos β hx hxy
  by_cases hySmall : ey ≤ fexp ey
  · have hconst := ((ValidExp.flocq_valid (fexp := fexp) ey).2 hySmall).2
    have hf : fexp ex = fexp ey := hconst ex (hmag.trans hySmall)
    apply round_le_of_cexp_eq rnd hxy
    simp [cexp, ex, ey, hf]
  · have hyLarge : fexp ey < ey := lt_of_not_ge hySmall
    by_cases heq : ex = ey
    · apply round_le_of_cexp_eq rnd hxy
      simp [cexp, ex, ey, heq]
    · have hmagLt : ex < ey := lt_of_le_of_ne hmag heq
      have hxUpper : round (β := β) (fexp := fexp) rnd x ≤
          bpow β (ey - 1) := by
        by_cases hxSmall : ex ≤ fexp ex
        · rcases round_pos_small_cases
            (β := β) (fexp := fexp) rnd x hx (by simpa [ex] using hxSmall) with hz | hp
          · rw [hz]
            exact bpow.nonneg β _
          · rw [hp]
            apply (bpow_le_bpow_iff β _ _).2
            have hfLt : fexp ex < ey := by
              by_contra hnot
              have hey : ey ≤ fexp ex := le_of_not_gt hnot
              have hconst := ((ValidExp.flocq_valid (fexp := fexp) ex).2 hxSmall).2
              have := hconst ey hey
              linarith
            linarith
        · have hxLarge : fexp ex < ex := lt_of_not_ge hxSmall
          have hb := (round_pos_large_bounds_and_generic
            (β := β) (fexp := fexp) rnd x hx (by simpa [ex] using hxLarge)).1.2
          exact hb.trans ((bpow_le_bpow_iff β _ _).2 (by linarith))
      have hyLower := (round_pos_large_bounds_and_generic
        (β := β) (fexp := fexp) rnd y hy (by simpa [ey] using hyLarge)).1.1
      exact hxUpper.trans (by simpa [ey] using hyLower)

omit [ValidExp fexp] in
/-- Rounding a nonnegative value with a valid mode produces a nonnegative value. -/
theorem round_nonneg (rnd : ℝ → ℤ) [ValidRnd rnd] {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ round (β := β) (fexp := fexp) rnd x := by
  have hs : 0 ≤ scaledMantissa β fexp x := by
    rw [scaledMantissa_eq_div]
    exact div_nonneg hx (bpow.nonneg β _)
  have hm : 0 ≤ rnd (scaledMantissa β fexp x) := by
    have := ValidRnd.monotone (rnd := rnd) 0 (scaledMantissa β fexp x) hs
    have hr0 : rnd 0 = 0 := by simpa using ValidRnd.id (rnd := rnd) (0 : ℤ)
    rwa [hr0] at this
  unfold round toReal
  exact mul_nonneg (by exact_mod_cast hm) (bpow.nonneg β _)

omit [ValidExp fexp] in
/-- Rounding a nonpositive value with a valid mode produces a nonpositive value. -/
theorem round_nonpos (rnd : ℝ → ℤ) [ValidRnd rnd] {x : ℝ} (hx : x ≤ 0) :
    round (β := β) (fexp := fexp) rnd x ≤ 0 := by
  have hs : scaledMantissa β fexp x ≤ 0 := by
    rw [scaledMantissa_eq_div]
    exact div_nonpos_of_nonpos_of_nonneg hx (bpow.nonneg β _)
  have hm : rnd (scaledMantissa β fexp x) ≤ 0 := by
    have := ValidRnd.monotone (rnd := rnd) (scaledMantissa β fexp x) 0 hs
    have hr0 : rnd 0 = 0 := by simpa using ValidRnd.id (rnd := rnd) (0 : ℤ)
    rwa [hr0] at this
  unfold round toReal
  exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hm) (bpow.nonneg β _)

/-- Generic rounding is monotone on all real inputs. -/
theorem round_mono (rnd : ℝ → ℤ) [ValidRnd rnd] {x y : ℝ} (hxy : x ≤ y) :
    round (β := β) (fexp := fexp) rnd x ≤
      round (β := β) (fexp := fexp) rnd y := by
  by_cases hx : 0 < x
  · exact round_mono_pos rnd hx hxy
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    by_cases hy : 0 < y
    · exact (round_nonpos rnd hx0).trans (round_nonneg rnd hy.le)
    · have hy0 : y ≤ 0 := le_of_not_gt hy
      by_cases hyz : y = 0
      · subst y
        exact (round_nonpos rnd hx0).trans (by
          have hr0 : round (β := β) (fexp := fexp) rnd 0 = 0 := by
            have hgeneric : genericFormat β fexp 0 := generic_format_zero
            exact round_preserves_generic rnd 0 hgeneric
          rw [hr0])
      · have hny : 0 < -y := neg_pos.mpr (lt_of_le_of_ne hy0 hyz)
        have hnegxy : -y ≤ -x := neg_le_neg hxy
        have hmono := round_mono_pos (β := β) (fexp := fexp)
          (negRound rnd) hny hnegxy
        have hxround := round_neg (β := β) (fexp := fexp) rnd (-x)
        have hyround := round_neg (β := β) (fexp := fexp) rnd (-y)
        simp only [neg_neg] at hxround hyround
        rw [hxround, hyround]
        exact neg_le_neg hmono

/-- A representable lower value remains below rounding of any larger input. -/
theorem generic_le_round (rnd : ℝ → ℤ) [ValidRnd rnd] {x y : ℝ}
    (hx : genericFormat β fexp x) (hxy : x ≤ y) :
    x ≤ round (β := β) (fexp := fexp) rnd y := by
  rw [← round_preserves_generic rnd x hx]
  exact round_mono rnd hxy

/-- Rounding of a smaller input remains below a representable upper value. -/
theorem round_le_generic (rnd : ℝ → ℤ) [ValidRnd rnd] {x y : ℝ}
    (hy : genericFormat β fexp y) (hxy : x ≤ y) :
    round (β := β) (fexp := fexp) rnd x ≤ y := by
  rw [← round_preserves_generic rnd y hy]
  exact round_mono rnd hxy

/-- Directed-down generic rounding selects the greatest representable value below its input. -/
theorem round_floor_point (x : ℝ) :
    RoundDownPoint (genericFormat β fexp) x
      (round (β := β) (fexp := fexp) floorRound x) := by
  refine ⟨generic_format_round floorRound x, round_floor_le x, ?_⟩
  intro g hg hgx
  exact generic_le_round floorRound hg hgx

/-- Directed-up generic rounding selects the least representable value above its input. -/
theorem round_ceil_point (x : ℝ) :
    RoundUpPoint (genericFormat β fexp) x
      (round (β := β) (fexp := fexp) ceilRound x) := by
  refine ⟨generic_format_round ceilRound x, le_round_ceil x, ?_⟩
  intro g hg hxg
  exact round_le_generic ceilRound hg hxg

/-- Generic truncation satisfies the toward-zero rounding specification. -/
theorem round_trunc_point (x : ℝ) :
    RoundTowardZeroPoint (genericFormat β fexp) x
      (round (β := β) (fexp := fexp) truncRound x) := by
  constructor
  · intro hx
    have hs : 0 ≤ scaledMantissa β fexp x := by
      rw [scaledMantissa_eq_div]
      exact div_nonneg hx (bpow.nonneg β _)
    have hr : round (β := β) (fexp := fexp) truncRound x =
        round (β := β) (fexp := fexp) floorRound x := by
      unfold round
      rw [truncRound_eq_floor hs]
    rw [hr]
    exact round_floor_point x
  · intro hx
    have hs : scaledMantissa β fexp x ≤ 0 := by
      rw [scaledMantissa_eq_div]
      exact div_nonpos_of_nonpos_of_nonneg hx (bpow.nonneg β _)
    have hr : round (β := β) (fexp := fexp) truncRound x =
        round (β := β) (fexp := fexp) ceilRound x := by
      unfold round
      rw [truncRound_eq_ceil hs]
    rw [hr]
    exact round_ceil_point x

/--
A nearest rounding rule selects an integer at least as close to the input as every other integer.

Only the half-unit bound of `ValidRndToNearest` is used: any other integer is at distance at least
one from the selected integer, hence at least one half from the input.
-/
theorem toNearest_is_nearest_integer (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) (n : ℤ) :
    abs ((rnd x : ℝ) - x) ≤ abs ((n : ℝ) - x) := by
  have hhalf := ValidRndToNearest.abs_sub_le_half (rnd := rnd) x
  by_cases hn : rnd x = n
  · rw [hn]
  · have hgap : (1 : ℝ) ≤ abs ((rnd x : ℝ) - (n : ℝ)) := by
      have h := Int.one_le_abs (sub_ne_zero.mpr hn)
      exact_mod_cast h
    have htri := abs_sub_le (rnd x : ℝ) x (n : ℝ)
    rw [abs_sub_comm (n : ℝ) x]
    linarith

omit [ValidExp fexp] in
/-- Nearest generic rounding is no farther from the input than any other integer rounding. -/
theorem round_toNearest_error_le (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (other : ℝ → ℤ)
    (x : ℝ) :
    abs (round (β := β) (fexp := fexp) rnd x - x) ≤
      abs (round (β := β) (fexp := fexp) other x - x) := by
  let s := scaledMantissa β fexp x
  let b := bpow β (cexp β fexp x)
  have hxb : x = s * b := by
    simpa [s, b] using (scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x).symm
  have hlocal := toNearest_is_nearest_integer rnd s (other s)
  have hb : 0 ≤ b := by simp [b, bpow.nonneg]
  have hscaled := mul_le_mul_of_nonneg_right hlocal hb
  have hnear : round (β := β) (fexp := fexp) rnd x - x =
      ((rnd s : ℝ) - s) * b := by
    unfold round toReal
    change (rnd s : ℝ) * b - x = ((rnd s : ℝ) - s) * b
    rw [hxb]
    ring
  have hother : round (β := β) (fexp := fexp) other x - x =
      ((other s : ℝ) - s) * b := by
    unfold round toReal
    change (other s : ℝ) * b - x = ((other s : ℝ) - s) * b
    rw [hxb]
    ring
  rw [hnear, hother, abs_mul, abs_mul, abs_of_nonneg hb]
  exact hscaled

omit [ValidExp fexp] in
/-- Nearest-even generic rounding is no farther from the input than any other integer rounding. -/
theorem round_nearestEven_error_le (rnd : ℝ → ℤ) (x : ℝ) :
    abs (round (β := β) (fexp := fexp) nearestEven x - x) ≤
      abs (round (β := β) (fexp := fexp) rnd x - x) :=
  round_toNearest_error_le nearestEven rnd x

/-- Every nearest rounding rule selects a globally nearest representable value. -/
theorem round_toNearest_point (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) :
    RoundNearestPoint (genericFormat β fexp) x
      (round (β := β) (fexp := fexp) rnd x) := by
  apply roundNearestPoint_of_down_up
    (round_floor_point (β := β) (fexp := fexp) x)
    (round_ceil_point (β := β) (fexp := fexp) x)
  · exact generic_format_round rnd x
  · exact round_toNearest_error_le rnd floorRound x
  · exact round_toNearest_error_le rnd ceilRound x

/-- Nearest-even rounding selects a globally nearest representable value. -/
theorem round_nearestEven_point (x : ℝ) :
    RoundNearestPoint (genericFormat β fexp) x
      (round (β := β) (fexp := fexp) nearestEven x) :=
  round_toNearest_point nearestEven x

end FloatLib.Floats.Formats.Flocq
