/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Proof.Region
public import LeanPool.Ratpoints.Proof.Sturm

import LeanPool.Ratpoints.Mathlib.Data.List.Chain
import LeanPool.Ratpoints.Proof.Bits
import LeanPool.Ratpoints.Proof.Double

/-!
# The intervals of the Sturm step

The structure of the intervals that the Sturm step (`Ratpoints.Sturm.computeSturm`) leaves, over the
values of the ends of their doubles: the bisection (`Ratpoints.Sturm.iterate`) at a depth of at most
`55`, where the search clamps it, meets only intervals of four shapes (`Ratpoints.Sturm.EndsWF`):
the ends at infinity `∓LONG_MAX` with the exponent `0`, finite ends `n / 2 ^ e` with `|n| ≤ 2 ^ 53`
and `0 ≤ e ≤ 55`, increasing, whose midpoints (`Ratpoints.Sturm.midpoint`) the `long`s compute
without overflow strictly between the ends (`Ratpoints.Sturm.EndsWF.halves`); the doubles
`ldexp((double)n, -e)` of the ends are exact, `±2 ^ 63` at infinity
(`Ratpoints.Sturm.EndsWF.hasValue_left`), so that the intervals it keeps, joined where one ends at
the beginning of the next (`Ratpoints.Sturm.AreIntervals.addInterval`), are closed, increasing and
strictly apart (`Ratpoints.Sturm.AreIntervals`, `Ratpoints.Sturm.iterate_wf`). Their intersection
with well-formed intervals of the caller (`Ratpoints.Sturm.intersectList`, the loop of
`Ratpoints.Sturm.intersect`) is well formed, inside both, and holds every value that lies in both
(`Ratpoints.Sturm.intervalsWF_intersectList`,
`Ratpoints.Sturm.inIntervals_of_inIntervals_intersectList`,
`Ratpoints.Sturm.inIntervals_intersectList`); hence the Sturm step leaves well-formed intervals
inside the caller's (`Ratpoints.Sturm.computeSturm_wf`).

## Main definitions

* `Ratpoints.Sturm.HasValue`: a double that is not a NaN, with its value.
* `Ratpoints.Sturm.endValue`: the value of the double of an end of the bisection.
* `Ratpoints.Sturm.EndsWF`: the intervals that the bisection meets at a depth.
* `Ratpoints.Sturm.IsInterval`, `Ratpoints.Sturm.EndsBefore`: an interval of doubles without a NaN
  whose ends are in order, and one interval ending strictly before another begins.
* `Ratpoints.Sturm.AreIntervals`: intervals of doubles without a NaN, increasing and strictly apart,
  equivalently well formed (`Ratpoints.Sturm.intervalsWF_domainBits_iff`).

## Main statements

* `Ratpoints.Sturm.EndsWF.halves`: the halves of an interval of the bisection at its midpoint are
  intervals of the bisection at the next depth.
* `Ratpoints.Sturm.EndsWF.hasValue_left`, `Ratpoints.Sturm.EndsWF.hasValue_right`: the doubles of
  the ends are exact.
* `Ratpoints.Sturm.iterate_wf`: the intervals that the bisection keeps are well formed.
* `Ratpoints.Sturm.intervalsWF_intersectList`,
  `Ratpoints.Sturm.inIntervals_of_inIntervals_intersectList`,
  `Ratpoints.Sturm.inIntervals_intersectList`, `Ratpoints.Sturm.length_intersectList_le`: the
  intersection is well formed, inside both lists, holds what lies in both, and has fewer intervals
  than the two lists together.
* `Ratpoints.Sturm.computeSturm_wf`: the Sturm step leaves well-formed intervals inside the
  caller's.
-/

@[expose] public section

namespace Ratpoints

namespace Sturm

theorem toInt_longMax : longMax.toInt = 2 ^ 63 - 1 := by decide

theorem toInt_neg_longMax : (-longMax).toInt = -(2 ^ 63 - 1) := by decide

/-- The value of an end `n / 2 ^ e` of the bisection, `±2 ^ 63` for the ends `±LONG_MAX` at
infinity, as their doubles have it. -/
def endValue (n e : Int64) : ℚ :=
  if n = longMax then 2 ^ 63 else if n = -longMax then -2 ^ 63 else n.toInt * 2 ^ (-e.toInt)

/-- The double `x` is not a NaN and has the value `q`. -/
abbrev HasValue (x : Double) (q : ℚ) : Prop :=
  x.isNaN = false ∧ doubleValue x.bits = (q : WithBotTop ℚ)

/-- The double `ldexp((double)n, -e)` of an end `n / 2 ^ e` of the bisection is exact for
`|n| ≤ 2 ^ 53` and `0 ≤ e ≤ 64`. -/
theorem hasValue_ldexp_ofInt64 {n e : Int64} (hn : n.toInt.natAbs ≤ 2 ^ 53) (he0 : 0 ≤ e.toInt)
    (he : e.toInt ≤ 64) :
    HasValue ((Double.ofInt64 n).ldexp (-e.toInt)) (n.toInt * 2 ^ (-e.toInt)) := by
  obtain ⟨hf, hr⟩ := Double.ofInt64_exact hn
  rcases eq_or_ne n.toInt 0 with h0 | h0
  · have hz : (Double.ofInt64 n).isZero = true := Double.isZero_eq_true_iff.mpr (by simp [hr, h0])
    have hl : (Double.ofInt64 n).ldexp (-e.toInt) = Double.ofInt64 n := by
      simp [Double.ldexp, hz]
    rw [hl, h0]
    refine ⟨Double.isNaN_eq_false_of_isFinite hf, ?_⟩
    rw [Double.doubleValue_eq_toRat hf, hr, h0]; simp
  have hr0 : (Double.ofInt64 n).toRat ≠ 0 := by rw [hr]; exact Int.cast_ne_zero.mpr h0
  have h1 : (1 : ℚ) ≤ |(n.toInt : ℚ)| := mod_cast Int.one_le_abs h0
  have h2 : |(n.toInt : ℚ)| ≤ 2 ^ 53 := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact mod_cast hn
  have h3 : (2 : ℚ) ^ (-e.toInt) ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two (by lia)
  have h4 : (2 : ℚ) ^ (-1022 : ℤ) ≤ 2 ^ (-e.toInt) := zpow_le_zpow_right₀ one_le_two (by lia)
  have h5 : (0 : ℚ) < 2 ^ (-e.toInt) := zpow_pos two_pos _
  obtain ⟨hf', -, hr'⟩ := Double.ldexp_exact (n := -e.toInt) hf hr0
    (by rw [hr]; exact h4.trans (le_mul_of_one_le_left h5.le h1))
    (by rw [hr]; calc |(n.toInt : ℚ)| * 2 ^ (-e.toInt) ≤ 2 ^ (53 : ℤ) * 1 := by gcongr; simpa
      _ < 2 ^ (1023 : ℤ) := by rw [mul_one]; exact zpow_lt_zpow_right₀ one_lt_two (by norm_num))
  exact ⟨Double.isNaN_eq_false_of_isFinite hf', by rw [Double.doubleValue_eq_toRat hf', hr', hr]⟩

/-- The end `LONG_MAX` at `+∞` of the bisection has the double `2 ^ 63`. -/
theorem hasValue_ldexp_ofInt64_longMax :
    HasValue ((Double.ofInt64 longMax).ldexp (-(0 : Int64).toInt)) (2 ^ 63) := by
  have h : ((Double.ofInt64 longMax).ldexp (-(0 : Int64).toInt)).bits = 0x43e0000000000000 := by
    decide
  refine ⟨by decide, ?_⟩
  rw [h]
  decide +kernel

/-- The end `-LONG_MAX` at `-∞` of the bisection has the double `-2 ^ 63`. -/
theorem hasValue_ldexp_ofInt64_neg_longMax :
    HasValue ((Double.ofInt64 (-longMax)).ldexp (-(0 : Int64).toInt)) (-2 ^ 63) := by
  have h : ((Double.ofInt64 (-longMax)).ldexp (-(0 : Int64).toInt)).bits = 0xc3e0000000000000 := by
    decide
  refine ⟨by decide, ?_⟩
  rw [h]
  decide +kernel

/-- The interval from `nl / 2 ^ del` to `nr / 2 ^ der` of the bisection at the depth `depth`, as
`Ratpoints.Sturm.iterate` meets it when the depth is at most `55`: one of the four shapes of the
intervals of the bisection (the whole line, the ends at infinity `∓LONG_MAX` with the exponent `0`,
an infinite interval with the finite end `0` or on its side of `0`, two finite ends with the
exponent `0` when they have the same exponent), the exponents from `0` to the depth, the finite
ends, scaled to the larger exponent, at most `2 ^ depth / 4` in absolute value (from the depth `1`
on), and the ends increasing. -/
structure EndsWF (depth : ℕ) (nl nr del der : Int64) : Prop where
  /-- The four shapes: the whole line; the end at `-∞` with a finite upper end `≤ 0`; a finite
  lower end `≥ 0` with the end at `+∞`, the exponents `0` in these three; two finite ends, with the
  exponent `0` when they have the same exponent. -/
  shape : nl = -longMax ∧ nr = longMax ∧ del = 0 ∧ der = 0 ∨
    nl = -longMax ∧ nr ≠ longMax ∧ del = 0 ∧ der = 0 ∧ nr.toInt ≤ 0 ∨
    nl ≠ -longMax ∧ nr = longMax ∧ del = 0 ∧ der = 0 ∧ 0 ≤ nl.toInt ∨
    nl ≠ -longMax ∧ nr ≠ longMax ∧ (del = der → del = 0)
  /-- The lower end is not at `+∞`. -/
  left_ne : nl ≠ longMax
  /-- The upper end is not at `-∞`. -/
  right_ne : nr ≠ -longMax
  /-- The exponent of the lower end is not negative. -/
  zero_le_del : 0 ≤ del.toInt
  /-- The exponent of the upper end is not negative. -/
  zero_le_der : 0 ≤ der.toInt
  /-- The exponent of the lower end is at most the depth. -/
  del_le : del.toInt ≤ depth
  /-- The exponent of the upper end is at most the depth. -/
  der_le : der.toInt ≤ depth
  /-- A finite lower end, scaled to the larger exponent, is at most `2 ^ depth / 4` in absolute
  value, from the depth `1` on. -/
  bound_left : nl ≠ -longMax →
    1 ≤ depth ∧ 4 * |nl.toInt| * 2 ^ (der.toInt - del.toInt).toNat ≤ 2 ^ depth
  /-- A finite upper end, scaled to the larger exponent, is at most `2 ^ depth / 4` in absolute
  value, from the depth `1` on. -/
  bound_right : nr ≠ longMax →
    1 ≤ depth ∧ 4 * |nr.toInt| * 2 ^ (del.toInt - der.toInt).toNat ≤ 2 ^ depth
  /-- The ends increase. -/
  lt : endValue nl del < endValue nr der

theorem endsWF_zero : EndsWF 0 (-longMax) longMax 0 0 where
  shape := .inl ⟨rfl, rfl, rfl, rfl⟩
  left_ne := by decide
  right_ne := by decide
  zero_le_del := by decide
  zero_le_der := by decide
  del_le := by decide
  der_le := by decide
  bound_left h := absurd rfl h
  bound_right h := absurd rfl h
  lt := by simp only [endValue]; norm_num [show (-longMax ≠ longMax) by decide]

-- A finite end scaled as the bound of `Ratpoints.Sturm.EndsWF` at a depth up to `55` is at most
-- `2 ^ 53` in absolute value.
private theorem natAbs_le_of_four_mul_le {n : ℤ} {k depth : ℕ} (hd : depth ≤ 55)
    (h : 4 * |n| * 2 ^ k ≤ 2 ^ depth) : n.natAbs ≤ 2 ^ 53 := by
  have h1 : (2 : ℤ) ^ depth ≤ 2 ^ 55 := pow_le_pow_right₀ one_le_two hd
  have h2 : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  have h3 : 4 * |n| ≤ 4 * |n| * 2 ^ k := le_mul_of_one_le_right (by positivity) h2
  have : |n| ≤ 2 ^ 53 := by norm_num at h1 ⊢; lia
  rw [Int.abs_eq_natAbs] at this
  lia

theorem EndsWF.natAbs_left_le {depth : ℕ} {nl nr del der : Int64}
    (h : EndsWF depth nl nr del der) (hd : depth ≤ 55) (hl : nl ≠ -longMax) :
    nl.toInt.natAbs ≤ 2 ^ 53 :=
  natAbs_le_of_four_mul_le hd (h.bound_left hl).2

theorem EndsWF.natAbs_right_le {depth : ℕ} {nl nr del der : Int64}
    (h : EndsWF depth nl nr del der) (hd : depth ≤ 55) (hr : nr ≠ longMax) :
    nr.toInt.natAbs ≤ 2 ^ 53 :=
  natAbs_le_of_four_mul_le hd (h.bound_right hr).2

theorem ne_longMax_of_natAbs_le {n : Int64} (h : n.toInt.natAbs ≤ 2 ^ 53) :
    n ≠ longMax ∧ n ≠ -longMax := by
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩ <;> subst h'
  · rw [toInt_longMax] at h; lia
  · rw [toInt_neg_longMax] at h; lia

theorem endValue_of_ne {n : Int64} (e : Int64) (h1 : n ≠ longMax) (h2 : n ≠ -longMax) :
    endValue n e = n.toInt * 2 ^ (-e.toInt) := by
  simp [endValue, h1, h2]

/-- The value of a finite end `n / 2 ^ e`, `e ≥ 0`, as the quotient that the evaluation of the chain
at it (`Ratpoints.Sturm.evalSign`) reads. -/
theorem endValue_eq_div {n e : Int64} (h1 : n ≠ longMax) (h2 : n ≠ -longMax) (h0 : 0 ≤ e.toInt) :
    endValue n e = n.toInt / 2 ^ e.toInt.toNat := by
  rw [endValue_of_ne e h1 h2, zpow_neg, ← zpow_natCast, Int.toNat_of_nonneg h0, div_eq_mul_inv]

/-- Two finite ends `a / 2 ^ p` and `b / 2 ^ q`, `p, q ≥ 0`, compare as `a 2 ^ q` and `b 2 ^ p`. -/
theorem endValue_lt_endValue_iff {nl nr del der : Int64} (hl1 : nl ≠ longMax)
    (hl2 : nl ≠ -longMax) (hr1 : nr ≠ longMax) (hr2 : nr ≠ -longMax) (hp : 0 ≤ del.toInt)
    (hq : 0 ≤ der.toInt) :
    endValue nl del < endValue nr der ↔
      nl.toInt * 2 ^ der.toInt.toNat < nr.toInt * 2 ^ del.toInt.toNat := by
  rw [endValue_eq_div hl1 hl2 hp, endValue_eq_div hr1 hr2 hq,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

/-- The double of the lower end of an interval of the bisection has the value of the end. -/
theorem EndsWF.hasValue_left {depth : ℕ} {nl nr del der : Int64}
    (h : EndsWF depth nl nr del der) (hd : depth ≤ 55) :
    HasValue ((Double.ofInt64 nl).ldexp (-del.toInt)) (endValue nl del) := by
  by_cases hl : nl = -longMax
  · obtain rfl : del = 0 := by rcases h.shape with h' | h' | h' | h' <;> grind
    subst hl
    simpa [endValue, show (-longMax ≠ longMax) by decide] using hasValue_ldexp_ofInt64_neg_longMax
  · rw [endValue_of_ne del h.left_ne hl]
    exact hasValue_ldexp_ofInt64 (h.natAbs_left_le hd hl) h.zero_le_del (by lia [h.del_le])

/-- The double of the upper end of an interval of the bisection has the value of the end. -/
theorem EndsWF.hasValue_right {depth : ℕ} {nl nr del der : Int64}
    (h : EndsWF depth nl nr del der) (hd : depth ≤ 55) :
    HasValue ((Double.ofInt64 nr).ldexp (-der.toInt)) (endValue nr der) := by
  by_cases hr : nr = longMax
  · obtain rfl : der = 0 := by rcases h.shape with h' | h' | h' | h' <;> grind
    subst hr
    simpa [endValue] using hasValue_ldexp_ofInt64_longMax
  · rw [endValue_of_ne der hr h.right_ne]
    exact hasValue_ldexp_ofInt64 (h.natAbs_right_le hd hr) h.zero_le_der (by lia [h.der_le])

theorem endsWF_left_inf {depth : ℕ} {nr : Int64} (hd : depth ≤ 55) (h1 : 1 ≤ depth)
    (hb : nr.toInt ≤ 0) (hB : 4 * |nr.toInt| ≤ 2 ^ depth) : EndsWF depth (-longMax) nr 0 0 := by
  have hn := natAbs_le_of_four_mul_le (k := 0) hd (by simpa using hB)
  obtain ⟨hn1, hn2⟩ := ne_longMax_of_natAbs_le hn
  refine ⟨.inr (.inl ⟨rfl, hn1, rfl, rfl, hb⟩), by decide, hn2, by decide, by decide, by simp,
    by simp, fun h ↦ absurd rfl h, fun _ ↦ ⟨h1, by simpa using hB⟩, ?_⟩
  rw [endValue_of_ne 0 hn1 hn2]
  simp only [endValue, show (-longMax ≠ longMax) by decide, ↓reduceIte, Int64.toInt_zero, neg_zero,
    zpow_zero, mul_one]
  have : (-(2 ^ 53) : ℚ) ≤ nr.toInt := mod_cast (by lia : -(2 ^ 53) ≤ nr.toInt)
  linarith

theorem endsWF_right_inf {depth : ℕ} {nl : Int64} (hd : depth ≤ 55) (h1 : 1 ≤ depth)
    (ha : 0 ≤ nl.toInt) (hA : 4 * |nl.toInt| ≤ 2 ^ depth) : EndsWF depth nl longMax 0 0 := by
  have hn := natAbs_le_of_four_mul_le (k := 0) hd (by simpa using hA)
  obtain ⟨hn1, hn2⟩ := ne_longMax_of_natAbs_le hn
  refine ⟨.inr (.inr (.inl ⟨hn2, rfl, rfl, rfl, ha⟩)), hn1, by decide, by decide, by decide,
    by simp, by simp, fun _ ↦ ⟨h1, by simpa using hA⟩, fun h ↦ absurd rfl h, ?_⟩
  rw [endValue_of_ne 0 hn1 hn2]
  simp only [endValue, ↓reduceIte, Int64.toInt_zero, neg_zero, zpow_zero, mul_one]
  have : (nl.toInt : ℚ) ≤ 2 ^ 53 := mod_cast (by lia : nl.toInt ≤ 2 ^ 53)
  linarith

theorem endsWF_finite {depth : ℕ} {nl nr del der : Int64} (hd : depth ≤ 55) (h1 : 1 ≤ depth)
    (hp0 : 0 ≤ del.toInt) (hpd : del.toInt ≤ depth) (hq0 : 0 ≤ der.toInt)
    (hqd : der.toInt ≤ depth) (heq : del = der → del = 0)
    (hA : 4 * |nl.toInt| * 2 ^ (der.toInt - del.toInt).toNat ≤ 2 ^ depth)
    (hB : 4 * |nr.toInt| * 2 ^ (del.toInt - der.toInt).toNat ≤ 2 ^ depth)
    (hlt : nl.toInt * 2 ^ der.toInt.toNat < nr.toInt * 2 ^ del.toInt.toNat) :
    EndsWF depth nl nr del der := by
  obtain ⟨hl1, hl2⟩ := ne_longMax_of_natAbs_le (natAbs_le_of_four_mul_le hd hA)
  obtain ⟨hr1, hr2⟩ := ne_longMax_of_natAbs_le (natAbs_le_of_four_mul_le hd hB)
  exact ⟨.inr (.inr (.inr ⟨hl2, hr1, heq⟩)), hl1, hr2, hp0, hq0, hpd, hqd, fun _ ↦ ⟨h1, hA⟩,
    fun _ ↦ ⟨h1, hB⟩, (endValue_lt_endValue_iff hl1 hl2 hr1 hr2 hp0 hq0).mpr hlt⟩

theorem endsWF_finite_zero {depth : ℕ} {nl nr : Int64} (hd : depth ≤ 55) (h1 : 1 ≤ depth)
    (hA : 4 * |nl.toInt| ≤ 2 ^ depth) (hB : 4 * |nr.toInt| ≤ 2 ^ depth)
    (hlt : nl.toInt < nr.toInt) : EndsWF depth nl nr 0 0 :=
  endsWF_finite hd h1 (by simp) (by simp) (by simp) (by simp) (fun _ ↦ rfl) (by simpa using hA)
    (by simpa using hB) (by simpa using hlt)

/-! ### The midpoint -/

theorem midpoint_of_inf_inf (del der : Int64) : midpoint (-longMax) longMax del der = (0, 0) := by
  simp [midpoint]

theorem midpoint_of_left_inf {nr : Int64} (del der : Int64) (h : nr ≠ longMax) :
    midpoint (-longMax) nr del der = (if nr = 0 then -1 else 2 * nr, 0) := by
  simp [midpoint, h]

theorem midpoint_of_right_inf {nl : Int64} (del der : Int64) (h : nl ≠ -longMax) :
    midpoint nl longMax del der = (if nl = 0 then 1 else 2 * nl, 0) := by
  simp [midpoint, h]

theorem midpoint_of_eq {nl nr : Int64} (del : Int64) (hl : nl ≠ -longMax) (hr : nr ≠ longMax) :
    midpoint nl nr del del =
      if (nl + nr) &&& 1 = 0 then ((nl + nr) >>> 1, 0) else (nl + nr, 1) := by
  simp [midpoint, hl, hr]

theorem midpoint_of_lt {nl nr del der : Int64} (hl : nl ≠ -longMax) (hr : nr ≠ longMax)
    (h : der < del) : midpoint nl nr del der = (nl + nr * (1 <<< (del - der)), del + 1) := by
  simp [midpoint, hl, hr, h, (Int64.ne_of_lt h).symm]

theorem midpoint_of_gt {nl nr del der : Int64} (hl : nl ≠ -longMax) (hr : nr ≠ longMax)
    (h : del < der) : midpoint nl nr del der = (nl * (1 <<< (der - del)) + nr, der + 1) := by
  simp [midpoint, hl, hr, Int64.ne_of_lt h, Int64.not_lt.mpr (Int64.le_of_lt h)]

theorem toInt_ite_two_mul {n : Int64} (c : Int64) (h : n.toInt.natAbs ≤ 2 ^ 53) :
    (if n = 0 then c else 2 * n).toInt = if n.toInt = 0 then c.toInt else 2 * n.toInt := by
  by_cases h0 : n = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, show ¬n.toInt = 0 from fun h' ↦ h0 (Int64.toInt_inj.mp h'),
      Int64.toInt_two_mul (x := n) (by lia)]

theorem EndsWF.midpoint_left_inf {depth : ℕ} {nr del der : Int64}
    (h : EndsWF depth (-longMax) nr del der) (hd : depth < 55) (hr : nr ≠ longMax) :
    EndsWF (depth + 1) (-longMax) (midpoint (-longMax) nr del der).1 del
        (midpoint (-longMax) nr del der).2 ∧
      EndsWF (depth + 1) (midpoint (-longMax) nr del der).1 nr (midpoint (-longMax) nr del der).2
        der := by
  obtain ⟨rfl, rfl, hb⟩ : del = 0 ∧ der = 0 ∧ nr.toInt ≤ 0 := by
    rcases h.shape with h' | h' | h' | h' <;> grind
  obtain ⟨h1, hB⟩ := h.bound_right hr
  simp only [Int64.toInt_zero, sub_self, Int.toNat_zero, pow_zero, mul_one] at hB
  have hM := toInt_ite_two_mul (-1) (h.natAbs_right_le (by lia) hr)
  have h4 : (2 : ℤ) ^ 2 ≤ 2 ^ (depth + 1) := pow_le_pow_right₀ one_le_two (by lia)
  rw [midpoint_of_left_inf 0 0 hr]
  refine ⟨endsWF_left_inf (by lia) (by lia) ?_ ?_,
    endsWF_finite_zero (by lia) (by lia) ?_ ?_ ?_⟩ <;>
    (try simp only [hM, show (-1 : Int64).toInt = -1 by decide]) <;> (try split_ifs) <;>
    (try simp only [abs_neg, abs_one, abs_mul, abs_two]) <;> lia

theorem EndsWF.midpoint_right_inf {depth : ℕ} {nl del der : Int64}
    (h : EndsWF depth nl longMax del der) (hd : depth < 55) (hl : nl ≠ -longMax) :
    EndsWF (depth + 1) nl (midpoint nl longMax del der).1 del (midpoint nl longMax del der).2 ∧
      EndsWF (depth + 1) (midpoint nl longMax del der).1 longMax (midpoint nl longMax del der).2
        der := by
  obtain ⟨rfl, rfl, ha⟩ : del = 0 ∧ der = 0 ∧ 0 ≤ nl.toInt := by
    rcases h.shape with h' | h' | h' | h' <;> grind
  obtain ⟨h1, hA⟩ := h.bound_left hl
  simp only [Int64.toInt_zero, sub_self, Int.toNat_zero, pow_zero, mul_one] at hA
  have hM := toInt_ite_two_mul 1 (h.natAbs_left_le (by lia) hl)
  have h4 : (2 : ℤ) ^ 2 ≤ 2 ^ (depth + 1) := pow_le_pow_right₀ one_le_two (by lia)
  rw [midpoint_of_right_inf 0 0 hl]
  refine ⟨endsWF_finite_zero (by lia) (by lia) ?_ ?_ ?_,
    endsWF_right_inf (by lia) (by lia) ?_ ?_⟩ <;>
    (try simp only [hM, show (1 : Int64).toInt = 1 by decide]) <;> (try split_ifs) <;>
    (try simp only [abs_one, abs_mul, abs_two]) <;> lia

/-- The halves of a finite interval `[a, b]` with the exponents `0` at its midpoint `m`,
`2 m = a + b`, when `a + b` is even. -/
theorem endsWF_halves_of_even {depth : ℕ} {nl nr m : Int64} (hd : depth < 55)
    (hA : 4 * (nl.toInt.natAbs : ℤ) ≤ 2 ^ depth) (hB : 4 * (nr.toInt.natAbs : ℤ) ≤ 2 ^ depth)
    (hlt : nl.toInt < nr.toInt) (hm : 2 * m.toInt = nl.toInt + nr.toInt) :
    EndsWF (depth + 1) nl m 0 0 ∧ EndsWF (depth + 1) m nr 0 0 := by
  refine ⟨endsWF_finite_zero (by lia) (by lia) ?_ ?_ ?_,
    endsWF_finite_zero (by lia) (by lia) ?_ ?_ ?_⟩ <;> (try simp only [Int.abs_eq_natAbs]) <;>
    lia

/-- The halves of a finite interval `[a, b]` with the exponents `0` at its midpoint `(a + b) / 2`
with the exponent `1`, when `a + b` is odd. -/
theorem endsWF_halves_of_odd {depth : ℕ} {nl nr m : Int64} (hd : depth < 55)
    (hA : 4 * (nl.toInt.natAbs : ℤ) ≤ 2 ^ depth) (hB : 4 * (nr.toInt.natAbs : ℤ) ≤ 2 ^ depth)
    (hlt : nl.toInt < nr.toInt) (hm : m.toInt = nl.toInt + nr.toInt) :
    EndsWF (depth + 1) nl m 0 1 ∧ EndsWF (depth + 1) m nr 1 0 := by
  have h0 : (0 : Int64).toInt = 0 := Int64.toInt_zero
  have h1 : (1 : Int64).toInt = 1 := by decide
  refine ⟨endsWF_finite (by lia) (by lia) (by lia) (by lia) (by lia) (by lia) (fun _ ↦ rfl)
    ?_ ?_ ?_, endsWF_finite (by lia) (by lia) (by lia) (by lia) (by lia) (by lia) id ?_ ?_ ?_⟩ <;>
  simp only [hm, h0, h1, sub_zero, zero_sub, Int.toNat_one, pow_one, Int.toNat_zero, pow_zero,
    mul_one, Int.abs_eq_natAbs] <;> lia

theorem EndsWF.midpoint_eq {depth : ℕ} {nl nr del : Int64} (h : EndsWF depth nl nr del del)
    (hd : depth < 55) (hl : nl ≠ -longMax) (hr : nr ≠ longMax) :
    EndsWF (depth + 1) nl (midpoint nl nr del del).1 del (midpoint nl nr del del).2 ∧
      EndsWF (depth + 1) (midpoint nl nr del del).1 nr (midpoint nl nr del del).2 del := by
  obtain rfl : del = 0 := by rcases h.shape with h' | h' | h' | h' <;> grind
  obtain ⟨-, hA⟩ := h.bound_left hl
  obtain ⟨-, hB⟩ := h.bound_right hr
  have hlt := (endValue_lt_endValue_iff h.left_ne hl hr h.right_ne (by simp) (by simp)).mp h.lt
  simp only [Int64.toInt_zero, sub_self, Int.toNat_zero, pow_zero, mul_one,
    Int.abs_eq_natAbs] at hA hB hlt
  have hs : (nl + nr).toInt = nl.toInt + nr.toInt := Int64.toInt_add_of_lt
    (by lia [h.natAbs_left_le (by lia) hl, h.natAbs_right_le (by lia) hr])
    (by lia [h.natAbs_left_le (by lia) hl, h.natAbs_right_le (by lia) hr])
  rw [midpoint_of_eq 0 hl hr]
  by_cases hev : (nl + nr) &&& 1 = 0
  · have := congr(Int64.toInt $hev)
    rw [Int64.toInt_and_one, hs, Int64.toInt_zero] at this
    simpa only [hev, ↓reduceIte] using endsWF_halves_of_even hd hA hB hlt
      (by rw [Int64.toInt_shiftRight_one, hs]; lia)
  · simpa only [hev, ↓reduceIte] using endsWF_halves_of_odd hd hA hB hlt hs

-- The halves of `[a, b X]` at its midpoint `a + b X`, scaled by `2 Q X`, for the bisection.
private theorem lt_and_lt_of_lt_mul {a b X Q : ℤ} (hQ : 0 < Q) (hX : 0 < X) (h : a < b * X) :
    a * (2 * (Q * X)) < (a + b * X) * (Q * X) ∧ (a + b * X) * Q < b * (2 * (Q * X)) := by
  have h' := sub_pos.mpr h
  have := mul_pos h' (mul_pos hQ hX)
  have := mul_pos h' hQ
  constructor <;> linarith

/-- The halves of a finite interval `[a / 2 ^ p, b / 2 ^ q]` with `q < p` at its midpoint
`m / 2 ^ (p + 1)`, `m = a + b 2 ^ (p - q)`. -/
theorem endsWF_halves_of_lt {depth k : ℕ} {nl nr m del der dem : Int64} (hd : depth < 55)
    (hq : 0 ≤ der.toInt) (hk : del.toInt = der.toInt + (k + 1))
    (hpd : del.toInt ≤ depth) (hA : 4 * |nl.toInt| ≤ 2 ^ depth)
    (hB : 4 * |nr.toInt| * 2 ^ (k + 1) ≤ 2 ^ depth) (hlt : nl.toInt < nr.toInt * 2 ^ (k + 1))
    (hm : m.toInt = nl.toInt + nr.toInt * 2 ^ (k + 1)) (hdem : dem.toInt = del.toInt + 1) :
    EndsWF (depth + 1) nl m del dem ∧ EndsWF (depth + 1) m nr dem der := by
  have hX0 : (0 : ℤ) < 2 ^ (k + 1) := by positivity
  have hP : (2 : ℤ) ^ del.toInt.toNat = 2 ^ der.toInt.toNat * 2 ^ (k + 1) := by
    rw [← pow_add]; congr 1; lia
  have hP1 : (2 : ℤ) ^ dem.toInt.toNat = 2 * (2 ^ der.toInt.toNat * 2 ^ (k + 1)) := by
    rw [← hP, ← pow_succ']; congr 1; lia
  have hd1 : (2 : ℤ) ^ (depth + 1) = 2 * 2 ^ depth := pow_succ' 2 depth
  have hab' := abs_add_le nl.toInt (nr.toInt * 2 ^ (k + 1))
  have hbX : |nr.toInt * 2 ^ (k + 1)| = |nr.toInt| * 2 ^ (k + 1) := by rw [abs_mul, abs_of_pos hX0]
  have hab := lt_and_lt_of_lt_mul (Q := 2 ^ der.toInt.toNat) (by positivity) hX0 hlt
  refine ⟨endsWF_finite (by lia) (by lia) (by lia) (by lia) (by lia) (by lia)
    (fun h' ↦ absurd congr(Int64.toInt $h') (by lia)) ?_ ?_ ?_,
    endsWF_finite (by lia) (by lia) (by lia) (by lia) hq (by lia)
    (fun h' ↦ absurd congr(Int64.toInt $h') (by lia)) ?_ ?_ ?_⟩ <;>
  simp only [hm, hP1, hP, show (dem.toInt - del.toInt).toNat = 1 by lia,
    show (del.toInt - dem.toInt).toNat = 0 by lia, show (der.toInt - dem.toInt).toNat = 0 by lia,
    show (dem.toInt - der.toInt).toNat = k + 2 by lia, pow_zero, pow_one, mul_one] <;>
  first | linarith | (rw [pow_succ]; linarith)

/-- The midpoint `a + b 2 ^ (p - q)` of the interval from `a / 2 ^ p` to `b / 2 ^ q`, `q < p`,
computed in `long`s, without overflow for `|a|` and `|b| 2 ^ (p - q)` at most `2 ^ 52`. -/
theorem toInt_add_mul_one_shiftLeft {k : ℕ} {nl nr del der : Int64}
    (hk : del.toInt - der.toInt = k + 1) (hk63 : k + 1 < 63) (hA : |nl.toInt| ≤ 2 ^ 52)
    (hB : |nr.toInt| * 2 ^ (k + 1) ≤ 2 ^ 52) :
    (nl + nr * ((1 : Int64) <<< (del - der))).toInt = nl.toInt + nr.toInt * 2 ^ (k + 1) := by
  have hX0 : (0 : ℤ) < 2 ^ (k + 1) := by positivity
  have hbX : |nr.toInt * 2 ^ (k + 1)| ≤ 2 ^ 52 := by rw [abs_mul, abs_of_pos hX0]; exact hB
  have hsub : (del - der).toInt = k + 1 := by
    rw [Int64.toInt_sub_of_lt (by lia) (by lia), hk]
  have hsh : ((1 : Int64) <<< (del - der)).toInt = 2 ^ (k + 1) := by
    rw [Int64.toInt_one_shiftLeft (by lia) (by lia), hsub]; rfl
  have hmul : (nr * ((1 : Int64) <<< (del - der))).toInt = nr.toInt * 2 ^ (k + 1) := by
    rw [Int64.toInt_mul_of_lt (by rw [hsh]; linarith [abs_le.mp hbX])
      (by rw [hsh]; linarith [abs_le.mp hbX]), hsh]
  rw [Int64.toInt_add_of_lt (by rw [hmul]; linarith [abs_le.mp hbX, abs_le.mp hA])
    (by rw [hmul]; linarith [abs_le.mp hbX, abs_le.mp hA]), hmul]

theorem EndsWF.midpoint_lt {depth : ℕ} {nl nr del der : Int64} (h : EndsWF depth nl nr del der)
    (hd : depth < 55) (hl : nl ≠ -longMax) (hr : nr ≠ longMax) (hlt : der < del) :
    EndsWF (depth + 1) nl (midpoint nl nr del der).1 del (midpoint nl nr del der).2 ∧
      EndsWF (depth + 1) (midpoint nl nr del der).1 nr (midpoint nl nr del der).2 der := by
  have hqp := Int64.lt_iff_toInt_lt.mp hlt
  have hpd := h.del_le
  have hq0 := h.zero_le_der
  obtain ⟨h1, hA⟩ := h.bound_left hl
  obtain ⟨-, hB⟩ := h.bound_right hr
  have hlt' := (endValue_lt_endValue_iff h.left_ne hl hr h.right_ne h.zero_le_del
    h.zero_le_der).mp h.lt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, del.toInt - der.toInt = k + 1 :=
    ⟨(del.toInt - der.toInt - 1).toNat, by lia⟩
  rw [show (der.toInt - del.toInt).toNat = 0 by lia, pow_zero, mul_one] at hA
  rw [hk, show ((k : ℤ) + 1).toNat = k + 1 by lia] at hB
  rw [show del.toInt.toNat = der.toInt.toNat + (k + 1) by lia, pow_add] at hlt'
  have h2d : (2 : ℤ) ^ depth ≤ 2 ^ 54 := pow_le_pow_right₀ one_le_two (by lia)
  rw [midpoint_of_lt hl hr hlt]
  exact endsWF_halves_of_lt hd h.zero_le_der (by lia) hpd hA hB
    (lt_of_mul_lt_mul_right (hlt'.trans_eq (by ring)) (by positivity))
    (toInt_add_mul_one_shiftLeft hk (by lia) (by linarith) (by linarith))
    (Int64.toInt_add_one_of_lt (by lia))

-- The halves of `[a X, b]` at its midpoint `a X + b`, scaled by `2 P X`, for the bisection.
private theorem lt_and_lt_of_mul_lt {a b X P : ℤ} (hP : 0 < P) (hX : 0 < X) (h : a * X < b) :
    a * (2 * (P * X)) < (a * X + b) * P ∧ (a * X + b) * (P * X) < b * (2 * (P * X)) := by
  have h' := sub_pos.mpr h
  have := mul_pos h' hP
  have := mul_pos h' (mul_pos hP hX)
  constructor <;> linarith

/-- The halves of a finite interval `[a / 2 ^ p, b / 2 ^ q]` with `p < q` at its midpoint
`m / 2 ^ (q + 1)`, `m = a 2 ^ (q - p) + b`. -/
theorem endsWF_halves_of_gt {depth k : ℕ} {nl nr m del der dem : Int64} (hd : depth < 55)
    (hp : 0 ≤ del.toInt) (hk : der.toInt = del.toInt + (k + 1))
    (hqd : der.toInt ≤ depth) (hA : 4 * |nl.toInt| * 2 ^ (k + 1) ≤ 2 ^ depth)
    (hB : 4 * |nr.toInt| ≤ 2 ^ depth) (hlt : nl.toInt * 2 ^ (k + 1) < nr.toInt)
    (hm : m.toInt = nl.toInt * 2 ^ (k + 1) + nr.toInt) (hdem : dem.toInt = der.toInt + 1) :
    EndsWF (depth + 1) nl m del dem ∧ EndsWF (depth + 1) m nr dem der := by
  have hX0 : (0 : ℤ) < 2 ^ (k + 1) := by positivity
  have hP : (2 : ℤ) ^ der.toInt.toNat = 2 ^ del.toInt.toNat * 2 ^ (k + 1) := by
    rw [← pow_add]; congr 1; lia
  have hP1 : (2 : ℤ) ^ dem.toInt.toNat = 2 * (2 ^ del.toInt.toNat * 2 ^ (k + 1)) := by
    rw [← hP, ← pow_succ']; congr 1; lia
  have hd1 : (2 : ℤ) ^ (depth + 1) = 2 * 2 ^ depth := pow_succ' 2 depth
  have hab' := abs_add_le (nl.toInt * 2 ^ (k + 1)) nr.toInt
  have haX : |nl.toInt * 2 ^ (k + 1)| = |nl.toInt| * 2 ^ (k + 1) := by rw [abs_mul, abs_of_pos hX0]
  have hab := lt_and_lt_of_mul_lt (P := 2 ^ del.toInt.toNat) (by positivity) hX0 hlt
  refine ⟨endsWF_finite (by lia) (by lia) hp (by lia) (by lia) (by lia)
    (fun h' ↦ absurd congr(Int64.toInt $h') (by lia)) ?_ ?_ ?_,
    endsWF_finite (by lia) (by lia) (by lia) (by lia) (by lia) (by lia)
    (fun h' ↦ absurd congr(Int64.toInt $h') (by lia)) ?_ ?_ ?_⟩ <;>
  simp only [hm, hP1, hP, show (dem.toInt - der.toInt).toNat = 1 by lia,
    show (der.toInt - dem.toInt).toNat = 0 by lia, show (del.toInt - dem.toInt).toNat = 0 by lia,
    show (dem.toInt - del.toInt).toNat = k + 2 by lia, pow_zero, pow_one, mul_one] <;>
  first | linarith | (rw [pow_succ]; linarith)

/-- The midpoint `a 2 ^ (q - p) + b` of the interval from `a / 2 ^ p` to `b / 2 ^ q`, `p < q`,
computed in `long`s, without overflow for `|a| 2 ^ (q - p)` and `|b|` at most `2 ^ 52`. -/
theorem toInt_mul_one_shiftLeft_add {k : ℕ} {nl nr del der : Int64}
    (hk : der.toInt - del.toInt = k + 1) (hk63 : k + 1 < 63)
    (hA : |nl.toInt| * 2 ^ (k + 1) ≤ 2 ^ 52) (hB : |nr.toInt| ≤ 2 ^ 52) :
    (nl * ((1 : Int64) <<< (der - del)) + nr).toInt = nl.toInt * 2 ^ (k + 1) + nr.toInt := by
  have hX0 : (0 : ℤ) < 2 ^ (k + 1) := by positivity
  have haX : |nl.toInt * 2 ^ (k + 1)| ≤ 2 ^ 52 := by rw [abs_mul, abs_of_pos hX0]; exact hA
  have hsub : (der - del).toInt = k + 1 := by
    rw [Int64.toInt_sub_of_lt (by lia) (by lia), hk]
  have hsh : ((1 : Int64) <<< (der - del)).toInt = 2 ^ (k + 1) := by
    rw [Int64.toInt_one_shiftLeft (by lia) (by lia), hsub]; rfl
  have hmul : (nl * ((1 : Int64) <<< (der - del))).toInt = nl.toInt * 2 ^ (k + 1) := by
    rw [Int64.toInt_mul_of_lt (by rw [hsh]; linarith [abs_le.mp haX])
      (by rw [hsh]; linarith [abs_le.mp haX]), hsh]
  rw [Int64.toInt_add_of_lt (by rw [hmul]; linarith [abs_le.mp haX, abs_le.mp hB])
    (by rw [hmul]; linarith [abs_le.mp haX, abs_le.mp hB]), hmul]

theorem EndsWF.midpoint_gt {depth : ℕ} {nl nr del der : Int64} (h : EndsWF depth nl nr del der)
    (hd : depth < 55) (hl : nl ≠ -longMax) (hr : nr ≠ longMax) (hlt : del < der) :
    EndsWF (depth + 1) nl (midpoint nl nr del der).1 del (midpoint nl nr del der).2 ∧
      EndsWF (depth + 1) (midpoint nl nr del der).1 nr (midpoint nl nr del der).2 der := by
  have hqp := Int64.lt_iff_toInt_lt.mp hlt
  have hqd := h.der_le
  have hp0 := h.zero_le_del
  obtain ⟨-, hA⟩ := h.bound_left hl
  obtain ⟨-, hB⟩ := h.bound_right hr
  have hlt' := (endValue_lt_endValue_iff h.left_ne hl hr h.right_ne h.zero_le_del
    h.zero_le_der).mp h.lt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, der.toInt - del.toInt = k + 1 :=
    ⟨(der.toInt - del.toInt - 1).toNat, by lia⟩
  rw [show (del.toInt - der.toInt).toNat = 0 by lia, pow_zero, mul_one] at hB
  rw [hk, show ((k : ℤ) + 1).toNat = k + 1 by lia] at hA
  rw [show der.toInt.toNat = del.toInt.toNat + (k + 1) by lia, pow_add] at hlt'
  have h2d : (2 : ℤ) ^ depth ≤ 2 ^ 54 := pow_le_pow_right₀ one_le_two (by lia)
  rw [midpoint_of_gt hl hr hlt]
  exact endsWF_halves_of_gt hd h.zero_le_del (by lia) hqd hA hB
    (lt_of_mul_lt_mul_right ((by ring : _ = _).trans_lt hlt') (by positivity))
    (toInt_mul_one_shiftLeft_add hk (by lia) (by linarith) (by linarith))
    (Int64.toInt_add_one_of_lt (by lia))

theorem EndsWF.halves {depth : ℕ} {nl nr del der : Int64} (h : EndsWF depth nl nr del der)
    (hd : depth < 55) :
    EndsWF (depth + 1) nl (midpoint nl nr del der).1 del (midpoint nl nr del der).2 ∧
      EndsWF (depth + 1) (midpoint nl nr del der).1 nr (midpoint nl nr del der).2 der := by
  rcases h.shape with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, hr, -⟩ | ⟨hl, rfl, -⟩ | ⟨hl, hr, -⟩
  · rw [midpoint_of_inf_inf]
    exact ⟨endsWF_left_inf (by lia) (by lia) (by simp) (by simp),
      endsWF_right_inf (by lia) (by lia) (by simp) (by simp)⟩
  · exact h.midpoint_left_inf hd hr
  · exact h.midpoint_right_inf hd hl
  · rcases lt_trichotomy del.toInt der.toInt with h' | h' | h'
    · exact h.midpoint_gt hd hl hr (Int64.lt_iff_toInt_lt.mpr h')
    · obtain rfl := Int64.toInt_inj.mp h'
      exact h.midpoint_eq hd hl hr
    · exact h.midpoint_lt hd hl hr (Int64.lt_iff_toInt_lt.mpr h')

/-- An interval of doubles whose ends are not NaNs and whose lower end is at most its upper end, by
their values. -/
def IsInterval (i : Double × Double) : Prop :=
  i.1.isNaN = false ∧ i.2.isNaN = false ∧ doubleValue i.1.bits ≤ doubleValue i.2.bits

/-- The relation of two intervals of doubles of which the first ends strictly before the second
begins, by the values of their ends. -/
def EndsBefore (i j : Double × Double) : Prop := doubleValue i.2.bits < doubleValue j.1.bits

/-- Intervals of doubles without a NaN, each with its ends in order, increasing and strictly apart,
by the values of their ends. -/
def AreIntervals (l : List (Double × Double)) : Prop :=
  (∀ i ∈ l, IsInterval i) ∧ l.Pairwise EndsBefore

theorem AreIntervals.nil : AreIntervals [] :=
  ⟨by simp, .nil⟩

theorem addInterval_eq (iv : Array (Double × Double)) (nl nr del der : Int64) :
    addInterval iv nl nr del der = match iv.back? with
      | some (lo, up) => if up.beq ((Double.ofInt64 nl).ldexp (-del.toInt)) then
          iv.pop.push (lo, (Double.ofInt64 nr).ldexp (-der.toInt))
        else
          iv.push ((Double.ofInt64 nl).ldexp (-del.toInt), (Double.ofInt64 nr).ldexp (-der.toInt))
      | none => iv.push ((Double.ofInt64 nl).ldexp (-del.toInt),
          (Double.ofInt64 nr).ldexp (-der.toInt)) := rfl

theorem AreIntervals.append_singleton {l : List (Double × Double)} {x : Double × Double}
    (hl : AreIntervals l) (hx : IsInterval x) (hlx : ∀ i ∈ l, EndsBefore i x) :
    AreIntervals (l ++ [x]) := by
  refine ⟨fun i hi ↦ ?_, List.pairwise_append.mpr ⟨hl.2, by simp, fun i hi j hj ↦ ?_⟩⟩
  · rcases List.mem_append.mp hi with hi | hi
    exacts [hl.1 i hi, List.mem_singleton.mp hi ▸ hx]
  · exact List.mem_singleton.mp hj ▸ hlx i hi

/-- Every interval of increasing intervals strictly apart ends at the end of the last at the
latest. -/
theorem AreIntervals.le_of_back?_eq_some {iv : Array (Double × Double)}
    (hiv : AreIntervals iv.toList) {x : Double × Double} (hx : iv.back? = some x)
    {i : Double × Double} (hi : i ∈ iv.toList) : doubleValue i.2.bits ≤ doubleValue x.2.bits := by
  obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp hx
  rw [Array.toList_push] at hi hiv
  rcases List.mem_append.mp hi with hi | hi
  · exact ((List.pairwise_append.mp hiv.2).2.2 i hi x (by simp)).le.trans
      (hiv.1 x (by simp)).2.2
  · rw [List.mem_singleton.mp hi]

/-- The join of the interval up to `u` to the last interval kept, from `lo` to `up`, keeps the
intervals increasing and strictly apart when `u` lies above `up`. -/
theorem AreIntervals.pop_push {iv : Array (Double × Double)} (hiv : AreIntervals iv.toList)
    {lo up u : Double} (hback : iv.back? = some (lo, up)) (hu : u.isNaN = false)
    (hlt : doubleValue up.bits ≤ doubleValue u.bits) :
    AreIntervals (iv.pop.push (lo, u)).toList := by
  obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp hback
  rw [Array.toList_push] at hiv
  rw [Array.pop_push, Array.toList_push]
  have hlo := hiv.1 (lo, up) (by simp)
  refine AreIntervals.append_singleton ⟨fun i hi ↦ hiv.1 i (by simp [hi]),
    (List.pairwise_append.mp hiv.2).1⟩ ⟨hlo.1, hu, hlo.2.2.trans hlt⟩ fun i hi ↦ ?_
  exact (List.pairwise_append.mp hiv.2).2.2 i hi (lo, up) (by simp)

/-- A new last interval `x` after increasing intervals strictly apart that end before `x` begins
keeps them so. -/
theorem AreIntervals.push {iv : Array (Double × Double)} (hiv : AreIntervals iv.toList)
    {y x : Double × Double} (hback : iv.back? = some y) (hx : IsInterval x)
    (hlt : doubleValue y.2.bits < doubleValue x.1.bits) : AreIntervals (iv.push x).toList := by
  rw [Array.toList_push]
  exact hiv.append_singleton hx fun i hi ↦ (hiv.le_of_back?_eq_some hback hi).trans_lt hlt

/-- The last interval kept after the bisection adds the interval up to `u` ends at `u`, whether
it is the new interval or the join of it to the last interval before. -/
theorem snd_eq_of_mem_back?_addInterval (iv : Array (Double × Double)) (nl nr del der : Int64) :
    ∀ i ∈ (addInterval iv nl nr del der).back?, i.2 = (Double.ofInt64 nr).ldexp (-der.toInt) := by
  rw [addInterval_eq]
  split
  · split <;> simp
  · simp

/-- The intervals kept stay increasing and strictly apart when the bisection adds the interval from
`l` to `u` (their values `L < U`) after kept intervals that end at `L` at the latest, joining it
to the last of them when that ends at `L`. -/
theorem AreIntervals.addInterval {iv : Array (Double × Double)} {nl nr del der : Int64} {L U : ℚ}
    (hiv : AreIntervals iv.toList)
    (hb : ∀ i ∈ iv.back?, doubleValue i.2.bits ≤ (L : WithBotTop ℚ))
    (hl : HasValue ((Double.ofInt64 nl).ldexp (-del.toInt)) L)
    (hu : HasValue ((Double.ofInt64 nr).ldexp (-der.toInt)) U) (hLU : L < U) :
    AreIntervals (addInterval iv nl nr del der).toList := by
  have hLU' : (L : WithBotTop ℚ) < U := WithBotTop.coe_lt_coe.mpr hLU
  have hx : IsInterval ((Double.ofInt64 nl).ldexp (-del.toInt),
      (Double.ofInt64 nr).ldexp (-der.toInt)) := ⟨hl.1, hu.1, by rw [hl.2, hu.2]; exact hLU'.le⟩
  rw [addInterval_eq]
  rcases hback : iv.back? with _ | ⟨lo, up⟩
  · obtain rfl : iv = #[] := by simpa using hback
    exact AreIntervals.nil.append_singleton hx nofun
  have hup : doubleValue up.bits ≤ L := hb (lo, up) (by simp [hback])
  have hlo := hiv.1 (lo, up) (Array.mem_toList_iff.mpr (Array.mem_of_back? hback))
  by_cases hbeq : up.beq ((Double.ofInt64 nl).ldexp (-del.toInt)) = true
  · have hv : doubleValue up.bits = L := by
      rw [← hl.2]; exact (Double.beq_eq_true_iff hlo.2.1 hl.1).mp hbeq
    simp only [hbeq, ↓reduceIte]
    exact hiv.pop_push hback hu.1 (by rw [hv, hu.2]; exact hLU'.le)
  · have hv : doubleValue up.bits < L := lt_of_le_of_ne hup fun h ↦ hbeq <| by
      rw [Double.beq_eq_true_iff hlo.2.1 hl.1, hl.2, h]
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    exact hiv.push hback hx (hv.trans_le hl.2.ge)

/-- What the intervals kept hold stays held when the bisection adds an interval up to `u` after
them, with the value `U` above `L`, the last of them ending at `L` at the latest: the join extends
the last interval. -/
theorem exists_mem_addInterval_of_exists_mem {iv : Array (Double × Double)} {nl nr del der : Int64}
    {L U : ℚ} (hiv : ∀ i ∈ iv.toList, IsInterval i)
    (hb : ∀ i ∈ iv.back?, doubleValue i.2.bits ≤ (L : WithBotTop ℚ))
    (hu : HasValue ((Double.ofInt64 nr).ldexp (-der.toInt)) U) (hLU : L < U) {x : WithBotTop ℚ}
    (hx : ∃ i ∈ iv.toList, doubleValue i.1.bits ≤ x ∧ x ≤ doubleValue i.2.bits) :
    ∃ i ∈ (addInterval iv nl nr del der).toList, doubleValue i.1.bits ≤ x ∧
      x ≤ doubleValue i.2.bits := by
  obtain ⟨i, hi, hx⟩ := hx
  rw [addInterval_eq]
  rcases hback : iv.back? with _ | ⟨lo, up⟩
  · exact absurd hi (by simp_all)
  obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp hback
  by_cases hbeq : up.beq ((Double.ofInt64 nl).ldexp (-del.toInt)) = true
  · simp only [hbeq, ↓reduceIte, Array.pop_push, Array.toList_push]
    rw [Array.toList_push] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ⟨i, by simp [hi], hx⟩
    · obtain rfl := List.mem_singleton.mp hi
      refine ⟨(lo, (Double.ofInt64 nr).ldexp (-der.toInt)), by simp, hx.1, hx.2.trans ?_⟩
      rw [hu.2]
      exact (hb _ (by simp [hback])).trans (WithBotTop.coe_le_coe.mpr hLU.le)
  · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    exact ⟨i, by rw [Array.toList_push]; exact List.mem_append_left _ hi, hx⟩

/-- The intervals kept hold every value from `L` to `U` after the bisection adds the interval from
`l` to `u` with these values. -/
theorem exists_mem_addInterval {iv : Array (Double × Double)} {nl nr del der : Int64} {L U : ℚ}
    (hiv : ∀ i ∈ iv.toList, IsInterval i)
    (hl : HasValue ((Double.ofInt64 nl).ldexp (-del.toInt)) L)
    (hu : HasValue ((Double.ofInt64 nr).ldexp (-der.toInt)) U) {x : WithBotTop ℚ}
    (hx : (L : WithBotTop ℚ) ≤ x ∧ x ≤ U) :
    ∃ i ∈ (addInterval iv nl nr del der).toList, doubleValue i.1.bits ≤ x ∧
      x ≤ doubleValue i.2.bits := by
  rw [addInterval_eq]
  rcases hback : iv.back? with _ | ⟨lo, up⟩
  · exact ⟨((Double.ofInt64 nl).ldexp (-del.toInt), (Double.ofInt64 nr).ldexp (-der.toInt)),
      by simp, by rw [hl.2]; exact hx.1, by rw [hu.2]; exact hx.2⟩
  have hlo := hiv (lo, up) (Array.mem_toList_iff.mpr (Array.mem_of_back? hback))
  by_cases hbeq : up.beq ((Double.ofInt64 nl).ldexp (-del.toInt)) = true
  · have hv : doubleValue up.bits = L := by
      rw [← hl.2]; exact (Double.beq_eq_true_iff hlo.2.1 hl.1).mp hbeq
    simp only [hbeq, ↓reduceIte]
    exact ⟨(lo, (Double.ofInt64 nr).ldexp (-der.toInt)), by simp, hlo.2.2.trans (hv ▸ hx.1),
      by rw [hu.2]; exact hx.2⟩
  · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    exact ⟨((Double.ofInt64 nl).ldexp (-del.toInt), (Double.ofInt64 nr).ldexp (-der.toInt)),
      by simp, by rw [hl.2]; exact hx.1, by rw [hu.2]; exact hx.2⟩

/-- The intervals that the bisection keeps from the interval from `nl / 2 ^ del` to `nr / 2 ^ der`
at the depth `depth ≤ iter ≤ 55`, after kept intervals that end at its lower end at the latest, are
increasing and strictly apart and end at its upper end at the latest. -/
theorem iterate_wf {rows : Array (Array ℤ)} {k iter : ℕ} {nl nr del der : Int64} {cleft cright : ℕ}
    {sl sr : ℤ} {depth : ℕ} {acc : Array (Double × Double)} (hE : EndsWF depth nl nr del der)
    (hit : iter ≤ 55) (hd : depth ≤ iter) (hacc : AreIntervals acc.toList)
    (hb : ∀ i ∈ acc.back?, doubleValue i.2.bits ≤ (endValue nl del : WithBotTop ℚ)) :
    AreIntervals (Id.run (iterate rows k iter nl nr del der cleft cright sl sr depth acc)).toList ∧
      ∀ i ∈ (Id.run (iterate rows k iter nl nr del der cleft cright sl sr depth acc)).back?,
        doubleValue i.2.bits ≤ (endValue nr der : WithBotTop ℚ) := by
  fun_induction iterate rows k iter nl nr del der cleft cright sl sr depth acc with
  | case1 => exact ⟨hacc, fun i hi ↦ (hb i hi).trans (WithBotTop.coe_le_coe.mpr hE.lt.le)⟩
  | case2 =>
    refine ⟨hacc.addInterval hb (hE.hasValue_left (by lia)) (hE.hasValue_right (by lia)) hE.lt,
      fun i hi ↦ ?_⟩
    rw [snd_eq_of_mem_back?_addInterval _ _ _ _ _ i hi, (hE.hasValue_right (by lia)).2]
  | case3 nl nr del der cleft cright sl sr depth acc _ hk nm dem hm ih2 ih1 =>
    obtain ⟨hL, hR⟩ := hE.halves (by lia)
    rw [hm] at hL hR
    simp only [Id.run_bind]
    rcases Id.run (signsAt rows k nm dem) with ⟨s0, s1, cmid⟩
    obtain ⟨h1, h2⟩ := ih2 s0 s1 cmid hL (by lia) hacc hb
    simpa only [dite_eq_ite] using ih1 s0 s1 cmid _ hR (by lia) h1 h2

/-- The first call of the bisection, on the whole line at the depth `0` with no interval kept so
far, keeps intervals increasing and strictly apart. -/
theorem areIntervals_run_iterate_zero {rows : Array (Array ℤ)} {k iter cleft cright : ℕ} {sl sr : ℤ}
    (hit : iter ≤ 55) :
    AreIntervals
      (Id.run (iterate rows k iter (-longMax) longMax 0 0 cleft cright sl sr 0 #[])).toList :=
  (iterate_wf endsWF_zero hit (Nat.zero_le _) .nil nofun).1

theorem intervalsWF_domainBits_iff (l : List (Double × Double)) :
    IntervalsWF (domainBits l) ↔ AreIntervals l := by
  have h (h1 : ∀ i ∈ l, doubleValue i.1.bits ≤ doubleValue i.2.bits) :
      (domainValues l).IsChain (fun i j ↦ i.2 < j.1) ↔ l.Pairwise EndsBefore := by
    have hm := List.pairwise_map (f := fun i : Double × Double ↦
      (doubleValue i.1.bits, doubleValue i.2.bits)) (R := fun i j ↦ i.2 < j.1) (l := l)
    refine ⟨fun hc ↦ hm.mp (List.pairwise_of_isChain_of_le (fun i hi ↦ ?_) hc),
      fun hp ↦ (hm.mpr hp).isChain⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact h1 j hj
  simp only [IntervalsWF, AreSearchIntervals, AreIntervals, domainBits, List.map_map,
    List.forall_mem_map, Function.comp_def, ← Double.isNaN_eq_false_iff, IsInterval]
  constructor
  · intro ⟨h0, h1, hc⟩
    exact ⟨fun i hi ↦ ⟨(h0 i hi).1, (h0 i hi).2, h1 _ hi⟩, (h fun i hi ↦ h1 _ hi).mp hc⟩
  · intro ⟨h0, hp⟩
    exact ⟨fun i hi ↦ ⟨(h0 i hi).1, (h0 i hi).2.1⟩, fun i hi ↦ (h0 i hi).2.2,
      (h fun i hi ↦ (h0 i hi).2.2).mpr hp⟩

theorem meet_eq {a b : Double × Double} (ha1 : a.1.isNaN = false) (ha2 : a.2.isNaN = false)
    (hb1 : b.1.isNaN = false) (hb2 : b.2.isNaN = false) :
    meet a b = if doubleValue a.1.bits ≤ doubleValue b.1.bits then
      if doubleValue a.2.bits < doubleValue b.1.bits then (none, true)
      else if doubleValue a.2.bits ≤ doubleValue b.2.bits then (some (b.1, a.2), true)
      else (some b, false)
    else
      if doubleValue b.2.bits < doubleValue a.1.bits then (none, false)
      else if doubleValue b.2.bits ≤ doubleValue a.2.bits then (some (a.1, b.2), false)
      else (some a, true) := by
  simp only [meet, Double.le_eq_true_iff ha1 hb1, Double.lt_eq_true_iff ha2 hb1,
    Double.le_eq_true_iff ha2 hb2, Double.lt_eq_true_iff hb2 ha1, Double.le_eq_true_iff hb2 ha2]

theorem le_of_meet_snd_eq_true {a b : Double × Double} (ha : IsInterval a) (hb : IsInterval b)
    (h : (meet a b).2 = true) : doubleValue a.2.bits ≤ doubleValue b.2.bits := by
  rw [meet_eq ha.1 ha.2.1 hb.1 hb.2.1] at h
  have := hb.2.2
  split_ifs at h <;> grind

theorem le_of_meet_snd_eq_false {a b : Double × Double} (ha : IsInterval a) (hb : IsInterval b)
    (h : (meet a b).2 = false) : doubleValue b.2.bits ≤ doubleValue a.2.bits := by
  rw [meet_eq ha.1 ha.2.1 hb.1 hb.2.1] at h
  have := ha.2.2
  split_ifs at h <;> grind

theorem lt_of_meet_fst_eq_none {a b : Double × Double} (ha : IsInterval a) (hb : IsInterval b)
    (h : (meet a b).1 = none) :
    min (doubleValue a.2.bits) (doubleValue b.2.bits) <
      max (doubleValue a.1.bits) (doubleValue b.1.bits) := by
  rw [meet_eq ha.1 ha.2.1 hb.1 hb.2.1] at h
  have := ha.2.2
  have := hb.2.2
  split_ifs at h <;> grind

theorem doubleValue_eq_max_and_min_of_meet_fst_eq_some {a b : Double × Double} (ha : IsInterval a)
    (hb : IsInterval b) {i : Double × Double} (h : (meet a b).1 = some i) :
    doubleValue i.1.bits = max (doubleValue a.1.bits) (doubleValue b.1.bits) ∧
      doubleValue i.2.bits = min (doubleValue a.2.bits) (doubleValue b.2.bits) := by
  rw [meet_eq ha.1 ha.2.1 hb.1 hb.2.1] at h
  have := ha.2.2
  have := hb.2.2
  split_ifs at h <;> grind

theorem isInterval_of_meet_fst_eq_some {a b : Double × Double} (ha : IsInterval a)
    (hb : IsInterval b) {i : Double × Double} (h : (meet a b).1 = some i) : IsInterval i := by
  rw [meet_eq ha.1 ha.2.1 hb.1 hb.2.1] at h
  split_ifs at h <;> grind [IsInterval]

/-- An interval of the intersection is that of an interval of each list, which it meets. -/
theorem exists_of_mem_intersectList {as bs : List (Double × Double)}
    (has : ∀ a ∈ as, IsInterval a) (hbs : ∀ b ∈ bs, IsInterval b) {i : Double × Double}
    (hi : i ∈ intersectList as bs) : ∃ a ∈ as, ∃ b ∈ bs, (meet a b).1 = some i := by
  induction as, bs using intersectList.induct with
  | case1 => simp at hi
  | case2 => simp at hi
  | case3 a as b bs ih1 ih2 =>
    rw [intersectList_cons_cons, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ⟨a, by simp, b, by simp, Option.mem_toList.mp hi⟩
    split_ifs at hi
    · obtain ⟨a', ha', b', hb', h'⟩ := ih1 (fun a ha ↦ has a (by simp [ha])) hbs hi
      exact ⟨a', by simp [ha'], b', hb', h'⟩
    · obtain ⟨a', ha', b', hb', h'⟩ := ih2 has (fun b hb ↦ hbs b (by simp [hb])) hi
      exact ⟨a', ha', b', by simp [hb'], h'⟩

/-- An interval of the intersection begins at the beginning of an interval of each list at the
earliest. -/
theorem exists_le_of_mem_intersectList {as bs : List (Double × Double)}
    (has : ∀ a ∈ as, IsInterval a) (hbs : ∀ b ∈ bs, IsInterval b) {j : Double × Double}
    (hj : j ∈ intersectList as bs) :
    (∃ a ∈ as, doubleValue a.1.bits ≤ doubleValue j.1.bits) ∧
      ∃ b ∈ bs, doubleValue b.1.bits ≤ doubleValue j.1.bits := by
  obtain ⟨a, ha, b, hb, h⟩ := exists_of_mem_intersectList has hbs hj
  have := (doubleValue_eq_max_and_min_of_meet_fst_eq_some (has a ha) (hbs b hb) h).1
  exact ⟨⟨a, ha, this ▸ le_max_left _ _⟩, ⟨b, hb, this ▸ le_max_right _ _⟩⟩

theorem pairwise_intersectList {as bs : List (Double × Double)} (has : ∀ a ∈ as, IsInterval a)
    (hbs : ∀ b ∈ bs, IsInterval b) (hpa : as.Pairwise EndsBefore) (hpb : bs.Pairwise EndsBefore) :
    (intersectList as bs).Pairwise EndsBefore := by
  induction as, bs using intersectList.induct with
  | case1 => simp
  | case2 => simp
  | case3 a as b bs ih1 ih2 =>
    have hi' {i} (hi : i ∈ (meet a b).1.toList) :=
      (doubleValue_eq_max_and_min_of_meet_fst_eq_some (has a (by simp)) (hbs b (by simp))
        (Option.mem_toList.mp hi)).2
    rw [intersectList_cons_cons, List.pairwise_append]
    refine ⟨by cases (meet a b).1 <;> simp, ?_, fun i hi j hj ↦ ?_⟩
    · split_ifs
      · exact ih1 (fun a ha ↦ has a (by simp [ha])) hbs hpa.of_cons hpb
      · exact ih2 has (fun b hb ↦ hbs b (by simp [hb])) hpa hpb.of_cons
    rw [EndsBefore, hi' hi]
    split_ifs at hj
    · obtain ⟨a', ha', h'⟩ := (exists_le_of_mem_intersectList (fun a ha ↦ has a (by simp [ha]))
        hbs hj).1
      exact (min_le_left _ _).trans_lt ((List.rel_of_pairwise_cons hpa ha').trans_le h')
    · obtain ⟨b', hb', h'⟩ := (exists_le_of_mem_intersectList has
        (fun b hb ↦ hbs b (by simp [hb])) hj).2
      exact (min_le_right _ _).trans_lt ((List.rel_of_pairwise_cons hpb hb').trans_le h')

/-- A value in two intervals lies in the interval that `Ratpoints.Sturm.meet` notes for them. -/
theorem exists_meet_fst_eq_some {a b : Double × Double} (ha : IsInterval a) (hb : IsInterval b)
    {x : WithBotTop ℚ} (hxa : doubleValue a.1.bits ≤ x ∧ x ≤ doubleValue a.2.bits)
    (hxb : doubleValue b.1.bits ≤ x ∧ x ≤ doubleValue b.2.bits) :
    ∃ i, (meet a b).1 = some i ∧ doubleValue i.1.bits ≤ x ∧ x ≤ doubleValue i.2.bits := by
  rcases hm : (meet a b).1 with _ | i
  · have := lt_of_meet_fst_eq_none ha hb hm
    grind
  · have := doubleValue_eq_max_and_min_of_meet_fst_eq_some ha hb hm
    exact ⟨i, rfl, by grind⟩

/-- A value in an interval `a` and an interval of `b :: bs` lies in the interval that
`Ratpoints.Sturm.meet` notes for `a` and `b` when the step goes on with the next interval after `a`:
an interval after `b` begins after the end of `a`. -/
theorem exists_meet_of_snd_eq_true {a b : Double × Double} {bs : List (Double × Double)}
    (ha : IsInterval a) (hb : IsInterval b) (hpb : (b :: bs).Pairwise EndsBefore)
    (hf : (meet a b).2 = true) {x : WithBotTop ℚ}
    (hxa : doubleValue a.1.bits ≤ x ∧ x ≤ doubleValue a.2.bits) {b' : Double × Double}
    (hb' : b' ∈ b :: bs) (hxb : doubleValue b'.1.bits ≤ x ∧ x ≤ doubleValue b'.2.bits) :
    ∃ i, (meet a b).1 = some i ∧ doubleValue i.1.bits ≤ x ∧ x ≤ doubleValue i.2.bits := by
  rcases List.mem_cons.mp hb' with rfl | hb'
  · exact exists_meet_fst_eq_some ha hb hxa hxb
  · have := le_of_meet_snd_eq_true ha hb hf
    have := List.rel_of_pairwise_cons hpb hb'
    grind [EndsBefore]

/-- A value in an interval of `a :: as` and an interval `b` lies in the interval that
`Ratpoints.Sturm.meet` notes for `a` and `b` when the step goes on with the next interval after `b`:
an interval after `a` begins after the end of `b`. -/
theorem exists_meet_of_snd_eq_false {a b : Double × Double} {as : List (Double × Double)}
    (ha : IsInterval a) (hb : IsInterval b) (hpa : (a :: as).Pairwise EndsBefore)
    (hf : (meet a b).2 = false) {x : WithBotTop ℚ} {a' : Double × Double} (ha' : a' ∈ a :: as)
    (hxa : doubleValue a'.1.bits ≤ x ∧ x ≤ doubleValue a'.2.bits)
    (hxb : doubleValue b.1.bits ≤ x ∧ x ≤ doubleValue b.2.bits) :
    ∃ i, (meet a b).1 = some i ∧ doubleValue i.1.bits ≤ x ∧ x ≤ doubleValue i.2.bits := by
  rcases List.mem_cons.mp ha' with rfl | ha'
  · exact exists_meet_fst_eq_some ha hb hxa hxb
  · have := le_of_meet_snd_eq_false ha hb hf
    have := List.rel_of_pairwise_cons hpa ha'
    grind [EndsBefore]

/-- A value in an interval of each list lies in an interval of their intersection: the step at the
two intervals notes their intersection, and every other step moves past an interval that ends
before one of them begins. -/
theorem exists_mem_intersectList {as bs : List (Double × Double)} (has : ∀ a ∈ as, IsInterval a)
    (hbs : ∀ b ∈ bs, IsInterval b) (hpa : as.Pairwise EndsBefore) (hpb : bs.Pairwise EndsBefore)
    {x : WithBotTop ℚ} (hxa : ∃ a ∈ as, doubleValue a.1.bits ≤ x ∧ x ≤ doubleValue a.2.bits)
    (hxb : ∃ b ∈ bs, doubleValue b.1.bits ≤ x ∧ x ≤ doubleValue b.2.bits) :
    ∃ i ∈ intersectList as bs, doubleValue i.1.bits ≤ x ∧ x ≤ doubleValue i.2.bits := by
  induction as, bs using intersectList.induct with
  | case1 => simp at hxa
  | case2 => simp at hxb
  | case3 a as b bs ih1 ih2 =>
    obtain ⟨a', ha', hxa'⟩ := hxa
    obtain ⟨b', hb', hxb'⟩ := hxb
    simp only [intersectList_cons_cons, List.mem_append, Option.mem_toList]
    split_ifs with hf
    · rcases List.mem_cons.mp ha' with rfl | ha'
      · exact (exists_meet_of_snd_eq_true (has _ (by simp)) (hbs b (by simp)) hpb hf hxa' hb'
          hxb').imp fun _ h ↦ ⟨.inl h.1, h.2⟩
      · exact (ih1 (fun a ha ↦ has a (by simp [ha])) hbs hpa.of_cons hpb ⟨a', ha', hxa'⟩
          ⟨b', hb', hxb'⟩).imp fun _ h ↦ ⟨.inr h.1, h.2⟩
    · rcases List.mem_cons.mp hb' with rfl | hb'
      · exact (exists_meet_of_snd_eq_false (has a (by simp)) (hbs _ (by simp)) hpa
          (Bool.eq_false_iff.mpr hf) ha' hxa' hxb').imp fun _ h ↦ ⟨.inl h.1, h.2⟩
      · exact (ih2 has (fun b hb ↦ hbs b (by simp [hb])) hpa hpb.of_cons ⟨a', ha', hxa'⟩
          ⟨b', hb', hxb'⟩).imp fun _ h ↦ ⟨.inr h.1, h.2⟩

theorem length_intersectList_le (as bs : List (Double × Double)) :
    (intersectList as bs).length ≤ as.length + bs.length - 1 := by
  induction as, bs using intersectList.induct with
  | case1 => simp
  | case2 => simp
  | case3 a as b bs ih1 ih2 =>
    rw [intersectList_cons_cons, List.length_append]
    have : (meet a b).1.toList.length ≤ 1 := by cases (meet a b).1 <;> simp
    split_ifs <;> simp only [List.length_cons] at ih1 ih2 ⊢ <;> lia

theorem intervalsWF_intersectList {loc ivs : List (Double × Double)}
    (hloc : IntervalsWF (domainBits loc)) (hivs : IntervalsWF (domainBits ivs)) :
    IntervalsWF (domainBits (intersectList loc ivs)) := by
  rw [intervalsWF_domainBits_iff] at hloc hivs ⊢
  refine ⟨fun i hi ↦ ?_, pairwise_intersectList hloc.1 hivs.1 hloc.2 hivs.2⟩
  obtain ⟨a, ha, b, hb, h⟩ := exists_of_mem_intersectList hloc.1 hivs.1 hi
  exact isInterval_of_meet_fst_eq_some (hloc.1 a ha) (hivs.1 b hb) h

theorem inIntervals_domainValues_iff {l : List (Double × Double)} {x : ℚ} :
    InIntervals (domainValues l) x ↔
      ∃ i ∈ l, doubleValue i.1.bits ≤ x ∧ (x : WithBotTop ℚ) ≤ doubleValue i.2.bits := by
  simp [InIntervals, domainValues]

theorem inIntervals_of_inIntervals_intersectList {loc ivs : List (Double × Double)}
    (hloc : IntervalsWF (domainBits loc)) (hivs : IntervalsWF (domainBits ivs)) {x : ℚ}
    (hx : InIntervals (domainValues (intersectList loc ivs)) x) :
    InIntervals (domainValues loc) x ∧ InIntervals (domainValues ivs) x := by
  rw [intervalsWF_domainBits_iff] at hloc hivs
  simp only [inIntervals_domainValues_iff] at hx ⊢
  obtain ⟨i, hi, h1, h2⟩ := hx
  obtain ⟨a, ha, b, hb, h⟩ := exists_of_mem_intersectList hloc.1 hivs.1 hi
  have := doubleValue_eq_max_and_min_of_meet_fst_eq_some (hloc.1 a ha) (hivs.1 b hb) h
  exact ⟨⟨a, ha, by grind, by grind⟩, ⟨b, hb, by grind, by grind⟩⟩

theorem inIntervals_intersectList {loc ivs : List (Double × Double)}
    (hloc : IntervalsWF (domainBits loc)) (hivs : IntervalsWF (domainBits ivs)) {x : ℚ}
    (h1 : InIntervals (domainValues loc) x) (h2 : InIntervals (domainValues ivs) x) :
    InIntervals (domainValues (intersectList loc ivs)) x := by
  rw [intervalsWF_domainBits_iff] at hloc hivs
  rw [inIntervals_domainValues_iff] at h1 h2 ⊢
  exact exists_mem_intersectList hloc.1 hivs.1 hloc.2 hivs.2 h1 h2

/-- The Sturm step after a successful chain: no interval at the exit when `f` has no real root and
`f(0) < 0`, and otherwise the intersection of the intervals that the bisection keeps from
`[-∞, +∞]` with the caller's. -/
theorem run_computeSturm_of_chain_eq_some {c : List ℤ} {d iter : ℕ} {ivs : Array (Double × Double)}
    {rows : Array (Array ℤ)} (hc : Id.run (chain c d) = some rows) :
    Id.run (computeSturm c d iter ivs) =
      if (Id.run (countsAtInfinity rows (rows.size - 1))).2 =
          (Id.run (countsAtInfinity rows (rows.size - 1))).1 ∧ c.getD 0 0 < 0 then some #[]
      else some (Id.run (intersect (Id.run (iterate rows (rows.size - 1) iter (-longMax) longMax 0 0
        (Id.run (countsAtInfinity rows (rows.size - 1))).2
        (Id.run (countsAtInfinity rows (rows.size - 1))).1
        (if d % 2 = 1 then -(c.getD d 0).sign else (c.getD d 0).sign) (c.getD d 0).sign 0 #[]))
        ivs)) := by
  simp only [computeSturm, Id.run_bind, hc]
  split_ifs <;> rfl

/-- The intervals of the Sturm step at a depth of at most `55` for well-formed intervals of the
caller are well formed and inside the caller's intervals. -/
theorem computeSturm_wf {c : List ℤ} {d iter : ℕ} {ivs iv' : Array (Double × Double)}
    (hit : iter ≤ 55) (hwf : IntervalsWF (domainBits ivs.toList))
    (h : Id.run (computeSturm c d iter ivs) = some iv') :
    IntervalsWF (domainBits iv'.toList) ∧
      ∀ x, InIntervals (domainValues iv'.toList) x → InIntervals (domainValues ivs.toList) x := by
  rcases hc : Id.run (chain c d) with _ | rows
  · rw [← run_computeSturm_eq_none_iff c d iter ivs] at hc
    simp [hc] at h
  rw [run_computeSturm_of_chain_eq_some hc] at h
  generalize Id.run (countsAtInfinity rows (rows.size - 1)) = cnt at h
  by_cases hcnt : cnt.2 = cnt.1 ∧ c.getD 0 0 < 0
  · simp only [hcnt, and_self, ↓reduceIte, Option.some.injEq] at h
    subst h
    exact ⟨by simp [IntervalsWF, AreSearchIntervals], fun x hx ↦ by simp [InIntervals] at hx⟩
  simp only [hcnt, ↓reduceIte, Option.some.injEq] at h
  subst h
  rw [toList_run_intersect]
  refine ⟨intervalsWF_intersectList ?_ hwf,
    fun x hx ↦ (inIntervals_of_inIntervals_intersectList ?_ hwf hx).2⟩ <;>
  exact (intervalsWF_domainBits_iff _).mpr (areIntervals_run_iterate_zero hit)

end Sturm

end Ratpoints

end
