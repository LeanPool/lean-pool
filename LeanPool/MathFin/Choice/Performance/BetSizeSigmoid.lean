/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Performance.Ratios

/-!
# Sigmoid bet-sizing function

López de Prado (*Advances in Financial Machine Learning*, Wiley 2018, ch. 10) sizes
a bet from the divergence `x = f - p` between the forecast price `f` and the
current market price `p` via the sigmoid `m(x) = x / √(w + x²)` (`w > 0` a width
parameter), rather than a hard threshold.

This file proves the three structural properties that justify using `m` as a
bet-sizing map: it is odd, bounded in `(-1,1)`, and strictly increasing in `x`
whenever `w > 0`. It also ties `m` to the Kelly criterion: fed the z-statistic
`z = (p − ½)/√(p(1 − p))` of a predicted win probability `p` (scaled by `√w`), the
sigmoid returns exactly `2p − 1`, the Kelly fraction of an even-money bet
(`kellyFraction p 1`, `Choice/Performance/Ratios.lean`). López de Prado's probability-based size
`2Φ(z) − 1` (ch. 10) is a different map and is not treated here.

## Main definitions

* `betSize`: the bet-sizing sigmoid `m(x) = x / √(w + x²)` with width parameter `w`.

## Main results

* `betSize_odd`: `m w (-x) = -m w x`.
* `betSize_mem_Ioo`: `m w x ∈ (-1, 1)` for `w > 0`.
* `betSize_strictMono`: `w > 0 → StrictMono (m w ·)`.
* `betSize_sqrt_mul_zScore`: `m w (√w · z) = kellyFraction p 1 = 2p − 1` for `0 < p < 1`.

## References

* [J. L. Kelly, *A new interpretation of information rate*][Kelly1956]
* [López de Prado, *Advances in Financial Machine Learning*][LopezDePrado2018], ch. 10

## Tags

bet sizing, López de Prado, sigmoid, Kelly criterion, machine learning for finance, MSC 91G10,
JEL G11
-/

@[expose] public section

namespace MathFin

/-- The bet-sizing sigmoid `m(x) = x / √(w + x²)`. -/
noncomputable def betSize (w x : ℝ) : ℝ := x / Real.sqrt (w + x ^ 2)

theorem betSize_odd (w x : ℝ) : betSize w (-x) = -betSize w x := by
  simp [betSize, neg_div]

theorem betSize_mem_Ioo {w : ℝ} (hw : 0 < w) (x : ℝ) : betSize w x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hpos : 0 < w + x ^ 2 := by positivity
  have hsqrt_pos : 0 < Real.sqrt (w + x ^ 2) := Real.sqrt_pos.mpr hpos
  have habs : |x| < Real.sqrt (w + x ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hm_abs : |betSize w x| < 1 := by
    rw [betSize, abs_div, abs_of_pos hsqrt_pos, div_lt_one hsqrt_pos]
    exact habs
  exact abs_lt.mp hm_abs

/-- Core monotonicity step: for `0 ≤ p < q` and `w > 0`,
`p · √(w+q²) < q · √(w+p²)`. -/
theorem mul_sqrt_add_sq_lt_of_nonneg {w : ℝ} (hw : 0 < w) {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) :
    p * Real.sqrt (w + q ^ 2) < q * Real.sqrt (w + p ^ 2) := by
  have hq : 0 < q := lt_of_le_of_lt hp hpq
  have hs1pos : 0 < Real.sqrt (w + p ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsqlt : (p * Real.sqrt (w + q ^ 2)) ^ 2 < (q * Real.sqrt (w + p ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ w + q ^ 2),
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ w + p ^ 2)]
    have hsq : p ^ 2 < q ^ 2 := sq_lt_sq' (by linarith) hpq
    nlinarith [mul_lt_mul_of_pos_right hsq hw]
  exact lt_of_pow_lt_pow_left₀ 2 (mul_pos hq hs1pos).le hsqlt

/-- The key cross-multiplied inequality behind strict monotonicity, for any
reals `a < b` (not just nonnegative ones). -/
theorem mul_sqrt_add_sq_lt {w : ℝ} (hw : 0 < w) {a b : ℝ} (hab : a < b) :
    a * Real.sqrt (w + b ^ 2) < b * Real.sqrt (w + a ^ 2) := by
  rcases le_total 0 a with ha | ha
  · exact mul_sqrt_add_sq_lt_of_nonneg hw ha hab
  · rcases le_total b 0 with hb | hb
    · have := mul_sqrt_add_sq_lt_of_nonneg hw (by linarith : (0:ℝ) ≤ -b) (by linarith : -b < -a)
      have ha2 : (-a) ^ 2 = a ^ 2 := by ring
      have hb2 : (-b) ^ 2 = b ^ 2 := by ring
      rw [ha2, hb2] at this
      linarith
    · have hs1pos : 0 < Real.sqrt (w + a ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have hs2pos : 0 < Real.sqrt (w + b ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have h1 : a * Real.sqrt (w + b ^ 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha hs2pos.le
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · have hb0 : 0 < b := by rw [ha0] at hab; exact hab
        have h2 : 0 < b * Real.sqrt (w + a ^ 2) := mul_pos hb0 hs1pos
        linarith
      · have h2 : a * Real.sqrt (w + b ^ 2) < 0 := mul_neg_of_neg_of_pos ha0 hs2pos
        have h3 : 0 ≤ b * Real.sqrt (w + a ^ 2) := mul_nonneg hb hs1pos.le
        linarith

theorem betSize_strictMono {w : ℝ} (hw : 0 < w) : StrictMono (betSize w) := by
  intro a b hab
  have hs1pos : 0 < Real.sqrt (w + a ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2pos : 0 < Real.sqrt (w + b ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [betSize, betSize, div_lt_div_iff₀ hs1pos hs2pos]
  exact mul_sqrt_add_sq_lt hw hab

/-- **The sigmoid of the probability z-score is the even-money Kelly fraction.** For a
predicted win probability `0 < p < 1`, let `z = (p − ½)/√(p(1 − p))` be the z-statistic of
`p` against `½`. For every width `w > 0`, `m w (√w · z) = 2p − 1 = kellyFraction p 1`, the
Kelly fraction of an even-money bet (`Choice/Performance/Ratios.lean`). The width only rescales
the argument, and `w + w z² = w / (4 p (1 − p))`, so `√w·z / √(w + w z²) = 2p − 1`. -/
theorem betSize_sqrt_mul_zScore {w p : ℝ} (hw : 0 < w) (hp₀ : 0 < p) (hp₁ : p < 1) :
    betSize w (√w * ((p - 1 / 2) / √(p * (1 - p)))) = kellyFraction p 1 := by
  have hpq : 0 < p * (1 - p) := mul_pos hp₀ (sub_pos.2 hp₁)
  have hp0 : p ≠ 0 := hp₀.ne'
  have hq0 : 1 - p ≠ 0 := (sub_pos.2 hp₁).ne'
  have hs0 : √(p * (1 - p)) ≠ 0 := (Real.sqrt_pos.2 hpq).ne'
  have hw0 : √w ≠ 0 := (Real.sqrt_pos.2 hw).ne'
  have hrad : w + (√w * ((p - 1 / 2) / √(p * (1 - p)))) ^ 2 =
      (√w / (2 * √(p * (1 - p)))) ^ 2 := by
    rw [mul_pow, div_pow, div_pow, mul_pow, Real.sq_sqrt hw.le, Real.sq_sqrt hpq.le]
    field_simp
    ring
  rw [betSize, hrad, Real.sqrt_sq (by positivity), kellyFraction]
  field_simp
  ring

end MathFin
