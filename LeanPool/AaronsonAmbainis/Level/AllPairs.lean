/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import LeanPool.AaronsonAmbainis.Level.Rows
public import LeanPool.AaronsonAmbainis.TwoSided.Overlap

/-!
# The all-pairs inequality at one level

Let `f` be a real function on the cube with a row `a x` at every point `x`, and let `t` be a
real number. The all-pairs inequality (Proposition 5.2 of the paper), applied to the level
function `g_t = 1_{f > t}` with the rows `a x / |f x - t|` (`levRow`, Lemma 2.4 (iii) of the
paper), reads

`2 ∑_x ∑_y (f x - t)⁺ (t - f y)⁺ / s_xy ≤ 2^n ∑_j b_j(g_t) / w_j`,
`s_xy = ∑_{j ∈ Δ(x,y)} w_j a^x_j a^y_j`

(`level_allPairs`; Lemma 7.2 of the paper, multiplied by `2`), for every real `t`. Also:
`s_xy > 0` when `f y < f x` (`pairSum_pos`; Lemma 7.1), and `b_j(g_t)` is the number of points
`x` with `f(x^j) ≤ t < f(x)` (`bdry_lev`).
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Level

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The overlap sum of the level rows at a point above the level and a point below it
(Lemma 7.1 (i) of the paper). -/
lemma sum_levRow (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) (w : ι → ℝ) {t : ℝ} {x y : Cube ι}
    (hx : t < f x) (hy : f y < t) :
    ∑ j ∈ diffSet x y, w j * levRow f a t x j * levRow f a t y j
      = (∑ j ∈ diffSet x y, w j * a x j * a y j) / ((f x - t) * (t - f y)) := by
  have hxne : f x ≠ t := ne_of_gt hx
  have hyne : f y ≠ t := ne_of_lt hy
  have h1 : f x - t ≠ 0 := sub_ne_zero.mpr hxne
  have h2 : t - f y ≠ 0 := sub_ne_zero.mpr hyne.symm
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have e1 : levRow f a t x j = a x j / (f x - t) := by
    change (if f x = t then 1 else a x j / |f x - t|) = a x j / (f x - t)
    rw [ite_eq_right hxne, abs_of_pos (sub_pos.mpr hx)]
  have e2 : levRow f a t y j = a y j / (t - f y) := by
    change (if f y = t then 1 else a y j / |f y - t|) = a y j / (t - f y)
    rw [ite_eq_right hyne, abs_of_neg (sub_neg.mpr hy), neg_sub]
  rw [e1, e2]
  field_simp

omit [DecidableEq ι] in
/-- Rows at two points with different values overlap on the difference set: `s_xy > 0`
(Lemma 7.1 (ii) of the paper). -/
theorem pairSum_pos {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) {w : ι → ℝ} (hw : ∀ j, 0 < w j)
    {x y : Cube ι} (hxy : f y < f x) :
    0 < ∑ j ∈ diffSet x y, w j * a x j * a y j := by
  classical
  have hx : (f x + f y) / 2 < f x := by linarith
  have hy : f y < (f x + f y) / 2 := by linarith
  have hne : lev f ((f x + f y) / 2) x ≠ lev f ((f x + f y) / 2) y := by
    simp [lev, hx, not_lt.mpr hy.le]
  have h := overlap_pos hne (isRow_levRow ha hrow ((f x + f y) / 2) x)
    (isRow_levRow ha hrow ((f x + f y) / 2) y) hw
  rw [sum_levRow f a w hx hy] at h
  have hden : 0 < (f x - (f x + f y) / 2) * ((f x + f y) / 2 - f y) :=
    mul_pos (by linarith) (by linarith)
  by_contra hcon
  have h0 : (∑ j ∈ diffSet x y, w j * a x j * a y j)
      / ((f x - (f x + f y) / 2) * ((f x + f y) / 2 - f y)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) hden.le
  linarith

/-- The all-pairs inequality at the level `t` (Lemma 7.2 of the paper, multiplied by `2`), from
the all-pairs inequality for Boolean functions. -/
theorem level_allPairs (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) (t : ℝ) :
    2 * ∑ x, ∑ y, max (f x - t) 0 * max (t - f y) 0
          * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
      ≤ 2 ^ Fintype.card ι * ∑ j, (bdry (lev f t) j : ℝ) / w j := by
  have hrows := isRow_levRow ha hrow t
  have h := hAllPairs ι (lev f t) w hw (levRow f a t) hrows
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : t < f x
  · have hlx : lev f t x = true := by simp [lev, hx]
    rw [ite_eq_left hlx, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : t < f y
    · have hly : ¬ lev f t y = false := by simp [lev, hy]
      rw [ite_eq_right hly, max_eq_right (by linarith : t - f y ≤ 0), mul_zero, zero_mul]
    · have hly : lev f t y = false := by simp [lev, hy]
      rw [ite_eq_left hly]
      rcases lt_or_eq_of_le (not_lt.mp hy) with hyt | hyt
      · rw [sum_levRow f a w hx hyt, inv_div, max_eq_left (by linarith : 0 ≤ f x - t),
          max_eq_left (by linarith : 0 ≤ t - f y), div_eq_mul_inv]
      · rw [max_eq_right (by linarith : t - f y ≤ 0), mul_zero, zero_mul]
        exact inv_nonneg.mpr (Finset.sum_nonneg fun j _ =>
          mul_nonneg (mul_nonneg (hw j).le ((hrows x).1 j)) ((hrows y).1 j))
  · have hlx : ¬ lev f t x = true := by simp [lev, hx]
    rw [ite_eq_right hlx]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro y _
    rw [max_eq_right (by linarith [not_lt.mp hx] : f x - t ≤ 0), zero_mul, zero_mul]

/-- `b_j(g_t)` is the number of points `x` with `f(x^j) ≤ t < f(x)`. -/
lemma bdry_lev (f : Cube ι → ℝ) (t : ℝ) (j : ι) :
    (bdry (lev f t) j : ℝ)
      = ∑ x, if f (flipSet x {j}) ≤ t ∧ t < f x then (1 : ℝ) else 0 := by
  unfold bdry
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro x _
  apply if_congr _ rfl rfl
  simp only [lev, decide_eq_true_eq, decide_eq_false_iff_not, not_lt]
  exact and_comm

end Level
end AaronsonAmbainis
