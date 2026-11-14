/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import LeanPool.AaronsonAmbainis.TwoSided.Basic

/-!
# Level functions and their rows

For a real function `f` on the cube and a real number `t`, `lev f t` is the level function
`g_t = 1_{f > t}`. If `a x` is a row of `f` at `x`, then `levRow f a t x`, which is
`a x / |f x - t|` (and the all-ones vector when `f x = t`), is a row of `g_t` at `x`
(`isRow_levRow`; the cases `f x ≠ t` and `f x = t` are parts (iii) and (i) of Lemma 2.4 of the
paper). These are the rows `λ^{t,x}` of Section 7.1 of the paper.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Level

open Finset

/-- The level function `g_t = 1_{f > t}`. -/
noncomputable def lev {ι : Type*} (f : Cube ι → ℝ) (t : ℝ) : Cube ι → Bool :=
  fun x => decide (t < f x)

/-- The row of `g_t` at `x` built from the row `a x` of `f`: `a x / |f x - t|`
(and the all-ones vector when `f x = t`). -/
noncomputable def levRow {ι : Type*} (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) (t : ℝ) :
    Cube ι → ι → ℝ :=
  fun x j => if f x = t then 1 else a x j / |f x - t|

/-- If `g_t` separates `x` and `y` then `t` lies weakly between `f x` and `f y`. -/
theorem abs_sub_le_of_lev_ne {ι : Type*} {f : Cube ι → ℝ} {t : ℝ} {x y : Cube ι}
    (h : lev f t y ≠ lev f t x) : |f x - t| ≤ |f x - f y| := by
  unfold lev at h
  by_cases h1 : t < f x <;> by_cases h2 : t < f y
  · simp [h1, h2] at h
  · rw [abs_of_pos (sub_pos.mpr h1)]
    exact le_trans (by linarith) (le_abs_self _)
  · rw [abs_sub_comm (f x) t, abs_sub_comm (f x) (f y), abs_of_nonneg (by linarith)]
    exact le_trans (by linarith) (le_abs_self _)
  · simp [h1, h2] at h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `levRow f a t x` is a row of `g_t` at `x`. -/
theorem isRow_levRow {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (t : ℝ) (x : Cube ι) :
    IsRow (lev f t) x (levRow f a t x) := by
  refine ⟨fun j => ?_, fun S hS => ?_⟩
  · unfold levRow
    split_ifs
    · exact zero_le_one
    · exact div_nonneg (ha x j) (abs_nonneg _)
  · by_cases hx : f x = t
    · have hne : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        rw [flipSet_empty] at hS
        exact hS rfl
      have h1 : ∀ j ∈ S, levRow f a t x j = 1 := fun j _ => by simp [levRow, hx]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hne.card_pos
    · have hpos : 0 < |f x - t| := abs_pos.mpr (sub_ne_zero.mpr hx)
      have h1 : |f x - t| ≤ ∑ j ∈ S, a x j := by
        have h2 := hrow x (flipSet x S)
        rw [diffSet_flipSet] at h2
        exact le_trans (abs_sub_le_of_lev_ne hS) h2
      have h3 : ∀ j ∈ S, levRow f a t x j = a x j / |f x - t| :=
        fun j _ => by simp [levRow, hx]
      rw [Finset.sum_congr rfl h3, ← Finset.sum_div, le_div_iff₀ hpos, one_mul]
      exact h1

end Level
end AaronsonAmbainis
