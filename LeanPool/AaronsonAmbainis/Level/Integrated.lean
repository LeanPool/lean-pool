/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Level.Basic
public import LeanPool.AaronsonAmbainis.Level.Integral
public import LeanPool.AaronsonAmbainis.Level.AllPairs

/-!
# The integrated all-pairs inequality

Let `f` be a real function on the cube with a row `a x` at every point `x`, and let `w > 0`.
Integrating the all-pairs inequality at the level `t` (`level_allPairs`) over all real `t`
(`level_integration`) gives the integrated all-pairs inequality (Proposition 7.4 of the paper):

`∑_{(x,y) : f y < f x} (f x - f y)^3 / (6 s_xy) ≤ 4^(n-1) ∑_j L_j / w_j`,
`s_xy = ∑_{j ∈ Δ(x,y)} w_j a^x_j a^y_j`,  `L_j = meanAbsIncr f j = E_x |f x - f (x^j)|`.

* `Level.integrated_core` — the form that comes out of the integration;
* `Level.integrated_four_mul` — multiplied by `4`, so that `4^n` appears;
* `integratedAllPairs_of_allPairs : AllPairsInequality → IntegratedAllPairsInequality` — with
  `4^(n-1)` as printed above (for `n = 0` both sides are `0`).

The denominators are positive: `Level.pairSum_pos` in `Level/AllPairs.lean`.
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

namespace Level

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The integrated all-pairs inequality, in the form that comes out of the integration over the
level. -/
theorem integrated_core (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    2 * ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
      ≤ 2 ^ Fintype.card ι * ∑ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j := by
  have key := level_integration (univ : Finset (Cube ι × Cube ι)) (univ : Finset (ι × Cube ι))
    (fun z => 2 * (∑ j ∈ diffSet z.1 z.2, w j * a z.1 j * a z.2 j)⁻¹)
    (fun z => f z.1) (fun z => f z.2)
    (fun k => 2 ^ Fintype.card ι / w k.1) (fun k => f (flipSet k.2 {k.1})) (fun k => f k.2) ?_
  · rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at key
    calc 2 * ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
        = ∑ x, ∑ y, 2 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
            * (max (f x - f y) 0 ^ 3 / 6) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
      _ ≤ ∑ j, ∑ x, 2 ^ Fintype.card ι / w j * max (f x - f (flipSet x {j})) 0 := key
      _ = 2 ^ Fintype.card ι * ∑ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_div, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
  · intro t
    have h := level_allPairs hAllPairs f a ha hrow w hw t
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc ∑ x, ∑ y, 2 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
            * (max (f x - t) 0 * max (t - f y) 0)
        = 2 * ∑ x, ∑ y, max (f x - t) 0 * max (t - f y) 0
            * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
      _ ≤ 2 ^ Fintype.card ι * ∑ j, (bdry (lev f t) j : ℝ) / w j := h
      _ = ∑ j, ∑ x, 2 ^ Fintype.card ι / w j
            * (if f (flipSet x {j}) ≤ t ∧ t < f x then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [bdry_lev, Finset.sum_div, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring

/-- `∑_x (f x - f (x^j))⁺ = (1/2) ∑_x |f x - f (x^j)|` (Lemma 7.3 (iii) of the paper). -/
lemma sum_posPart_incr (f : Cube ι → ℝ) (j : ι) :
    ∑ x, max (f x - f (flipSet x {j})) 0 = (∑ x, |f x - f (flipSet x {j})|) / 2 := by
  have hinv : Function.Involutive (fun x : Cube ι => flipSet x {j}) :=
    fun x => flipSet_flipSet_self x {j}
  have hflip : ∑ x, max (f (flipSet x {j}) - f x) 0 = ∑ x, max (f x - f (flipSet x {j})) 0 := by
    have h := Equiv.sum_comp hinv.toPerm (fun x => max (f x - f (flipSet x {j})) 0)
    rw [← h]
    apply Finset.sum_congr rfl
    intro x _
    change max (f (flipSet x {j}) - f x) 0
      = max (f (flipSet x {j}) - f (flipSet (flipSet x {j}) {j})) 0
    rw [flipSet_flipSet_self]
  have h2 : ∀ x, |f x - f (flipSet x {j})|
      = max (f x - f (flipSet x {j})) 0 + max (f (flipSet x {j}) - f x) 0 := by
    intro x
    rcases le_total 0 (f x - f (flipSet x {j})) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : f (flipSet x {j}) - f x ≤ 0),
        abs_of_nonneg h, add_zero]
    · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ f (flipSet x {j}) - f x),
        abs_of_nonpos h, zero_add]
      ring
  rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_add_distrib, hflip]
  ring

/-- The integrated all-pairs inequality, multiplied by `4`: for a real function `f` on the cube,
rows `a x` of `f` and weights `w > 0`,
`4 ∑_{(x,y) : f y < f x} (f x - f y)^3 / (6 ∑_{j ∈ Δ(x,y)} w_j a^x_j a^y_j) ≤ 4^n ∑_j L_j / w_j`,
where `L_j = meanAbsIncr f j = E_x |f x - f (x^j)|`. -/
theorem integrated_four_mul (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    4 * ∑ x, ∑ y ∈ univ.filter (fun y => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      ≤ 4 ^ Fintype.card ι * ∑ j, meanAbsIncr f j / w j := by
  have h := integrated_core hAllPairs f a ha hrow w hw
  have hL : ∑ x, ∑ y ∈ univ.filter (fun y => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      = ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6
          * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹ := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hxy : f y < f x
    · rw [ite_eq_left hxy, max_eq_left (by linarith : 0 ≤ f x - f y)]
      ring
    · rw [ite_eq_right hxy, max_eq_right (by linarith [not_lt.mp hxy] : f x - f y ≤ 0)]
      ring
  have hRt : ∀ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j
      = 2 ^ Fintype.card ι / 2 * (meanAbsIncr f j / w j) := by
    intro j
    have h2 : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
    rw [sum_posPart_incr]
    unfold meanAbsIncr
    field_simp
  have h4 : (4 : ℝ) ^ Fintype.card ι = 2 ^ Fintype.card ι * 2 ^ Fintype.card ι := by
    rw [← mul_pow]
    norm_num
  rw [hL]
  calc 4 * ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6
          * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
      ≤ 2 * (2 ^ Fintype.card ι * ∑ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j) := by
        linarith
    _ = 4 ^ Fintype.card ι * ∑ j, meanAbsIncr f j / w j := by
        rw [Finset.sum_congr rfl (fun j _ => hRt j), ← Finset.mul_sum, h4]
        ring

end Level

/-- The integrated all-pairs inequality (Proposition 7.4 of the paper) from the all-pairs
inequality for Boolean functions (Proposition 5.2). -/
theorem integratedAllPairs_of_allPairs : AllPairsInequality → IntegratedAllPairsInequality := by
  intro hAllPairs ι _ _ f a ha hrow w hw
  have h := Level.integrated_four_mul hAllPairs f a ha hrow w hw
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hL : ∑ x, ∑ y ∈ univ.filter (fun y => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      apply Finset.sum_eq_zero
      intro y hy
      have hlt := (Finset.mem_filter.mp hy).2
      rw [Subsingleton.elim y x] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [hL, Finset.univ_eq_empty (α := ι), Finset.sum_empty, mul_zero]
  · rw [Level.four_pow_card, mul_assoc] at h
    linarith

end AaronsonAmbainis
