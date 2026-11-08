/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.TwoSided.Basic

/-!
# Mean, variance, mean absolute increments, rows: elementary facts

Helper lemmas about real functions on the cube, with no reference to the degree:

* the cube has `2 ^ n` points (`card_cube`, `sum_const_cube`, `four_pow_card`);
* the variance is nonnegative (`variance_nonneg`); it is `0` for a function with all values
  equal, in particular on the empty index type (`variance_eq_zero_of_const`,
  `variance_eq_zero_of_isEmpty`); the mean minimises the mean square distance to a constant
  (`variance_le_sq_dist`);
* `Inf_j(f)` is nonnegative and is one quarter of `E[(f(x) - f(x^j))^2]` (`inflR_nonneg`,
  `inflR_eq_quarter`);
* the mean absolute increments `L_j(f) = meanAbsIncr f j` are nonnegative (`meanAbsIncr_nonneg`)
  and satisfy `L_j(f)^2 ≤ 4 Inf_j(f)` (`meanAbsIncr_sq_le`; Section 2 of the paper);
* rows of a real function `f`: the cost of a row at `x` is at least `|f(x) - f(y)|` for every `y`
  (`abs_sub_le_rowSum`), so it is positive if `f` is not constant (`rowSum_pos`), and a number
  `K` that bounds the costs of rows at all points is positive if `Var(f) > 0` (`cost_pos`); every
  function has a row at every point (`exists_rows_cost`; Remark 7.12 of the paper);
* a row `a` of cost at most `K` at `u` gives `|f(u) - f(u^j)| ≤ a_j` and
  `∑_j |f(u) - f(u^j)| ≤ K` (`abs_incr_le_of_rows`, `sum_abs_incr_le_of_rows`); a bound `G` for
  these sums at all points `u` gives `L(f) = ∑_j L_j(f) ≤ G` (`sum_meanAbsIncr_le`); so
  `L(f) ≤ K` for a function with rows of cost at most `K` (`sum_meanAbsIncr_le_cost`).
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Level

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cube has `2 ^ n` points. -/
theorem card_cube : ((Fintype.card (Cube ι) : ℕ) : ℝ) = 2 ^ Fintype.card ι := by
  have h : Fintype.card (Cube ι) = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_bool]
  rw [h]
  push_cast
  rfl

/-- Sum of a constant over the cube. -/
theorem sum_const_cube (c : ℝ) : ∑ _x : Cube ι, c = 2 ^ Fintype.card ι * c := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube]

omit [DecidableEq ι] in
/-- `4 ^ n = 4 · 4 ^ (n - 1)` for `n ≥ 1`. -/
theorem four_pow_card [Nonempty ι] :
    (4 : ℝ) ^ Fintype.card ι = 4 * 4 ^ (Fintype.card ι - 1) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  rw [← pow_succ']
  congr 1
  omega

/-! ### Mean and variance -/

theorem variance_nonneg (f : Cube ι → ℝ) : 0 ≤ variance f := by
  unfold variance
  exact div_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _)) (by positivity)

/-- A function with all values equal has variance zero. -/
theorem variance_eq_zero_of_const (f : Cube ι → ℝ) (h : ∀ x y, f x = f y) : variance f = 0 := by
  have hm : ∀ x, f x = mean f := by
    intro x
    unfold mean
    rw [Finset.sum_congr rfl (fun y _ => h y x), sum_const_cube,
      mul_div_cancel_left₀ _ (by positivity)]
  unfold variance
  rw [Finset.sum_eq_zero (fun x _ => by rw [hm x, sub_self]; norm_num), zero_div]

/-- On the empty index type every variance is `0`. -/
theorem variance_eq_zero_of_isEmpty [IsEmpty ι] (f : Cube ι → ℝ) : variance f = 0 :=
  variance_eq_zero_of_const f (fun x y => congrArg f (Subsingleton.elim x y))

/-- `E (f - E f) = 0`, unnormalised. -/
theorem sum_sub_mean (f : Cube ι → ℝ) : ∑ x, (f x - mean f) = 0 := by
  rw [Finset.sum_sub_distrib, sum_const_cube]
  unfold mean
  rw [mul_div_cancel₀ _ (by positivity), sub_self]

/-- The mean minimises the mean square distance to a constant. -/
theorem variance_le_sq_dist (f : Cube ι → ℝ) (c : ℝ) :
    variance f ≤ (∑ x, (f x - c) ^ 2) / 2 ^ Fintype.card ι := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have h1 : ∑ x, (f x - c) ^ 2
      = ∑ x, (f x - mean f) ^ 2 + 2 * (mean f - c) * ∑ x, (f x - mean f)
        + ∑ _x : Cube ι, (mean f - c) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  have h2 : 0 ≤ ∑ _x : Cube ι, (mean f - c) ^ 2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  unfold variance
  refine div_le_div_of_nonneg_right ?_ hpos.le
  rw [h1, sum_sub_mean, mul_zero, add_zero]
  exact le_add_of_nonneg_right h2

/-! ### Influences and mean absolute increments -/

theorem inflR_nonneg (f : Cube ι → ℝ) (j : ι) : 0 ≤ inflR f j := by
  unfold inflR
  exact div_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _)) (by positivity)

/-- `inflR` is one quarter of the unnormalised L2 influence `E[(f(x) - f(x^j))^2]`. -/
theorem inflR_eq_quarter (f : Cube ι → ℝ) (j : ι) :
    inflR f j = (∑ x, (f x - f (flipSet x {j})) ^ 2) / 2 ^ Fintype.card ι / 4 := by
  have h : ∀ x : Cube ι,
      ((f x - f (flipSet x {j})) / 2) ^ 2 = (f x - f (flipSet x {j})) ^ 2 / 4 :=
    fun x => by ring
  simp only [inflR, h]
  rw [← Finset.sum_div, div_right_comm]

theorem meanAbsIncr_nonneg (f : Cube ι → ℝ) (j : ι) : 0 ≤ meanAbsIncr f j :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)

/-- `L_j(f)^2 ≤ 4 Inf_j(f)` (the Cauchy–Schwarz inequality; Section 2 of the paper). -/
theorem meanAbsIncr_sq_le (f : Cube ι → ℝ) (j : ι) : meanAbsIncr f j ^ 2 ≤ 4 * inflR f j := by
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Cube ι)))
    (f := fun x => |f x - f (flipSet x {j})|)
  simp only [sq_abs] at h
  rw [Finset.card_univ, card_cube] at h
  have e : 4 * inflR f j
      = (2 ^ Fintype.card ι * ∑ x, (f x - f (flipSet x {j})) ^ 2) / (2 ^ Fintype.card ι) ^ 2 := by
    rw [inflR_eq_quarter]
    field_simp
  unfold meanAbsIncr
  rw [e, div_pow]
  exact div_le_div_of_nonneg_right h (by positivity)

/-! ### Rows of a real function -/

omit [DecidableEq ι] in
/-- The cost of a row of `f` at `x` is at least `|f(x) - f(y)|`, for every `y`. -/
theorem abs_sub_le_rowSum {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (x y : Cube ι) :
    |f x - f y| ≤ ∑ j, a x j :=
  le_trans (hrow x y)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => ha x j))

omit [DecidableEq ι] in
/-- A row at `x` has positive cost if `f` takes another value somewhere. -/
theorem rowSum_pos {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) {x y : Cube ι} (hxy : f x ≠ f y) :
    0 < ∑ j, a x j :=
  lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hxy)) (abs_sub_le_rowSum ha hrow x y)

/-- If `f` has a row of cost at most `K` at every point and `Var(f) > 0`, then `K > 0`. -/
theorem cost_pos {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (hvar : 0 < variance f) : 0 < K := by
  by_contra hK
  have hconst : ∀ x y, f x = f y := by
    intro x y
    by_contra hxy
    exact hK (lt_of_lt_of_le (rowSum_pos ha hrow hxy) (hsum x))
  rw [variance_eq_zero_of_const f hconst] at hvar
  exact lt_irrefl 0 hvar

/-- A row at `u` bounds each increment of `f` at `u`: `|f(u) - f(u^j)| ≤ a u j`. -/
theorem abs_incr_le_of_rows {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ}
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (u : Cube ι) (j : ι) :
    |f u - f (flipSet u {j})| ≤ a u j := by
  have h := hrow u (flipSet u {j})
  rwa [diffSet_flipSet, Finset.sum_singleton] at h

/-- A row at `u` of cost at most `K` bounds the sum of the increments of `f` at `u`:
`∑_j |f(u) - f(u^j)| ≤ K`. -/
theorem sum_abs_incr_le_of_rows {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (u : Cube ι) : ∑ j, |f u - f (flipSet u {j})| ≤ K :=
  le_trans (Finset.sum_le_sum fun j _ => abs_incr_le_of_rows hrow u j) (hsum u)

/-- If `∑_j |f(u) - f(u^j)| ≤ G` at every point `u`, then `L(f) = ∑_j L_j(f) ≤ G`. -/
theorem sum_meanAbsIncr_le (f : Cube ι → ℝ) {G : ℝ}
    (hG : ∀ u, ∑ j, |f u - f (flipSet u {j})| ≤ G) : ∑ j, meanAbsIncr f j ≤ G := by
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  unfold meanAbsIncr
  rw [← Finset.sum_div, div_le_iff₀ h2, Finset.sum_comm]
  calc ∑ x, ∑ j, |f x - f (flipSet x {j})| ≤ ∑ _x : Cube ι, G :=
        Finset.sum_le_sum (fun x _ => hG x)
    _ = G * 2 ^ Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube, mul_comm]

/-- The sum `L(f)` of the mean absolute increments of a function with rows of cost at most `K`
is at most `K`. -/
theorem sum_meanAbsIncr_le_cost {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) :
    ∑ j, meanAbsIncr f j ≤ K :=
  sum_meanAbsIncr_le f (sum_abs_incr_le_of_rows hsum hrow)

omit [DecidableEq ι] in
/-- Every real function on the cube has a row at every point, of cost at most some `K`: the
hypotheses on rows can be met for every function (Remark 7.12 of the paper). -/
theorem exists_rows_cost (f : Cube ι → ℝ) :
    ∃ (K : ℝ) (a : Cube ι → ι → ℝ), (∀ x j, 0 ≤ a x j) ∧ (∀ x, ∑ j, a x j ≤ K) ∧
      ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j := by
  classical
  have hnn : ∀ x : Cube ι, 0 ≤ ∑ z, |f x - f z| := fun x =>
    Finset.sum_nonneg (fun z _ => abs_nonneg _)
  refine ⟨∑ x : Cube ι, ∑ _j : ι, ∑ z, |f x - f z|, fun x _ => ∑ z, |f x - f z|,
    fun x _ => hnn x, fun x => ?_, fun x y => ?_⟩
  · exact Finset.single_le_sum (f := fun x : Cube ι => ∑ _j : ι, ∑ z, |f x - f z|)
      (fun x _ => Finset.sum_nonneg (fun _ _ => hnn x)) (Finset.mem_univ x)
  · by_cases hxy : x = y
    · rw [hxy, sub_self, abs_zero]
      exact Finset.sum_nonneg (fun _ _ => hnn y)
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra hcon
        exact hxy (funext (fun i => by_contra (fun h => hcon ⟨i, h⟩)))
      have hmem : i ∈ diffSet x y := mem_diffSet.mpr hi
      calc |f x - f y| ≤ ∑ z, |f x - f z| :=
            Finset.single_le_sum (f := fun z => |f x - f z|) (fun z _ => abs_nonneg _)
              (Finset.mem_univ y)
        _ ≤ ∑ _j ∈ diffSet x y, ∑ z, |f x - f z| :=
            Finset.single_le_sum (f := fun _ : ι => ∑ z, |f x - f z|) (fun _ _ => hnn x) hmem

end Level
end AaronsonAmbainis
