/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.TwoSided.Basic

/-!
# Averaging a function over one coordinate

For a coordinate `j` let `avg j f x = (f x + f (x^j)) / 2`. Then (Lemma 8.1 of the paper)

* `variance_avg`         — `Var f = Var (avg j f) + Inf_j f` (`f = avg j f + (f - f ∘ flip_j)/2`,
                           and the two parts are even and odd under the flip of `j`);
* `inflR_avg_le`         — `Inf_k (avg j f) ≤ Inf_k f` for every `k`;
* `meanAbsIncr_avg_le`   — `L_k (avg j f) ≤ L_k f` for every `k`;
* `meanAbsIncr_avg_self` — `L_j (avg j f) = 0`;
* `rows_avg`             — if `a x` is a row of `f` at `x` for every `x`, of cost at most `K`,
                           then `(a x + a (x^j)) / 2` is a row of `avg j f` at `x`, of cost at
                           most `K`.

Here `L_k(f) = meanAbsIncr f k` is the mean absolute increment of `f` in the coordinate `k`.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Average

open Finset

section NoFintype

variable {ι : Type*} [DecidableEq ι]

/-- Flips commute. -/
lemma flipSet_comm (x : Cube ι) (S T : Finset ι) :
    flipSet (flipSet x S) T = flipSet (flipSet x T) S := by
  funext i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [flipSet, hS, hT]

end NoFintype

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Flipping the same coordinates in two points does not change the set where they differ. -/
lemma diffSet_flip (x y : Cube ι) (S : Finset ι) :
    diffSet (flipSet x S) (flipSet y S) = diffSet x y := by
  ext i
  rw [mem_diffSet, mem_diffSet, flipSet_apply, flipSet_apply]
  by_cases hS : i ∈ S
  · rw [ite_eq_left hS, ite_eq_left hS]
    cases x i <;> cases y i <;> simp
  · rw [ite_eq_right hS, ite_eq_right hS]

/-- The flip of the coordinate `j` is a bijection of the cube. -/
lemma sum_flip (j : ι) (F : Cube ι → ℝ) : ∑ x, F (flipSet x {j}) = ∑ x, F x := by
  have hinv : Function.Involutive (fun x : Cube ι => flipSet x {j}) :=
    fun x => flipSet_flipSet_self x {j}
  exact Equiv.sum_comp hinv.toPerm F

/-- The average of `f` over the coordinate `j`. -/
noncomputable def avg (j : ι) (f : Cube ι → ℝ) : Cube ι → ℝ :=
  fun x => (f x + f (flipSet x {j})) / 2

omit [Fintype ι] in
lemma avg_flip (j : ι) (f : Cube ι → ℝ) (x : Cube ι) : avg j f (flipSet x {j}) = avg j f x := by
  unfold avg
  rw [flipSet_flipSet_self]
  ring

theorem mean_avg (j : ι) (f : Cube ι → ℝ) : mean (avg j f) = mean f := by
  unfold mean avg
  congr 1
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_flip j f]
  ring

/-- `Var f = Var (avg j f) + Inf_j f`. -/
theorem variance_avg (j : ι) (f : Cube ι → ℝ) :
    variance f = variance (avg j f) + inflR f j := by
  have hm := mean_avg j f
  have hre : ∑ x, (f (flipSet x {j}) - mean f) ^ 2 = ∑ x, (f x - mean f) ^ 2 :=
    sum_flip j (fun x => (f x - mean f) ^ 2)
  have hpt : ∀ x, (f x - mean f) ^ 2 + (f (flipSet x {j}) - mean f) ^ 2
      = 2 * ((avg j f x - mean f) ^ 2 + ((f x - f (flipSet x {j})) / 2) ^ 2) := by
    intro x
    unfold avg
    ring
  have hsum : ∑ x, (f x - mean f) ^ 2 + ∑ x, (f (flipSet x {j}) - mean f) ^ 2
      = 2 * (∑ x, (avg j f x - mean f) ^ 2 + ∑ x, ((f x - f (flipSet x {j})) / 2) ^ 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => hpt x)
  rw [hre] at hsum
  have hkey : ∑ x, (f x - mean f) ^ 2
      = ∑ x, (avg j f x - mean f) ^ 2 + ∑ x, ((f x - f (flipSet x {j})) / 2) ^ 2 := by
    linarith
  unfold variance inflR
  rw [hm, ← add_div, hkey]

/-- `Inf_k (avg j f) ≤ Inf_k f` for every `k`. -/
theorem inflR_avg_le (j k : ι) (f : Cube ι → ℝ) : inflR (avg j f) k ≤ inflR f k := by
  have hcomm : ∀ x : Cube ι, flipSet (flipSet x {k}) {j} = flipSet (flipSet x {j}) {k} :=
    fun x => flipSet_comm x {k} {j}
  have hpt : ∀ x, ((avg j f x - avg j f (flipSet x {k})) / 2) ^ 2
      ≤ (((f x - f (flipSet x {k})) / 2) ^ 2
        + ((f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})) / 2) ^ 2) / 2 := by
    intro x
    unfold avg
    rw [hcomm x]
    nlinarith [sq_nonneg ((f x - f (flipSet x {k}))
      - (f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})))]
  have hre : ∑ x, ((f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})) / 2) ^ 2
      = ∑ x, ((f x - f (flipSet x {k})) / 2) ^ 2 :=
    sum_flip j (fun x => ((f x - f (flipSet x {k})) / 2) ^ 2)
  unfold inflR
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ∑ x, ((avg j f x - avg j f (flipSet x {k})) / 2) ^ 2
      ≤ ∑ x, (((f x - f (flipSet x {k})) / 2) ^ 2
          + ((f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})) / 2) ^ 2) / 2 :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = ∑ x, ((f x - f (flipSet x {k})) / 2) ^ 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hre]
        ring

/-- `L_k (avg j f) ≤ L_k f` for every `k`. -/
theorem meanAbsIncr_avg_le (j k : ι) (f : Cube ι → ℝ) :
    meanAbsIncr (avg j f) k ≤ meanAbsIncr f k := by
  have hcomm : ∀ x : Cube ι, flipSet (flipSet x {k}) {j} = flipSet (flipSet x {j}) {k} :=
    fun x => flipSet_comm x {k} {j}
  have hpt : ∀ x, |avg j f x - avg j f (flipSet x {k})|
      ≤ (|f x - f (flipSet x {k})|
        + |f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})|) / 2 := by
    intro x
    have e : avg j f x - avg j f (flipSet x {k})
        = ((f x - f (flipSet x {k}))
          + (f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k}))) / 2 := by
      unfold avg
      rw [hcomm x]
      ring
    rw [e, abs_div, abs_two]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  have hre : ∑ x, |f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})|
      = ∑ x, |f x - f (flipSet x {k})| :=
    sum_flip j (fun x => |f x - f (flipSet x {k})|)
  unfold meanAbsIncr
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ∑ x, |avg j f x - avg j f (flipSet x {k})|
      ≤ ∑ x, (|f x - f (flipSet x {k})|
          + |f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})|) / 2 :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = ∑ x, |f x - f (flipSet x {k})| := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hre]
        ring

/-- `L_j (avg j f) = 0`. -/
theorem meanAbsIncr_avg_self (j : ι) (f : Cube ι → ℝ) : meanAbsIncr (avg j f) j = 0 := by
  unfold meanAbsIncr
  rw [Finset.sum_eq_zero (fun x _ => by rw [avg_flip, sub_self, abs_zero]), zero_div]

/-- Rows of `f` give rows of `avg j f` of the same cost. -/
theorem rows_avg (j : ι) {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) :
    (∀ x i, 0 ≤ (a x i + a (flipSet x {j}) i) / 2) ∧
    (∀ x, ∑ i, (a x i + a (flipSet x {j}) i) / 2 ≤ K) ∧
    ∀ x y, |avg j f x - avg j f y| ≤ ∑ i ∈ diffSet x y, (a x i + a (flipSet x {j}) i) / 2 := by
  refine ⟨fun x i => div_nonneg (add_nonneg (ha x i) (ha _ i)) (by norm_num), fun x => ?_,
    fun x y => ?_⟩
  · rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith [hsum x, hsum (flipSet x {j})]
  · have h1 := hrow x y
    have h2 := hrow (flipSet x {j}) (flipSet y {j})
    rw [diffSet_flip] at h2
    have e : avg j f x - avg j f y
        = ((f x - f y) + (f (flipSet x {j}) - f (flipSet y {j}))) / 2 := by
      unfold avg
      ring
    rw [e, abs_div, abs_two, ← Finset.sum_div, Finset.sum_add_distrib]
    exact div_le_div_of_nonneg_right (le_trans (abs_add_le _ _) (add_le_add h1 h2))
      (by norm_num)

end Average
end AaronsonAmbainis
