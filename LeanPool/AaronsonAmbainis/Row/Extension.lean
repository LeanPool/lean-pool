/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Row.Chi

/-!
# Bounded multilinear extension

Lemma 6.2 (Extension) of the paper, `Row.abs_multilinear_le_one`: if `∑_T a_T chi_T` is bounded
by `1` in absolute value on the cube, then `∑_T a_T ∏_{i ∈ T} u_i` is bounded by `1` for every
real vector `u` with `|u_i| ≤ 1`. The proof averages over the product measure `weight u`.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Row

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product weight `W_u(z) = ∏_i (1 + sgn(z_i) u_i) / 2`. -/
noncomputable def weight (u : ι → ℝ) (z : Cube ι) : ℝ := ∏ i, (1 + sgn (z i) * u i) / 2

omit [DecidableEq ι] in
lemma weight_nonneg (u : ι → ℝ) (hu : ∀ i, |u i| ≤ 1) (z : Cube ι) : 0 ≤ weight u z := by
  refine Finset.prod_nonneg (fun i _ => ?_)
  have h1 : |sgn (z i) * u i| ≤ 1 := by
    rw [abs_mul, abs_sgn, one_mul]
    exact hu i
  have h2 := abs_le.mp h1
  linarith [h2.1]

/-- The `weight u`-average of the character `chi T` is `∏_{i ∈ T} u_i`. -/
lemma sum_weight_mul_chi (u : ι → ℝ) (T : Finset ι) :
    ∑ z : Cube ι, weight u z * chi T z = ∏ i ∈ T, u i := by
  have h1 : ∀ z : Cube ι, weight u z * chi T z
      = ∏ i, ((1 + sgn (z i) * u i) / 2 * (if i ∈ T then sgn (z i) else 1)) := by
    intro z
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem T (fun i => sgn (z i))]
    rfl
  have h2 : ∑ z : Cube ι, ∏ i, ((1 + sgn (z i) * u i) / 2 * (if i ∈ T then sgn (z i) else 1))
      = ∏ i, ∑ b : Bool, ((1 + sgn b * u i) / 2 * (if i ∈ T then sgn b else 1)) :=
    (Fintype.prod_sum
      (fun i (b : Bool) => (1 + sgn b * u i) / 2 * (if i ∈ T then sgn b else 1))).symm
  rw [Finset.sum_congr rfl (fun z _ => h1 z), h2, ← Fintype.prod_ite_mem T u]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  by_cases hi : i ∈ T <;> simp [hi] <;> ring

lemma sum_weight (u : ι → ℝ) : ∑ z : Cube ι, weight u z = 1 := by
  have h := sum_weight_mul_chi u (∅ : Finset ι)
  simpa [chi] using h

omit [DecidableEq ι] in
/-- Bounded multilinear extension (Lemma 6.2 of the paper). -/
theorem abs_multilinear_le_one (a : Finset ι → ℝ)
    (h : ∀ z : Cube ι, |∑ T, a T * chi T z| ≤ 1) (u : ι → ℝ) (hu : ∀ i, |u i| ≤ 1) :
    |∑ T, a T * ∏ i ∈ T, u i| ≤ 1 := by
  classical
  have key : ∑ T, a T * ∏ i ∈ T, u i = ∑ z : Cube ι, weight u z * ∑ T, a T * chi T z := by
    calc ∑ T, a T * ∏ i ∈ T, u i
        = ∑ T, a T * ∑ z : Cube ι, weight u z * chi T z := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [sum_weight_mul_chi]
      _ = ∑ T, ∑ z : Cube ι, weight u z * (a T * chi T z) := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z _ => ?_)
          ring
      _ = ∑ z : Cube ι, ∑ T, weight u z * (a T * chi T z) := Finset.sum_comm
      _ = ∑ z : Cube ι, weight u z * ∑ T, a T * chi T z := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [Finset.mul_sum]
  rw [key]
  calc |∑ z : Cube ι, weight u z * ∑ T, a T * chi T z|
      ≤ ∑ z : Cube ι, |weight u z * ∑ T, a T * chi T z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z : Cube ι, weight u z := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        rw [abs_mul, abs_of_nonneg (weight_nonneg u hu z)]
        exact mul_le_of_le_one_right (weight_nonneg u hu z) (h z)
    _ = 1 := sum_weight u

end Row
end AaronsonAmbainis
