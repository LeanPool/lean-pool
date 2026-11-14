/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# One-variable Taylor data via iterated `dslope`

For `g : ℂ → ℂ` put `tc k g = ((swap dslope 0)^[k] g) 0`. Then:

* `taylor_split`: for every `K` and `z` (no hypothesis on `g`),
  `g z = Σ_{k<K} tc k g · z^k + z^K · ((swap dslope 0)^[K] g) z`;
* `tc_mul_factorial`: for `g` entire, `tc k g · k! = iteratedDeriv k g 0`;
* `differentiable_iterate_dslope`: the remainder is entire when `g` is.
-/

@[expose] public section

namespace LeanPool

open Complex Finset Function

namespace StrongSix.Thm1

/-- The `k`-th Taylor coefficient of `g` at `0`, computed by iterated `dslope`. -/
noncomputable def tc (k : ℕ) (g : ℂ → ℂ) : ℂ := (swap dslope (0 : ℂ))^[k] g 0

theorem tc_zero (g : ℂ → ℂ) : tc 0 g = g 0 := rfl

theorem tc_succ (k : ℕ) (g : ℂ → ℂ) : tc (k + 1) g = tc k (dslope g 0) := by
  simp only [tc, iterate_succ_apply, swap]

theorem differentiable_dslope {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (dslope g 0) := by
  have := (differentiableOn_dslope (s := Set.univ) (f := g) (c := 0) Filter.univ_mem).mpr
    hg.differentiableOn
  exact fun w => (this w trivial).differentiableAt Filter.univ_mem

theorem differentiable_iterate_dslope {g : ℂ → ℂ} (hg : Differentiable ℂ g) (K : ℕ) :
    Differentiable ℂ ((swap dslope (0 : ℂ))^[K] g) := by
  induction K generalizing g with
  | zero => exact hg
  | succ K ih =>
    rw [iterate_succ_apply]
    exact ih (differentiable_dslope hg)

/-- `g z = g 0 + z · (dslope g 0) z`. -/
theorem eq_add_mul_dslope (g : ℂ → ℂ) (z : ℂ) : g z = g 0 + z * dslope g 0 z := by
  have h := sub_smul_dslope g 0 z
  rw [sub_zero, smul_eq_mul] at h
  rw [h]; ring

/-- **Exact Taylor split.** -/
theorem taylor_split (g : ℂ → ℂ) (K : ℕ) (z : ℂ) :
    g z = ∑ k ∈ range K, tc k g * z ^ k + z ^ K * (swap dslope (0 : ℂ))^[K] g z := by
  induction K generalizing g with
  | zero => simp
  | succ K ih =>
    rw [ih g, sum_range_succ, iterate_succ_apply']
    have h := eq_add_mul_dslope ((swap dslope (0 : ℂ))^[K] g) z
    rw [h]
    simp only [tc, swap]
    ring

/-- `iteratedDeriv (k+1) (z ↦ z · u z) w = (k+1) · iteratedDeriv k u w + w · iteratedDeriv (k+1)
  u w`. -/
theorem iteratedDeriv_id_mul {u : ℂ → ℂ} (hu : Differentiable ℂ u) (k : ℕ) :
    iteratedDeriv (k + 1) (fun z => z * u z) =
      fun w => (k + 1 : ℂ) * iteratedDeriv k u w + w * iteratedDeriv (k + 1) u w := by
  have hc : ContDiff ℂ ⊤ u := hu.contDiff
  have hd : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m u) := fun m =>
    hc.differentiable_iteratedDeriv m (WithTop.coe_lt_top _)
  induction k with
  | zero =>
    rw [zero_add, iteratedDeriv_one]
    funext w
    have : HasDerivAt (fun z => z * u z) (1 * u w + w * deriv u w) w :=
      (hasDerivAt_id w).mul (hu w).hasDerivAt
    rw [this.deriv, iteratedDeriv_zero, iteratedDeriv_one]
    push_cast; ring
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext w
    have h1 : HasDerivAt (fun w => (k + 1 : ℂ) * iteratedDeriv k u w + w * iteratedDeriv (k + 1)
      u w)
        ((k + 1 : ℂ) * deriv (iteratedDeriv k u) w +
          (1 * iteratedDeriv (k + 1) u w + w * deriv (iteratedDeriv (k + 1) u) w)) w :=
      (((hd k) w).hasDerivAt.const_mul _).add ((hasDerivAt_id w).mul ((hd (k + 1)) w).hasDerivAt)
    rw [h1.deriv, ← iteratedDeriv_succ, ← iteratedDeriv_succ]
    push_cast; ring

/-- **Taylor coefficients.** For `g` entire, `tc k g · k! = iteratedDeriv k g 0`. -/
theorem tc_mul_factorial {g : ℂ → ℂ} (hg : Differentiable ℂ g) (k : ℕ) :
    tc k g * k.factorial = iteratedDeriv k g 0 := by
  induction k generalizing g with
  | zero => simp [tc_zero]
  | succ k ih =>
    have hh := differentiable_dslope hg
    rw [tc_succ]
    have hgeq : g = fun z => g 0 + z * dslope g 0 z := funext (eq_add_mul_dslope g)
    have hderiv : iteratedDeriv (k + 1) g = iteratedDeriv (k + 1) (fun z => z * dslope g 0 z) := by
      conv_lhs => rw [hgeq]
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      congr 1
      funext w
      have h1 : HasDerivAt (fun z => g 0 + z * dslope g 0 z) (1 * dslope g 0 w + w * deriv
        (dslope g 0) w) w :=
        ((hasDerivAt_id w).mul (hh w).hasDerivAt).const_add _
      have h2 : HasDerivAt (fun z => z * dslope g 0 z) (1 * dslope g 0 w + w * deriv (dslope g
        0) w) w :=
        (hasDerivAt_id w).mul (hh w).hasDerivAt
      rw [h1.deriv, h2.deriv]
    rw [hderiv, iteratedDeriv_id_mul hh k]
    simp only [zero_mul, add_zero]
    rw [← ih hh, Nat.factorial_succ]
    push_cast; ring

end StrongSix.Thm1

end LeanPool
