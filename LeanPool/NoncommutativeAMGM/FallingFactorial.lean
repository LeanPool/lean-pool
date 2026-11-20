/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.Basic

/-!
# Falling factorials and the scalar factorization in Lemma 3.8
-/

@[expose] public section

namespace NoncommutativeAMGM

open scoped BigOperators

/-- The real falling factorial `(x)ₖ`. -/
noncomputable def falling (x : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (x - j)

theorem falling_eq_descPochhammer (x : ℝ) (k : ℕ) :
    falling x k = (descPochhammer ℝ k).eval x :=
  (descPochhammer_eval_eq_prod_range k x).symm

@[simp] theorem falling_zero (x : ℝ) : falling x 0 = 1 := by simp [falling]

theorem falling_succ (x : ℝ) (k : ℕ) :
    falling x (k + 1) = falling x k * (x - k) := by
  simp [falling, Finset.prod_range_succ]

/-- On natural numbers this is exactly mathlib's descending factorial. -/
@[simp] theorem falling_natCast (n k : ℕ) : falling n k = (n.descFactorial k : ℝ) := by
  rw [falling_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]

theorem falling_nonneg {x : ℝ} {k : ℕ} (hx : (k : ℝ) - 1 ≤ x) : 0 ≤ falling x k := by
  rw [falling_eq_descPochhammer]
  exact descPochhammer_nonneg hx

/-- The coefficient βₗ used in Lemma 3.8. -/
noncomputable def beta (n : ℝ) (l : ℕ) : ℝ := 4 * l * (n - l) / n ^ 2

@[simp] theorem beta_zero (n : ℝ) : beta n 0 = 0 := by simp [beta]

theorem beta_nonneg {n : ℝ} {l : ℕ} (hl : (l : ℝ) ≤ n) : 0 ≤ beta n l := by
  unfold beta
  positivity

/-- The unnormalized product identity in Lemma 3.8, valid for all nonzero real `n`. -/
theorem falling_pair_factorization (n t : ℝ) (hn : n ≠ 0) (k : ℕ) :
    falling (n / 2 * (1 - t)) k * falling (n / 2 * (1 + t)) k =
      (n ^ 2 / 4) ^ k * ∏ l ∈ Finset.range k, (1 - t ^ 2 - beta n l) := by
  unfold falling
  have hc : (n ^ 2 / 4) ^ k = ∏ _l ∈ Finset.range k, (n ^ 2 / 4) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l _
  unfold beta
  field_simp [hn]
  ring

/-- Lemma 3.8, including its falling-factorial denominator. -/
theorem slice_weight_factorization (n t : ℝ) (hn : n ≠ 0) (k : ℕ) :
    falling (n / 2 * (1 - t)) k * falling (n / 2 * (1 + t)) k /
        falling n (2 * k) =
      ((n ^ 2 / 4) ^ k / falling n (2 * k)) *
        ∏ l ∈ Finset.range k, (1 - t ^ 2 - beta n l) := by
  rw [falling_pair_factorization n t hn k]
  ring

/-- The scalar prefactor of Lemma 3.8 is nonnegative in the paper's regime. -/
theorem slice_prefactor_nonneg (n k : ℕ) :
    0 ≤ ((n : ℝ) ^ 2 / 4) ^ k / falling n (2 * k) := by
  rw [falling_natCast]
  positivity

/-- Nonnegativity of the harmonic weight in equation (28), without assuming a
harmonic decomposition has already been constructed. -/
theorem harmonic_weight_nonneg {n d j : ℕ} {s : ℝ} (hjd : j ≤ d)
    (hs : (d : ℝ) - 1 ≤ s) (hns : (d : ℝ) - 1 ≤ (n : ℝ) - s) :
    0 ≤ falling s j * falling ((n : ℝ) - s) j / falling n (2 * j) := by
  have hj : (j : ℝ) ≤ d := by exact_mod_cast hjd
  have h1 := falling_nonneg (k := j) (x := s) (by linarith)
  have h2 := falling_nonneg (k := j) (x := (n : ℝ) - s) (by linarith)
  rw [falling_natCast]
  exact div_nonneg (mul_nonneg h1 h2) (Nat.cast_nonneg _)

end NoncommutativeAMGM
