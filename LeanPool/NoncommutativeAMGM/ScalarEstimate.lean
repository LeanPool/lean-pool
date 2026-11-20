/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.Alternating
public import LeanPool.NoncommutativeAMGM.FallingFactorial

/-!
# The scalar estimates in Section 3.6

These results prove the numerical closing argument from explicit inequalities
for `S` and `H`. They do not construct the quadrature or prove its norm estimates.
-/

public section

namespace NoncommutativeAMGM

open scoped BigOperators

/-- Equation (42), with the zero term included in the sum. -/
theorem sum_beta (n : ℝ) (hn : n ≠ 0) (k : ℕ) :
    ∑ l ∈ Finset.range k, beta n l =
      2 * k * ((k : ℝ) - 1) / n * (1 - (2 * k - 1) / (3 * n)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold beta
    push_cast
    field_simp [hn]
    ring

/-- A convenient bound for the first symmetric sum. -/
theorem sum_beta_le (n : ℝ) (hn : 0 < n) (k : ℕ) :
    ∑ l ∈ Finset.range k, beta n l ≤ 2 * k * ((k : ℝ) - 1) / n := by
  by_cases hk : k = 0
  · simp [hk]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
  rw [sum_beta n hn.ne' k]
  have hp : 0 ≤ 2 * (k : ℝ) * ((k : ℝ) - 1) / n := by positivity
  have hq : 0 ≤ (2 * (k : ℝ) - 1) / (3 * n) :=
    div_nonneg (by linarith) (by positivity)
  nlinarith [mul_nonneg hp hq]

/-- The product of the two recurrence ratios in Section 3.6 is at most one. -/
theorem recurrence_ratio_le_one (n d K L : ℝ) (hL : 1 ≤ L) (hLK : L + 2 ≤ K)
    (hKd : K ≤ d) (hn : 2 * d ^ 2 ≤ n) :
    (4 * (K - 1) * (K - 1 - L) / ((L + 1) * n)) *
      ((d - L) ^ 2 / ((K - L - 1) * (K - L))) ≤ 1 := by
  have hd : 0 < d := by linarith
  have hn0 : 0 < n := by nlinarith [sq_pos_of_pos hd]
  have hL1 : 0 < L + 1 := by linarith
  have hKL : 0 < K - L := by linarith
  have hKL1 : 0 < K - L - 1 := by linarith
  have hK1 : 0 ≤ K - 1 := by linarith
  have hfactor : 2 * (K - 1) ≤ (L + 1) * (K - L) := by
    nlinarith [mul_nonneg (show 0 ≤ L - 1 by linarith)
      (show 0 ≤ K - L - 2 by linarith)]
  have hsq : (d - L) ^ 2 ≤ d ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ L by linarith)
      (show 0 ≤ 2 * d - L by linarith)]
  have hmain : 4 * (K - 1) * (d - L) ^ 2 ≤ (L + 1) * n * (K - L) := by
    calc
      _ ≤ 4 * (K - 1) * d ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (2 * (K - 1)) * (2 * d ^ 2) := by ring
      _ ≤ ((L + 1) * (K - L)) * n :=
        mul_le_mul hfactor hn (by positivity) (by positivity)
      _ = _ := by ring
  have heq : (4 * (K - 1) * (K - 1 - L) / ((L + 1) * n)) *
      ((d - L) ^ 2 / ((K - L - 1) * (K - L))) =
      4 * (K - 1) * (d - L) ^ 2 / ((L + 1) * n * (K - L)) := by
    field_simp [hn0.ne', hL1.ne', hKL.ne', hKL1.ne']
    ring
  rw [heq, div_le_one (by positivity)]
  exact hmain

/-- Multiplying the estimates (40) and (41) makes consecutive correction terms decrease. -/
theorem correction_term_le (n d K L S₀ S₁ H₀ H₁ : ℝ)
    (hL : 1 ≤ L) (hLK : L + 2 ≤ K) (hKd : K ≤ d) (hn : 2 * d ^ 2 ≤ n)
    (hS₀ : 0 ≤ S₀) (hS₁ : 0 ≤ S₁) (hH₀ : 0 ≤ H₀)
    (hS : S₁ ≤ (4 * (K - 1) * (K - 1 - L) / ((L + 1) * n)) * S₀)
    (hH : H₁ ≤ ((d - L) ^ 2 / ((K - L - 1) * (K - L))) * H₀) :
    S₁ * H₁ ≤ S₀ * H₀ := by
  have hratio := recurrence_ratio_le_one n d K L hL hLK hKd hn
  have hden : 0 < (K - L - 1) * (K - L) := by
    apply mul_pos <;> linarith
  calc
    _ ≤ S₁ * (((d - L) ^ 2 / ((K - L - 1) * (K - L))) * H₀) :=
      mul_le_mul_of_nonneg_left hH hS₁
    _ ≤ ((4 * (K - 1) * (K - 1 - L) / ((L + 1) * n)) * S₀) *
        (((d - L) ^ 2 / ((K - L - 1) * (K - L))) * H₀) :=
      mul_le_mul_of_nonneg_right hS (by positivity)
    _ = ((4 * (K - 1) * (K - 1 - L) / ((L + 1) * n)) *
        ((d - L) ^ 2 / ((K - L - 1) * (K - L)))) * (S₀ * H₀) := by ring
    _ ≤ 1 * (S₀ * H₀) := mul_le_mul_of_nonneg_right hratio (mul_nonneg hS₀ hH₀)
    _ = _ := one_mul _

/-- The first negative correction is absorbed when `n ≥ 2d²`. -/
theorem first_correction_le (n d K S₁ Hprev Htop : ℝ)
    (hn0 : 0 < n) (hn : 2 * d ^ 2 ≤ n) (hHprev : 0 ≤ Hprev) (hHtop : 0 ≤ Htop)
    (hS : S₁ ≤ 2 * K * (K - 1) / n)
    (hH : K * (K - 1) * Hprev ≤ d ^ 2 * Htop) : S₁ * Hprev ≤ Htop := by
  calc
    _ ≤ (2 * K * (K - 1) / n) * Hprev := mul_le_mul_of_nonneg_right hS hHprev
    _ = (2 / n) * (K * (K - 1) * Hprev) := by ring
    _ ≤ (2 / n) * (d ^ 2 * Htop) := mul_le_mul_of_nonneg_left hH (by positivity)
    _ = (2 * d ^ 2 / n) * Htop := by ring
    _ ≤ 1 * Htop := mul_le_mul_of_nonneg_right ((div_le_one hn0).mpr hn) hHtop
    _ = _ := one_mul _

/-- The finite scalar closing step in Section 3.6. Every estimate required from
the quadrature construction is explicit in the hypotheses. -/
theorem scalar_expansion_nonneg (k : ℕ) (S H : ℕ → ℝ)
    (hS : ∀ i, 0 ≤ S i) (hH : ∀ i, 0 ≤ H i)
    (hfirst : S 1 * H (k - 1) ≤ H k)
    (hdec : ∀ l, 1 ≤ l → l + 2 ≤ k →
      S (l + 1) * H (k - (l + 1)) ≤ S l * H (k - l)) :
    0 ≤ H k + ∑ i ∈ Finset.range (k - 1),
      (-1 : ℝ) ^ (i + 1) * S (i + 1) * H (k - (i + 1)) := by
  have h := alternating_sum_ge_neg_first (k - 1)
    (fun i ↦ S (i + 1) * H (k - (i + 1)))
    (mul_nonneg (hS _) (hH _))
    (fun i _ ↦ mul_nonneg (hS _) (hH _))
    (fun i hi ↦ hdec (i + 1) (by omega) (by omega))
  simp only [Nat.zero_add] at h
  simp_rw [mul_assoc]
  linarith

end NoncommutativeAMGM
