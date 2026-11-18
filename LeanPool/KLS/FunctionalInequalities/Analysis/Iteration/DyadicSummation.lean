/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The dyadic summation in the proof of BKL Theorem 3.1

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Theorem 3.1, p. 17: the recursion (63)
between the degree-`d` and degree-`2d` quantities is summed along the dyadic degrees
`d = 1, 2, 4, …`. This file isolates that step as a statement about real sequences.

## What is proved

* `le_of_dyadic_recursion`: let `S : ℕ → ℝ` vanish from some index `N` on, let `x` be any real
  number and `0 ≤ A`, `0 ≤ y ≤ 1/100`. If for every `d ≥ 1`
  `x^(d-1) S(d) ≤ x^(2d-1) S(2d) + A d y^d`, then `S(1) ≤ A / 90`.

The intended instance is `x = cλ`, `y = c²λR²`, with the source's (63) multiplied by
`(cλ)^(d-1)`.

## The argument

Put `T(d) = x^(d-1) S(d)`; the recursion reads `T(d) ≤ T(2d) + A d y^d`. Applying it at
`d = 2^j` for `j < m` and chaining gives
`S(1) = T(1) ≤ T(2^m) + A Σ_{j<m} 2^j y^(2^j)` (`le_dyadic_chain`). With `m = N` we have
`2^m ≥ N`, so `S(2^m) = 0`. Since `y ≤ 1/100` and the dyadic indices are a subfamily of
`ℕ`, `Σ_{j<m} 2^j y^(2^j) ≤ Σ_{d} d (1/100)^d = (1/100)/(1 - 1/100)² = 100/9801 < 1/90`
(`sum_dyadic_le`).

## What this is not

This is only the elementary summation. It does not prove the recursion (63), the bounds on the
iterates feeding it, or Theorem 3.1 itself. The hypotheses `0 ≤ S d` and `x ≤ 1` of the main
theorem are not used by the argument; they are kept to match the source's setting.
-/

@[expose] public section

namespace FunctionalInequalities.Analysis

open Finset

/-- Chaining the dyadic recursion `m` times: with `T(d) = x^(d-1) S(d)`,
`S(1) ≤ T(2^m) + A Σ_{j<m} 2^j y^(2^j)`. -/
private theorem le_dyadic_chain {S : ℕ → ℝ} {x y A : ℝ}
    (hrec : ∀ d, 1 ≤ d → x ^ (d - 1) * S d ≤ x ^ (2 * d - 1) * S (2 * d) + A * d * y ^ d)
    (m : ℕ) :
    S 1 ≤ x ^ (2 ^ m - 1) * S (2 ^ m) +
      A * ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := hrec (2 ^ m) (Nat.one_le_two_pow)
    rw [sum_range_succ, pow_succ' 2 m, mul_add]
    linarith [ih, h]

/-- The dyadic partial sums are bounded by `Σ_d d (1/100)^d = 100/9801 ≤ 1/90`. -/
private theorem sum_dyadic_le {y : ℝ} (hy : 0 ≤ y) (hy1 : 100 * y ≤ 1) (m : ℕ) :
    ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j) ≤ 1 / 90 := by
  set r : ℝ := 1 / 100 with hr
  have hyr : y ≤ r := by rw [hr]; linarith
  have hnorm : ‖r‖ < 1 := by rw [hr, Real.norm_eq_abs]; norm_num
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hinj : Set.InjOn (fun j : ℕ => 2 ^ j) (range m : Set ℕ) :=
    fun a _ b _ hab => Nat.pow_right_injective le_rfl hab
  calc ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j)
      ≤ ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * r ^ (2 ^ j) := by
        gcongr
    _ = ∑ d ∈ (range m).image (fun j : ℕ => 2 ^ j), ((d : ℕ) : ℝ) * r ^ d :=
        (sum_image (f := fun d : ℕ => (d : ℝ) * r ^ d) hinj).symm
    _ ≤ ∑' d : ℕ, (d : ℝ) * r ^ d :=
        hsum.summable.sum_le_tsum _ (fun d _ => by positivity)
    _ = r / (1 - r) ^ 2 := hsum.tsum_eq
    _ ≤ 1 / 90 := by rw [hr]; norm_num

/-- **The dyadic summation of BKL Theorem 3.1** (arXiv:2610.05474v1, p. 17). If `S` vanishes
from `N` on, `0 ≤ x ≤ 1`, `0 ≤ A`, `0 ≤ y ≤ 1/100`, and
`x^(d-1) S(d) ≤ x^(2d-1) S(2d) + A d y^d` for all `d ≥ 1`, then `S(1) ≤ A / 90`. -/
theorem le_of_dyadic_recursion {S : ℕ → ℝ} {x y A : ℝ} {N : ℕ}
    (hN : ∀ d, N ≤ d → S d = 0) (hA : 0 ≤ A) (hy : 0 ≤ y) (hy1 : 100 * y ≤ 1)
    (hrec : ∀ d, 1 ≤ d → x ^ (d - 1) * S d ≤ x ^ (2 * d - 1) * S (2 * d) + A * d * y ^ d) :
    S 1 ≤ A / 90 := by
  have hchain := le_dyadic_chain hrec N
  rw [hN (2 ^ N) (Nat.lt_two_pow_self).le, mul_zero, zero_add] at hchain
  have hsum := sum_dyadic_le hy hy1 N
  calc S 1 ≤ A * ∑ j ∈ range N, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j) := hchain
    _ ≤ A * (1 / 90) := mul_le_mul_of_nonneg_left hsum hA
    _ = A / 90 := by ring


/-! ## Geometric recurrences of Moser iterations

The real-sequence recurrences that drive the Moser iterations of Gilbarg–Trudinger (2001), proof of
Theorem 8.18:
`geometric_exponential_recurrence_bound` sums the weighted geometric series of an exponential
recurrence
`x_{k+1} ≤ exp((a^k/p)(A + B k)) x_k`, `0 ≤ a < 1`; `geometric_root_recurrence_bound` and its
finite-horizon form
`finite_geometric_root_recurrence_bound` bound the normalized root recurrence `y_{m+1} ≤ (C
4^m)^{1/(p0 κ^m)} y_m`. -/

section GeometricRecurrence

open scoped BigOperators

private theorem geom_sum_formula (a : ℝ) (n : ℕ) :
    (1 - a) * (∑ i ∈ Finset.range n, a ^ i) = 1 - a ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (1 - a) * ((∑ i ∈ Finset.range n, a ^ i) + a ^ n) =
            (1 - a) * (∑ i ∈ Finset.range n, a ^ i) +
              (1 - a) * a ^ n := by ring
        _ = (1 - a ^ n) + (1 - a) * a ^ n := by rw [ih]
        _ = 1 - a ^ (n + 1) := by
          rw [pow_succ]
          ring

private theorem weighted_sum_formula (a : ℝ) (n : ℕ) :
    (1 - a) ^ 2 * (∑ i ∈ Finset.range n, (i : ℝ) * a ^ i) =
      a - (n : ℝ) * a ^ n + ((n : ℝ) - 1) * a ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (1 - a) ^ 2 *
              ((∑ i ∈ Finset.range n, (i : ℝ) * a ^ i) +
                (n : ℝ) * a ^ n) =
            (1 - a) ^ 2 * (∑ i ∈ Finset.range n, (i : ℝ) * a ^ i) +
              (1 - a) ^ 2 * ((n : ℝ) * a ^ n) := by ring
        _ = (a - (n : ℝ) * a ^ n + ((n : ℝ) - 1) * a ^ (n + 1)) +
              (1 - a) ^ 2 * ((n : ℝ) * a ^ n) := by rw [ih]
        _ = a - (Nat.succ n : ℝ) * a ^ Nat.succ n +
              ((Nat.succ n : ℝ) - 1) * a ^ (Nat.succ n + 1) := by
          simp only [Nat.cast_succ, pow_succ]
          ring

private theorem weighted_tail_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    0 ≤ (n : ℝ) * a ^ n - ((n : ℝ) - 1) * a ^ (n + 1) := by
  have hden : 0 ≤ 1 - a := le_of_lt (sub_pos.mpr ha1)
  have hbr : 0 ≤ (n : ℝ) * (1 - a) + a :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg n) hden) ha0
  calc
    0 ≤ a ^ n * ((n : ℝ) * (1 - a) + a) :=
      mul_nonneg (pow_nonneg ha0 n) hbr
    _ = (n : ℝ) * a ^ n - ((n : ℝ) - 1) * a ^ (n + 1) := by
      rw [pow_succ]
      ring

private theorem geom_sum_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, a ^ i ≤ 1 / (1 - a) := by
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  apply (le_div_iff₀ hden).2
  calc
    (∑ i ∈ Finset.range n, a ^ i) * (1 - a) =
        (1 - a) * (∑ i ∈ Finset.range n, a ^ i) := by ring
    _ = 1 - a ^ n := geom_sum_formula a n
    _ ≤ 1 := by linarith [pow_nonneg ha0 n]

private theorem weighted_sum_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℝ) * a ^ i ≤ a / (1 - a) ^ 2 := by
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  have hden2 : 0 < (1 - a) ^ 2 := sq_pos_of_pos hden
  apply (le_div_iff₀ hden2).2
  calc
    (∑ i ∈ Finset.range n, (i : ℝ) * a ^ i) * (1 - a) ^ 2 =
        (1 - a) ^ 2 * (∑ i ∈ Finset.range n, (i : ℝ) * a ^ i) := by ring
    _ = a - (n : ℝ) * a ^ n + ((n : ℝ) - 1) * a ^ (n + 1) :=
      weighted_sum_formula a n
    _ ≤ a := by
      linarith [weighted_tail_nonneg ha0 ha1 n]

/-- The dimensionless finite-product estimate used after normalizing the inverse Moser iteration.
This is an arithmetic supporting lemma, not the PDE or weak Harnack conclusion. -/
theorem geometric_exponential_recurrence_bound
    {a p A B : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hp : 0 < p)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (x : ℕ → ℝ)
    (hx : ∀ k, 0 ≤ x k)
    (hstep : ∀ k, x (k + 1) ≤ Real.exp ((a ^ k / p) * (A + B * (k : ℝ))) * x k) :
    ∀ k, x k ≤ Real.exp ((A / (1 - a) + B * a / (1 - a) ^ 2) / p) * x 0 := by
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  let c : ℕ → ℝ :=
    fun k => ∑ i ∈ Finset.range k, (a ^ i / p) * (A + B * (i : ℝ))
  have hc_step (k : ℕ) :
      c (k + 1) = c k + (a ^ k / p) * (A + B * (k : ℝ)) := by
    dsimp [c]
    rw [Finset.sum_range_succ]
  have hc_expand (k : ℕ) :
      c k =
        (A / p) * (∑ i ∈ Finset.range k, a ^ i) +
          (B / p) * (∑ i ∈ Finset.range k, (i : ℝ) * a ^ i) := by
    dsimp [c]
    calc
      (∑ i ∈ Finset.range k, (a ^ i / p) * (A + B * (i : ℝ))) =
          ∑ i ∈ Finset.range k,
            ((A / p) * a ^ i + (B / p) * ((i : ℝ) * a ^ i)) := by
              apply Finset.sum_congr rfl
              intro i _hi
              ring
      _ = (A / p) * (∑ i ∈ Finset.range k, a ^ i) +
            (B / p) * (∑ i ∈ Finset.range k, (i : ℝ) * a ^ i) := by
              rw [Finset.sum_add_distrib]
              rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hc_bound (k : ℕ) :
      c k ≤ (A / (1 - a) + B * a / (1 - a) ^ 2) / p := by
    have hAp : 0 ≤ A / p := div_nonneg hA (le_of_lt hp)
    have hBp : 0 ≤ B / p := div_nonneg hB (le_of_lt hp)
    calc
      c k =
          (A / p) * (∑ i ∈ Finset.range k, a ^ i) +
            (B / p) * (∑ i ∈ Finset.range k, (i : ℝ) * a ^ i) :=
        hc_expand k
      _ ≤ (A / p) * (1 / (1 - a)) +
            (B / p) * (a / (1 - a) ^ 2) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (geom_sum_le ha0 ha1 k) hAp)
          (mul_le_mul_of_nonneg_left (weighted_sum_le ha0 ha1 k) hBp)
      _ = (A / (1 - a) + B * a / (1 - a) ^ 2) / p := by
        field_simp [ne_of_gt hp, ne_of_gt hden]
  have hbound : ∀ k, x k ≤ Real.exp (c k) * x 0 := by
    intro k
    induction k with
    | zero =>
        simp [c]
    | succ k ih =>
        calc
          x (Nat.succ k) ≤
              Real.exp ((a ^ k / p) * (A + B * (k : ℝ))) * x k := by
                simpa [Nat.succ_eq_add_one] using hstep k
          _ ≤ Real.exp ((a ^ k / p) * (A + B * (k : ℝ))) *
                (Real.exp (c k) * x 0) :=
            mul_le_mul_of_nonneg_left ih (le_of_lt (Real.exp_pos _))
          _ = Real.exp (c (Nat.succ k)) * x 0 := by
            rw [hc_step k, Real.exp_add]
            ring
  intro k
  calc
    x k ≤ Real.exp (c k) * x 0 := hbound k
    _ ≤ Real.exp ((A / (1 - a) + B * a / (1 - a) ^ 2) / p) * x 0 :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (hc_bound k)) (hx 0)

/--
The normalized root recurrence `y_{m+1} ≤ (C 4^m)^{1/(p0 κ^m)} y_m` has a uniform finite bound: it
is the case
`a = κ⁻¹`, `A = log C`, `B = log 4` of `geometric_exponential_recurrence_bound`. -/
theorem geometric_root_recurrence_bound {κ p0 C : ℝ} (hκ : 1 < κ) (hp : 0 < p0) (hC : 1 ≤ C)
    (y : ℕ → ℝ) (hy : ∀ m, 0 ≤ y m)
    (hstep : ∀ m, y (m + 1) ≤ (C * (4 : ℝ) ^ m) ^ (1 / (p0 * κ ^ m)) * y m) :
    ∀ m,
      y m ≤ Real.exp ((Real.log C / (1 - κ⁻¹) + Real.log 4 * κ⁻¹ / (1 - κ⁻¹) ^ 2) / p0) * y 0 := by
  have hκ0 : 0 < κ := lt_trans zero_lt_one hκ
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have heq (m : ℕ) :
    (C * (4 : ℝ) ^ m) ^ (1 / (p0 * κ ^ m)) =
      Real.exp (((κ⁻¹) ^ m / p0) * (Real.log C + Real.log 4 * (m : ℝ))) := by
    rw [Real.rpow_def_of_pos (mul_pos hC0 (pow_pos (by norm_num) m)),
      Real.log_mul hC0.ne' (pow_pos (by norm_num : (0 : ℝ) < 4) m).ne', Real.log_pow]
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, one_mul]
    ring
  apply
    geometric_exponential_recurrence_bound (inv_nonneg.mpr hκ0.le) (inv_lt_one_of_one_lt₀ hκ) hp
      (Real.log_nonneg hC) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)) y hy
  intro m
  rw [← heq m]
  exact hstep m

/-- A finite horizon of the normalized Moser root recurrence suffices; after the horizon the
sequence may be kept constant because every multiplier is at least one. -/
theorem finite_geometric_root_recurrence_bound {κ p0 C : ℝ} (hκ : 1 < κ) (hp : 0 < p0)
    (hC : 1 ≤ C) (y : ℕ → ℝ) (hy : ∀ m, 0 ≤ y m) (K : ℕ)
    (hstep : ∀ m < K, y (m + 1) ≤ (C * (4 : ℝ) ^ m) ^ (1 / (p0 * κ ^ m)) * y m) :
    y K ≤ Real.exp ((Real.log C / (1 - κ⁻¹) + Real.log 4 * κ⁻¹ / (1 - κ⁻¹) ^ 2) / p0) * y 0 := by
  let z := fun m : ℕ => y (min m K)
  have hfactor (m : ℕ) : 1 ≤ (C * (4 : ℝ) ^ m) ^ (1 / (p0 * κ ^ m)) := by
    apply Real.one_le_rpow
    · exact one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4))
    · positivity
  have hz (m : ℕ) : z (m + 1) ≤ (C * (4 : ℝ) ^ m) ^ (1 / (p0 * κ ^ m)) * z m := by
    by_cases hm : m < K
    · simpa only [z, Nat.min_eq_left (Nat.succ_le_of_lt hm), Nat.min_eq_left hm.le] using
        hstep m hm
    · have hKm : K ≤ m := Nat.le_of_not_gt hm
      have hKm1 : K ≤ m + 1 := hKm.trans (Nat.le_succ m)
      simp only [z, Nat.min_eq_right hKm1, Nat.min_eq_right hKm]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hfactor m) (hy K)
  have H := geometric_root_recurrence_bound hκ hp hC z (fun m => hy _) hz K
  simpa only [z, Nat.min_self, Nat.zero_min] using H

end GeometricRecurrence

end FunctionalInequalities.Analysis
