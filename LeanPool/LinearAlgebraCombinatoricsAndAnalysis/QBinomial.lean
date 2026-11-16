/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.Ring

/-!
# Gaussian binomial coefficients and the `q`-binomial theorem

The Gaussian binomial coefficient `[n, k]_q`, for `q` in any commutative ring, defined by the
`q`-Pascal recursion, and the `q`-binomial theorem
`∏_{i < n} (1 + q^i t) = Σ_{k ≤ n} q^(k choose 2) [n, k] t^k`.

## Main definitions

* `qBinomial`: `[n, k]_q`, by the recursion `[n+1, k+1] = [n, k] + q^(k+1) [n, k+1]`.

## Main statements

* `qBinomial_eq_zero_of_lt`: `[n, k] = 0` for `k > n`.
* `prod_one_add_pow_mul_eq_sum_qBinomial`: the `q`-binomial theorem.
* `sum_neg_one_pow_mul_qBinomial_eq_zero`: `Σ_{k ≤ n} (-1)^k q^(k choose 2) [n, k] = 0` for
  `n ≥ 1`.
-/

@[expose] public section

open Finset

variable {R : Type*} [CommRing R]

/-- The Gaussian binomial `[n, k]_q`, by the `q`-Pascal recursion
`[n+1, k+1] = [n, k] + q^(k+1) [n, k+1]`. -/
def qBinomial (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinomial q n k + q ^ (k + 1) * qBinomial q n (k + 1)

@[simp] theorem qBinomial_zero_right (q : R) (n : ℕ) : qBinomial q n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem qBinomial_zero_succ (q : R) (k : ℕ) : qBinomial q 0 (k + 1) = 0 := rfl

/-- The `q`-Pascal recursion. -/
theorem qBinomial_succ_succ (q : R) (n k : ℕ) :
    qBinomial q (n + 1) (k + 1) = qBinomial q n k + q ^ (k + 1) * qBinomial q n (k + 1) := rfl

/-- `[n, k] = 0` for `k > n`. -/
theorem qBinomial_eq_zero_of_lt (q : R) : ∀ {n k : ℕ}, n < k → qBinomial q n k = 0
  | 0, k + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [qBinomial_succ_succ, qBinomial_eq_zero_of_lt q (by omega : n < k),
      qBinomial_eq_zero_of_lt q (by omega : n < k + 1), mul_zero, add_zero]

/-- The `q`-binomial theorem: `∏_{i < n} (1 + q^i t) = Σ_{k ≤ n} q^(k choose 2) [n, k] t^k`. -/
theorem prod_one_add_pow_mul_eq_sum_qBinomial (q : R) (n : ℕ) (t : R) :
    ∏ i ∈ range n, (1 + q ^ i * t) =
      ∑ k ∈ range (n + 1), q ^ k.choose 2 * qBinomial q n k * t ^ k := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ', prod_congr rfl (fun k _ => show 1 + q ^ (k + 1) * t = 1 + q ^ k * (q * t)
      by ring), ih (q * t)]
    have hc : ∀ k : ℕ, (k + 1).choose 2 = k.choose 2 + k := fun k => by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    have h1 : ∀ k ∈ range (n + 1), q ^ k.choose 2 * qBinomial q n k * (q * t) ^ k * t =
        q ^ (k + 1).choose 2 * qBinomial q n k * t ^ (k + 1) := fun k _ => by
      rw [hc, pow_add, mul_pow, pow_succ]; ring
    have h2 : ∀ k ∈ range n, q ^ (k + 1).choose 2 * qBinomial q n (k + 1) * (q * t) ^ (k + 1) =
        q ^ (k + 1).choose 2 * (q ^ (k + 1) * qBinomial q n (k + 1)) * t ^ (k + 1) :=
      fun k _ => by rw [mul_pow]; ring
    -- left: `S * (1 + t) = S + S * t`, with `S * t` the shifted sum
    rw [pow_zero, one_mul, mul_add, mul_one, sum_mul, sum_congr rfl h1,
      sum_range_succ' (fun k => q ^ k.choose 2 * qBinomial q n k * (q * t) ^ k), sum_congr rfl h2]
    -- right: split at `k = 0`, apply the recursion, drop the vanishing term `k = n + 1`
    rw [sum_range_succ' _ (n + 1)]
    simp only [qBinomial_succ_succ, mul_add, add_mul, sum_add_distrib]
    rw [sum_range_succ (fun k => q ^ (k + 1).choose 2 * (q ^ (k + 1) * qBinomial q n (k + 1)) *
      t ^ (k + 1)), qBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
    simp only [Nat.choose_zero_succ, pow_zero, qBinomial_zero_right, mul_zero, zero_mul, add_zero,
      mul_one]
    ring

/-- The alternating sum of the Möbius function of the subspace lattice vanishes:
`Σ_{k ≤ n} (-1)^k q^(k choose 2) [n, k] = 0` for `n ≥ 1`. -/
theorem sum_neg_one_pow_mul_qBinomial_eq_zero (q : R) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), (-1) ^ k * q ^ k.choose 2 * qBinomial q n k = 0 := by
  have h := prod_one_add_pow_mul_eq_sum_qBinomial q n (-1)
  rw [prod_eq_zero (i := 0) (mem_range.2 hn) (by simp)] at h
  exact (sum_congr rfl fun k _ => by ring).trans h.symm
