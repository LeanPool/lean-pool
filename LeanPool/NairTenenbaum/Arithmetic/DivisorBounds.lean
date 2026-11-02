/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import LeanPool.NairTenenbaum.Hooley.Hooley
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Positivity

/-! # Divisor bounds and admissibility of Hooley's function

An elementary proof of `τ(n) ≤ 2^Ω(n)` and `τ(n) ≪_ε n^ε`.
These complete the membership assertion for `Δ` in the introduction.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real

theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have h : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
    omega

theorem card_divisors_le_two_pow {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ≤ 2 ^ bigOmega n := by
  rw [Nat.card_divisors hn]
  calc
    ∏ p ∈ n.primeFactors, (n.factorization p + 1) ≤
        ∏ p ∈ n.primeFactors, 2 ^ n.factorization p :=
      Finset.prod_le_prod (fun p _ => succ_le_two_pow _)
    _ = 2 ^ bigOmega n := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      exact (ArithmeticFunction.cardFactors_eq_sum_factorization (n := n)).symm

/-- A uniform bound for the linear factor in a prime-power divisor count. -/
theorem linear_le_geometric {a : ℝ} (ha : 1 < a) (ν : ℕ) :
    (ν : ℝ) + 1 ≤ (1 + (a - 1)⁻¹) * a ^ ν := by
  have hd : 0 < a - 1 := sub_pos.mpr ha
  have hpow : 1 ≤ a ^ ν := one_le_pow₀ ha.le
  have hbern := one_add_mul_sub_le_pow (a := a) (by linarith : -1 ≤ a) ν
  have hν : (ν : ℝ) ≤ (a - 1)⁻¹ * a ^ ν := by
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hd).2
    linarith
  nlinarith

theorem primePower_divisor_bound {ε : ℝ} (hε : 0 < ε)
    (N : ℕ) (hN : (2 : ℝ) ^ ε⁻¹ ≤ N) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    (ν : ℝ) + 1 ≤
      (if p ≤ N then 1 + ((2 : ℝ) ^ ε - 1)⁻¹ else 1) * ((p : ℝ) ^ ε) ^ ν := by
  have ha : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  split_ifs with h
  · have hbase : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp.two_le) hε.le
    exact (linear_le_geometric ha ν).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase ν) (by positivity))
  · have hbase : (2 : ℝ) ≤ (p : ℝ) ^ ε :=
      (Real.rpow_inv_le_iff_of_pos (by norm_num) (by positivity) hε).mp
        (hN.trans (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge h)))
    have hν : (ν : ℝ) + 1 ≤ (2 : ℝ) ^ ν := by exact_mod_cast succ_le_two_pow ν
    simpa using hν.trans (pow_le_pow_left₀ (by norm_num) hbase ν)

/-- The standard subpolynomial divisor bound, with constants uniform in `n`. -/
theorem exists_card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ B * (n : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 : ℝ) ^ ε⁻¹)
  let C : ℝ := 1 + ((2 : ℝ) ^ ε - 1)⁻¹
  have hC : 1 ≤ C := by
    have : 0 < (2 : ℝ) ^ ε - 1 := sub_pos.mpr (Real.one_lt_rpow (by norm_num) hε)
    dsimp [C]
    exact le_add_of_nonneg_right (inv_nonneg.mpr this.le)
  refine ⟨C ^ (N + 1), one_le_pow₀ hC, fun n hn => ?_⟩
  have hprod : (∏ p ∈ n.primeFactors, (if p ≤ N then C else 1)) ≤ C ^ (N + 1) := by
    classical
    have hcard : (n.primeFactors.filter (· ≤ N)).card ≤ N + 1 := by
      apply le_trans (Finset.card_le_card (t := Finset.range (N + 1)) ?_) (by simp)
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
    simpa [Finset.prod_ite] using pow_le_pow_right₀ hC hcard
  have hpowers : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) = (n : ℝ) ^ ε := by
    calc
      _ = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε := by
        apply Finset.prod_congr rfl
        intro p _
        exact Real.rpow_pow_comm (by positivity) _ _
      _ = (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) ^ ε :=
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity) _
      _ = (n : ℝ) ^ ε := by
        congr 1
        exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn]
      push_cast
      rfl
    _ ≤ ∏ p ∈ n.primeFactors, (if p ≤ N then C else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro p hp
      exact primePower_divisor_bound hε N hN.le (Nat.prime_of_mem_primeFactors hp) _
    _ = (∏ p ∈ n.primeFactors, (if p ≤ N then C else 1)) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ C ^ (N + 1) * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)

/-- Hooley's function as a function of a one-dimensional positive tuple. -/
noncomputable def hooleyMap : ArithmeticMap 1 := fun n => hooleyDelta (n 0)

/-- The admissibility assertion in §1, for every positive exponent. -/
theorem hooley_admissible {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧ Admissible 2 B ε hooleyMap := by
  obtain ⟨B, hB, hτ⟩ := exists_card_divisors_le_rpow hε
  refine ⟨B, hB, ⟨fun _ => Nat.cast_nonneg _, fun m n hmn => ?_⟩⟩
  have hm : (m 0 : ℕ) ≠ 0 := (m 0).ne_zero
  have hmass : mass m = (m 0 : ℕ) := by simp [mass]
  have hbound : ((m 0 : ℕ).divisors.card : ℝ) ≤ growthBound 2 B ε m := by
    rw [growthBound, hmass]
    exact le_min (by exact_mod_cast card_divisors_le_two_pow hm) (hτ _ hm)
  calc
    hooleyMap (m * n) ≤ ((m 0 : ℕ).divisors.card : ℝ) * hooleyMap n := by
      unfold hooleyMap
      exact_mod_cast hooleyDelta_mul_le (hmn 0)
    _ ≤ growthBound 2 B ε m * hooleyMap n := mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _)

/-- Every positive real power of Hooley's function lies in an arithmetic class
with an arbitrarily small positive growth exponent. -/
theorem hooley_rpow_admissible {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    ∃ B : ℝ, 1 ≤ B ∧ Admissible ((2 : ℝ) ^ t) B ε (fun n => hooleyMap n ^ t) := by
  obtain ⟨B, hB, hF⟩ := hooley_admissible (div_pos hε ht)
  refine ⟨B ^ t, Real.one_le_rpow hB ht.le, ?_⟩
  simpa only [div_mul_cancel₀ ε ht.ne'] using hF.rpow (by norm_num) (zero_le_one.trans hB) ht.le

end NairTenenbaum
