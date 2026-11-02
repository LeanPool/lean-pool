/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.AuxiliarySeries
import Mathlib.Tactic.Positivity

/-! # An obstruction to the local deduction in Lemma 1

Equation (25) only assumes summability of `|λ(p^ν)| / p^ν`. The proof then
inserts an exponentially growing auxiliary factor. The following single-prime
example proves that this insertion need not preserve summability.

For `1 < a < 2`, take `θ(2^ν) = (2/a)^ν`. Its consecutive differences satisfy
(23) at this prime, but multiplication by `a^ν` turns the positive-exponent
terms into the positive constant `1 - a/2`.

These are local sequence statements. `LemmaOneCounterexample` connects them to
a complete arithmetic counterexample to the printed Lemma 1.
-/

@[expose] public section

namespace NairTenenbaum.LemmaOneObstruction

/-- The auxiliary twist in the counterexample to the printed Lemma 1. -/
noncomputable def theta (a : ℝ) (ν : ℕ) : ℝ := (2 / a) ^ ν

/-- `λ(2^(ν+1)) / 2^(ν+1)`, so the index begins at exponent one. -/
noncomputable def localDifference (a : ℝ) (ν : ℕ) : ℝ :=
  |theta a (ν + 1) - theta a ν| / (2 : ℝ) ^ (ν + 1)

theorem localDifference_eq {a : ℝ} (ha₀ : 0 < a) (ha₂ : a < 2) (ν : ℕ) :
    localDifference a ν = (1 / a - 1 / 2) * (1 / a) ^ ν := by
  have hratio : 1 < 2 / a := (one_lt_div ha₀).mpr ha₂
  have hdiff : 0 ≤ theta a (ν + 1) - theta a ν := by
    dsimp [theta]
    rw [pow_succ, sub_nonneg]
    exact le_mul_of_one_le_right (pow_nonneg (by positivity : 0 ≤ 2 / a) ν) hratio.le
  rw [localDifference, abs_of_nonneg hdiff]
  simp only [theta, div_pow, pow_succ]
  field_simp [ha₀.ne']
  ring

theorem unweighted_summable {a : ℝ} (ha₁ : 1 < a) (ha₂ : a < 2) :
    Summable (localDifference a) := by
  have ha₀ : 0 < a := lt_trans zero_lt_one ha₁
  change Summable (fun ν => localDifference a ν)
  simp_rw [localDifference_eq ha₀ ha₂]
  exact (summable_geometric_of_lt_one (by positivity) ((div_lt_one ha₀).mpr ha₁)).mul_left _

theorem weighted_term {a : ℝ} (ha₁ : 1 < a) (ha₂ : a < 2) (ν : ℕ) :
    localDifference a ν * a ^ (ν + 1) = 1 - a / 2 := by
  have ha₀ : 0 < a := lt_trans zero_lt_one ha₁
  rw [localDifference_eq ha₀ ha₂]
  simp only [one_div_pow, pow_succ]
  field_simp [ha₀.ne']

theorem weighted_not_summable {a : ℝ} (ha₁ : 1 < a) (ha₂ : a < 2) :
    ¬ Summable (fun ν : ℕ => localDifference a ν * a ^ (ν + 1)) := by
  simp_rw [weighted_term ha₁ ha₂]
  rw [summable_const_iff]
  linarith

theorem weighted_partial_sum {a : ℝ} (ha₁ : 1 < a) (ha₂ : a < 2) (N : ℕ) :
    ∑ ν ∈ Finset.range N, localDifference a ν * a ^ (ν + 1) = N * (1 - a / 2) := by
  simp only [weighted_term ha₁ ha₂, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem weighted_partial_sums_unbounded {a : ℝ} (ha₁ : 1 < a) (ha₂ : a < 2) (C : ℝ) :
    ∃ N : ℕ, C < ∑ ν ∈ Finset.range N, localDifference a ν * a ^ (ν + 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (C / (1 - a / 2))
  refine ⟨N, ?_⟩
  rw [weighted_partial_sum ha₁ ha₂]
  exact (div_lt_iff₀ (by linarith : 0 < 1 - a / 2)).mp hN

theorem untwisted_model_summable {a : ℝ} (ha₀ : 0 ≤ a) (ha₂ : a < 2) :
    Summable (fun ν : ℕ => a ^ ν / (2 : ℝ) ^ ν) := by
  simp_rw [← div_pow]
  exact summable_geometric_of_lt_one (by positivity) (by linarith)

theorem twisted_model_term {a : ℝ} (ha : a ≠ 0) (ν : ℕ) :
    a ^ ν * theta a ν / (2 : ℝ) ^ ν = 1 := by
  simp only [theta, div_pow]
  field_simp

theorem twisted_model_not_summable {a : ℝ} (ha : a ≠ 0) :
    ¬ Summable (fun ν : ℕ => a ^ ν * theta a ν / (2 : ℝ) ^ ν) := by
  simp_rw [twisted_model_term ha]
  simp only [summable_const_iff, one_ne_zero, not_false_eq_true]

/-- The geometric weight is the paper's actual auxiliary function at `p=2`,
with `A=2^η`, `B=1`, `γ=1`. -/
theorem auxiliaryLocal_two (η : ℝ) (ν : ℕ) :
    auxiliaryLocal ((2 : ℝ) ^ η) 1 η 1 2 ν = ((2 : ℝ) ^ η) ^ ν := by
  by_cases hν : ν = 0
  · simp [hν]
  simp only [auxiliaryLocal, ite_eq_right hν, one_mul, Nat.cast_ofNat]
  split_ifs
  · rfl
  · rw [Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]

/-- The failure persists for arbitrarily small positive growth exponents. -/
theorem auxiliary_weighted_not_summable {η : ℝ} (hη₀ : 0 < η) (hη₁ : η < 1) :
    Summable (localDifference ((2 : ℝ) ^ η)) ∧
      ¬ Summable (fun ν : ℕ => localDifference ((2 : ℝ) ^ η) ν *
        auxiliaryLocal ((2 : ℝ) ^ η) 1 η 1 2 (ν + 1)) := by
  have ha₁ : 1 < (2 : ℝ) ^ η := Real.one_lt_rpow (by norm_num) hη₀
  have ha₂ : (2 : ℝ) ^ η < 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hη₁
  refine ⟨unweighted_summable ha₁ ha₂, ?_⟩
  simp_rw [auxiliaryLocal_two]
  exact weighted_not_summable ha₁ ha₂

end NairTenenbaum.LemmaOneObstruction
