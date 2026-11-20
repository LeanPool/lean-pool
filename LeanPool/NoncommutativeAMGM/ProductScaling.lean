/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.MatrixOrder
public import LeanPool.NoncommutativeAMGM.FallingFactorial

/-! # Scaling and exact falling-factorial normalization of the ordered products -/

@[expose] public section
namespace NoncommutativeAMGM
open scoped BigOperators

theorem orderedWord_smul {R : Type*} [Semiring R] [Algebra ℝ R]
    {n : ℕ} (A : Fin n → R) (a : ℝ) (m : ℕ) (f : Fin m → Fin n) :
    (List.ofFn fun j ↦ a • A (f j)).prod = a ^ m • (List.ofFn fun j ↦ A (f j)).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih, smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ']

theorem distinctProductSum_smul {R : Type*} [Semiring R] [Algebra ℝ R]
    (n m : ℕ) (A : Fin n → R) (a : ℝ) :
    distinctProductSum n m (fun i ↦ a • A i) = a ^ m • distinctProductSum n m A := by
  classical
  rw [distinctProductSum, distinctProductSum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro f _
  exact orderedWord_smul A a m f

theorem withoutReplacementMean_eq_inv_falling {R : Type*} [Semiring R] [Algebra ℝ R]
    {n m : ℕ} (hmn : m ≤ n) (A : Fin n → R) :
    withoutReplacementMean n m A = (falling (n : ℝ) m)⁻¹ • distinctProductSum n m A := by
  rw [withoutReplacementMean, normalization_eq_inv_card hmn, card_distinct_tuples, falling_natCast]

theorem normalized_distinctProductSum {R : Type*} [Semiring R] [Algebra ℝ R]
    {n m : ℕ} (hn : 0 < n) (hmn : m ≤ n) (A : Fin n → R) :
    ((n : ℝ) ^ m / falling n m) •
      distinctProductSum n m (fun i ↦ (n : ℝ)⁻¹ • A i) = withoutReplacementMean n m A := by
  rw [distinctProductSum_smul, smul_smul, withoutReplacementMean_eq_inv_falling hmn]
  congr 1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [inv_pow]
  calc
    _ = ((n : ℝ) ^ m * ((n : ℝ) ^ m)⁻¹) * (falling n m)⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hn0), one_mul]

/-- Normalize every arbitrary admissible PSD input by `n`, including its slack inequality. -/
theorem admissible_normalized {n d : ℕ} (hn : 0 < n)
    (A : Fin n → Matrix (Fin d) (Fin d) ℝ) (hA : Admissible A) :
    (∀ i, ((n : ℝ)⁻¹ • A i).PosSemidef) ∧
      (1 - ∑ i, (n : ℝ)⁻¹ • A i).PosSemidef := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · intro i
    exact (hA.1 i).smul (by positivity)
  · have h := loewner_smul hA.2 (show 0 ≤ (n : ℝ)⁻¹ by positivity)
    simpa only [Matrix.le_iff, ← Finset.smul_sum, smul_smul, inv_mul_cancel₀ hn0, one_smul] using h

end NoncommutativeAMGM
