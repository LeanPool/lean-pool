/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.DifferenceFamily

/-! # The coefficient estimate with the actual polynomial endpoint removed -/

@[expose] public section
namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators

theorem powerTail_dvd {L j : ℕ} (p : Polynomial ℝ) (hp : p ∈ powerTail L j) :
    (X - 1 : Polynomial ℝ) ^ j ∣ p := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨l, hjl, _, rfl⟩ := hq
    exact pow_dvd_pow _ hjl
  | zero => exact dvd_zero _
  | add p q _ _ hp hq => exact dvd_add hp hq
  | smul a p _ hp =>
    rw [Algebra.smul_def]
    exact dvd_mul_of_dvd_right hp _

/-- The vanishing condition survives reduction to the polynomial's actual degree. -/
theorem powerTail_actual_degree {L j : ℕ} (p : Polynomial ℝ) (hp : p ∈ powerTail L j)
    (hpz : p ≠ 0) : p ∈ powerTail (p.natDegree + 1) j := by
  obtain ⟨q, hq⟩ := powerTail_dvd p hp
  have hx : (X - 1 : Polynomial ℝ) ≠ 0 := by exact X_sub_C_ne_zero 1
  have hqz : q ≠ 0 := by intro he; rw [he, mul_zero] at hq; exact hpz hq
  have hdeg : p.natDegree = j + q.natDegree := by
    rw [hq, natDegree_mul (pow_ne_zero _ hx) hqz, natDegree_pow]
    rw [show (X - 1 : Polynomial ℝ).natDegree = 1 from natDegree_X_sub_C (1 : ℝ), Nat.mul_one]
  have hmem := shift_pow_mul_mem_powerTail (j := j) q
    (show q.degree < (q.natDegree + 1 : ℕ) by
      apply degree_le_natDegree.trans_lt
      exact_mod_cast Nat.lt_succ_self q.natDegree)
  have hL : q.natDegree + 1 + j = p.natDegree + 1 := by omega
  simpa only [hL, ← hq] using hmem

/-- The coefficient seminorm deleting the first and actual last coefficients. -/
noncomputable def actualInteriorCoefficientNormSq (p : Polynomial ℝ) : ℝ :=
  interiorCoefficientNormSq p.natDegree p

/-- Lemma 3.10 with the literal actual-degree seminorm from the paper. -/
theorem coefficient_norm_step_actual {L j : ℕ} (hjL : j < L) (p : Polynomial ℝ)
    (hp : p ∈ powerTail L j) :
    ((j : ℝ) * ((j : ℝ) + 1)) * realCoefficientInner p p ≤
      ((L : ℝ) ^ 2 / 4) * actualInteriorCoefficientNormSq ((X - 1) * p) := by
  by_cases hpz : p = 0
  · simp [hpz, realCoefficientInner, actualInteriorCoefficientNormSq, interiorCoefficientNormSq]
  have hx : (X - 1 : Polynomial ℝ) ≠ 0 := X_sub_C_ne_zero 1
  have hprod : ((X - 1) * p).natDegree = p.natDegree + 1 := by
    rw [natDegree_mul hx hpz]
    rw [show (X - 1 : Polynomial ℝ).natDegree = 1 from natDegree_X_sub_C (1 : ℝ)]
    omega
  have hmem := powerTail_actual_degree p hp hpz
  have hj : j < p.natDegree + 1 := by
    have hdvd := natDegree_le_of_dvd (powerTail_dvd p hp) hpz
    simp only [natDegree_pow, show (X - 1 : Polynomial ℝ).natDegree = 1 from
      natDegree_X_sub_C (1 : ℝ), Nat.mul_one] at hdvd
    omega
  have hbound := coefficient_norm_step_padded hj p hmem
  have hdegree := powerTail_natDegree_lt (by omega : 0 < L) p hp
  have hle : ((p.natDegree + 1 : ℕ) : ℝ) ≤ L := by
    exact_mod_cast (show p.natDegree + 1 ≤ L by omega)
  have hsq : (((p.natDegree + 1 : ℕ) : ℝ) ^ 2 / 4) ≤ (L : ℝ) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((L : ℝ) - ((p.natDegree + 1 : ℕ) : ℝ))]
  apply hbound.trans
  rw [actualInteriorCoefficientNormSq, hprod]
  exact mul_le_mul_of_nonneg_right hsq (interiorCoefficientNormSq_nonneg _ _)

end NoncommutativeAMGM
