/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Hooley.HooleyDirichletCoefficients
public import Mathlib.Analysis.PSeries

/-! # Convergence of the squarefree Hooley moment Dirichlet series

Both the series and its logarithmically weighted series converge for every
real argument greater than one. The coefficient bounds are proved rather
than imposed as hypotheses on the Dirichlet series.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

/-- The Dirichlet series of the root-weighted Hooley moment. -/
noncomputable def hooleyDirichlet (Q : ℤ[X]) (t : ℝ) (q : ℕ) (σ : ℝ) : ℝ :=
  ∑' n : ℕ, hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-σ)

theorem summable_hooleyDirichlet {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    Summable (fun n : ℕ => hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-σ)) := by
  let η := (σ - 1) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨C, hC, hbound⟩ := exists_hooleyMomentCoefficient_le_rpow Q.natDegree ht hη
  have hmajor : Summable (fun n : ℕ => C * (n : ℝ) ^ (η - σ)) :=
    (Real.summable_nat_rpow.mpr (by dsimp [η]; linarith)).mul_left C
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg
    (hooleyMomentCoefficient_nonneg Q t q n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _ hmajor
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [hooleyMomentCoefficient_zero, zero_mul]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc
    _ ≤ (C * (n : ℝ) ^ η) * (n : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_right (hbound Q hQ le_rfl q hq n) (Real.rpow_nonneg hn'.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hn', sub_eq_add_neg]

theorem summable_log_hooleyDirichlet {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    Summable (fun n : ℕ => hooleyMomentCoefficient Q t q n * Real.log n * (n : ℝ) ^ (-σ)) := by
  let η := (σ - 1) / 4
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨C, hC, hbound⟩ := exists_hooleyMomentCoefficient_le_rpow Q.natDegree ht hη
  have hmajor : Summable (fun n : ℕ => (C / η) * (n : ℝ) ^ (2 * η - σ)) :=
    (Real.summable_nat_rpow.mpr (by dsimp [η]; linarith)).mul_left (C / η)
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg
    (hooleyMomentCoefficient_nonneg Q t q n) (Real.log_natCast_nonneg n))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _ hmajor
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [hooleyMomentCoefficient_zero, zero_mul]
    exact mul_nonneg (div_nonneg (zero_le_one.trans hC) hη.le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc
    _ ≤ ((C * (n : ℝ) ^ η) * ((n : ℝ) ^ η / η)) * (n : ℝ) ^ (-σ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn'.le _)
      exact mul_le_mul (hbound Q hQ le_rfl q hq n) (Real.log_le_rpow_div hn'.le hη)
        (Real.log_natCast_nonneg n) (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hn'.le _))
    _ = (C / η) * ((n : ℝ) ^ η * (n : ℝ) ^ η * (n : ℝ) ^ (-σ)) := by ring
    _ = _ := by rw [← Real.rpow_add hn', ← Real.rpow_add hn']; congr 2; ring

theorem hooleyDirichlet_nonneg (Q : ℤ[X]) (t : ℝ) (q : ℕ) (σ : ℝ) :
    0 ≤ hooleyDirichlet Q t q σ :=
  tsum_nonneg (fun n => mul_nonneg (hooleyMomentCoefficient_nonneg Q t q n)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem one_le_hooleyDirichlet {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    1 ≤ hooleyDirichlet Q t q σ := by
  have H := (summable_hooleyDirichlet hQ ht hq hσ).le_tsum 1 (fun n _ =>
    mul_nonneg (hooleyMomentCoefficient_nonneg Q t q n) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  simpa only [hooleyMomentCoefficient_one Q t hq, Nat.cast_one, Real.one_rpow, one_mul,
      hooleyDirichlet] using H

end NairTenenbaum
