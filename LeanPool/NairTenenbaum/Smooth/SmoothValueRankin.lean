/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SelectedTiltComparison

/-! # Separating small polynomial values before the smoothness saving -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem extendArithmeticMap_selectedTilt {k : ℕ} (F : ArithmeticMap k) (j : Fin k)
    (s : Finset ℕ) (β : ℝ) (n : Fin k → ℕ) :
    extendArithmeticMap (selectedTilt F j s β) n =
      extendArithmeticMap F n * selectedMoment s β (n j) := by
  unfold extendArithmeticMap
  split_ifs
  · rfl
  · simp only [zero_mul]

theorem smooth_value_le_tilt {k : ℕ} {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n)
    (j : Fin k) (s : Finset ℕ) {β T : ℝ} (hβ : 0 ≤ β) (hT : 0 < T)
    (n : Fin k → ℕ) (hs : n j ∈ Nat.factoredNumbers s) (hlarge : T ≤ (n j : ℝ)) :
    extendArithmeticMap F n ≤ T ^ (-β) * extendArithmeticMap (selectedTilt F j s β) n := by
  rw [extendArithmeticMap_selectedTilt, selectedMoment_eq_rpow β hs]
  have H := Real.rpow_le_rpow hT.le hlarge hβ
  have H' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left H (Real.rpow_nonneg hT.le (-β)))
    (extendArithmeticMap_nonneg hF n)
  rw [← Real.rpow_add hT, neg_add_cancel, Real.rpow_zero, one_mul] at H'
  exact H'.trans_eq (by ring)

/-- The small-value term is explicit. No lower bound on polynomial values
near their roots is assumed. -/
theorem smooth_values_sum_le_small_add_tilt {ι : Type*} {k : ℕ} {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) (j : Fin k) (s : Finset ℕ) {β T : ℝ}
    (hβ : 0 ≤ β) (hT : 0 < T) (S : Finset ι) (v : ι → Fin k → ℕ) :
    (∑ i ∈ S.filter (fun i => v i j ∈ Nat.factoredNumbers s), extendArithmeticMap F (v i)) ≤
      (∑ i ∈ S.filter (fun i => (v i j : ℝ) ≤ T), extendArithmeticMap F (v i)) +
        T ^ (-β) * ∑ i ∈ S, extendArithmeticMap (selectedTilt F j s β) (v i) := by
  classical
  rw [sum_filter, sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hterm : 0 ≤ T ^ (-β) * extendArithmeticMap (selectedTilt F j s β) (v i) := by
    apply mul_nonneg (Real.rpow_nonneg hT.le _)
    exact extendArithmeticMap_nonneg (fun n => mul_nonneg (hF n) (selectedMoment_nonneg _ _ _)) _
  by_cases hs : v i j ∈ Nat.factoredNumbers s
  · rw [ite_eq_left hs]
    by_cases hsmall : (v i j : ℝ) ≤ T
    · rw [ite_eq_left hsmall]
      exact le_add_of_nonneg_right hterm
    · rw [ite_eq_right hsmall, zero_add]
      exact smooth_value_le_tilt hF j s hβ hT (v i) hs (le_of_lt (lt_of_not_ge hsmall))
  · rw [ite_eq_right hs]
    exact add_nonneg (by split_ifs <;> [exact extendArithmeticMap_nonneg hF _; exact le_rfl]) hterm

/-- The short sum restricted to polynomial values with the prescribed smoothness. -/
noncomputable def smoothShortSum {k : ℕ} (Q : Fin k → ℤ[X]) (F : ArithmeticMap k)
    (j : Fin k) (x y z : ℝ) : ℝ :=
  ∑ n ∈ (shortInterval x y).filter (fun n : ℕ =>
    ((Q j).eval (n : ℤ)).natAbs ∈ Nat.factoredNumbers (Icc 0 ⌊z⌋₊)),
      extendArithmeticMap F (fun i => ((Q i).eval (n : ℤ)).natAbs)

theorem smoothShortSum_le_small_add_tilt {k : ℕ} (Q : Fin k → ℤ[X]) {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) (j : Fin k) {κ z T : ℝ} (hκ : 0 ≤ κ) (hz : 1 < z)
    (hT : 0 < T) (x y : ℝ) :
    smoothShortSum Q F j x y z ≤
      (∑ n ∈ (shortInterval x y).filter (fun n : ℕ => (((Q j).eval (n : ℤ)).natAbs : ℝ) ≤ T),
        extendArithmeticMap F (fun i => ((Q i).eval (n : ℤ)).natAbs)) +
      Real.exp (-κ * Real.log T / Real.log z) *
        shortSum Q (selectedTilt F j (Icc 0 ⌊z⌋₊) (κ / Real.log z)) x y := by
  have H := smooth_values_sum_le_small_add_tilt hF j (Icc 0 ⌊z⌋₊)
    (div_nonneg hκ (Real.log_pos hz).le) hT (shortInterval x y)
    (fun n i => ((Q i).eval (n : ℤ)).natAbs)
  have Hexp : T ^ (-(κ / Real.log z)) = Real.exp (-κ * Real.log T / Real.log z) := by
    rw [Real.rpow_def_of_pos hT]
    congr 1
    ring
  simpa only [Hexp, shortSum, smoothShortSum] using H

end NairTenenbaum
