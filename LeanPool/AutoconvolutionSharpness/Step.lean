/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import LeanPool.AutoconvolutionSharpness.Definitions
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Convolution

/-!
# Integrability and positivity of finite step functions
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Autoconvolutions

/-- Every finite unit - cell input is in every Lᵖ space, including L¹ and L². -/
theorem step_memLp (d : ℕ) (p : Fin (d + 1) → ℝ) (q : ℝ≥0∞) :
    MemLp (step d p) q volume := by
  apply memLp_finsetSum
  intro j _
  apply memLp_indicator_const _ measurableSet_Ico.nullMeasurableSet _ (.inr ?_)
  simp [Real.volume_Ico]

theorem step_nonneg (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∀ j, 0 ≤ p j) (x : ℝ) :
    0 ≤ step d p x := by
  apply Finset.sum_nonneg
  intro j _
  exact Set.indicator_nonneg (fun _ _ => hp j) x

/-- Unit cells have Lebesgue measure one, so their coefficients add without weights. -/
theorem integral_step (d : ℕ) (p : Fin (d + 1) → ℝ) :
    (∫ x : ℝ, step d p x) = ∑ j, p j := by
  simp only [step]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    simp [integral_indicator_const _ measurableSet_Ico, Measure.real, Real.volume_Ico]
  · intro j _
    apply (integrable_indicator_iff measurableSet_Ico).2
    exact integrableOn_const (by simp [Real.volume_Ico])

theorem sum_pos_of_positive_cell {d : ℕ} {p : Fin (d + 1) → ℝ}
    (hp : ∀ j, 0 ≤ p j) (hne : ∃ j, 0 < p j) : 0 < ∑ j, p j := by
  obtain ⟨j, hj⟩ := hne
  exact Finset.sum_pos' (fun i _ => hp i) ⟨j, Finset.mem_univ _, hj⟩

theorem auto_step_nonneg {d : ℕ} {p : Fin (d + 1) → ℝ} (hp : ∀ j, 0 ≤ p j) (x : ℝ) :
    0 ≤ auto (step d p) x :=
  integral_nonneg fun t => mul_nonneg (step_nonneg d p hp t) (step_nonneg d p hp (x - t))

/-- Fubini for scalar convolution gives the paper's identity F(1)². -/
theorem integral_auto_step (d : ℕ) (p : Fin (d + 1) → ℝ) :
    (∫ x : ℝ, auto (step d p) x) = (∑ j, p j) ^ 2 := by
  have hf : Integrable (step d p) volume := memLp_one_iff_integrable.mp (step_memLp d p 1)
  have he := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf hf
  change (∫ x : ℝ, auto (step d p) x) =
    (∫ x : ℝ, step d p x) * (∫ x : ℝ, step d p x) at he
  simpa only [integral_step, pow_two] using he

theorem auto_step_not_ae_zero {d : ℕ} {p : Fin (d + 1) → ℝ}
    (hp : ∀ j, 0 ≤ p j) (hne : ∃ j, 0 < p j) : ¬ auto (step d p) =ᵐ[volume] 0 := by
  intro h
  have h0 := integral_eq_zero_of_ae h
  rw [integral_auto_step] at h0
  exact (pow_pos (sum_pos_of_positive_cell hp hne) 2).ne' h0

end Autoconvolutions
