/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Hooley.Hooley
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Integral moments of Hooley's divisor windows

These moments are the analytic starting point of the weighted mean estimate
in Tenenbaum, *Sur une question d'Erdős et Schinzel, II*, Lemma 2.2.
Integrability is proved from the finite indicator representation, including
the convention at `n=0`.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real MeasureTheory

/-- The divisor count in a logarithmic window used to define Hooley's function. -/
noncomputable def hooleyWindow (n : ℕ) (u : ℝ) : ℝ := divisorWindow n u

theorem hooleyWindow_nonneg (n : ℕ) (u : ℝ) : 0 ≤ hooleyWindow n u := Nat.cast_nonneg _

theorem hooleyWindow_le_card (n : ℕ) (u : ℝ) :
    hooleyWindow n u ≤ (n.divisors.card : ℝ) := by
  unfold hooleyWindow
  exact_mod_cast divisorWindow_le_card n u

theorem hooleyWindow_eq_sum_indicator (n : ℕ) (u : ℝ) :
    hooleyWindow n u = ∑ d ∈ n.divisors,
      (Set.Ico (Real.log d - 1) (Real.log d)).indicator (fun _ : ℝ => (1 : ℝ)) u := by
  classical
  rw [hooleyWindow, divisorWindow_eq_sum, Nat.cast_sum]
  apply sum_congr rfl
  intro d hd
  have H : (u < Real.log d ∧ Real.log d ≤ u + 1) ↔
      u ∈ Set.Ico (Real.log d - 1) (Real.log d) := by
    simp only [Set.mem_Ico]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  by_cases h : u ∈ Set.Ico (Real.log d - 1) (Real.log d) <;> simp [H, h]

theorem measurable_hooleyWindow (n : ℕ) : Measurable (hooleyWindow n) := by
  have H : hooleyWindow n = fun u => ∑ d ∈ n.divisors,
      (Set.Ico (Real.log d - 1) (Real.log d)).indicator (fun _ : ℝ => (1 : ℝ)) u :=
    funext (hooleyWindow_eq_sum_indicator n)
  rw [H]
  exact Finset.measurable_sum _ fun d _ => measurable_const.indicator measurableSet_Ico

theorem integrable_hooleyWindow (n : ℕ) : Integrable (hooleyWindow n) := by
  have H : hooleyWindow n = fun u => ∑ d ∈ n.divisors,
      (Set.Ico (Real.log d - 1) (Real.log d)).indicator (fun _ : ℝ => (1 : ℝ)) u :=
    funext (hooleyWindow_eq_sum_indicator n)
  rw [H]
  apply integrable_finsetSum
  intro d hd
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (μ := volume) (s := Set.Ico (Real.log d - 1) (Real.log d))
      (C := (1 : ℝ)) (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))

theorem integral_hooleyWindow (n : ℕ) :
    (∫ u : ℝ, hooleyWindow n u) = n.divisors.card := by
  simp_rw [hooleyWindow_eq_sum_indicator]
  have hi (d : ℕ) : Integrable ((Set.Ico (Real.log d - 1) (Real.log d)).indicator
      (fun _ : ℝ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ico).mpr
      (integrableOn_const (μ := volume) (s := Set.Ico (Real.log d - 1) (Real.log d))
        (C := (1 : ℝ)) (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  rw [integral_finsetSum _ (fun d _ => hi d)]
  have H (d : ℕ) : (∫ u : ℝ,
      (Set.Ico (Real.log d - 1) (Real.log d)).indicator (fun _ : ℝ => (1 : ℝ)) u) = 1 := by
    rw [integral_indicator_const _ measurableSet_Ico]
    simp [Measure.real, Real.volume_Ico]
  simp_rw [H]
  simp

theorem integrable_hooleyWindow_pow (n : ℕ) {q : ℕ} (hq : 0 < q) :
    Integrable (fun u => hooleyWindow n u ^ q) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  simp_rw [pow_succ]
  apply (integrable_hooleyWindow n).bdd_mul ((measurable_hooleyWindow n).pow_const
      r).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hooleyWindow_nonneg n u) r)]
    exact pow_le_pow_left₀ (hooleyWindow_nonneg n u) (hooleyWindow_le_card n u) r

/-- The moment `M_q(n)`; positive orders are the integrable ones used below. -/
noncomputable def hooleyMoment (q n : ℕ) : ℝ := ∫ u : ℝ, hooleyWindow n u ^ q

theorem hooleyMoment_nonneg (q n : ℕ) : 0 ≤ hooleyMoment q n :=
  integral_nonneg fun u => pow_nonneg (hooleyWindow_nonneg n u) q

@[simp] theorem hooleyMoment_one (n : ℕ) : hooleyMoment 1 n = n.divisors.card := by
  simp only [hooleyMoment, pow_one, integral_hooleyWindow]

@[simp] theorem hooleyMoment_at_zero {q : ℕ} (hq : 0 < q) : hooleyMoment q 0 = 0 := by
  simp [hooleyMoment, hooleyWindow, divisorWindow, hq.ne']

/-- The elementary upper half of the moment comparison (2.6). -/
theorem hooleyMoment_le_card_pow (n : ℕ) {q : ℕ} (hq : 0 < q) :
    hooleyMoment q n ≤ (n.divisors.card : ℝ) ^ q := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  have H := integral_mono (integrable_hooleyWindow_pow n (Nat.succ_pos r))
    ((integrable_hooleyWindow n).const_mul ((n.divisors.card : ℝ) ^ r))
    (fun u => by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (hooleyWindow_nonneg n u) (hooleyWindow_le_card n u) r)
        (hooleyWindow_nonneg n u))
  simpa only [integral_const_mul, integral_hooleyWindow, pow_succ, hooleyMoment] using H

end NairTenenbaum
