/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Finite-order and linear-moment bounds for compact Fourier analysis

The scalar norm of an actual tempered distribution is controlled by finitely
many genuine Schwartz seminorms. The polynomial moments of a compact cutoff
have explicit derivative and seminorm bounds, retaining the descending
factorials needed for exponential Taylor convergence. No Schwartz norm or
completeness instance is assumed.
-/

@[expose] public section

open scoped SchwartzMap NNReal

namespace VacuumBellSeparation

/-- Continuity of the actual distribution implies a finite family of seminorm bounds. -/
theorem temperedDistribution_finite_seminorm_bound
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ,
        ‖T φ‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 3)) ℂ)) φ := by
  let q : Seminorm ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :=
    (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq : Continuous q := T.continuous.norm
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin 3)) ℂ) q hq
  refine ⟨s, C, hC, fun φ => ?_⟩
  exact hb φ

/-- An exact linear phase permits the sharp descending-factorial derivative bound. -/
theorem norm_iteratedFDeriv_realLinear_pow_le
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (n j : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖iteratedFDeriv ℝ j (fun y => (a y) ^ n) x‖ ≤
      (n.descFactorial j : ℝ) * |a x| ^ (n - j) * ‖a‖ ^ j := by
  have hdiff : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ n) := by fun_prop
  have hcomp := a.iteratedFDeriv_comp_right hdiff x (i := j) (by simp)
  rw [show (fun y => (a y) ^ n) = (fun t : ℝ => t ^ n) ∘ a by rfl, hcomp]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun t : ℝ => t ^ n) (a x)‖ * ∏ _ : Fin j, ‖a‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = _ := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_pow]
      simp [norm_mul, norm_pow, Real.norm_eq_abs]

/-- Multiplication by a power of the actual real linear phase on Schwartz space. -/
noncomputable def spatialLinearMoment (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (n : ℕ) (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x => (a x) ^ n) φ

@[simp] theorem spatialLinearMoment_apply (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (n : ℕ) (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    spatialLinearMoment a n φ x = (a x) ^ n • φ x := by
  apply SchwartzMap.smulLeftCLM_apply_apply
  exact a.hasTemperateGrowth.pow n

theorem tsupport_spatialLinearMoment_subset (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (n : ℕ) (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    tsupport (spatialLinearMoment a n φ) ⊆ tsupport φ := by
  have heq : ⇑(spatialLinearMoment a n φ) = fun x => (a x) ^ n • φ x :=
    funext (spatialLinearMoment_apply a n φ)
  rw [heq]
  exact tsupport_smul_subset_right (fun x => (a x) ^ n) (fun x => φ x)

/-- A cutoff-support phase bound controls every actual Schwartz seminorm of its moments. -/
theorem seminorm_spatialLinearMoment_le
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    {R : ℝ} (hR : 0 ≤ R) (ha : ∀ x ∈ tsupport φ, |a x| ≤ R) (k j n : ℕ) :
    SchwartzMap.seminorm ℂ k j (spatialLinearMoment a n φ) ≤
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ((n.descFactorial i : ℝ) * R ^ (n - i) * ‖a‖ ^ i) *
          SchwartzMap.seminorm ℂ k (j - i) φ := by
  apply SchwartzMap.seminorm_le_bound
  · positivity
  · intro x
    by_cases hx : x ∈ tsupport φ
    · have hdiff : ContDiff ℝ (⊤ : ℕ∞) (fun y => (a y) ^ n) := by fun_prop
      have hb := norm_iteratedFDeriv_smul_le hdiff (φ.smooth ⊤) x (n := j) (by simp)
      have heq : (fun y => (a y) ^ n • φ y) = spatialLinearMoment a n φ := by
        funext y
        exact (spatialLinearMoment_apply a n φ y).symm
      rw [heq] at hb
      calc
        _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y => (a y) ^ n) x‖ *
              ‖iteratedFDeriv ℝ (j - i) φ x‖ :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y => (a y) ^ n) x‖ *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ (j - i) φ x‖) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i hi
          have hp := norm_iteratedFDeriv_realLinear_pow_le a n i x
          have hp' : ‖iteratedFDeriv ℝ i (fun y => (a y) ^ n) x‖ ≤
              (n.descFactorial i : ℝ) * R ^ (n - i) * ‖a‖ ^ i := by
            apply hp.trans
            gcongr
            exact ha x hx
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hp' (by positivity))
            (φ.le_seminorm ℂ k (j - i) x) (by positivity) (by positivity)
    · have hzero : iteratedFDeriv ℝ j (spatialLinearMoment a n φ) x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h =>
          hx ((tsupport_spatialLinearMoment_subset a n φ)
            ((tsupport_iteratedFDeriv_subset j) h))
      rw [hzero, norm_zero, mul_zero]
      positivity

end VacuumBellSeparation
