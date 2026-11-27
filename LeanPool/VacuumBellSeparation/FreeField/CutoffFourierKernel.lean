/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SchwartzBanachFactorization
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Actual oscillatory kernels and polynomial Schwartz bounds

These kernels use Mathlib's normalized Fourier character, with the negative
sign of the forward transform. Their derivatives are derived from the actual
Fourier integral against a Dirac measure. The resulting polynomial frequency
bounds are appropriate for integrating against arbitrary Schwartz functions;
no exponential decay of a Schwartz function is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped SchwartzMap FourierTransform InnerProductSpace

namespace VacuumBellSeparation

/-- Spatial Fourier character defined as `𝐞 (-⟪p, x⟫_ℝ)`. -/
noncomputable def spatialFourierCharacter
    (p x : EuclideanSpace ℝ (Fin 3)) : ℂ := 𝐞 (-⟪p, x⟫_ℝ)

@[simp] theorem norm_spatialFourierCharacter (p x : EuclideanSpace ℝ (Fin 3)) :
    ‖spatialFourierCharacter p x‖ = 1 := by
  simp [spatialFourierCharacter]

theorem hasTemperateGrowth_spatialFourierCharacter (p : EuclideanSpace ℝ (Fin 3)) :
    Function.HasTemperateGrowth (spatialFourierCharacter p) := by
  have h : Function.HasTemperateGrowth
      (fun x : EuclideanSpace ℝ (Fin 3) => -2 * Real.pi * ⟪p, x⟫_ℝ) := by fun_prop
  convert Complex.hasTemperateGrowth_exp_mul_I.comp h using 1
  funext x
  simp only [Function.comp_def, spatialFourierCharacter, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem iteratedFDeriv_spatialFourierCharacter (p x : EuclideanSpace ℝ (Fin 3)) (j : ℕ) :
    iteratedFDeriv ℝ j (spatialFourierCharacter p) x =
      (𝐞 (-⟪p, x⟫_ℝ)) •
        VectorFourier.fourierPowSMulRight (innerSL ℝ)
          (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℂ)) p j := by
  have h := congrFun (VectorFourier.iteratedFDeriv_fourierIntegral (innerSL ℝ)
    (μ := Measure.dirac p) (f := fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℂ))
    (N := (⊤ : ℕ∞))
    (fun _ _ => integrable_dirac (by simp)) aestronglyMeasurable_const
    (n := j) le_top) x
  have he : VectorFourier.fourierIntegral 𝐞 (Measure.dirac p)
      (innerSL ℝ).toLinearMap₁₂ (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℂ)) =
        spatialFourierCharacter p := by
    funext y
    simp [VectorFourier.fourierIntegral, Circle.smul_def, spatialFourierCharacter]
  rw [he] at h
  simp only [VectorFourier.fourierIntegral, integral_dirac, Circle.smul_def] at h
  convert h using 1; rfl

theorem norm_iteratedFDeriv_spatialFourierCharacter_le
    (p x : EuclideanSpace ℝ (Fin 3)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (spatialFourierCharacter p) x‖ ≤
      (2 * Real.pi * ‖innerSL ℝ (E := EuclideanSpace ℝ (Fin 3))‖) ^ j * ‖p‖ ^ j := by
  rw [iteratedFDeriv_spatialFourierCharacter, Circle.norm_smul]
  simpa only [norm_one, mul_one] using
    VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ)
      (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℂ)) p j

/-- Actual multiplication by the normalized forward Fourier character. -/
noncomputable def cutoffFourierKernel
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (spatialFourierCharacter p) χ

@[simp] theorem cutoffFourierKernel_apply
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (p x : EuclideanSpace ℝ (Fin 3)) :
    cutoffFourierKernel χ p x = spatialFourierCharacter p x * χ x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_spatialFourierCharacter p) χ x

theorem tsupport_cutoffFourierKernel_subset
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) : tsupport (cutoffFourierKernel χ p) ⊆ tsupport χ := by
  have he : (cutoffFourierKernel χ p : EuclideanSpace ℝ (Fin 3) → ℂ) =
      fun x => spatialFourierCharacter p x * χ x := funext (cutoffFourierKernel_apply χ p)
  rw [he]
  exact tsupport_mul_subset_right

/-- Every kernel seminorm has polynomial, rather than exponential, frequency growth. -/
theorem seminorm_cutoffFourierKernel_le
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) (k j : ℕ) :
    SchwartzMap.seminorm ℂ k j (cutoffFourierKernel χ p) ≤
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ((2 * Real.pi * ‖innerSL ℝ (E := EuclideanSpace ℝ (Fin 3))‖) ^ i * ‖p‖ ^ i) *
          SchwartzMap.seminorm ℂ k (j - i) χ := by
  apply SchwartzMap.seminorm_le_bound
  · positivity
  · intro x
    have h := norm_iteratedFDeriv_smul_le
      (hasTemperateGrowth_spatialFourierCharacter p).1 (χ.smooth ⊤) x (n := j)
      (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
    have heq : (fun y => spatialFourierCharacter p y • χ y) = cutoffFourierKernel χ p := by
      funext y
      exact (cutoffFourierKernel_apply χ p y).symm
    rw [heq] at h
    calc
      _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (spatialFourierCharacter p) x‖ *
            ‖iteratedFDeriv ℝ (j - i) χ x‖ :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (spatialFourierCharacter p) x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (j - i) χ x‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_spatialFourierCharacter_le p x i) (by positivity))
          (χ.le_seminorm ℂ k (j - i) x) (by positivity) (by positivity)

end VacuumBellSeparation
