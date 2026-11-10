/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianLinearForm
public import LeanPool.EhrhardGaussian.Ehrhard.ScalarOUProfile
public import LeanPool.EhrhardGaussian.Ehrhard.OrnsteinUhlenbeck

/-! # Pullback of scalar OU smoothing along Gaussian linear forms -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open EhrhardGaussian.Gaussian (standardGaussianMeasure coordinateDerivative)
open scoped NNReal BigOperators

namespace EhrhardGaussian.Ehrhard

/-- Scaling a standard Gaussian variable gives variance equal to the squared scale. -/
theorem hasLaw_gaussian_scale (σ : ℝ) :
    HasLaw (fun z : ℝ => σ * z) (gaussianReal 0 (σ ^ 2).toNNReal) (gaussianReal 0 1) := by
  have hid : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1) := ⟨aemeasurable_id, Measure.map_id⟩
  have h := gaussianReal_const_mul hid σ
  have hv : NNReal.mk (σ ^ 2) (sq_nonneg σ) * 1 = (σ ^ 2).toNNReal := by
    ext
    simpa only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one] using
      (Real.coe_toNNReal _ (sq_nonneg σ)).symm
  rw [mul_zero, hv] at h
  exact h

/-- Ornstein–Uhlenbeck averaging along a linear form reduces to scalar averaging with the
corresponding variance. -/
theorem ouAverage_comp_coordinateForm {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f)
    (c : Fin n → ℝ) {σ : ℝ} (hvar : ∑ i, c i ^ 2 = σ ^ 2) (x : Fin n → ℝ) (t : ℝ) :
    ouAverage (f ∘ coordinateForm c) x t = scalarOU f σ (coordinateForm c x) t := by
  let b := Real.sqrt (1 - Real.exp (-2 * t))
  let g := fun u => f (Real.exp (-t) * coordinateForm c x + b * u)
  have hg : Measurable g := hf.comp (by fun_prop)
  have hform := (hasLaw_coordinateForm c).integral_comp hg.aestronglyMeasurable
  rw [hvar] at hform
  have hscale := (hasLaw_gaussian_scale σ).integral_comp hg.aestronglyMeasurable
  calc
    _ = ∫ z, g (coordinateForm c z) ∂standardGaussianMeasure n := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        simp only [Function.comp_def, g, map_add, map_smul, smul_eq_mul, b]
    _ = ∫ u, g u ∂gaussianReal 0 (σ ^ 2).toNNReal := hform
    _ = ∫ z, g (σ * z) ∂gaussianReal 0 1 := hscale.symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by dsimp only [g, b]; congr 1; ring

/-- The coordinate derivative of a linear pullback average is the scalar derivative times its
coefficient. -/
theorem coordinateDerivative_ouAverage_comp_coordinateForm {n : ℕ} {f : ℝ → ℝ}
    (hf : Measurable f) (hbound : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (c : Fin n → ℝ) {σ : ℝ} (hσ : 0 < σ) (hvar : ∑ i, c i ^ 2 = σ ^ 2)
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 < t) (j : Fin n) :
    coordinateDerivative (fun y => ouAverage (f ∘ coordinateForm c) y t) j x =
      deriv (fun u => scalarOU f σ u t) (coordinateForm c x) * c j := by
  have heq : (fun y => ouAverage (f ∘ coordinateForm c) y t) =
      (fun u => scalarOU f σ u t) ∘ coordinateForm c := by
    funext y
    exact ouAverage_comp_coordinateForm hf c hvar y t
  rw [heq, coordinateDerivative]
  have hd := (hasDerivAt_scalarOU hf hbound hσ ht (coordinateForm c x)).hasFDerivAt.comp x
    (coordinateForm c).hasFDerivAt
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, coordinateForm_single]
  rw [(hasDerivAt_scalarOU hf hbound hσ ht (coordinateForm c x)).deriv]
  exact mul_comm _ _

end EhrhardGaussian.Ehrhard

end
