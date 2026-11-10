/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OrnsteinUhlenbeck

/-! # The generator identity for Ornstein–Uhlenbeck averages -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- The standard OU generator `ΔF - x·∇F`. -/
def ouGenerator {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, coordinateDerivative (coordinateDerivative F i) i x) - fderiv ℝ F x x

/-- An affine Gaussian shift of a fixed directional derivative is integrable under second derivative
growth bounds. -/
theorem integrable_shift_fderiv_fixed {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x v : Fin n → ℝ) (c : ℝ) :
    Integrable (fun z => fderiv ℝ F (x + c • z) v) (standardGaussianMeasure n) := by
  obtain ⟨C, hC, d, _, hfirst, _⟩ := hF.2
  have hterm (i : Fin n) : Integrable
      (fun z => v i * coordinateDerivative F i (x + c • z)) (standardGaussianMeasure n) :=
    (integrable_shift_of_polynomial_bound
      (contDiff_coordinateDerivative_of_two hF.1 i).continuous.measurable hC (hfirst i) x
        c).const_mul (v i)
  have h := integrable_finsetSum (s := Finset.univ) (fun i _ => hterm i)
  apply h.congr
  exact ae_of_all _ fun z => (concentration_fderiv_apply_eq_sum (x + c • z) v).symm

/-- The derivative evaluated in the Gaussian direction is integrable under second derivative growth
bounds. -/
theorem integrable_shift_fderiv_id {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x : Fin n → ℝ) (c : ℝ) :
    Integrable (fun z => fderiv ℝ F (x + c • z) z) (standardGaussianMeasure n) := by
  obtain ⟨C, hC, d, _, hfirst, _⟩ := hF.2
  have hterm (i : Fin n) : Integrable
      (fun z => z i * coordinateDerivative F i (x + c • z)) (standardGaussianMeasure n) :=
    integrable_eval_mul_shift_of_polynomial_bound
      (contDiff_coordinateDerivative_of_two hF.1 i).continuous.measurable hC (hfirst i) i x c
  have h := integrable_finsetSum (s := Finset.univ) (fun i _ => hterm i)
  simpa only [← concentration_fderiv_apply_eq_sum] using h

/-- An affine Gaussian shift of the Laplacian is integrable under second derivative growth bounds.
-/
theorem integrable_shift_laplacian {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x : Fin n → ℝ) (c : ℝ) :
    Integrable (fun z => ∑ i, coordinateDerivative (coordinateDerivative F i) i (x + c • z))
      (standardGaussianMeasure n) := by
  obtain ⟨C, hC, d, _, _, hsecond⟩ := hF.2
  apply integrable_finsetSum
  intro i _
  have hcont : Continuous (coordinateDerivative (coordinateDerivative F i) i) := by
    unfold coordinateDerivative
    exact ((contDiff_coordinateDerivative_of_two hF.1 i).continuous_fderiv
      (by norm_num)).clm_apply continuous_const
  exact integrable_shift_of_polynomial_bound hcont.measurable hC (hsecond i i) x c

/-- An affine Gaussian shift of the Ornstein–Uhlenbeck generator is integrable under second
derivative growth bounds. -/
theorem integrable_shift_ouGenerator {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x : Fin n → ℝ) (c : ℝ) :
    Integrable (fun z => ouGenerator F (x + c • z)) (standardGaussianMeasure n) := by
  have hfixed := integrable_shift_fderiv_fixed hF x x c
  have hid := integrable_shift_fderiv_id hF x c
  have hdrift : Integrable (fun z => fderiv ℝ F (x + c • z) (x + c • z))
      (standardGaussianMeasure n) := by
    apply (hfixed.add (hid.const_mul c)).congr
    exact ae_of_all _ fun z => by
      change fderiv ℝ F (x + c • z) x + c * fderiv ℝ F (x + c • z) z = _
      dsimp only
      rw [map_add, map_smul, smul_eq_mul]
  exact (integrable_shift_laplacian hF x c).sub hdrift

/-- Differentiating the OU operator in time equals averaging its generator.
The polynomial smoothness hypotheses justify every integral split and IBP. -/
theorem hasDerivAt_ouAverage_generator {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) (x : Fin n → ℝ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (ouAverage F x) (ouAverage (ouGenerator F) x t) t := by
  let e := Real.exp (-t)
  let r := Real.exp (-2 * t)
  let b := Real.sqrt (1 - r)
  let w : (Fin n → ℝ) → (Fin n → ℝ) := fun z => e • x + b • z
  have hF₂ := hF
  have hF₁ := hasPolynomiallyBoundedCoordinateDerivatives_of_second hF₂
  have hpos : 0 < 1 - r := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    linarith only [ht]
  have hb : b ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hb2 : b ^ 2 = 1 - r := Real.sq_sqrt hpos.le
  have hxint := integrable_shift_fderiv_fixed hF (e • x) x b
  have hzint := integrable_shift_fderiv_id hF₂ (e • x) b
  have hlap := integrable_shift_laplacian hF₂ (e • x) b
  have hz : (∫ z, fderiv ℝ F (w z) z ∂standardGaussianMeasure n) =
      b * ∫ z, ∑ i, coordinateDerivative (coordinateDerivative F i) i (w z)
        ∂standardGaussianMeasure n :=
    integral_fderiv_shift_scaled_eq_sqrt_mul_laplacian hF₁ hF₂ (e • x) hpos
  have hdrift : Integrable (fun z => fderiv ℝ F (w z) (w z))
      (standardGaussianMeasure n) := by
    have h := (hxint.const_mul e).add (hzint.const_mul b)
    apply h.congr
    exact ae_of_all _ fun z => by
      change e * fderiv ℝ F (w z) x + b * fderiv ℝ F (w z) z =
        fderiv ℝ F (w z) (w z)
      dsimp only [w]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hgen : ouAverage (ouGenerator F) x t =
      ∫ z, fderiv ℝ F (w z) (-e • x + (r / b) • z) ∂standardGaussianMeasure n := by
    change (∫ z, (∑ i, coordinateDerivative (coordinateDerivative F i) i (w z)) -
      fderiv ℝ F (w z) (w z) ∂standardGaussianMeasure n) = _
    rw [integral_sub hlap hdrift]
    simp only [w, map_add, map_smul, smul_eq_mul]
    rw [integral_add (hxint.const_mul e) (hzint.const_mul b),
      integral_add (hxint.const_mul (-e)) (hzint.const_mul (r / b)),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
    dsimp only [w] at hz
    rw [hz]
    rw [show r = 1 - b ^ 2 by linarith only [hb2]]
    field_simp
    ring
  rw [hgen]
  exact hasDerivAt_ouAverage hF₁ x ht

end EhrhardGaussian.Ehrhard

end
