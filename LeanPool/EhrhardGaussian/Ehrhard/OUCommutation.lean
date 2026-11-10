/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUSpatialDerivatives

/-! # Commutation of the OU generator with its Gaussian integral operator -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- Time derivative expressed using averaged spatial derivatives of the input. -/
theorem hasDerivAt_ouAverage_laplacian {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) (x : Fin n → ℝ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (ouAverage F x)
      (Real.exp (-t) ^ 2 *
          ouAverage (fun y => ∑ i, coordinateDerivative (coordinateDerivative F i) i y) x t -
        Real.exp (-t) * ouAverage (fun y => fderiv ℝ F y x) x t) t := by
  let e := Real.exp (-t)
  let r := Real.exp (-2 * t)
  let b := Real.sqrt (1 - r)
  let w : (Fin n → ℝ) → (Fin n → ℝ) := fun z => e • x + b • z
  have hpos : 0 < 1 - r := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [ht]))
  have hb : b ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have he2 : r = e ^ 2 := exp_neg_two_eq_sq t
  have hF₁ := hasPolynomiallyBoundedCoordinateDerivatives_of_second hF
  have hxint := integrable_shift_fderiv_fixed hF (e • x) x b
  have hzint := integrable_shift_fderiv_id hF (e • x) b
  have hz : (∫ z, fderiv ℝ F (w z) z ∂standardGaussianMeasure n) =
      b * ∫ z, ∑ i, coordinateDerivative (coordinateDerivative F i) i (w z)
        ∂standardGaussianMeasure n :=
    integral_fderiv_shift_scaled_eq_sqrt_mul_laplacian hF₁ hF (e • x) hpos
  convert hasDerivAt_ouAverage hF₁ x ht using 1
  change e ^ 2 * (∫ z, ∑ i, coordinateDerivative (coordinateDerivative F i) i (w z)
    ∂standardGaussianMeasure n) - e * (∫ z, fderiv ℝ F (w z) x ∂standardGaussianMeasure n) =
    ∫ z, fderiv ℝ F (w z) (-e • x + (r / b) • z) ∂standardGaussianMeasure n
  simp only [map_add, map_smul, smul_eq_mul]
  rw [integral_add (hxint.const_mul (-e)) (hzint.const_mul (r / b)),
    integral_const_mul, integral_const_mul, hz, ← mul_assoc, div_mul_cancel₀ _ hb, he2]
  ring

/-- The spatial generator applied after averaging has the same explicit
Laplacian and drift formula. -/
theorem ouGenerator_ouAverage_eq_laplacian {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) (x : Fin n → ℝ) (t : ℝ) :
    ouGenerator (fun y => ouAverage F y t) x =
      Real.exp (-t) ^ 2 *
          ouAverage (fun y => ∑ i, coordinateDerivative (coordinateDerivative F i) i y) x t -
        Real.exp (-t) * ouAverage (fun y => fderiv ℝ F y x) x t := by
  have hF₁ := hasPolynomiallyBoundedCoordinateDerivatives_of_second hF
  have hsum : (∑ i, ouAverage (coordinateDerivative (coordinateDerivative F i) i) x t) =
      ouAverage (fun y => ∑ i, coordinateDerivative (coordinateDerivative F i) i y) x t := by
    symm
    apply integral_finsetSum
    intro i _
    obtain ⟨C, hC, d, _, _, hsecond⟩ := hF.2
    have hcont : Continuous (coordinateDerivative (coordinateDerivative F i) i) := by
      unfold coordinateDerivative
      exact ((contDiff_coordinateDerivative_of_two hF.1 i).continuous_fderiv
        (by norm_num)).clm_apply continuous_const
    exact integrable_shift_of_polynomial_bound hcont.measurable hC (hsecond i i)
      (Real.exp (-t) • x) (Real.sqrt (1 - Real.exp (-2 * t)))
  rw [ouGenerator]
  simp_rw [secondCoordinateDerivative_ouAverage hF x t]
  rw [← Finset.mul_sum, hsum, fderiv_ouAverage_apply hF₁ x x t]
  rfl

/-- The OU operator commutes with its generator at positive times. This is
the linear commutation identity underlying the nonlinear interpolation formula. -/
theorem ouGenerator_ouAverage {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) (x : Fin n → ℝ)
    {t : ℝ} (ht : 0 < t) :
    ouGenerator (fun y => ouAverage F y t) x = ouAverage (ouGenerator F) x t := by
  rw [ouGenerator_ouAverage_eq_laplacian hF x t]
  exact (hasDerivAt_ouAverage_laplacian hF x ht).unique
    (hasDerivAt_ouAverage_generator hF x ht)

end EhrhardGaussian.Ehrhard

end
