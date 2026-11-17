/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUGenerator

/-! # Spatial derivatives of Ornstein–Uhlenbeck averages -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- The spatial derivative of an Ornstein–Uhlenbeck average is its averaged derivative times
exponential decay. -/
theorem hasFDerivAt_ouAverage_center {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) (x : Fin n → ℝ) (t : ℝ) :
    HasFDerivAt (fun y => ouAverage F y t)
      (Real.exp (-t) • ∫ z,
        fderiv ℝ F (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • z)
          ∂standardGaussianMeasure n) x := by
  have hcenter := hasFDerivAt_shiftAverage_center hF (Real.exp (-t) • x)
    (Real.sqrt (1 - Real.exp (-2 * t)))
  have h := hcenter.2.1.comp x ((hasFDerivAt_id x).const_smul (Real.exp (-t)))
  convert h using 1
  · rfl
  · ext v
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul]

/-- A directional derivative passes through Ornstein–Uhlenbeck averaging with the exponential decay
factor. -/
theorem fderiv_ouAverage_apply {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) (x v : Fin n → ℝ) (t : ℝ) :
    fderiv ℝ (fun y => ouAverage F y t) x v =
      Real.exp (-t) * ∫ z,
        fderiv ℝ F (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • z) v
          ∂standardGaussianMeasure n := by
  rw [(hasFDerivAt_ouAverage_center hF x t).fderiv, smul_apply, smul_eq_mul]
  congr 1
  exact ContinuousLinearMap.integral_apply
    (hasFDerivAt_shiftAverage_center hF (Real.exp (-t) • x)
      (Real.sqrt (1 - Real.exp (-2 * t)))).1 v

/-- Coordinate differentiation commutes with Ornstein–Uhlenbeck averaging up to exponential decay.
-/
theorem coordinateDerivative_ouAverage {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) (x : Fin n → ℝ) (t : ℝ)
    (i : Fin n) :
    coordinateDerivative (fun y => ouAverage F y t) i x =
      Real.exp (-t) * ouAverage (coordinateDerivative F i) x t :=
  fderiv_ouAverage_apply hF x (Pi.single i 1) t

/-- Second derivative growth bounds give polynomially bounded first derivatives of each coordinate
derivative. -/
theorem polynomiallySmooth_coordinateDerivative {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) (i : Fin n) :
    HasPolynomiallyBoundedCoordinateDerivatives (coordinateDerivative F i) := by
  have h := hasPolynomiallyBoundedCoordinateDerivatives_affinePartial hF 0 1 i
  simpa only [one_smul, zero_add] using h

/-- Second coordinate differentiation commutes with Ornstein–Uhlenbeck averaging up to squared
exponential decay. -/
theorem secondCoordinateDerivative_ouAverage {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) (x : Fin n → ℝ) (t : ℝ)
    (i j : Fin n) :
    coordinateDerivative (coordinateDerivative (fun y => ouAverage F y t) i) j x =
      Real.exp (-t) ^ 2 * ouAverage (coordinateDerivative (coordinateDerivative F i) j) x t := by
  have hF₁ := hasPolynomiallyBoundedCoordinateDerivatives_of_second hF
  have hFi := polynomiallySmooth_coordinateDerivative hF i
  have heq : coordinateDerivative (fun y => ouAverage F y t) i =
      fun y => Real.exp (-t) * ouAverage (coordinateDerivative F i) y t := by
    funext y
    exact coordinateDerivative_ouAverage hF₁ y t i
  rw [heq, coordinateDerivative,
    ((hasFDerivAt_ouAverage_center hFi x t).const_mul (Real.exp (-t))).fderiv,
    smul_apply, smul_eq_mul]
  have h := fderiv_ouAverage_apply hFi x (Pi.single j 1) t
  rw [(hasFDerivAt_ouAverage_center hFi x t).fderiv, smul_apply, smul_eq_mul] at h
  simp only [smul_apply, smul_eq_mul]
  rw [h]
  simp only [ouAverage, coordinateDerivative]
  ring

end EhrhardGaussian.Ehrhard

end
