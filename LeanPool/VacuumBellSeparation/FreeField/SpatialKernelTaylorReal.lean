/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialKernelMultiIndex
public import LeanPool.VacuumBellSeparation.FreeField.SpatialSeparatedCovarianceKernel

/-!
# The actual Taylor series restricts to the original real covariance kernels

The principal complex radius on real triples is exactly the Euclidean
norm of s e_0 + y - x. Thus the full contour series is a series for the
same field and momentum kernels already identified with the original
Fourier covariance, not a separate analytic kernel model.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped BigOperators ComplexOrder

/-- Embed the real spatial coordinates into their complex Euclidean space component by component. -/
noncomputable def spatialComplexOfReal (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℂ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm (fun j => (x j : ℂ))

/-- Spatial axis displacement. -/
noncomputable def spatialAxisDisplacement (s : ℝ) (δ : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
    (fun j => (if j = 0 then s else 0) + δ j)

@[simp] theorem spatialComplexOfReal_apply (x : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    spatialComplexOfReal x j = (x j : ℂ) := rfl

theorem spatialComplexOfReal_sub (x y : EuclideanSpace ℝ (Fin 3)) :
    spatialComplexOfReal (x - y) = spatialComplexOfReal x - spatialComplexOfReal y := by
  ext j
  simp

theorem spatialSquaredRadius_ofReal (s : ℝ) (δ : EuclideanSpace ℝ (Fin 3)) :
    spatialSquaredRadius s (spatialComplexOfReal δ) =
      (‖spatialAxisDisplacement s δ‖ ^ 2 : ℝ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [spatialSquaredRadius, spatialComplexOfReal_apply,
    spatialAxisDisplacement, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, Complex.ofReal_sum,
    Complex.ofReal_pow, Complex.ofReal_add]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem spatialComplexRadius_ofReal (s : ℝ) (δ : EuclideanSpace ℝ (Fin 3)) :
    spatialComplexRadius s (spatialComplexOfReal δ) = (‖spatialAxisDisplacement s δ‖ : ℂ) := by
  rw [spatialComplexRadius, spatialSquaredRadius_ofReal,
    Complex.sqrt_of_nonneg (by exact_mod_cast (sq_nonneg ‖spatialAxisDisplacement s δ‖)),
    Complex.ofReal_re, Real.sqrt_sq (norm_nonneg _)]

theorem besselFieldKernel_ofReal (μ r : ℝ) :
    besselFieldKernel μ (r : ℂ) =
      (μ / (4 * Real.pi ^ 2 * r) * besselKReal 1 (μ * r) : ℝ) := by
  unfold besselFieldKernel
  rw [← Complex.ofReal_mul μ r, modifiedBesselComplexIntegral_ofReal,
    modifiedBesselIntegral_eq_besselKReal]
  push_cast
  rfl

theorem besselMomentumKernel_ofReal (μ r : ℝ) :
    besselMomentumKernel μ (r : ℂ) =
      (-(μ ^ 2) / (4 * Real.pi ^ 2 * r ^ 2) * besselKReal 2 (μ * r) : ℝ) := by
  unfold besselMomentumKernel
  rw [← Complex.ofReal_mul μ r, modifiedBesselComplexIntegral_ofReal,
    modifiedBesselIntegral_eq_besselKReal]
  push_cast
  rfl

theorem spatialPairFieldKernel_ofReal (μ s : ℝ) (x y : EuclideanSpace ℝ (Fin 3)) :
    spatialPairFieldKernel μ s (spatialComplexOfReal x, spatialComplexOfReal y) =
      (spatialFieldBesselKernel μ (spatialAxisDisplacement s (y - x)) : ℂ) := by
  rw [spatialPairFieldKernel, ← spatialComplexOfReal_sub, spatialComplexRadius_ofReal,
    besselFieldKernel_ofReal]
  rfl

theorem spatialPairMomentumKernel_ofReal (μ s : ℝ) (x y : EuclideanSpace ℝ (Fin 3)) :
    spatialPairMomentumKernel μ s (spatialComplexOfReal x, spatialComplexOfReal y) =
      (spatialMomentumBesselKernel μ (spatialAxisDisplacement s (y - x)) : ℂ) := by
  rw [spatialPairMomentumKernel, ← spatialComplexOfReal_sub, spatialComplexRadius_ofReal,
    besselMomentumKernel_ofReal]
  rfl

theorem spatialFieldMultiCoefficient_real_expansion {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (x y : EuclideanSpace ℝ (Fin 3))
    (hx : ∀ j, ‖x j‖ < R) (hy : ∀ j, ‖y j‖ < R) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      spatialFieldMultiCoefficient μ s R k.1 k.2 *
        (∏ j, (x j : ℂ) ^ k.1 j) * ∏ j, (y j : ℂ) ^ k.2 j)
      (spatialFieldBesselKernel μ (spatialAxisDisplacement s (y - x)) : ℂ) := by
  have h := (spatialFieldMultiCoefficient_expansion hμ hs hR hsep
    (spatialComplexOfReal x) (spatialComplexOfReal y)
    (by simpa only [spatialComplexOfReal_apply, Complex.norm_real] using hx)
    (by simpa only [spatialComplexOfReal_apply, Complex.norm_real] using hy)).1
  simpa only [spatialComplexOfReal_apply, spatialPairFieldKernel_ofReal] using h

theorem spatialMomentumMultiCoefficient_real_expansion {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (x y : EuclideanSpace ℝ (Fin 3))
    (hx : ∀ j, ‖x j‖ < R) (hy : ∀ j, ‖y j‖ < R) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      spatialMomentumMultiCoefficient μ s R k.1 k.2 *
        (∏ j, (x j : ℂ) ^ k.1 j) * ∏ j, (y j : ℂ) ^ k.2 j)
      (spatialMomentumBesselKernel μ (spatialAxisDisplacement s (y - x)) : ℂ) := by
  have h := (spatialMomentumMultiCoefficient_expansion hμ hs hR hsep
    (spatialComplexOfReal x) (spatialComplexOfReal y)
    (by simpa only [spatialComplexOfReal_apply, Complex.norm_real] using hx)
    (by simpa only [spatialComplexOfReal_apply, Complex.norm_real] using hy)).1
  simpa only [spatialComplexOfReal_apply, spatialPairMomentumKernel_ofReal] using h

end VacuumBellSeparation
