/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Special.BesselK
public import LeanPool.VacuumBellSeparation.Gaussian.SpatialBesselKernels

/-!
# Compatibility with the repository's existing modified Bessel functions

The newer shifted-Laplace proof uses exactly the existing cosh-integral
definition. These identities expose reuse of the existing all-order
integrability theorem, and extend the original function with genuine
right-half-plane holomorphy. There is no separate special-function model.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Set

theorem modifiedBesselIntegral_eq_besselKReal (n : ℕ) (x : ℝ) :
    modifiedBesselIntegral n x = besselKReal (n : ℝ) x := by
  simp only [modifiedBesselIntegral, besselKReal, neg_mul]

theorem modifiedBesselComplexIntegral_eq_besselK (n : ℕ) (z : ℂ) :
    modifiedBesselComplexIntegral n z = besselK (n : ℝ) z := by
  simp only [modifiedBesselComplexIntegral, besselK, neg_mul]

theorem hasDerivAt_besselK_nat (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (besselK (n : ℝ))
      (∫ u in Ioi (0 : ℝ), modifiedBesselDerivativeIntegrand n z u) z := by
  have hint (x : ℝ) (hx : 0 < x) : IntegrableOn
      (fun u : ℝ => Real.exp (-x * Real.cosh u) * Real.cosh ((n : ℝ) * u)) (Ioi 0) := by
    simpa only [neg_mul] using integrableOn_besselKReal_integrand (n : ℝ) hx
  have h := hasDerivAt_modifiedBesselComplexIntegral n hint hz
  have he : modifiedBesselComplexIntegral n = besselK (n : ℝ) :=
    funext (modifiedBesselComplexIntegral_eq_besselK n)
  rw [he] at h
  exact h

theorem differentiableOn_besselK_nat (n : ℕ) :
    DifferentiableOn ℂ (besselK (n : ℝ)) {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (hasDerivAt_besselK_nat n hz).differentiableAt.differentiableWithinAt

theorem besselFieldKernel_eq_existing (μ : ℝ) (ρ : ℂ) :
    besselFieldKernel μ ρ = (μ : ℂ) / ((4 * Real.pi ^ 2 : ℝ) * ρ) *
      besselK 1 ((μ : ℂ) * ρ) := by
  simp only [besselFieldKernel, modifiedBesselComplexIntegral_eq_besselK, Nat.cast_one]

theorem besselMomentumKernel_eq_existing (μ : ℝ) (ρ : ℂ) :
    besselMomentumKernel μ ρ = -(μ : ℂ) ^ 2 / ((4 * Real.pi ^ 2 : ℝ) * ρ ^ 2) *
      besselK 2 ((μ : ℂ) * ρ) := by
  simp only [besselMomentumKernel, modifiedBesselComplexIntegral_eq_besselK, Nat.cast_ofNat]

end VacuumBellSeparation.Gaussian
