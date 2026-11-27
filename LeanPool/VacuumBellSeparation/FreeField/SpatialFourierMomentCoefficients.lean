/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscCoefficientLinearity
public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceFourierComponents
public import LeanPool.VacuumBellSeparation.FreeField.SpatialTestMoments

/-!
# Actual Fourier contour coefficients are the literal spatial moments

The original Fourier phase is -i z dot x, with no 2 pi rescaling.
Compact-test Fubini evaluates its genuine nested contour coefficients.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory
open scoped BigOperators

/-- Spatial moment phase given by `(-Complex.I) ^ (∑ j, α j) / ∏ j, ((α j).factorial : ℂ)`. -/
noncomputable def spatialMomentPhase (α : Fin 3 → ℕ) : ℂ :=
  (-Complex.I) ^ (∑ j, α j) / ∏ j, ((α j).factorial : ℂ)

theorem spatialMomentPhase_ne_zero (α : Fin 3 → ℕ) : spatialMomentPhase α ≠ 0 := by
  unfold spatialMomentPhase
  exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
    (Finset.prod_ne_zero_iff.mpr fun j _ => Nat.cast_ne_zero.mpr (α j).factorial_ne_zero)

theorem spatialFourier_phase_sum (z : Fin 3 → ℂ) (x : EuclideanSpace ℝ (Fin 3)) :
    -(Complex.I * spatialDot z (fun j => (x j : ℂ))) =
      ∑ j, (-Complex.I * (x j : ℂ)) * z j := by
  rw [spatialDot, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem polydiscCoefficient_spatialFourier_kernel {R : ℝ} (hR : 0 < R)
    (α : Fin 3 → ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    polydiscCoefficient 3 R
      (fun z => Complex.exp (-(Complex.I * spatialDot z (fun j => (x j : ℂ))))) α =
        spatialMomentPhase α * spatialMonomial α x := by
  simp_rw [spatialFourier_phase_sum]
  rw [polydiscCoefficient_exp_sum 3 hR]
  simp only [mul_pow, Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, spatialMomentPhase, spatialMonomial]
  ring

theorem polydiscCoefficient_complexSpatialFourier {R : ℝ} (hR : 0 < R)
    (f : SpatialTestFunction) (α : Fin 3 → ℕ) :
    polydiscCoefficient 3 R (complexSpatialFourier f) α =
      spatialMomentPhase α * spatialTestMoment f α := by
  have hK : Continuous (fun y : (Fin 3 → ℂ) × EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * spatialDot y.1 (fun j => (y.2 j : ℂ))))) := by
    unfold spatialDot
    fun_prop
  have hfc : HasCompactSupport (fun x => (f.1 x : ℂ)) :=
    f.2.2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  change polydiscCoefficient 3 R
    (fun z => ∫ x, Complex.exp (-(Complex.I * spatialDot z (fun j => (x j : ℂ)))) *
      (f.1 x : ℂ)) α = _
  have hIntegral := polydiscCoefficient_compact_integral 3 hR _ hK
    (fun x => (f.1 x : ℂ))
    (show Continuous (fun x => (f.1 x : ℂ)) from
      Complex.continuous_ofReal.comp f.2.1.continuous) hfc
    (continuous_complexSpatialFourier f) α
  change polydiscCoefficient 3 R
    (fun z => ∫ x, Complex.exp (-(Complex.I * spatialDot z (fun j => (x j : ℂ)))) *
      (f.1 x : ℂ)) α = _ at hIntegral
  rw [hIntegral]
  simp_rw [polydiscCoefficient_spatialFourier_kernel hR, mul_assoc]
  exact integral_const_mul _ _

theorem spatialMomentPhase_norm (α : Fin 3 → ℕ) :
    ‖spatialMomentPhase α‖ = (∏ j, ((α j).factorial : ℝ))⁻¹ := by
  simp [spatialMomentPhase, norm_prod, norm_pow]

theorem spatialMomentPhase_norm_cancel (α : Fin 3 → ℕ) (a : ℂ) :
    (∏ j, ((α j).factorial : ℝ)) * ‖spatialMomentPhase α * a‖ = ‖a‖ := by
  have hfac : (∏ j, ((α j).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Nat.cast_ne_zero.mpr (α j).factorial_ne_zero
  rw [norm_mul, spatialMomentPhase_norm, ← mul_assoc, mul_inv_cancel₀ hfac, one_mul]

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

theorem polydiscCoefficient_complexSourceFieldFourier {R : ℝ} (hR : 0 < R)
    (x : ComplexSourceTestSpace hm U) (α : Fin 3 → ℕ) :
    polydiscCoefficient 3 R (fun z => complexSourceFieldFourier hm U z x) α =
      spatialMomentPhase α * (spatialTestMoment x.re.1.1 α +
        Complex.I * spatialTestMoment x.im.1.1 α) := by
  simp only [complexSourceFieldFourier_apply]
  rw [polydiscCoefficient_add_of_continuous 3 hR _ _
    (continuous_complexSpatialFourier _) ((continuous_complexSpatialFourier _).const_mul _),
    polydiscCoefficient_const_mul, polydiscCoefficient_complexSpatialFourier hR,
    polydiscCoefficient_complexSpatialFourier hR]
  ring

theorem polydiscCoefficient_complexSourceMomentumFourier {R : ℝ} (hR : 0 < R)
    (x : ComplexSourceTestSpace hm U) (α : Fin 3 → ℕ) :
    polydiscCoefficient 3 R (fun z => complexSourceMomentumFourier hm U z x) α =
      spatialMomentPhase α * (spatialTestMoment x.re.1.2 α +
        Complex.I * spatialTestMoment x.im.1.2 α) := by
  simp only [complexSourceMomentumFourier_apply]
  rw [polydiscCoefficient_add_of_continuous 3 hR _ _
    (continuous_complexSpatialFourier _) ((continuous_complexSpatialFourier _).const_mul _),
    polydiscCoefficient_const_mul, polydiscCoefficient_complexSpatialFourier hR,
    polydiscCoefficient_complexSpatialFourier hR]
  ring

end VacuumBellSeparation
