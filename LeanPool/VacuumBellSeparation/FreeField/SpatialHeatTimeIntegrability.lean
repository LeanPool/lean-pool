/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatBoundary

/-!
# Integrability of the actual heat-time integration-by-parts terms

The singular three-halves weight is controlled by the actual linear
zero-time estimate for separated tests. All time integrals are therefore
absolutely convergent before integration by parts is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory Set Filter
open scoped ComplexConjugate

theorem stronglyMeasurable_spatialHeatFourierPairing (f g : SpatialTestFunction) :
    StronglyMeasurable (spatialHeatFourierPairing f g) := by
  have hc : Continuous (fun tp : ℝ × EuclideanSpace ℝ (Fin 3) =>
      (Real.exp (-tp.1 * ‖tp.2‖ ^ 2) : ℂ) *
        (conj (spatialFourier f tp.2) * spatialFourier g tp.2)) := by
    have hf := continuous_spatialFourier f
    have hg := continuous_spatialFourier g
    fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'

theorem stronglyMeasurable_spatialHeatFourierDerivative (f g : SpatialTestFunction) :
    StronglyMeasurable (spatialHeatFourierDerivative f g) := by
  have hc : Continuous (fun tp : ℝ × EuclideanSpace ℝ (Fin 3) =>
      (-(‖tp.2‖ ^ 2 : ℝ) : ℂ) * ((Real.exp (-tp.1 * ‖tp.2‖ ^ 2) : ℂ) *
        (conj (spatialFourier f tp.2) * spatialFourier g tp.2))) := by
    have hf := continuous_spatialFourier f
    have hg := continuous_spatialFourier g
    fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'

theorem spatialHeatFourierDerivative_norm_le {t : ℝ} (ht : 0 ≤ t)
    (f g : SpatialTestFunction) :
    ‖spatialHeatFourierDerivative f g t‖ ≤
      ∫ p : EuclideanSpace ℝ (Fin 3),
        (‖p‖ ^ 2 * ‖spatialFourier f p‖) * ‖spatialFourier g p‖ :=
  norm_integral_le_of_norm_le (integrable_pow_norm_spatialFourier_product f g 2)
    (Eventually.of_forall (spatialHeatFourier_derivative_integrand_bound ht f g))

theorem integrableOn_spatialHeatMassPrimitive {m : ℝ} (hm : 0 < m)
    (f g : SpatialTestFunction) :
    IntegrableOn (spatialHeatMassPrimitive m f g) (Ioi 0) := by
  have hmajor := (integrableOn_laplace_rpow (show 0 < m ^ 2 by positivity)
    (show -1 < -(1 / 2 : ℝ) by norm_num)).mul_const
      (∫ p : EuclideanSpace ℝ (Fin 3), ‖conj (spatialFourier f p) * spatialFourier g p‖)
  apply hmajor.mono'
  · exact ((show Measurable (fun t : ℝ =>
      ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ)) by
      fun_prop).aestronglyMeasurable.mul
        (stronglyMeasurable_spatialHeatFourierPairing f g).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    exact spatialHeatMassPrimitive_norm_le m ht f g

theorem integrableOn_spatialHeat_weighted_derivative {m : ℝ} (hm : 0 < m)
    (f g : SpatialTestFunction) :
    IntegrableOn (fun t : ℝ =>
      ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ) *
        spatialHeatFourierDerivative f g t) (Ioi 0) := by
  have hmajor := (integrableOn_laplace_rpow (show 0 < m ^ 2 by positivity)
    (show -1 < -(1 / 2 : ℝ) by norm_num)).mul_const
      (∫ p : EuclideanSpace ℝ (Fin 3),
        (‖p‖ ^ 2 * ‖spatialFourier f p‖) * ‖spatialFourier g p‖)
  apply hmajor.mono'
  · exact ((show Measurable (fun t : ℝ =>
      ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ)) by
      fun_prop).aestronglyMeasurable.mul
        (stronglyMeasurable_spatialHeatFourierDerivative f g).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (spatialHeatFourierDerivative_norm_le ht.le f g)
      (by positivity)

theorem integrableOn_spatialHeat_three_halves {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    IntegrableOn (fun t : ℝ =>
      ((t ^ (-(3 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ) *
        spatialHeatFourierPairing f g t) (Ioi 0) := by
  have hmajor := (integrableOn_laplace_rpow (show 0 < m ^ 2 by positivity)
    (show -1 < -(1 / 2 : ℝ) by norm_num)).mul_const
      (∫ p : EuclideanSpace ℝ (Fin 3),
        (‖p‖ ^ 2 * ‖spatialFourier f p‖) * ‖spatialFourier g p‖)
  apply hmajor.mono'
  · exact ((show Measurable (fun t : ℝ =>
      ((t ^ (-(3 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ)) by
      fun_prop).aestronglyMeasurable.mul
        (stronglyMeasurable_spatialHeatFourierPairing f g).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hC := spatialHeatFourierPairing_sub_zero_norm_le ht.le f g
    rw [spatialHeatFourierPairing_zero_of_separated hd f g hsep, sub_zero] at hC
    have hpower : t ^ (-(3 / 2 : ℝ)) * t = t ^ (-(1 / 2 : ℝ)) := by
      calc
        _ = t ^ (-(3 / 2 : ℝ)) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = t ^ (-(3 / 2 : ℝ) + 1) := (Real.rpow_add ht _ _).symm
        _ = _ := by norm_num
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (t ^ (-(3 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t)) *
          (t * ∫ p : EuclideanSpace ℝ (Fin 3),
            (‖p‖ ^ 2 * ‖spatialFourier f p‖) * ‖spatialFourier g p‖) :=
        mul_le_mul_of_nonneg_left hC (by positivity)
      _ = _ := by
        calc
          _ = (t ^ (-(3 / 2 : ℝ)) * t) * Real.exp (-(m ^ 2) * t) *
              (∫ p : EuclideanSpace ℝ (Fin 3),
                (‖p‖ ^ 2 * ‖spatialFourier f p‖) * ‖spatialFourier g p‖) := by ring
          _ = _ := by rw [hpower]

end VacuumBellSeparation
