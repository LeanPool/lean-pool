/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatTimeIntegrability
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Actual heat-time integration by parts for separated tests

Both boundary limits and all terms' absolute convergence are proved in
the preceding modules. This gives the negative three-halves heat weight
needed for the momentum covariance kernel.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set Filter
open scoped ComplexConjugate Topology

/-- Spatial heat mass weight given by `((t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ)`. -/
noncomputable def spatialHeatMassWeight (m t : ℝ) : ℂ :=
  ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ)

/-- Spatial heat mass weight derivative. -/
noncomputable def spatialHeatMassWeightDerivative (m t : ℝ) : ℂ :=
  ((-(1 / 2 : ℝ) * (t ^ (-(3 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t)) -
    m ^ 2 * (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t)) : ℝ) : ℂ)

theorem hasDerivAt_spatialHeatMassWeight (m : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (spatialHeatMassWeight m) (spatialHeatMassWeightDerivative m t) t := by
  have hp := Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl ht.ne')
  have he := ((hasDerivAt_id t).const_mul (-(m ^ 2))).exp
  have h := (hp.mul he).ofReal_comp
  convert h using 1
  · rfl
  · simp only [spatialHeatMassWeightDerivative,
      show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num, id_eq]
    push_cast
    ring

theorem integrableOn_spatialHeat_weight_derivative_pairing {m d : ℝ}
    (hm : 0 < m) (hd : 0 < d) (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    IntegrableOn (fun t : ℝ => spatialHeatMassWeightDerivative m t *
      spatialHeatFourierPairing f g t) (Ioi 0) := by
  have h1 := (integrableOn_spatialHeat_three_halves hm hd f g hsep).const_mul
    (-(1 / 2 : ℂ))
  have h2 := (integrableOn_spatialHeatMassPrimitive hm f g).const_mul ((m ^ 2 : ℝ) : ℂ)
  apply (h1.sub h2).congr
  exact Eventually.of_forall fun t => by
    simp only [Pi.sub_apply, spatialHeatMassWeightDerivative, spatialHeatMassPrimitive]
    push_cast
    ring

theorem spatialHeat_weighted_derivative_integral {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    (∫ t in Ioi (0 : ℝ), spatialHeatMassWeight m t * spatialHeatFourierDerivative f g t) =
      (1 / 2 : ℂ) * (∫ t in Ioi (0 : ℝ),
        ((t ^ (-(3 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ) *
          spatialHeatFourierPairing f g t) +
      ((m ^ 2 : ℝ) : ℂ) * (∫ t in Ioi (0 : ℝ), spatialHeatMassPrimitive m f g t) := by
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := spatialHeatMassWeight m) (u' := spatialHeatMassWeightDerivative m)
    (v := spatialHeatFourierPairing f g) (v' := spatialHeatFourierDerivative f g)
    (fun t ht => hasDerivAt_spatialHeatMassWeight m ht)
    (fun t ht => hasDerivAt_spatialHeatFourier_pairing ht f g)
    (integrableOn_spatialHeat_weighted_derivative hm f g)
    (integrableOn_spatialHeat_weight_derivative_pairing hm hd f g hsep)
    (spatialHeatMassPrimitive_tendsto_zero_right m hd f g hsep)
    (spatialHeatMassPrimitive_tendsto_zero_atTop hm f g)
  have heq : (fun t : ℝ => spatialHeatMassWeightDerivative m t *
      spatialHeatFourierPairing f g t) = fun t =>
      (-(1 / 2 : ℂ)) * (((t ^ (-(3 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ) *
        spatialHeatFourierPairing f g t) -
      ((m ^ 2 : ℝ) : ℂ) * spatialHeatMassPrimitive m f g t := by
    funext t
    simp only [spatialHeatMassWeightDerivative, spatialHeatMassPrimitive]
    push_cast
    ring
  rw [heq, integral_sub
    ((integrableOn_spatialHeat_three_halves hm hd f g hsep).const_mul (-(1 / 2 : ℂ)))
    ((integrableOn_spatialHeatMassPrimitive hm f g).const_mul ((m ^ 2 : ℝ) : ℂ)),
    integral_const_mul, integral_const_mul] at h
  calc
    _ = _ := h
    _ = _ := by ring

theorem spatialHeat_time_integration_by_parts {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    (∫ t in Ioi (0 : ℝ), spatialHeatMassWeight m t *
      (((m ^ 2 : ℝ) : ℂ) * spatialHeatFourierPairing f g t -
        spatialHeatFourierDerivative f g t)) =
      (-(1 / 2 : ℂ)) * ∫ t in Ioi (0 : ℝ),
        ((t ^ (-(3 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ) *
          spatialHeatFourierPairing f g t := by
  have heq : (fun t : ℝ => spatialHeatMassWeight m t *
      (((m ^ 2 : ℝ) : ℂ) * spatialHeatFourierPairing f g t -
        spatialHeatFourierDerivative f g t)) = fun t =>
      ((m ^ 2 : ℝ) : ℂ) * spatialHeatMassPrimitive m f g t -
        spatialHeatMassWeight m t * spatialHeatFourierDerivative f g t := by
    funext t
    unfold spatialHeatMassPrimitive spatialHeatMassWeight
    ring
  have hi : IntegrableOn (fun t : ℝ =>
      spatialHeatMassWeight m t * spatialHeatFourierDerivative f g t) (Ioi 0) :=
    integrableOn_spatialHeat_weighted_derivative hm f g
  rw [heq, integral_sub
    ((integrableOn_spatialHeatMassPrimitive hm f g).const_mul ((m ^ 2 : ℝ) : ℂ))
    hi, integral_const_mul,
    spatialHeat_weighted_derivative_integral hm hd f g hsep]
  ring

end VacuumBellSeparation
