/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SchwartzKleinGordon
public import LeanPool.VacuumBellSeparation.Gaussian.SpatialLaplaceMoments

/-!
# Actual heat subordination of the reciprocal spatial energy

The Gamma integral is identified with the literal massive Schwartz
symbol in Mathlib's normalized Fourier coordinates. No exchange with a
spatial or momentum integral is assumed here.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory Set

theorem reciprocal_sqrt_laplace {a : ℝ} (ha : 0 < a) :
    (Real.sqrt a)⁻¹ = (Real.sqrt Real.pi)⁻¹ *
      ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * Real.exp (-a * t) := by
  rw [integral_laplace_rpow ha (by norm_num),
    show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
    Real.Gamma_one_half_eq, Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]

theorem integrableOn_reciprocal_energy_heat {m : ℝ} (hm : 0 < m)
    (p : EuclideanSpace ℝ (Fin 3)) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(m ^ 2 + ‖p‖ ^ 2) * t)) (Ioi 0) :=
  integrableOn_laplace_rpow (by positivity) (by norm_num)

theorem reciprocal_dispersion_heat {m : ℝ} (hm : 0 < m)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (dispersion m p)⁻¹ = (Real.sqrt Real.pi)⁻¹ *
      ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(m ^ 2 + ‖p‖ ^ 2) * t) :=
  reciprocal_sqrt_laplace (by positivity)

theorem massiveSchwartzSymbol_neg_one_heat {m : ℝ} (hm : 0 < m)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    massiveSchwartzSymbol m (-1) ξ = (Real.sqrt Real.pi)⁻¹ *
      ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(m ^ 2 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) * t) := by
  rw [massiveSchwartzSymbol_neg_one hm, reciprocal_dispersion_heat hm]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_pow]

theorem reciprocal_dispersion_heat_separated {m : ℝ} (hm : 0 < m)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (dispersion m p)⁻¹ = (Real.sqrt Real.pi)⁻¹ *
      ∫ t in Ioi (0 : ℝ), (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t)) *
        Real.exp (-t * ‖p‖ ^ 2) := by
  rw [reciprocal_dispersion_heat hm]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    rw [show -(m ^ 2 + ‖p‖ ^ 2) * t = -(m ^ 2) * t + -t * ‖p‖ ^ 2 by ring,
      Real.exp_add, mul_assoc])

end VacuumBellSeparation
