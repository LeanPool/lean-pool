/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpacetimeSlices
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Joint continuity of the actual partial spatial Fourier transform

The common compact spatial support comes from the original spacetime source.
The parametric integral theorem is applied to the literal Fourier integrand.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped InnerProductSpace

/-- Spacetime partial Fourier obtained from `spatialFourier`. -/
noncomputable def spacetimePartialFourier (F : RealTestFunction) (t : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  spatialFourier (spacetimeSpatialSlice F t) p

theorem continuous_spacetimePartialFourier (F : RealTestFunction) :
    Continuous (fun z : ℝ × EuclideanSpace ℝ (Fin 3) => spacetimePartialFourier F z.1 z.2) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support (F.2.2.image continuous_snd)
  · exact (by
      change ContinuousOn (fun z : (ℝ × EuclideanSpace ℝ (Fin 3)) ×
          EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (⟪z.1.2, z.2⟫_ℝ : ℂ))) * (F.1 (z.1.1, z.2) : ℂ)) _
      have hF := F.2.1.continuous
      fun_prop)
  · intro z x _ hx
    have hz : F.1 (z.1, x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hx ⟨(z.1, x), h, rfl⟩
    change _ * (F.1 (z.1, x) : ℂ) = 0
    rw [hz, Complex.ofReal_zero, mul_zero]

theorem spacetimePartialFourier_eq_zero_of_slice_zero (F : RealTestFunction)
    {t : ℝ} (ht : spacetimeSpatialSlice F t = 0)
    (p : EuclideanSpace ℝ (Fin 3)) : spacetimePartialFourier F t p = 0 := by
  change spatialFourier (spacetimeSpatialSlice F t) p = 0
  rw [ht]
  change (∫ x : EuclideanSpace ℝ (Fin 3),
    Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ))) * (0 : ℂ)) = 0
  simp

/-- The literal mass-shell phase applied to the actual slice Fourier transform. -/
noncomputable def spacetimeEvolvedFourier (m : ℝ) (F : RealTestFunction) (t : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (Complex.I * ((t * dispersion m p : ℝ) : ℂ)) * spacetimePartialFourier F t p

theorem continuous_spacetimeEvolvedFourier (m : ℝ) (F : RealTestFunction) :
    Continuous (fun z : ℝ × EuclideanSpace ℝ (Fin 3) => spacetimeEvolvedFourier m F z.1 z.2) := by
  unfold spacetimeEvolvedFourier
  exact (Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_fst.mul
      ((continuous_dispersion m).comp continuous_snd))))).mul
    (continuous_spacetimePartialFourier F)

@[simp] theorem norm_spacetimeEvolvedFourier (m : ℝ) (F : RealTestFunction) (t : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖spacetimeEvolvedFourier m F t p‖ = ‖spacetimePartialFourier F t p‖ := by
  rw [spacetimeEvolvedFourier, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

end VacuumBellSeparation
