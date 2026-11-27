/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeSliceSource
public import LeanPool.VacuumBellSeparation.FreeField.OneParticle

/-!
# The actual one-particle integral in time and spatial Fourier variables

Fubini is justified by the existing compact-support integrability theorem for
the literal one-particle integrand. For genuine Schwartz spatial slices the
spatial integral is exactly the normalized Fourier transform at ξ, with
physical momentum 2πξ. No time-slice source identity is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter FourierTransform
open scoped FourierTransform

theorem oneParticle_eq_time_fourier {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (S : ℝ → SpatialSchwartz) (hS : ∀ t x, S t x = (F.1 (t, x) : ℂ))
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m F ((2 * Real.pi) • ξ) =
      ∫ t, massiveEvolutionPhase m t ξ * (𝓕 (S t)) ξ := by
  rw [oneParticle_eq_integral]
  change (∫ x : ℝ × EuclideanSpace ℝ (Fin 3),
    oneParticleIntegrand m F ((2 * Real.pi) • ξ) x ∂volume.prod volume) = _
  rw [integral_prod _ (integrable_oneParticleIntegrand m F ((2 * Real.pi) • ξ))]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change (∫ y : EuclideanSpace ℝ (Fin 3),
      oneParticleIntegrand m F ((2 * Real.pi) • ξ) (t, y)) =
        massiveEvolutionPhase m t ξ *
          (𝓕 (S t : EuclideanSpace ℝ (Fin 3) → ℂ)) ξ
    rw [Real.fourier_eq, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [hS]
      simp only [oneParticleIntegrand, massiveEvolutionPhase, massiveSchwartzSymbol_one hm,
        Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, real_inner_smul_left]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      rw [real_inner_comm ξ x]
      ring

/-- Time slice Schwartz source. -/
noncomputable def timeSliceSchwartzSource (ε m t : ℝ) (f g : SpatialSchwartz) : SpatialSchwartz :=
  ((deriv (deriv (timeSliceCutoff ε)) t : ℝ) : ℂ) • massiveSchwartzCauchy m t f g +
    (2 * ((deriv (timeSliceCutoff ε) t : ℝ) : ℂ)) • massiveSchwartzCauchyVelocity m t f g

@[simp] theorem timeSliceSchwartzSource_apply (ε m t : ℝ) (f g : SpatialSchwartz)
    (x : EuclideanSpace ℝ (Fin 3)) :
    timeSliceSchwartzSource ε m t f g x = timeSliceComplexSource ε m f g (t, x) := rfl

theorem oneParticle_timeSliceTestFunction_eq_time_fourier {m ε r : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hr : 0 ≤ r) (x₀ : EuclideanSpace ℝ (Fin 3))
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ r)
    (hg : tsupport g ⊆ Metric.closedBall x₀ r)
    (hfr : spatialSchwartzConjugate f = f) (hgr : spatialSchwartzConjugate g = g)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (timeSliceTestFunction hm hε hr x₀ f g hf hg) ((2 * Real.pi) • ξ) =
      ∫ t, massiveEvolutionPhase m t ξ * (𝓕 (timeSliceSchwartzSource ε m t f g)) ξ := by
  apply oneParticle_eq_time_fourier hm _ (fun t => timeSliceSchwartzSource ε m t f g)
  intro t x
  exact (timeSliceTestFunction_complex_eq hm hε hr x₀ f g hf hg hfr hgr (t, x)).symm

end VacuumBellSeparation
