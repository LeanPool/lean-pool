/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpacetimeSlicePairingIntegrability
public import LeanPool.VacuumBellSeparation.FreeField.EvolvedSpacetimeSlices

/-!
# Exact scalar pairing identity for the forward time-slice direction

The original one-particle integral equals the time integral of the actual
evolved spatial slices. Absolute integrability was proved on the full
product measure, so scalar Fubini applies to every physical L² test vector.
Both the complex identity and its real-Hilbert-space form are recorded.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter FourierTransform
open scoped ComplexConjugate FourierTransform InnerProductSpace

theorem oneParticle_eq_integral_spacetimeEvolvedFourier (m : ℝ)
    (F : RealTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m F p = ∫ t, spacetimeEvolvedFourier m F t p := by
  rw [oneParticle_eq_integral]
  change (∫ x : ℝ × EuclideanSpace ℝ (Fin 3),
    oneParticleIntegrand m F p x ∂volume.prod volume) = _
  rw [integral_prod _ (integrable_oneParticleIntegrand m F p)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    unfold spacetimeEvolvedFourier spacetimePartialFourier spatialFourier
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [oneParticleIntegrand, spacetimeSpatialSlice_apply]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem timeZeroOneParticle_evolvedSpacetimeSlice {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    timeZeroOneParticle m (evolvedSpatialSource hm t (spacetimeSpatialSlice F t)) p =
      spacetimeEvolvedFourier m F t p := by
  let ξ : EuclideanSpace ℝ (Fin 3) := (2 * Real.pi)⁻¹ • p
  have hξ : (2 * Real.pi) • ξ = p := by
    simp only [ξ, smul_smul, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]
  have hphase : massiveEvolutionPhase m t ξ =
      Complex.exp (Complex.I * ((t * dispersion m p : ℝ) : ℂ)) := by
    rw [massiveEvolutionPhase, massiveSchwartzSymbol_one hm, hξ]
    congr 1
    exact mul_comm _ _
  have hfourier : (𝓕 (spatialSchwartz (spacetimeSpatialSlice F t))) ξ =
      spacetimePartialFourier F t p := by
    rw [← spatialFourier_two_pi, hξ]
    rfl
  simpa only [hξ, hphase, hfourier, spacetimeEvolvedFourier] using
    timeZeroOneParticle_evolvedSpatialSource hm t (spacetimeSpatialSlice F t) ξ

theorem inner_timeZeroL2_evolvedSpacetimeSlice {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (t : ℝ) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    ⟪ψ, timeZeroL2 hm (evolvedSpatialSource hm t (spacetimeSpatialSlice F t))⟫_ℂ =
      ∫ p, conj (ψ p) * spacetimeEvolvedFourier m F t p ∂oneParticleMeasure m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_timeZeroL2 hm (evolvedSpatialSource hm t (spacetimeSpatialSlice F t))]
    with p hp
  rw [hp, RCLike.inner_apply', timeZeroOneParticle_evolvedSpacetimeSlice]

theorem integrable_inner_evolvedSpacetimeSlice {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    Integrable (fun t =>
      ⟪ψ, timeZeroL2 hm (evolvedSpatialSource hm t (spacetimeSpatialSlice F t))⟫_ℂ) := by
  let := oneParticleMeasure_isLocallyFinite hm
  simpa only [inner_timeZeroL2_evolvedSpacetimeSlice] using
    (integrable_spacetimeSlicePairing hm F ψ).integral_prod_left

/-- Exact scalar Fubini identity against every vector in the physical
one-particle Hilbert space. -/
theorem inner_oneParticleL2_eq_integral_timeZeroL2 {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    ⟪ψ, oneParticleL2 hm F⟫_ℂ = ∫ t,
      ⟪ψ, timeZeroL2 hm (evolvedSpatialSource hm t (spacetimeSpatialSlice F t))⟫_ℂ := by
  let := oneParticleMeasure_isLocallyFinite hm
  rw [L2.inner_def]
  calc
    (∫ p, ⟪ψ p, oneParticleL2 hm F p⟫_ℂ ∂oneParticleMeasure m) =
        ∫ p, conj (ψ p) * oneParticle m F p ∂oneParticleMeasure m := by
      apply integral_congr_ae
      filter_upwards [coeFn_oneParticleL2 hm F] with p hp
      rw [hp, RCLike.inner_apply']
    _ = ∫ p, (∫ t, conj (ψ p) * spacetimeEvolvedFourier m F t p)
        ∂oneParticleMeasure m := by
      simp only [oneParticle_eq_integral_spacetimeEvolvedFourier, integral_const_mul]
    _ = ∫ t, ∫ p, conj (ψ p) * spacetimeEvolvedFourier m F t p
        ∂oneParticleMeasure m :=
      (integral_integral_swap (integrable_spacetimeSlicePairing hm F ψ)).symm
    _ = _ := by simp only [inner_timeZeroL2_evolvedSpacetimeSlice]

/-- The real part is essential for local source closure. This is a real
orthogonality statement, with no assumption of complex-local density. -/
theorem real_inner_oneParticleL2_eq_integral_timeZeroL2 {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    ⟪ψ, oneParticleL2 hm F⟫_ℝ = ∫ t,
      ⟪ψ, timeZeroL2 hm (evolvedSpatialSource hm t (spacetimeSpatialSlice F t))⟫_ℝ := by
  have hr (u v : Lp ℂ 2 (oneParticleMeasure m)) :
      ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re := by
    rw [L2.inner_def, L2.inner_def]
    calc
      _ = ∫ p, RCLike.re (⟪u p, v p⟫_ℂ) ∂oneParticleMeasure m := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by
          simp only [Complex.inner, RCLike.inner_apply]
          rfl
      _ = _ := integral_re (L2.integrable_inner (𝕜 := ℂ) u v)
  simp only [hr]
  rw [inner_oneParticleL2_eq_integral_timeZeroL2]
  exact (integral_re (integrable_inner_evolvedSpacetimeSlice hm F ψ)).symm

end VacuumBellSeparation
