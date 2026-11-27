/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialMassShellBound
public import LeanPool.VacuumBellSeparation.FreeField.CauchySpatialTest
public import LeanPool.VacuumBellSeparation.FreeField.UpperHalfPlaneUniqueness

/-!
# Physical scalar Laplace amplitudes

The amplitude is the literal product of an arbitrary physical mass-shell L²
vector with the Fourier transform of an actual compact real spatial test.
Its first energy moment is integrable because the momentum-smearing time-zero
source is itself a physical L² vector. No extra regularity of ψ is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter FourierTransform
open scoped ComplexConjugate InnerProductSpace FourierTransform

/-- Spatial Laplace amplitude given by `conj (ψ p) * spatialFourier g p`. -/
noncomputable def spatialLaplaceAmplitude {m : ℝ}
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) (g : SpatialTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  conj (ψ p) * spatialFourier g p

theorem integrable_spatialLaplaceAmplitude {m : ℝ} (hm : 0 < m)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) (g : SpatialTestFunction) :
    Integrable (spatialLaplaceAmplitude ψ g) (oneParticleMeasure m) := by
  exact (Lp.memLp ψ).star.integrable_mul (memLp_spatialFourier_massShell hm g)

theorem integrable_spatialLaplaceAmplitude_energy {m : ℝ} (hm : 0 < m)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) (g : SpatialTestFunction) :
    Integrable (fun p => dispersion m p * ‖spatialLaplaceAmplitude ψ g p‖)
      (oneParticleMeasure m) := by
  have hi : Integrable
      (fun p => conj (ψ p) * timeZeroOneParticle m (0, g) p) (oneParticleMeasure m) := by
    apply (L2.integrable_inner (𝕜 := ℂ) ψ (timeZeroL2 hm (0, g))).congr
    filter_upwards [coeFn_timeZeroL2 hm (0, g)] with p hp
    rw [hp, RCLike.inner_apply']
  apply hi.norm.congr
  exact Eventually.of_forall fun p => by
    simp only [spatialLaplaceAmplitude, timeZeroOneParticle]
    have hz : spatialFourier (0 : SpatialTestFunction) p = 0 := by
      change (∫ x : EuclideanSpace ℝ (Fin 3),
        Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ))) * (0 : ℂ)) = 0
      simp
    rw [hz, zero_add]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hm.le.trans (le_dispersion hm.le p))]
    ring

theorem timeZeroOneParticle_evolvedSpatialSource_physical {m : ℝ} (hm : 0 < m)
    (t : ℝ) (g : SpatialTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    timeZeroOneParticle m (evolvedSpatialSource hm t g) p =
      positiveEnergyPhase (dispersion m p) (t : ℂ) * spatialFourier g p := by
  let ξ : EuclideanSpace ℝ (Fin 3) := (2 * Real.pi)⁻¹ • p
  have hξ : (2 * Real.pi) • ξ = p := by
    simp only [ξ, smul_smul, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]
  have hphase : massiveEvolutionPhase m t ξ = positiveEnergyPhase (dispersion m p) (t : ℂ) := by
    rw [massiveEvolutionPhase, massiveSchwartzSymbol_one hm, hξ, positiveEnergyPhase]
    congr 1
    push_cast
    ring
  have hfourier : (𝓕 (spatialSchwartz g)) ξ = spatialFourier g p := by
    rw [← spatialFourier_two_pi, hξ]
  simpa only [hξ, hphase, hfourier] using timeZeroOneParticle_evolvedSpatialSource hm t g ξ

theorem spatialLaplace_eq_inner_evolvedSpatialSource {m : ℝ} (hm : 0 < m)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) (g : SpatialTestFunction) (t : ℝ) :
    positiveEnergyLaplace (oneParticleMeasure m) (dispersion m)
      (spatialLaplaceAmplitude ψ g) (t : ℂ) =
      ⟪ψ, timeZeroL2 hm (evolvedSpatialSource hm t g)⟫_ℂ := by
  rw [L2.inner_def]
  unfold positiveEnergyLaplace spatialLaplaceAmplitude
  apply integral_congr_ae
  filter_upwards [coeFn_timeZeroL2 hm (evolvedSpatialSource hm t g)] with p hp
  rw [hp, RCLike.inner_apply', timeZeroOneParticle_evolvedSpatialSource_physical]
  ring

end VacuumBellSeparation
