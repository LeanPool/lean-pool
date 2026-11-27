/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.DampedSpatialAnalytic
public import LeanPool.VacuumBellSeparation.FreeField.ScalarSpatialFourier
public import LeanPool.VacuumBellSeparation.FreeField.LocalAnnihilatorLaplace

/-!
# The actual damped spatial Fourier transform of a local annihilator

Scalar Fubini converts its local test pairing to the positive imaginary-time
Laplace transform. The local fundamental lemma and actual continuity then give
pointwise zero throughout the original ball.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ComplexConjugate

/-- Spatial Fourier integral with an extra exponential weight from the imaginary spatial
displacement. -/
noncomputable def dampedSpatialFourier {m : ℝ} (a : ℝ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) : EuclideanSpace ℝ (Fin 3) → ℂ :=
  scalarSpatialFourier (oneParticleMeasure m) (dampedShellAmplitude a ψ)

theorem continuous_dampedSpatialFourier {m a : ℝ} (hm : 0 < m) (ha : 0 < a)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) : Continuous (dampedSpatialFourier a ψ) :=
  continuous_scalarSpatialFourier (integrable_dampedShellAmplitude hm ha ψ)

theorem dampedSpatialSlice_ofReal {m : ℝ} (a : ℝ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) (x v : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    dampedSpatialSlice a ψ x v (t : ℂ) = dampedSpatialFourier a ψ (x + t • v) := by
  unfold dampedSpatialSlice dampedSpatialFourier scalarSpatialFourier dampedShellAmplitude
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    dsimp only
    unfold dampedSpatialKernel
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [inner_add_right, inner_smul_right]
    push_cast
    ring

theorem integral_dampedSpatialFourier_spatialTest {m a : ℝ} (hm : 0 < m) (ha : 0 < a)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) (g : SpatialTestFunction) :
    (∫ x, (g.1 x : ℂ) * dampedSpatialFourier a ψ x) =
      positiveEnergyLaplace (oneParticleMeasure m) (dispersion m)
        (spatialLaplaceAmplitude ψ g) ((a : ℂ) * Complex.I) := by
  let := oneParticleMeasure_isLocallyFinite hm
  have hg : Integrable (fun x => (g.1 x : ℂ)) :=
    (Complex.continuous_ofReal.comp g.2.1.continuous).integrable_of_hasCompactSupport
      (g.2.2.comp_left Complex.ofReal_zero)
  have h := integral_scalarSpatialFourier_pairing
    (integrable_dampedShellAmplitude hm ha ψ) hg 1
  simp only [one_smul, one_mul] at h
  change (∫ x, (g.1 x : ℂ) * scalarSpatialFourier (oneParticleMeasure m)
    (dampedShellAmplitude a ψ) x) = _
  rw [h]
  unfold positiveEnergyLaplace
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    have he : positiveEnergyPhase (dispersion m p) ((a : ℂ) * Complex.I) =
        (Real.exp (-a * dispersion m p) : ℂ) := by
      rw [positiveEnergyPhase, Complex.ofReal_exp]
      congr 1
      push_cast
      calc
        _ = (a : ℂ) * (Complex.I * Complex.I) * (dispersion m p : ℂ) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    simp only [he, spatialLaplaceAmplitude, dampedShellAmplitude, spatialFourier]
    ring

theorem dampedSpatialFourier_eq_zero_on_ball_of_local_annihilator {m R a : ℝ}
    (hm : 0 < m) (hR : 0 < R) (ha : 0 < a) (x₀ : EuclideanSpace ℝ (Fin 3))
    (ψ : Lp ℂ 2 (oneParticleMeasure m))
    (hψ : ∀ u ∈ localizedTimeZeroSources (Metric.ball x₀ R),
      ⟪ψ, timeZeroL2 hm u⟫_ℂ = 0) :
    EqOn (dampedSpatialFourier a ψ) 0 (Metric.ball x₀ R) := by
  have hc := continuous_dampedSpatialFourier hm ha ψ
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      x ∈ Metric.ball x₀ R → dampedSpatialFourier a ψ x = 0 := by
    apply Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hc.locallyIntegrable.locallyIntegrableOn _)
    intro g hg hgc hgs
    let g' : SpatialTestFunction := ⟨g, hg, hgc⟩
    change (∫ x, (g x : ℂ) * dampedSpatialFourier a ψ x) = 0
    rw [integral_dampedSpatialFourier_spatialTest hm ha ψ g']
    exact spatialLaplace_eq_zero_of_local_annihilator hm hR x₀ ψ hψ g' hgs
      ((a : ℂ) * Complex.I) (by simpa using ha)
  apply Measure.eqOn_open_of_ae_eq (μ := volume)
    ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr hae) Metric.isOpen_ball
      hc.continuousOn continuous_const.continuousOn

end VacuumBellSeparation
