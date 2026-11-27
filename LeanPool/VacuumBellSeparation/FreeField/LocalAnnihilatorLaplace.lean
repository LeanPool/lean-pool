/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PositiveEnergySpatialAmplitude
public import LeanPool.VacuumBellSeparation.FreeField.SourceSpace

/-!
# Local complex annihilators vanish on all positive-energy Laplace slices

Finite propagation supplies an actual open time interval on which each evolved
compact spatial test remains in the original ball. Orthogonality therefore gives
literal zero boundary values. Actual mass-shell integrability and the proved
upper-half-plane uniqueness theorem give vanishing at every positive imaginary
time. This is a step toward density, not an assumed density theorem.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped InnerProductSpace

theorem evolvedSpatialSource_mem_ball_of_support_margin {m r R : ℝ}
    (hm : 0 < m) (hr : 0 ≤ r) (x₀ : EuclideanSpace ℝ (Fin 3))
    (g : SpatialTestFunction) (hg : tsupport g.1 ⊆ Metric.closedBall x₀ r)
    {t : ℝ} (ht : r + |t| < R) :
    evolvedSpatialSource hm t g ∈ localizedTimeZeroSources (Metric.ball x₀ R) := by
  apply localizedTimeZeroSources_mono (Metric.closedBall_subset_ball ht)
  constructor
  · exact tsupport_spatialCauchyTest_subset hm hr t x₀ g 0 hg (by
      change tsupport (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ⊆ _
      simp)
  · exact tsupport_spatialCauchyTest_subset hm hr t x₀ 0 g (by
      change tsupport (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ⊆ _
      simp) hg

theorem spatialLaplace_eq_zero_of_local_annihilator {m R : ℝ}
    (hm : 0 < m) (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3))
    (ψ : Lp ℂ 2 (oneParticleMeasure m))
    (hψ : ∀ u ∈ localizedTimeZeroSources (Metric.ball x₀ R),
      ⟪ψ, timeZeroL2 hm u⟫_ℂ = 0)
    (g : SpatialTestFunction) (hg : tsupport g.1 ⊆ Metric.ball x₀ R) :
    ∀ z : ℂ, 0 < z.im →
      positiveEnergyLaplace (oneParticleMeasure m) (dispersion m)
        (spatialLaplaceAmplitude ψ g) z = 0 := by
  obtain ⟨r, hr, hgr⟩ := exists_pos_lt_subset_ball hR (isClosed_tsupport _) hg
  have hδ : 0 < R - r := sub_pos.mpr hr.2
  apply positiveEnergyLaplace_eq_zero_of_boundary_interval
    (continuous_dispersion m).aestronglyMeasurable
    (fun p => hm.le.trans (le_dispersion hm.le p))
    (integrable_spatialLaplaceAmplitude hm ψ g)
    (integrable_spatialLaplaceAmplitude_energy hm ψ g)
    (a := -(R - r)) (b := R - r) (by linarith)
  intro t ht
  rw [spatialLaplace_eq_inner_evolvedSpatialSource hm]
  apply hψ
  apply evolvedSpatialSource_mem_ball_of_support_margin hm hr.1.le x₀ g
    (hgr.trans Metric.ball_subset_closedBall)
  have ht' : |t| < R - r := abs_lt.mpr ht
  linarith

end VacuumBellSeparation
