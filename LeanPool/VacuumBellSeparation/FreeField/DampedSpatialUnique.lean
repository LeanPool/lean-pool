/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.DampedSpatialFourier

/-!
# Spatial continuation of an actual damped local annihilator

Restricting each genuinely holomorphic affine slice to the real line gives
real analyticity on all ℝ. Its zero interval propagates by the ordinary
analytic identity theorem. This proves global vanishing of the actual
Fourier integral, without an assumed elliptic unique-continuation result.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

theorem dampedSpatialFourier_eq_zero_of_zero_on_ball {m a R : ℝ}
    (hm : 0 < m) (ha : 0 < a) (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3))
    (ψ : Lp ℂ 2 (oneParticleMeasure m))
    (hzero : EqOn (dampedSpatialFourier a ψ) 0 (Metric.ball x₀ R)) :
    dampedSpatialFourier a ψ = 0 := by
  funext y
  let v := y - x₀
  have hc : Continuous (fun t : ℝ => x₀ + t • v) := by fun_prop
  have hlocal : (fun t : ℝ => dampedSpatialSlice a ψ x₀ v (t : ℂ)) =ᶠ[𝓝 0] 0 := by
    have hmem : (0 : ℝ) ∈ (fun t : ℝ => x₀ + t • v) ⁻¹' Metric.ball x₀ R := by
      simpa using (Metric.mem_ball_self (x := x₀) hR)
    filter_upwards [((Metric.isOpen_ball (x := x₀) (ε := R)).preimage hc).mem_nhds hmem] with t ht
    rw [dampedSpatialSlice_ofReal]
    exact hzero ht
  have hall := (analyticOnNhd_real_dampedSpatialSlice hm ha x₀ v ψ).eq_of_eventuallyEq
    (analyticOnNhd_const (𝕜 := ℝ) (v := (0 : ℂ))) hlocal
  have h := congrFun hall 1
  have hv : x₀ + (1 : ℝ) • v = y := by simp [v]
  simpa only [dampedSpatialSlice_ofReal, hv, Pi.zero_apply] using h

theorem dampedSpatialFourier_eq_zero_of_local_annihilator {m a R : ℝ}
    (hm : 0 < m) (ha : 0 < a) (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3))
    (ψ : Lp ℂ 2 (oneParticleMeasure m))
    (hψ : ∀ u ∈ localizedTimeZeroSources (Metric.ball x₀ R),
      ⟪ψ, timeZeroL2 hm u⟫_ℂ = 0) : dampedSpatialFourier a ψ = 0 := by
  exact dampedSpatialFourier_eq_zero_of_zero_on_ball hm ha hR x₀ ψ
    (dampedSpatialFourier_eq_zero_on_ball_of_local_annihilator hm hR ha x₀ ψ hψ)

end VacuumBellSeparation
