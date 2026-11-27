/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CauchyFinitePropagation
public import LeanPool.VacuumBellSeparation.FreeField.EvolutionPointwiseDerivative

/-! # Cone support of the actual Cauchy velocity -/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology

theorem massiveSchwartzCauchyVelocity_eq_zero_outside_cone {m : ℝ} (hm : 0 < m)
    {x₀ x : EuclideanSpace ℝ (Fin 3)} {R : ℝ} (hR : 0 ≤ R) (t : ℝ)
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ R)
    (hg : tsupport g ⊆ Metric.closedBall x₀ R)
    (hx : R + |t| < ‖x - x₀‖) : massiveSchwartzCauchyVelocity m t f g x = 0 := by
  have hn : ∀ᶠ s in 𝓝 t, R + |s| < ‖x - x₀‖ :=
    (continuous_const.add continuous_abs).continuousAt.eventually_lt_const hx
  have heq : (fun s => massiveSchwartzCauchy m s f g x) =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [hn] with s hs
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hball := tsupport_massiveSchwartzCauchy_subset hm hR s f g hf hg hmem
    have hnorm : ‖x - x₀‖ ≤ R + |s| := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hball
    exact (not_lt_of_ge hnorm) hs
  have hz : deriv (fun s => massiveSchwartzCauchy m s f g x) t = 0 := by
    rw [heq.deriv_eq]
    exact deriv_const _ _
  rw [(hasDerivAt_massiveSchwartzCauchy_pointwise m t f g x).deriv] at hz
  exact hz

theorem tsupport_massiveSchwartzCauchyVelocity_subset {m : ℝ} (hm : 0 < m)
    {x₀ : EuclideanSpace ℝ (Fin 3)} {R : ℝ} (hR : 0 ≤ R) (t : ℝ)
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ R)
    (hg : tsupport g ⊆ Metric.closedBall x₀ R) :
    tsupport (massiveSchwartzCauchyVelocity m t f g) ⊆ Metric.closedBall x₀ (R + |t|) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hout
  have hn : R + |t| < ‖x - x₀‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hout
  exact hx (massiveSchwartzCauchyVelocity_eq_zero_outside_cone hm hR t f g hf hg hn)

end VacuumBellSeparation
