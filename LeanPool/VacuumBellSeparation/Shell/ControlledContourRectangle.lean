/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ControlledContourNeighborhood

/-!
# Rectangular inverse coordinates with uniform physical control

A genuine product neighbourhood in free shell coordinates and all
retained auxiliary coordinates is mapped back into the controlled
physical parameter ball. In particular the same neighbourhood permits
variation of mass and of all three integration-fibre coordinates.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped Topology

private theorem localChart_inverse_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (e : OpenPartialHomeomorph E F) (h0 : (0 : E) ∈ e.source)
    {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ y : F, dist y (e 0) < δ → y ∈ e.target ∧ ‖e.symm y‖ < r := by
  have hcenter := e.map_source h0
  have hc : ContinuousAt e.symm (e 0) := e.continuousAt_symm hcenter
  have hi : ‖e.symm (e 0)‖ < r := by simpa only [e.left_inv h0, norm_zero] using hr
  have hall : ∀ᶠ y in 𝓝 (e 0), y ∈ e.target ∧ ‖e.symm y‖ < r := by
    filter_upwards [e.open_target.mem_nhds hcenter,
      hc.norm.eventually_lt continuousAt_const hi] with y hy hn
    exact ⟨hy, hn⟩
  exact Metric.eventually_nhds_iff.mp hall

theorem controlledContour_target_rectangle {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (m : ℝ) {B θ R : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ)
    (henergy : radialShellEnergy m B 0 < R)
    (hnorm : spacetimeEuclideanOperatorNorm Λ < R)
    (hinv : spacetimeEuclideanOperatorNorm Λ.symm < R) :
    ∃ δ > 0, ∀ w : Fin 3 → ℂ, ∀ n : ShellContourAux,
      dist w (referenceContourMap m B θ 0) < δ → ‖n‖ < δ →
      (w, n) ∈ (fullContourLocalCoordinates m hB hθ).target ∧
      let q := (fullContourLocalCoordinates m hB hθ).symm (w, n)
      q.2 = n ∧ fullContourMap m B θ q = w ∧
      0 < fullContourEnergy m B q ∧ fullContourEnergy m B q < R ∧
      spacetimeEuclideanOperatorNorm (fullContourLorentzMap Λ q) < R ∧
      spacetimeEuclideanOperatorNorm (fullContourLorentzMap Λ q).symm < R := by
  obtain ⟨r, hr, hball⟩ := controlledContour_parameter_ball hΛ m hB hθ henergy hnorm hinv
  let e := fullContourLocalCoordinates m hB hθ
  obtain ⟨δ, hδ, hδball⟩ := localChart_inverse_ball e
    (zero_mem_fullContourLocalCoordinates m hB hθ) hr
  have he0 : e 0 = (referenceContourMap m B θ 0, 0) := by
    rw [fullContourLocalCoordinates_apply]
    exact Prod.ext (fullContourMap_active_slice m B θ 0) rfl
  refine ⟨δ, hδ, fun w n hw hn => ?_⟩
  have hy : dist (w, n) (e 0) < δ := by
    rw [he0, Prod.dist_eq]
    exact max_lt hw (by simpa only [dist_zero_right] using hn)
  obtain ⟨hyt, hqn⟩ := hδball (w, n) hy
  refine ⟨hyt, ?_⟩
  let q := e.symm (w, n)
  have hq := hball q hqn
  have hright : (fullContourMap m B θ q, q.2) = (w, n) := e.right_inv hyt
  exact ⟨congrArg Prod.snd hright, congrArg Prod.fst hright,
    hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2⟩

end VacuumBellSeparation
