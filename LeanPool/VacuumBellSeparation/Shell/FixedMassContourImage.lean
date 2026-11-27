/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.FixedMassContourJacobian

/-!
# Uniform fixed-mass rectangles in actual contour images

A single open rectangle works for all sufficiently nearby masses. Its
preimages lie in any prescribed small physical parameter ball and in
the genuine inverse-function source.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped Topology

/-- Set of points satisfying the fixed mass contour small domain condition. -/
noncomputable def fixedMassContourSmallDomain (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) (r τ : ℝ) : Set ShellPhysicalParameters :=
  {q | fixedMassContourEmbedding τ q ∈ (fullContourLocalCoordinates m hB hθ).source ∧
    ‖fixedMassContourEmbedding τ q‖ < r}

theorem continuous_fixedMassContourEmbedding (τ : ℝ) :
    Continuous (fixedMassContourEmbedding τ) := by
  exact continuous_fst.prodMk (continuous_const.prodMk continuous_snd)

theorem isOpen_fixedMassContourSmallDomain (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) (r τ : ℝ) :
    IsOpen (fixedMassContourSmallDomain m hB hθ r τ) :=
  ((fullContourLocalCoordinates m hB hθ).open_source.preimage
    (continuous_fixedMassContourEmbedding τ)).inter
      (isOpen_lt (continuous_fixedMassContourEmbedding τ).norm continuous_const)

theorem fixedMassContour_smallDomain_rectangle (m : ℝ) {B θ r : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) (hr : 0 < r) :
    ∃ δ > 0, ∀ τ : ℝ, |τ| < δ →
      (Metric.ball (referenceContourMap m B θ 0) δ ×ˢ
        Metric.ball (0 : Fin 3 → ℝ) δ) ⊆
      fixedMassContourMap m B θ τ '' fixedMassContourSmallDomain m hB hθ r τ := by
  let e := fullContourLocalCoordinates m hB hθ
  have h0 : (0 : ShellContourParameters) ∈ e.source := zero_mem_fullContourLocalCoordinates m hB hθ
  have he0 : e 0 = (referenceContourMap m B θ 0, 0) := by
    rw [fullContourLocalCoordinates_apply]
    exact Prod.ext (fullContourMap_active_slice m B θ 0) rfl
  have hc := (e.continuousAt_symm (e.map_source h0)).norm
  have hn : ‖e.symm (e 0)‖ < r := by simpa only [e.left_inv h0, norm_zero] using hr
  have hall : ∀ᶠ y in 𝓝 (e 0), y ∈ e.target ∧ ‖e.symm y‖ < r := by
    filter_upwards [e.open_target.mem_nhds (e.map_source h0),
      hc.eventually_lt continuousAt_const hn] with y hy hyr
    exact ⟨hy, hyr⟩
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨δ, hδ, fun τ hτ => ?_⟩
  rintro ⟨w, n⟩ ⟨hw, hn⟩
  have hy : dist (w, (τ, n)) (e 0) < δ := by
    rw [he0]
    change max (dist w (referenceContourMap m B θ 0))
      (max (dist τ (0 : ℝ)) (dist n (0 : Fin 3 → ℝ))) < δ
    exact max_lt hw (max_lt (by simpa only [dist_zero_right, Real.norm_eq_abs] using hτ) hn)
  obtain ⟨hyt, hqr⟩ := hδball hy
  let q := e.symm (w, (τ, n))
  have hright : (fullContourMap m B θ q, q.2) = (w, (τ, n)) := e.right_inv hyt
  have haux : q.2 = (τ, n) := congrArg Prod.snd hright
  let x : ShellPhysicalParameters := (q.1, q.2.2)
  have hx : fixedMassContourEmbedding τ x = q := by
    apply Prod.ext
    · rfl
    · exact Prod.ext (congrArg Prod.fst haux).symm rfl
  refine ⟨x, ?_, ?_⟩
  · change fixedMassContourEmbedding τ x ∈ e.source ∧ ‖fixedMassContourEmbedding τ x‖ < r
    rw [hx]
    exact ⟨e.map_target hyt, hqr⟩
  · apply Prod.ext
    · change fullContourMap m B θ (fixedMassContourEmbedding τ x) = w
      rw [hx]
      exact congrArg Prod.fst hright
    · change q.2.2 = n
      exact congrArg (fun y : ShellContourAux => y.2) haux

end VacuumBellSeparation
