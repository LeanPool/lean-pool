/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffAdmissibleL2

/-!
# Derivatives on the Gaussian cutoff plateau

The spatial factor is constant on the inner ball, and both time factors
are constant away from their transition intervals.
-/

public section


open Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

/-- The first spatial derivative of the ball cutoff vanishes on its
inner plateau. -/
theorem ucSpatialCutoff_spatialPartial_zero_on_inner
    {ρ : ℝ} (hρ : 0 < ρ) {x : Vec3}
    (hx : x ∈ vec3Ball 0 (ρ / 2)) (j : Fin 3) (s : ℝ) :
    spatialPartial
      (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j (x, s) = 0 := by
  have heq : (ucSpatialCutoff ρ hρ) =ᶠ[𝓝 x] (fun _ : Vec3 => (1 : ℝ)) :=
    by
      filter_upwards [((isOpen_vec3Ball 0 (ρ / 2)).mem_nhds hx)] with y hy
      exact ucSpatialCutoff_eq_one hρ hy
  change (fderiv ℝ (ucSpatialCutoff ρ hρ) x) (basisVec j) = 0
  rw [heq.fderiv_eq]
  simp

/-- The second spatial derivative of the ball cutoff vanishes on its
inner plateau. -/
theorem ucSpatialCutoff_spatialSecondPartial_zero_on_inner
    {ρ : ℝ} (hρ : 0 < ρ) {x : Vec3}
    (hx : x ∈ vec3Ball 0 (ρ / 2)) (j k : Fin 3) (s : ℝ) :
    spatialSecondPartial
      (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j k (x, s) = 0 := by
  have heq :
      (fun y : Vec3 => spatialPartial
        (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j (y, s))
        =ᶠ[𝓝 x] (fun _ : Vec3 => (0 : ℝ)) := by
    filter_upwards [((isOpen_vec3Ball 0 (ρ / 2)).mem_nhds hx)] with y hy
    exact ucSpatialCutoff_spatialPartial_zero_on_inner hρ hy j s
  change (fderiv ℝ (fun y : Vec3 => spatialPartial
    (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j (y, s)) x)
      (basisVec k) = 0
  rw [heq.fderiv_eq]
  simp

/-- The Gaussian cutoff has no first spatial derivative on the inner ball. -/
theorem ucGaussianCutoff_spatialPartial_zero_on_inner
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    {z : ParabolicPoint} (hz : z ∈ ucInnerRegion ρ) (j : Fin 3) :
    spatialPartial (ucGaussianCutoff ρ hρ ε) j z = 0 := by
  rw [ucGaussianCutoff_spatialPartial hρ ε z j]
  have h := ucSpatialCutoff_spatialPartial_zero_on_inner hρ hz.1 j z.2
  rw [show spatialPartial
    (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j z = 0 by
      rcases z with ⟨x, s⟩
      exact h]
  simp

/-- The Gaussian cutoff has no second spatial derivative on the inner ball. -/
theorem ucGaussianCutoff_spatialSecondPartial_zero_on_inner
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    {z : ParabolicPoint} (hz : z ∈ ucInnerRegion ρ) (j k : Fin 3) :
    spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j k z = 0 := by
  rw [ucGaussianCutoff_spatialSecondPartial hρ ε z j k]
  have h := ucSpatialCutoff_spatialSecondPartial_zero_on_inner hρ hz.1 j k z.2
  rw [show spatialSecondPartial
    (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j k z = 0 by
      rcases z with ⟨x, s⟩
      exact h]
  simp

/-- The final-time factor has zero derivative before its transition. -/
theorem ucFinalTimeCutoff_deriv_zero {s : ℝ} (hs : s < 3 / 2) :
    deriv ucFinalTimeCutoff s = 0 := by
  have heq : ucFinalTimeCutoff =ᶠ[𝓝 s] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hs] with t ht
    exact ucFinalTimeCutoff_eq_one ht.le
  rw [heq.deriv_eq]
  simp

/-- The initial-time factor has zero derivative after its transition. -/
theorem ucInitialTimeCutoff_deriv_zero
    {ε s : ℝ} (hε : 0 < ε) (hs : 2 * ε < s) :
    deriv (ucInitialTimeCutoff ε) s = 0 := by
  have heq : ucInitialTimeCutoff ε =ᶠ[𝓝 s] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact ucInitialTimeCutoff_eq_one hε ht.le
  rw [heq.deriv_eq]
  simp

/-- Away from the initial transition, the Gaussian cutoff has zero time
    derivative on the inner region. -/
theorem ucGaussianCutoff_timePartial_zero_on_inner_late
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {z : ParabolicPoint} (hz : z ∈ ucInnerRegion ρ)
    (hlate : 2 * ε < z.2) :
    timePartial (ucGaussianCutoff ρ hρ ε) z = 0 := by
  rw [ucGaussianCutoff_timePartial hρ ε z,
    ucGaussianTimeCutoff_deriv,
    ucFinalTimeCutoff_deriv_zero hz.2.2,
    ucInitialTimeCutoff_deriv_zero hε hlate]
  ring

end ESS
