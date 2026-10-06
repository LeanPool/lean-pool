/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.Analysis.SpecificLimits.Basic

public section

open Filter Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The geometric time sequence in `lem:bu-iterate` eventually passes every
time strictly below one. -/
theorem bu_iteration_time_coverage {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {t : ℝ} (ht : t < 1) :
    ∃ k : ℕ, t < 1 - (1 - γ) ^ k := by
  let q : ℝ := 1 - γ
  have hq0 : 0 ≤ q := by dsimp [q]; linarith only [hγ1]
  have hq1 : q < 1 := by dsimp [q]; linarith only [hγ0]
  have hpow : Tendsto (fun k : ℕ => q ^ k) atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have htimes : Tendsto (fun k : ℕ => 1 - q ^ k) atTop (nhds (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hpow
  have hev : ∀ᶠ k : ℕ in atTop, t < 1 - q ^ k :=
    htimes.eventually (Ioi_mem_nhds ht)
  obtain ⟨k, hk⟩ := eventually_atTop.1 hev
  exact ⟨k, by simpa only [q] using hk k le_rfl⟩

/-- A pointwise half-space conclusion on `Q⁺` implies the corresponding
space-time carrier statement (`thm:bu`). -/
theorem bu_backwardUniqueness_from_halfSpaceConclusion
    {w : ParabolicPoint → Vec3}
    (hzero : ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
      0 < t → t < 1 → w (x, t) = 0) :
    ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1), w z = 0 := by
  intro z hz
  rcases z with ⟨x, t⟩
  change x ∈ {x : Vec3 | 0 < x 2} ∧ t ∈ Ioo 0 1 at hz
  rcases hz with ⟨hx, ⟨ht0, ht1⟩⟩
  exact hzero x hx t ht0 ht1

end ESS
