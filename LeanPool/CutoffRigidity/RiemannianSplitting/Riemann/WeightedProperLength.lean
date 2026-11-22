/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.UniformSpace.Cauchy

/-! # Hopf–Rinow–Cohn-Vossen: complete locally compact length spaces are proper

We only use the following weak form of the length property (`ApproxSegment`): for every pair of
points `x, y`, every `0 ≤ s ≤ dist x y` and every `η > 0` there is a point `z` with `dist x z = s`
and `dist z y ≤ dist x y - s + η`.  Under this property a complete, locally compact metric
space is proper.
-/

@[expose] public section

open Metric Set

namespace CutCur

variable {X : Type*} [MetricSpace X]

/-- The weak length property used in the Cohn-Vossen argument. -/
def ApproxSegment (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∀ s η : ℝ, 0 ≤ s → s ≤ dist x y → 0 < η →
    ∃ z, dist x z = s ∧ dist z y ≤ dist x y - s + η

/-- One-step enlargement: if `closedBall x₀ r` is compact then so is `closedBall x₀ (r+δ)`
for some `δ > 0`. -/
theorem exists_isCompact_closedBall_add [LocallyCompactSpace X] (hX : ApproxSegment X)
    {x₀ : X} {r : ℝ} (hr : 0 ≤ r) (hK : IsCompact (closedBall x₀ r)) :
    ∃ δ > 0, IsCompact (closedBall x₀ (r + δ)) := by
  obtain ⟨δ, hδ, hc⟩ := hK.exists_isCompact_cthickening
  refine ⟨δ / 2, by positivity, hc.of_isClosed_subset isClosed_closedBall ?_⟩
  intro y hy
  rw [mem_closedBall, dist_comm] at hy
  by_cases hyr : dist x₀ y ≤ r
  · exact self_subset_cthickening _ (by rwa [mem_closedBall, dist_comm])
  · push Not at hyr
    obtain ⟨z, hz1, hz2⟩ := hX x₀ y r (δ / 2) hr hyr.le (by positivity)
    refine mem_cthickening_of_dist_le y z δ _ ?_ ?_
    · rw [mem_closedBall, dist_comm, hz1]
    · rw [dist_comm]; linarith

/-- Limit step: if all smaller closed balls are compact, so is the closed ball of radius `R`. -/
theorem isCompact_closedBall_of_lt [CompleteSpace X] (hX : ApproxSegment X) {x₀ : X} {R : ℝ}
    (hR : 0 < R) (h : ∀ r, 0 ≤ r → r < R → IsCompact (closedBall x₀ r)) :
    IsCompact (closedBall x₀ R) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨?_, isClosed_closedBall.isComplete⟩
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set r := max 0 (R - ε / 2) with hr
  have hr0 : 0 ≤ r := le_max_left _ _
  have hrR : r < R := max_lt hR (by linarith)
  have hRr : R - r ≤ ε / 2 := by
    rcases le_total 0 (R - ε / 2) with h1 | h1
    · rw [hr, max_eq_right h1]; linarith
    · rw [hr, max_eq_left h1]; linarith
  obtain ⟨t, htK, htf, hcov⟩ := (h r hr0 hrR).finite_cover_balls (e := ε / 4) (by positivity)
  refine ⟨t, htf, fun y hy => ?_⟩
  rw [mem_closedBall, dist_comm] at hy
  by_cases hyr : dist x₀ y ≤ r
  · have := hcov (show y ∈ closedBall x₀ r by rw [mem_closedBall, dist_comm]; exact hyr)
    simp only [mem_iUnion] at this ⊢
    obtain ⟨c, hc, hyc⟩ := this
    exact ⟨c, hc, by simp only [mem_ball] at hyc ⊢; linarith⟩
  · push Not at hyr
    obtain ⟨z, hz1, hz2⟩ := hX x₀ y r (ε / 8) hr0 hyr.le (by positivity)
    have hzK : z ∈ closedBall x₀ r := by rw [mem_closedBall, dist_comm]; exact hz1.le
    have := hcov hzK
    simp only [mem_iUnion] at this ⊢
    obtain ⟨c, hc, hzc⟩ := this
    refine ⟨c, hc, ?_⟩
    simp only [mem_ball] at hzc ⊢
    have := dist_triangle_left y c z
    linarith [dist_comm y z]

/-- **Cohn-Vossen**: a complete locally compact metric space with the approximate segment
property is proper. -/
theorem properSpace_of_approxSegment [CompleteSpace X] [LocallyCompactSpace X]
    (hX : ApproxSegment X) : ProperSpace X := by
  refine ⟨fun x₀ r => ?_⟩
  by_contra hcon
  set S : Set ℝ := {r | 0 ≤ r ∧ IsCompact (closedBall x₀ r)} with hS
  have h0 : (0 : ℝ) ∈ S := ⟨le_rfl, by simp⟩
  have hdown : ∀ a b, 0 ≤ a → a ≤ b → b ∈ S → a ∈ S := fun a b ha hab hb =>
    ⟨ha, hb.2.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hab)⟩
  have hbdd : BddAbove S := by
    refine ⟨r, fun s hs => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hcon (hs.2.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hlt.le))
  set R := sSup S with hR
  have h0R : 0 ≤ R := le_csSup hbdd h0
  have hRS : R ∈ S := by
    rcases h0R.eq_or_lt with h | h
    · rw [← h]; exact h0
    · refine ⟨h0R, isCompact_closedBall_of_lt hX h (fun a ha haR => ?_)⟩
      obtain ⟨b, hb, hab⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ haR
      exact (hdown a b ha hab.le hb).2
  obtain ⟨δ, hδ, hc⟩ := exists_isCompact_closedBall_add hX hRS.1 hRS.2
  have : R + δ ∈ S := ⟨by linarith, hc⟩
  have := le_csSup hbdd this
  linarith

end CutCur
