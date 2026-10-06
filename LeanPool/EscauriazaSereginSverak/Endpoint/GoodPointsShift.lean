/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsDefinition
public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Regularity at shifted cylinder centers

This file records the interior-neighborhood consequence of a Hölder
representative on the shifted cylinder from `lem:regular-point-shift`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A Hölder representative on a shifted half-cylinder makes its interior
center a CKN regular point. -/
theorem isRegularPoint_of_holder_on_shifted_cylinder
    (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
    (x₀ : Vec3) (t₀ R γ : ℝ) (hR : 0 < R)
    (w : ParabolicPoint → Vec3)
    (hAE : w =ᵐ[volume.restrict
      (goodPointPastCylinder x₀ (t₀ + R ^ 2 / 8) (R / 2))] u)
    (hγ : 0 < γ) (hγle : γ ≤ 1)
    (hHolder : ParabolicHolderVecOn
      (closure (parabolicCylinder x₀ (t₀ + R ^ 2 / 8) (R / 2))) w γ)
    (hclosure : closure
      (parabolicCylinder x₀ (t₀ + R ^ 2 / 8) (R / 2)) ⊆
        spaceTimeSet Ω I) :
    IsRegularPoint Ω I u (x₀, t₀) := by
  let z₀ : ParabolicPoint := (x₀, t₀)
  let t₁ : ℝ := t₀ + R ^ 2 / 8
  let N : Set ParabolicPoint := Metric.ball z₀ (R / 4)
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hradius : 0 < R / 2 := by positivity
  have hz₀cyl : z₀ ∈ parabolicCylinder x₀ t₁ (R / 2) := by
    change (x₀, t₀) ∈ parabolicCylinder x₀ t₁ (R / 2)
    rw [mem_parabolicCylinder]
    refine ⟨?_, ?_, ?_⟩
    · simp [vec3EuclideanNorm_zero, hradius]
    ·
      dsimp [t₁]
      nlinarith only [hR2]
    · dsimp [t₁]
      nlinarith only [hR2]
  have hz₀closure : z₀ ∈ closure
      (parabolicCylinder x₀ t₁ (R / 2)) :=
    subset_closure hz₀cyl
  have hz₀domain : z₀ ∈ spaceTimeSet Ω I := hclosure hz₀closure
  have hNsub : N ⊆ goodPointPastCylinder x₀ t₁ (R / 2) := by
    intro z hz
    have hdist : dist z z₀ < R / 4 := by
      simpa [N, Metric.mem_ball] using hz
    rw [dist_eq_parabolicDist, parabolicDist] at hdist
    rcases max_lt_iff.mp hdist with ⟨hspace, htime⟩
    have htime' : |z.2 - t₀| < (R / 4) ^ 2 :=
      (Real.sqrt_lt' (by positivity : 0 < R / 4)).mp htime
    change z.1 ∈ vec3Ball x₀ (R / 2) ∧ z.2 ∈ Ioo
      (t₁ - (R / 2) ^ 2) t₁
    refine ⟨?_, ?_⟩
    · change vec3EuclideanNorm (z.1 - x₀) < R / 2
      exact hspace.trans (by linarith only [hR])
    · constructor
      · have hleft : t₁ - (R / 2) ^ 2 < t₀ := by
          dsimp [t₁]
          nlinarith only [hR2]
        have hnear : t₀ - (R / 4) ^ 2 < z.2 := by
          rw [abs_lt] at htime'
          linarith only [htime'.1]
        dsimp [t₁]
        nlinarith only [hR2, hR, hleft, hnear]
      · have hright : t₀ < t₁ := by
          dsimp [t₁]
          nlinarith only [hR2]
        have hnear : z.2 < t₀ + (R / 4) ^ 2 := by
          rw [abs_lt] at htime'
          linarith only [htime'.2]
        exact hnear.trans (by
          dsimp [t₁]
          nlinarith only [hR2, hR, hright])
  have hNsubCylinder : N ⊆ parabolicCylinder x₀ t₁ (R / 2) := by
    intro z hz
    rcases hNsub hz with ⟨hx, ht⟩
    rcases ht with ⟨ht₁, ht₂⟩
    exact ⟨hx, ht₁, le_of_lt ht₂⟩
  have hNclosure : N ⊆ closure
      (parabolicCylinder x₀ t₁ (R / 2)) :=
    hNsubCylinder.trans subset_closure
  have hEq : w =ᵐ[volume.restrict N] u :=
    ae_restrict_of_ae_restrict_of_subset hNsub hAE
  have hNopen : IsOpen N := by
    exact Metric.isOpen_ball
  have hz₀N : z₀ ∈ N := by
    simp [N, Metric.mem_ball, hR]
  have hNdomain : N ⊆ spaceTimeSet Ω I :=
    hNclosure.trans hclosure
  rcases hHolder with ⟨B, K, hB, hK, hbound, hsemi⟩
  have hHolderN : ParabolicHolderVecOn N w γ := by
    refine ⟨B, K, hB, hK, ?_, ?_⟩
    · intro z hz
      exact hbound z (hNclosure hz)
    · intro z hz z' hz'
      exact hsemi z (hNclosure hz) z' (hNclosure hz')
  refine ⟨hz₀domain, N, hNopen, hz₀N, hNdomain, γ, hγ, hγle, w, hEq, hHolderN⟩

end ESS
