/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ShellSubmeanNeighborhood
public import LeanPool.VacuumBellSeparation.Shell.InducedShellChartCoverage
public import LeanPool.VacuumBellSeparation.Shell.NormalizedTargetCompact

/-!
# Uniform actual chart balls over the compact normalized target

The original target is compact, including mass zero. An actual finite
subcover of the local chart constructions yields one positive radius
and one positive Gram lower bound. No chart controls are supplied as
hypotheses at this endpoint.
-/

@[expose] public section

namespace VacuumBellSeparation

open Metric Set

theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, r ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s his ih =>
    obtain ⟨r, hr, hle⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min (f i) r, lt_min (hf i (Finset.mem_insert_self _ _)) hr, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hle j hj)

theorem normalizedTarget_uniform_submean_charts
    {V : Set (ℝ × ComplexSpacetime)} (hV : IsOpen V) (hcover : normalizedTarget ⊆ V) :
    ∃ R d : ℝ, 0 < R ∧ 0 < d ∧
      ∀ t z, (t, z) ∈ normalizedTarget →
        ∃ (Λ : Spacetime ≃L[ℝ] Spacetime) (c : ShellEuclideanDomain),
          IsLorentzMap Λ ∧
          lorentzComplexShellChart t Λ (shellEuclideanCoordinates c) = z ∧
          ∀ w ∈ ball c (2 * R), w ∈ euclideanShellChartDomain t ∧
            d ≤ inducedShellChartDensity t Λ w ∧
            (t, lorentzComplexShellChart t Λ (shellEuclideanCoordinates w)) ∈ V := by
  classical
  have hlocal (p : normalizedTarget) :
      ∃ (Λ : Spacetime ≃L[ℝ] Spacetime) (W : Set (ℝ × ComplexSpacetime)) (R d : ℝ),
        IsLorentzMap Λ ∧ IsOpen W ∧ p.1 ∈ W ∧ 0 < R ∧ 0 < d ∧
        ∀ t z, (t, z) ∈ W → z ∈ complexShell t →
          lorentzComplexShellChart t Λ
            (shellEuclideanCoordinates (shellAmbientCoordinates Λ z)) = z ∧
          ∀ w ∈ ball (shellAmbientCoordinates Λ z) (2 * R),
            w ∈ euclideanShellChartDomain t ∧ d ≤ inducedShellChartDensity t Λ w ∧
            (t, lorentzComplexShellChart t Λ (shellEuclideanCoordinates w)) ∈ V := by
    obtain ⟨Λ, w, hΛ, _, hw, him, _, _⟩ :=
      normalizedTarget_volume_chart_coverage p.2 (θ := Real.pi / 2) (by simp)
    have him' : lorentzComplexShellChart p.1.1 Λ (shellEuclideanCoordinates w) = p.1.2 :=
      complexSpacetimeEuclideanEquiv.injective him
    obtain ⟨W, hW, hmem, R, d, hR, hd, hctl⟩ :=
      shell_submean_local_neighborhood Λ hΛ.1 hw hV
        (by rw [him']; exact hcover p.2)
    rw [him'] at hmem
    exact ⟨Λ, W, R, d, hΛ.1, hW, hmem, hR, hd, hctl⟩
  choose Λ W R d hΛ hW hmem hR hd hctl using hlocal
  have hfull : normalizedTarget ⊆ ⋃ p : normalizedTarget, W p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hmem ⟨p, hp⟩⟩
  obtain ⟨s, hs⟩ := normalizedTarget_finite_subcover W hW hfull
  obtain ⟨R₀, hR₀, hRle⟩ := finite_positive_lower_bound s R (fun i _ => hR i)
  obtain ⟨d₀, hd₀, hdle⟩ := finite_positive_lower_bound s d (fun i _ => hd i)
  refine ⟨R₀, d₀, hR₀, hd₀, ?_⟩
  intro t z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hz)
  obtain ⟨his, hiW⟩ := mem_iUnion.mp hi
  obtain ⟨him, hball⟩ := hctl i t z hiW hz.2.2.1
  refine ⟨Λ i, shellAmbientCoordinates (Λ i) z, hΛ i, him, ?_⟩
  intro w hw
  have hw' : w ∈ ball (shellAmbientCoordinates (Λ i) z) (2 * R i) :=
    ball_subset_ball (mul_le_mul_of_nonneg_left (hRle i his) (by norm_num)) hw
  have h := hball w hw'
  exact ⟨h.1, (hdle i his).trans h.2.1, h.2.2⟩

end VacuumBellSeparation
