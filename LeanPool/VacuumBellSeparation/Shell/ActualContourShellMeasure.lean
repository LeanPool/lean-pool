/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.FiniteContourMixture

/-!
# The actual cutoff pushforward dominates induced shell volume

The pushforward takes values in the original complex mass shell. Borel
ambient weights determine measures on this closed subtype, so the
proved integral bound gives an actual measure inequality.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped ENNReal

theorem isClosed_complexShell (t : ℝ) : IsClosed (complexShell t) := by
  unfold complexShell spatialDot
  exact isClosed_eq (by fun_prop) continuous_const

theorem complexShellMeasure_le_of_lintegral {t : ℝ} {μ ν : Measure (complexShell t)}
    (h : ∀ F : ComplexSpacetime → ℝ≥0∞, Measurable F →
      (∫⁻ z, F z.1 ∂μ) ≤ ∫⁻ z, F z.1 ∂ν) : μ ≤ ν := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  have him : MeasurableSet (Subtype.val '' s : Set ComplexSpacetime) :=
    (MeasurableEmbedding.subtype_coe (isClosed_complexShell
      t).measurableSet).measurableSet_image' hs
  let F : ComplexSpacetime → ℝ≥0∞ := (Subtype.val '' s).indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator him
  have he : (fun z : complexShell t => F z.1) = s.indicator (fun _ => 1) := by
    funext z
    simp only [F, Set.indicator_apply, Subtype.coe_injective.mem_set_image]
  have hb := h F hF
  simpa only [he, lintegral_indicator_const hs, one_mul] using hb

variable {θ : ℝ} {N : ℕ}

/-- Contour mixture shell point. -/
noncomputable def contourMixtureShellPoint (t : ℝ) (D : Fin N → ControlledContourPatch θ)
    (y : (Fin N × (Fin 6 → ℝ)) × EuclideanSpace ℝ (Fin 3)) : complexShell t :=
  ⟨contourMixturePoint t D y,
    complexifiedSpacetimeMap_mem_shell _ (contourMixtureFamily_isProper D y.1).1
      (complexShellBoost_mem_shell t _ y.2)⟩

theorem continuous_contourMixtureShellPoint (t : ℝ) (D : Fin N → ControlledContourPatch θ) :
    Continuous (contourMixtureShellPoint t D) :=
  (continuous_contourMixturePoint t D).subtype_mk _

/-- Contour mixture shell measure. -/
noncomputable def contourMixtureShellMeasure (t : ℝ) (D : Fin N → ControlledContourPatch θ) :
    Measure (complexShell t) :=
  Measure.map (contourMixtureShellPoint t D)
    (((contourMixtureProbability D).prod (oneParticleMeasure t)).restrict
      {y | dispersion t y.2 ≤ 32 / Real.sin θ})

theorem contourMixtureShellMeasure_lintegral (t : ℝ) (D : Fin N → ControlledContourPatch θ)
    {F : ComplexSpacetime → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z.1 ∂contourMixtureShellMeasure t D) =
      ∫⁻ y, contourMixtureCutoffWeight t D F y
        ∂(contourMixtureProbability D).prod (oneParticleMeasure t) := by
  rw [contourMixtureShellMeasure]
  rw [lintegral_map (f := fun z : complexShell t => F z.1)
    (μ := ((contourMixtureProbability D).prod (oneParticleMeasure t)).restrict
      {y | dispersion t y.2 ≤ 32 / Real.sin θ})
    (hF.comp measurable_subtype_coe) (continuous_contourMixtureShellPoint t D).measurable]
  have hs : MeasurableSet {y : (Fin N × (Fin 6 → ℝ)) × EuclideanSpace ℝ (Fin 3) |
      dispersion t y.2 ≤ 32 / Real.sin θ} :=
    (isClosed_le ((continuous_dispersion t).comp continuous_snd) continuous_const).measurableSet
  simpa only [contourMixtureShellPoint, contourMixtureCutoffWeight] using
    (lintegral_indicator (μ := (contourMixtureProbability D).prod (oneParticleMeasure t))
      hs (fun y => F (contourMixturePoint t D y))).symm

theorem contourMixture_uniform_measure_bound [NeZero N]
    (D : Fin N → ControlledContourPatch θ) :
    ∃ k : ℝ≥0∞, 0 < k ∧ k < ∞ ∧ ∀ t : ℝ,
      k • (inducedRegularShellVolume t).restrict
        {z : complexShell t | (t, z.1) ∈ contourMixtureNeighborhood D} ≤
          contourMixtureShellMeasure t D := by
  obtain ⟨k, hk, hkt, hb⟩ := contourMixture_uniform_integral_bound D
  refine ⟨k, hk, hkt, fun t => complexShellMeasure_le_of_lintegral ?_⟩
  intro F hF
  rw [lintegral_smul_measure, contourMixtureShellMeasure_lintegral t D hF]
  exact hb t F hF

theorem contourMixtureProbability_compact_support (D : Fin N → ControlledContourPatch θ) :
    ∃ K : Set (Fin N × (Fin 6 → ℝ)), IsCompact K ∧
      (∀ᵐ a ∂contourMixtureProbability D, a ∈ K) ∧
      ∀ a ∈ K,
        spacetimeEuclideanOperatorNorm (contourMixtureFamily D a) < 32 / Real.sin θ ∧
        spacetimeEuclideanOperatorNorm (contourMixtureFamily D a).symm < 32 / Real.sin θ := by
  let K : Set (Fin N × (Fin 6 → ℝ)) :=
    ⋃ i, {i} ×ˢ Metric.closedBall 0 (D i).radius
  have hK : IsCompact K := isCompact_iUnion
    (fun i => isCompact_singleton.prod (isCompact_closedBall (0 : Fin 6 → ℝ) (D i).radius))
  refine ⟨K, hK, ?_, ?_⟩
  · apply finiteTaggedProbability_ae _ hK.isClosed.measurableSet
    intro i
    filter_upwards [smoothBallProbability_ae_norm_lt (D i).radius (D i).radius_pos] with s hs
    exact mem_iUnion.mpr ⟨i, ⟨rfl, by simpa only [Metric.mem_closedBall, dist_zero_right]
      using hs.le⟩⟩
  · intro a ha
    obtain ⟨i, hi, hs⟩ := mem_iUnion.mp ha
    have he : a.1 = i := hi
    have hn : ‖a.2‖ ≤ (D a.1).radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right, he] using hs
    exact (D a.1).norm_bound a.2 hn

/-- Actual mass-uniform geometric domination on an open neighborhood of
the entire normalized target, with a compactly supported probability
on genuine proper future Lorentz parameter patches. -/
theorem normalizedTarget_uniform_contour_domination {θ : ℝ} (hθ : 0 < Real.sin θ) :
    ∃ N : ℕ, 0 < N ∧ ∃ D : Fin N → ControlledContourPatch θ,
      IsProbabilityMeasure (contourMixtureProbability D) ∧
      IsOpen (contourMixtureNeighborhood D) ∧
      normalizedTarget ⊆ contourMixtureNeighborhood D ∧
      ∃ k : ℝ≥0∞, 0 < k ∧ k < ∞ ∧ ∀ t : ℝ,
        k • (inducedRegularShellVolume t).restrict
          {z : complexShell t | (t, z.1) ∈ contourMixtureNeighborhood D} ≤
            contourMixtureShellMeasure t D := by
  obtain ⟨N, hN, D, hcover⟩ := normalizedTarget_finite_contourPatches hθ
  let _ : NeZero N := ⟨hN.ne'⟩
  exact ⟨N, hN, D, inferInstance, isOpen_contourMixtureNeighborhood D, hcover,
    contourMixture_uniform_measure_bound D⟩

end VacuumBellSeparation
