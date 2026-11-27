/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialLocalizedMomentSeries

/-!
# The actual field-and-momentum index for the source cross series
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian

/-- Spatial moment index. -/
abbrev SpatialMomentIndex := (Fin 3 → ℕ) × (Fin 3 → ℕ)
/-- A disjoint sum recording whether a spatial moment comes from the field or momentum kernel. -/
abbrev SpatialCrossIndex := SpatialMomentIndex ⊕ SpatialMomentIndex

/-- Spatial cross coefficient. -/
noncomputable def spatialCrossCoefficient (μ s R : ℝ) : SpatialCrossIndex → ℝ :=
  Sum.elim (fun k => (spatialFieldMultiCoefficient μ s R k.1 k.2).re)
    (fun k => (spatialMomentumMultiCoefficient μ s R k.1 k.2).re)

/-- Spatial cross left moment defined as `Sum.elim (fun k => spatialRealTestMoment u.1 k.1) (fun k
=> spatialRealTestMoment u.2 k.1) i`. -/
noncomputable def spatialCrossLeftMoment (i : SpatialCrossIndex) (u : TimeZeroSource) : ℝ :=
  Sum.elim (fun k => spatialRealTestMoment u.1 k.1) (fun k => spatialRealTestMoment u.2 k.1) i

/-- Spatial cross right moment. -/
noncomputable def spatialCrossRightMoment (s : ℝ) (i : SpatialCrossIndex)
  (v : TimeZeroSource) : ℝ :=
  Sum.elim (fun k => centeredSpatialTestMoment (spatialAxisDisplacement s 0) v.1 k.2)
    (fun k => centeredSpatialTestMoment (spatialAxisDisplacement s 0) v.2 k.2) i

theorem hasSum_localized_source_cross_index {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    {U W : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : ∀ x ∈ U, ∀ j, ‖x j‖ ≤ R / 2)
    (hW : ∀ x ∈ W, ∀ j, ‖(x - spatialAxisDisplacement s 0) j‖ ≤ R / 2)
    (u : SourceTestSpace hμ U) (v : SourceTestSpace hμ W) :
    HasSum (fun i => spatialCrossCoefficient μ s R i *
      spatialCrossLeftMoment i u.1 * spatialCrossRightMoment s i v.1)
      (inner ℝ (sourceEmbedding hμ U (u : SourceHilbert hμ U))
        (sourceEmbedding hμ W (v : SourceHilbert hμ W))) := by
  let f : SpatialMomentIndex → ℝ := fun k =>
    (spatialFieldMultiCoefficient μ s R k.1 k.2).re * spatialRealTestMoment u.1.1 k.1 *
      centeredSpatialTestMoment (spatialAxisDisplacement s 0) v.1.1 k.2
  let g : SpatialMomentIndex → ℝ := fun k =>
    (spatialMomentumMultiCoefficient μ s R k.1 k.2).re * spatialRealTestMoment u.1.2 k.1 *
      centeredSpatialTestMoment (spatialAxisDisplacement s 0) v.1.2 k.2
  have hf : Summable f := by
    have ht := (hasSum_spatialFourier_field_moments hμ hs hR hsep u.1.1
      (spatialTestTranslate (-(spatialAxisDisplacement s 0)) v.1.1)
      (fun x hx j => hU x (u.2.1 (subset_tsupport _ hx)) j)
      (spatialTestTranslate_back_coordinate_bound hW v.1.1 v.2.1)).summable
    simpa only [f, spatialTestMoment_eq_ofReal, centeredSpatialTestMoment,
      Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero] using ht.mapL Complex.reCLM
  have hg : Summable g := by
    have ht := (hasSum_spatialFourier_momentum_moments hμ hs hR hsep u.1.2
      (spatialTestTranslate (-(spatialAxisDisplacement s 0)) v.1.2)
      (fun x hx j => hU x (u.2.2 (subset_tsupport _ hx)) j)
      (spatialTestTranslate_back_coordinate_bound hW v.1.2 v.2.2)).summable
    simpa only [g, spatialTestMoment_eq_ofReal, centeredSpatialTestMoment,
      Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero] using ht.mapL Complex.reCLM
  have hk : HasSum (fun k => f k + g k)
      (inner ℝ (sourceEmbedding hμ U (u : SourceHilbert hμ U))
        (sourceEmbedding hμ W (v : SourceHilbert hμ W))) :=
    hasSum_localized_source_realMoments hμ hs hR hsep hU hW u v
  have heq := (hf.hasSum.add hg.hasSum).unique hk
  have hj : HasSum (Sum.elim f g) ((∑' k, f k) + ∑' k, g k) := hf.hasSum.sum hg.hasSum
  rw [heq] at hj
  convert hj using 1
  funext i
  cases i <;> rfl

end VacuumBellSeparation
