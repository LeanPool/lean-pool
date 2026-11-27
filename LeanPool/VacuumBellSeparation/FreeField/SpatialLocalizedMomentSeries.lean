/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialRealMomentSeries
public import LeanPool.VacuumBellSeparation.FreeField.SourceSpace

/-!
# Literal localized source covariance and centered regional moments

The right-region moments use the original test translated back to its
center. Region geometry discharges every support condition in the actual
Fourier-to-Bessel-to-moment calculation.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian ClosedSubmodule

/-- Centered spatial test moment obtained from `spatialRealTestMoment`. -/
noncomputable def centeredSpatialTestMoment (a : EuclideanSpace ℝ (Fin 3))
    (f : SpatialTestFunction) (α : Fin 3 → ℕ) : ℝ :=
  spatialRealTestMoment (spatialTestTranslate (-a) f) α

theorem timeZeroTranslate_neg_cancel (a : EuclideanSpace ℝ (Fin 3)) (v : TimeZeroSource) :
    timeZeroTranslate (-a) (timeZeroTranslate a v) = v := by
  apply Prod.ext <;> exact spatialTestTranslate_neg_cancel a _

theorem spatialTestTranslate_back_coordinate_bound {a : EuclideanSpace ℝ (Fin 3)}
    {W : Set (EuclideanSpace ℝ (Fin 3))} {R : ℝ}
    (hW : ∀ x ∈ W, ∀ j, ‖(x - a) j‖ ≤ R)
    (f : SpatialTestFunction) (hf : tsupport f.1 ⊆ W) :
    ∀ x, (spatialTestTranslate (-a) f).1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R := by
  intro x hx j
  have hx' : f.1 (x + a) ≠ 0 := by simpa only [spatialTestTranslate, sub_neg_eq_add] using hx
  simpa only [add_sub_cancel_right] using hW (x + a) (hf (subset_tsupport _ hx')) j

theorem hasSum_localized_source_realMoments {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    {U W : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : ∀ x ∈ U, ∀ j, ‖x j‖ ≤ R / 2)
    (hW : ∀ x ∈ W, ∀ j, ‖(x - spatialAxisDisplacement s 0) j‖ ≤ R / 2)
    (u : SourceTestSpace hμ U) (v : SourceTestSpace hμ W) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      (spatialFieldMultiCoefficient μ s R k.1 k.2).re * spatialRealTestMoment u.1.1 k.1 *
          centeredSpatialTestMoment (spatialAxisDisplacement s 0) v.1.1 k.2 +
        (spatialMomentumMultiCoefficient μ s R k.1 k.2).re * spatialRealTestMoment u.1.2 k.1 *
          centeredSpatialTestMoment (spatialAxisDisplacement s 0) v.1.2 k.2)
      (inner ℝ (sourceEmbedding hμ U (u : SourceHilbert hμ U))
        (sourceEmbedding hμ W (v : SourceHilbert hμ W))) := by
  have h := hasSum_timeZeroCovariance_realMoments hμ hs hR hsep u.1
    (timeZeroTranslate (-(spatialAxisDisplacement s 0)) v.1)
    (fun x hx j => hU x (u.2.1 (subset_tsupport _ hx)) j)
    (fun x hx j => hU x (u.2.2 (subset_tsupport _ hx)) j)
    (spatialTestTranslate_back_coordinate_bound hW v.1.1 v.2.1)
    (spatialTestTranslate_back_coordinate_bound hW v.1.2 v.2.2)
  have hv : timeZeroTranslate (spatialAxisDisplacement s 0)
      (timeZeroTranslate (-(spatialAxisDisplacement s 0)) v.1) = v.1 := by
    simpa only [neg_neg] using timeZeroTranslate_neg_cancel (-(spatialAxisDisplacement s 0)) v.1
  rw [hv] at h
  have hreal (x y : TimeZeroSource) :
      inner ℝ (timeZeroL2 hμ x) (timeZeroL2 hμ y) = timeZeroFourierCovariance μ x y := by
    have hinner : inner ℝ (timeZeroL2 hμ x) (timeZeroL2 hμ y) =
        (inner ℂ (timeZeroL2 hμ x) (timeZeroL2 hμ y)).re := by
      rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
      calc
        _ = ∫ p, RCLike.re (inner ℂ ((timeZeroL2 hμ x) p) ((timeZeroL2 hμ y) p))
            ∂oneParticleMeasure μ := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun p => by
            simp only [Complex.inner, RCLike.inner_apply]
            rfl
        _ = _ := integral_re
          (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (timeZeroL2 hμ x) (timeZeroL2 hμ y))
    rw [hinner, inner_timeZeroL2_gram]
    simp [Complex.mul_re]
  have hcov : inner ℝ (sourceEmbedding hμ U (u : SourceHilbert hμ U))
      (sourceEmbedding hμ W (v : SourceHilbert hμ W)) =
        timeZeroFourierCovariance μ u.1 v.1 :=
    (congrArg₂ (inner ℝ) (sourceEmbedding_coe hμ U u)
      (sourceEmbedding_coe hμ W v)).trans (hreal u.1 v.1)
  rw [hcov]
  simpa only [centeredSpatialTestMoment, timeZeroTranslate] using h

end VacuumBellSeparation
