/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointRealPolynomialError
public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelOriginalForm

/-!
# Actual polynomial-error operators on the original joint source space

Each of the four error patches is the literal kernel error on its own
component. The common local derivative bound constructs bounded operators
on one total-source completion, without a regional decomposition inverse.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian Metric Set
open scoped SchwartzMap

/-- Joint center index obtained from `jointSpatialCenter`. -/
def jointCenterIndex (s : ℝ) (i : Fin 2) : EuclideanSpace ℝ (Fin 3) :=
  jointSpatialCenter s (decide (i = 1))

@[simp] theorem jointCenterIndex_zero (s : ℝ) : jointCenterIndex s 0 = 0 := by
  simp [jointCenterIndex, jointSpatialCenter]

@[simp] theorem jointCenterIndex_one (s : ℝ) :
    jointCenterIndex s 1 = spatialAxisDisplacement s 0 := by
  simp [jointCenterIndex, jointSpatialCenter]

/-- The union of the two unit spatial balls centered at the normalized separation. -/
def jointSourceRegion (s : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ball (jointCenterIndex s 0) 1 ∪ ball (jointCenterIndex s 1) 1

/-- Joint polynomial error patch. -/
def jointPolynomialErrorPatch {s : ℝ} (hs : 600 ≤ s)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (n : ℕ) (i j : Fin 2) : SchwartzMap JointKernelSpace ℂ :=
  cutOffJointLocalKernel (jointCenterIndex s i) (jointCenterIndex s j)
    (jointRealPolynomialError F s n (decide (i = 1)) (decide (j = 1)))
    (jointOpenComponentBox s (decide (i = 1)) (decide (j = 1)))
    (isOpen_jointOpenComponentBox s _ _)
    (jointKernelBox_subset_openComponent s _ _)
    (jointRealPolynomialError_contDiffOn hs F hF n _ _)

theorem jointPolynomialErrorPatch_eq {s : ℝ} (hs : 600 ≤ s)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (n : ℕ) (i j : Fin 2) (x : JointKernelSpace)
    (hx : x.fst ∈ closedBall (jointCenterIndex s i) 1)
    (hy : x.snd ∈ closedBall (jointCenterIndex s j) 1) :
    jointPolynomialErrorPatch hs F hF n i j x =
      jointRealPolynomialError F s n (decide (i = 1)) (decide (j = 1)) x :=
  cutOffJointLocalKernel_eq _ _ _ _ _ _ _ x hx hy

/-- Continuous linear map for the joint field error operator, of type `SourceHilbert hμ
(jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s)`. -/
def jointFieldErrorOperator {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    SourceHilbert hμ (jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s) :=
  jointFourFieldKernelOperator hμ (jointSourceRegion s)
    (jointPolynomialErrorPatch hs (jointNormalizedFieldKernel μ s)
      (jointNormalizedFieldKernel_analyticAt hμ (by linarith)) n)

/-- Continuous linear map for the joint momentum error operator, of type `SourceHilbert hμ
(jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s)`. -/
def jointMomentumErrorOperator {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    SourceHilbert hμ (jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s) :=
  jointFourMomentumKernelOperator hμ (jointCenterIndex s 0) (jointCenterIndex s 1)
    (jointPolynomialErrorPatch hs (jointNormalizedMomentumKernel μ s)
      (jointNormalizedMomentumKernel_analyticAt hμ (by linarith)) n)

theorem jointPolynomialError_four_operator_bounds {μ s M : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s) (hM : 0 ≤ M)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖F z‖ ≤ M) (n : ℕ) :
    ‖jointFourFieldKernelOperator hμ (jointSourceRegion s) (jointPolynomialErrorPatch hs F hF n)‖ ≤
        (4 * jointSmoothKernelUniversalConstant) * max 1 μ *
          (11680000 * M * (78643200 / s) ^ n) ∧
      ‖jointFourMomentumKernelOperator hμ (jointCenterIndex s 0) (jointCenterIndex s 1)
        (jointPolynomialErrorPatch hs F hF n)‖ ≤
        (4 * jointSmoothKernelUniversalConstant) * (11680000 * M * (78643200 / s) ^ n) := by
  have hs₀ : 0 < s := by linarith
  exact jointLocalKernel_four_operator_bounds hμ (by positivity) (jointCenterIndex s)
    (fun i j => jointRealPolynomialError F s n (decide (i = 1)) (decide (j = 1)))
    (fun i j => jointOpenComponentBox s (decide (i = 1)) (decide (j = 1)))
    (fun i j => isOpen_jointOpenComponentBox s _ _)
    (fun i j => jointKernelBox_subset_openComponent s _ _)
    (fun i j => jointRealPolynomialError_contDiffOn hs F hF n _ _)
    (fun i j k hk x hx => jointRealPolynomialError_derivative hs hM F hF hbound n _ _ x hx
      (by omega))

theorem norm_jointFieldErrorOperator_le {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    ‖jointFieldErrorOperator hμ hs n‖ ≤ (4 * jointSmoothKernelUniversalConstant) * max 1 μ *
      (11680000 * jointFieldEnvelope μ s * (78643200 / s) ^ n) := by
  exact (jointPolynomialError_four_operator_bounds hμ hs
    (by unfold jointFieldEnvelope; positivity) (jointNormalizedFieldKernel μ s)
    (jointNormalizedFieldKernel_analyticAt hμ (by linarith))
    (jointNormalizedFieldKernel_norm_le hμ (by linarith)) n).1

theorem norm_jointMomentumErrorOperator_le {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    ‖jointMomentumErrorOperator hμ hs n‖ ≤ (4 * jointSmoothKernelUniversalConstant) *
      (11680000 * jointMomentumEnvelope μ s * (78643200 / s) ^ n) := by
  exact (jointPolynomialError_four_operator_bounds hμ hs
    (by unfold jointMomentumEnvelope; positivity) (jointNormalizedMomentumKernel μ s)
    (jointNormalizedMomentumKernel_analyticAt hμ (by linarith))
    (jointNormalizedMomentumKernel_norm_le hμ (by linarith)) n).2

end VacuumBellSeparation
