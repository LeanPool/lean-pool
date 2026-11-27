/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointFiniteSourceDecomposition

/-!
# Actual compression of the joint kernel difference to finite covariances

The isometry is the existing original-source covariance whitening. Its
compression is the literal product-minus-joint covariance normalized by
the joint covariance, as required for the reverse estimate.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

variable {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
  (S : Submodule ℝ TimeZeroSource)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (FiniteSourceSpace hμ S))
  (hSU : S ≤ localizedTimeZeroSources (jointSourceRegion s))
  (L R : Submodule ℝ (ι → ℝ)) (hLR : IsCompl L R)
  (hLA : ∀ x ∈ L, finiteSourceCoordinates hμ S b x ∈
    localizedTimeZeroSources (Metric.ball (jointCenterIndex s 0) 1))
  (hRB : ∀ x ∈ R, finiteSourceCoordinates hμ S b x ∈
    localizedTimeZeroSources (Metric.ball (jointCenterIndex s 1) 1))

include hLA hRB in
theorem includedFiniteSourceFamily_joint_difference_form :
    realFamilyForm (includedFiniteSourceFamily hμ S b hSU) (jointDifferenceKernelOperator hμ hs) =
      labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hμ S b) L R hLR -
        finiteSourceCovarianceMatrix hμ S b := by
  ext i j
  have h := jointDifferenceKernelOperator_pairing_sum hμ hs
    (jointProjectedSourceTests hμ S b L R hLR hLA hRB i)
    (jointProjectedSourceTests hμ S b L R hLR hLA hRB j)
    (jointProjectedSourceTests_localized hμ S b L R hLR hLA hRB i)
    (jointProjectedSourceTests_localized hμ S b L R hLR hLA hRB j)
  rw [jointProjectedSourceTests_sum hμ S b L R hLR hLA hRB hSU i,
    jointProjectedSourceTests_sum hμ S b L R hLR hLA hRB hSU j,
    jointProjectedSourceTests_diagonal_gram hμ S b L R hLR hLA hRB i j] at h
  change realFamilyForm (includedFiniteSourceFamily hμ S b hSU)
    (jointDifferenceKernelOperator hμ hs) i j =
    labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hμ S b) L R hLR i j -
      realFamilyGram (includedFiniteSourceFamily hμ S b hSU) i j at h
  rw [includedFiniteSourceFamily_gram] at h
  exact h

include hLA hRB in
theorem finiteSourceCompression_joint_difference :
    compression (finiteSourceCompressionIsometry hμ S b hSU)
      (complexify (jointDifferenceKernelOperator hμ hs)) =
      realMatrixOperator (relativeCovariancePerturbation (finiteSourceCovarianceMatrix hμ S b)
        (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hμ S b) L R hLR -
          finiteSourceCovarianceMatrix hμ S b)) := by
  have h := compression_whitened_complexify
    (includedFiniteSourceFamily hμ S b hSU)
    (includedFiniteSourceFamily_linearIndependent hμ S b hSU)
    (jointDifferenceKernelOperator hμ hs)
  rw [includedFiniteSourceFamily_gram,
    includedFiniteSourceFamily_joint_difference_form hμ hs S b hSU L R hLR hLA hRB] at h
  exact h

end VacuumBellSeparation
