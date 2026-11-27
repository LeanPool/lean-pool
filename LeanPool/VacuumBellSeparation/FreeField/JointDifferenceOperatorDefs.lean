/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialErrorOperators
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialEnvelope

/-!
# Literal statement construction extracted from FreeField/JointDifferenceOperator

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Filter
open scoped Topology

/-- The actual sum of field and momentum error operators on one joint completion. -/
def jointErrorOperator {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    SourceHilbert hμ (jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s) :=
  jointFieldErrorOperator hμ hs n + jointMomentumErrorOperator hμ hs n

/-- Constructed from the actual zero-order four-patch kernel. -/
def jointDifferenceKernelOperator {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s) :
    SourceHilbert hμ (jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s) :=
  jointErrorOperator hμ hs 0

/-- Continuous linear map for the joint polynomial kernel operator, of type `SourceHilbert hμ
(jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s)`. -/
def jointPolynomialKernelOperator {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    SourceHilbert hμ (jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s) :=
  jointDifferenceKernelOperator hμ hs - jointErrorOperator hμ hs n

/-- Joint polynomial error constant defined as `4 * jointSmoothKernelUniversalConstant * 11680000 *
134`. -/
def jointPolynomialErrorConstant : ℝ :=
  4 * jointSmoothKernelUniversalConstant * 11680000 * 134


end VacuumBellSeparation
