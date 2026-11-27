/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialPatchDifference
public import LeanPool.VacuumBellSeparation.FreeField.JointKernelOperatorLinearity
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialMidpointForm
public import LeanPool.VacuumBellSeparation.FreeField.JointDifferenceOperator

/-!
# The convergent approximants are the actual finite moment operators

The identity is established in the original joint source completion by
the literal compact-test integrals. The moment family can be any family
constructed from those same test moments; density makes the answer unique.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian MvPolynomial
open scoped SchwartzMap InnerProductSpace

theorem jointFieldPolynomial_operator_eq {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
    (v : JointSourceMomentFamily hμ (jointSourceRegion s))
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z) (n : ℕ) :
    jointFourFieldKernelOperator hμ (jointSourceRegion s) (jointPolynomialErrorPatch hs F hF 0) -
      jointFourFieldKernelOperator hμ (jointSourceRegion s) (jointPolynomialErrorPatch hs F hF n) =
        jointPolynomialMomentOperator (𝕜 := ℝ) v.field (jointPhysicalPolynomial s
          (jointMidpointPolynomial F n)) := by
  rw [← jointFourFieldKernelOperator_sub]
  apply completionOperator_eq_of_test_pairings
  intro x y
  rw [jointPhysicalPolynomial_field_pairing]
  exact jointFourFieldKernelOperator_pairing hμ (jointCenterIndex s)
    (fun i j => jointPolynomialErrorPatch hs F hF 0 i j - jointPolynomialErrorPatch hs F hF n i j)
    (fun z => eval (jointPhysicalMidpoint s (jointComplexCoordinates z))
      (jointMidpointPolynomial F n))
    (jointPolynomialErrorPatch_sub_sum hs F hF n) x y

theorem jointMomentumPolynomial_operator_eq {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
    (v : JointSourceMomentFamily hμ (jointSourceRegion s))
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z) (n : ℕ) :
    jointFourMomentumKernelOperator hμ (jointCenterIndex s 0) (jointCenterIndex s 1)
        (jointPolynomialErrorPatch hs F hF 0) -
      jointFourMomentumKernelOperator hμ (jointCenterIndex s 0) (jointCenterIndex s 1)
        (jointPolynomialErrorPatch hs F hF n) =
          jointPolynomialMomentOperator (𝕜 := ℝ) v.momentum (jointPhysicalPolynomial s
            (jointMidpointPolynomial F n)) := by
  rw [← jointFourMomentumKernelOperator_sub]
  apply completionOperator_eq_of_test_pairings
  intro x y
  -- The kernel operator lives on the unfolded union of balls; compose the two
  -- pairing identities instead of rewriting across the two spellings of the region.
  refine (jointFourMomentumKernelOperator_pairing hμ (jointCenterIndex s)
    (fun i j => jointPolynomialErrorPatch hs F hF 0 i j - jointPolynomialErrorPatch hs F hF n i j)
    (fun z => eval (jointPhysicalMidpoint s (jointComplexCoordinates z))
      (jointMidpointPolynomial F n))
    (jointPolynomialErrorPatch_sub_sum hs F hF n) x y).trans ?_
  exact (jointPhysicalPolynomial_momentum_pairing hμ (jointSourceRegion s) v s
    (jointMidpointPolynomial F n) x y).symm

/-- Exact equality with two genuine finite sums of original moment vectors. -/
theorem jointPolynomialKernelOperator_eq_moments {μ s : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s) (v : JointSourceMomentFamily hμ (jointSourceRegion s)) (n : ℕ) :
    jointPolynomialKernelOperator hμ hs n =
      jointPolynomialMomentOperator (𝕜 := ℝ) v.field
        (jointPhysicalPolynomial s (jointMidpointPolynomial (jointNormalizedFieldKernel μ s) n)) +
      jointPolynomialMomentOperator (𝕜 := ℝ) v.momentum
        (jointPhysicalPolynomial s (jointMidpointPolynomial
          (jointNormalizedMomentumKernel μ s) n)) := by
  have hf := jointFieldPolynomial_operator_eq hμ hs v (jointNormalizedFieldKernel μ s)
    (jointNormalizedFieldKernel_analyticAt hμ (by linarith)) n
  have hg := jointMomentumPolynomial_operator_eq hμ hs v (jointNormalizedMomentumKernel μ s)
    (jointNormalizedMomentumKernel_analyticAt hμ (by linarith)) n
  change jointFieldErrorOperator hμ hs 0 - jointFieldErrorOperator hμ hs n = _ at hf
  change jointMomentumErrorOperator hμ hs 0 - jointMomentumErrorOperator hμ hs n = _ at hg
  rw [← hf, ← hg]
  unfold jointPolynomialKernelOperator jointDifferenceKernelOperator jointErrorOperator
  abel

end VacuumBellSeparation
