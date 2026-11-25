/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CompactVariableCurrentTests
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalSmoothScalarCurrents

/-! # Actual finite scalar transposition of full coefficient-current tests -/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.ScalarFullTestTranspose

open FirstPass StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorSmooth LocalSmoothScalarCurrents ScalarLeviPositiveCurrent
  CompactVariableCurrentTests LocalCurrentLebesgue TopDegreeDensity

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

/-- The genuine finite scalar test with the literal current normalization and derivative order. -/
def scalarAdjointTest (α : 𝓓(U, RealForm (m + 1) (2 * m))) : 𝓓(U, ℝ) :=
  ∑ i, ∑ a, ∑ b,
    (-(1 / (4 * Real.pi)) *
      topDensity ((wedgeLM m (isOneOne_coeffForm a b) (formBasis (m + 1) m i) :
        formSpan (m + 1) (m + 1)) : RealForm (m + 1) (2 * (m + 1)))) •
      dTest (realBasis (m + 1) b) (dTest (realBasis (m + 1) a) (coeffTest α i))

/-- The actual distribution differential transposes to the internally constructed scalar test. -/
theorem ddc_scalarTopCurrent_full_test_transpose (T : 𝓓'(U, ℝ))
    (α : 𝓓(U, RealForm (m + 1) (2 * m))) :
    (∑ i, ddc (scalarTopCurrent T) (formBasis (m + 1) m i) (coeffTest α i)) =
      T (scalarAdjointTest α) := by
  simp only [scalarAdjointTest, map_sum, map_smul, smul_eq_mul,
    ddc_apply_apply, scalarTopCurrent_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Smoothness on the actual open set internally gives the full scalar integral pairing. -/
theorem local_smooth_scalar_full_test_integral
    {f : ComplexModel (m + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (α : 𝓓(U, RealForm (m + 1) (2 * m))) :
    (∑ i, ddcWedge (oneCurrent U) hf (formBasis (m + 1) m i) (coeffTest α i)) =
      ∫ x in (U : Set (ComplexModel (m + 1))), scalarAdjointTest α x * f x := by
  rw [← ddc_scalarTopCurrent_regularDistribution_eq_ddcWedge hf,
    ddc_scalarTopCurrent_full_test_transpose, regularDistribution_apply]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro x hx
  have hzero : scalarAdjointTest α x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx ((scalarAdjointTest α).tsupport_subset h))
  rw [hzero, zero_mul]

end SGPT.Foundations.Analysis.Pending.ScalarFullTestTranspose
