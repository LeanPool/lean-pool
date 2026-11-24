/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ConstantFormLocalDdc

/-! # Actual compact smooth test operators for normalized complex differentials -/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.CompactDifferentialTests

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  ConstantFormProducts ClosedProductCurrents XiaoLocalComplexStokes ConstantFormLocalDdc

/-- The genuine exterior derivative maps actual smooth compact form tests continuously. -/
def exteriorTestCLM {n k : ℕ} {U : Opens (ComplexModel n)} :
    𝓓(U, RealForm n k) →L[ℝ] 𝓓(U, RealForm n (k + 1)) :=
  (TestFunction.postcompCLM (Ω := U) (n := ⊤)
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ (ComplexModel n) ℝ)).comp
      (TestFunction.fderivCLM (Ω := U) (F := RealForm n k) ℝ ⊤ ⊤)

/-- Infinite regularity internally selects the actual derivative branch. -/
theorem exteriorTestCLM_apply {n k : ℕ} {U : Opens (ComplexModel n)}
    (α : 𝓓(U, RealForm n k)) (x : ComplexModel n) :
    exteriorTestCLM α x = extDeriv α x := by
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
    (TestFunction.fderivCLM ℝ ⊤ ⊤ α x) = _
  rw [congrFun (TestFunction.fderivCLM_apply_of_le α (by simp)) x]
  rfl

/-- The literal normalized complex differential is a genuine compact-test map. -/
def localDcTestCLM {n k : ℕ} {U : Opens (ComplexModel n)} :
    𝓓(U, RealForm n k) →L[ℝ] 𝓓(U, RealForm n (k + 1)) :=
  let Jk : RealForm n k →L[ℝ] RealForm n k :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)
  let Jk1 : RealForm n (k + 1) →L[ℝ] RealForm n (k + 1) :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)
  ((-1 : ℝ) ^ (k + 1) / (4 * Real.pi)) •
    (TestFunction.postcompCLM (Ω := U) (n := ⊤) Jk1).comp
      ((exteriorTestCLM (n := n) (k := k) (U := U)).comp
        (TestFunction.postcompCLM (Ω := U) (n := ⊤) Jk))

/-- The pointwise operator agrees with the entire actual local formula. -/
theorem localDcTestCLM_apply {n k : ℕ} {U : Opens (ComplexModel n)}
    (α : 𝓓(U, RealForm n k)) (x : ComplexModel n) :
    localDcTestCLM α x = localDc α x := by
  change (((-1 : ℝ) ^ (k + 1) / (4 * Real.pi)) •
    (exteriorTestCLM
      (TestFunction.postcompCLM
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)) α)
          x).compContinuousLinearMap (modelComplexStructure n)) = _
  rw [exteriorTestCLM_apply]
  rfl

/-- The composed second differential has true compact smooth output. -/
def localDdcTestCLM {n k : ℕ} {U : Opens (ComplexModel n)} :
    𝓓(U, RealForm n k) →L[ℝ] 𝓓(U, RealForm n (k + 1 + 1)) :=
  (exteriorTestCLM (n := n) (k := k + 1) (U := U)).comp
    (localDcTestCLM (n := n) (k := k) (U := U))

/-- Its values are the actual exterior derivative of the actual local complex field. -/
theorem localDdcTestCLM_apply {n k : ℕ} {U : Opens (ComplexModel n)}
    (α : 𝓓(U, RealForm n k)) (x : ComplexModel n) :
    localDdcTestCLM α x = extDeriv (fun y => localDc α y) x := by
  change exteriorTestCLM (localDcTestCLM α) x = _
  rw [exteriorTestCLM_apply]
  have h : (localDcTestCLM α : ComplexModel n → RealForm n (k + 1)) = fun y => localDc α y :=
    funext (localDcTestCLM_apply α)
  rw [h]

/-- The actual compact second operator recovers the full constant-form identity. -/
theorem localDdcTestCLM_constForm_apply {n q : ℕ} {U : Opens (ComplexModel n)}
    (φ : 𝓓(U, ℝ)) (γ : formSpan n q) (x : ComplexModel n) :
    localDdcTestCLM
      (TestFunction.postcompCLM
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (γ : RealForm n (2 * q))) φ) x =
      wedgeTo (by omega : 2 + 2 * q = 2 * q + 1 + 1)
        (smoothDDC φ x) (γ : RealForm n (2 * q)) := by
  rw [localDdcTestCLM_apply]
  change extDeriv (fun y => localDc
    (fun z => φ z • (γ : RealForm n (2 * q))) y) x = _
  have hφ : ContDiffAt ℝ 2 φ x :=
    φ.contDiff.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact localDdc_smul_const_form_at hφ γ

end SGPT.Foundations.Analysis.Pending.CompactDifferentialTests
