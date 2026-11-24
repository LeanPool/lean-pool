/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CompactDifferentialTests
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ScalarFullTestTranspose

/-! # Literal full compact second differentials and their finite coordinate expansion -/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.CompactDdcCoordinateExpansion

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorForms CompactVariableCurrentTests
  CompactDifferentialTests ConstantFormProducts LocalCurrentLebesgue
  TopDegreeDensity ScalarFullTestTranspose XiaoLocalComplexStokes

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

/-- Natural type-span membership produces equality in the genuine compact test space. -/
theorem eq_sum_constFormTest {n q : ℕ} {U : Opens (ComplexModel n)}
    (α : 𝓓(U, RealForm n (2 * q))) (hα : ∀ x, α x ∈ formSpan n q) :
    α = ∑ i, TestFunction.postcompCLM
      ((ContinuousLinearMap.id ℝ ℝ).smulRight
        ((formBasis n q i : formSpan n q) : RealForm n (2 * q))) (coeffTest α i) := by
  apply TestFunction.ext
  intro x
  simpa only [_root_.sum_apply, TestFunction.postcompCLM_apply,
    Function.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply] using
    eq_sum_coeffTest α hα x

/-- The true order of two actual compact test derivatives is preserved. -/
theorem dTest_dTest_eq_realHessian {n : ℕ} {U : Opens (ComplexModel n)}
    (φ : 𝓓(U, ℝ)) (a b : Fin (n * 2)) (x : ComplexModel n) :
    dTest (realBasis n b) (dTest (realBasis n a) φ) x =
      realHessian φ x (realBasis n b) (realBasis n a) := by
  rw [dTest_apply]
  have hfield : (dTest (realBasis n a) φ : ComplexModel n → ℝ) = dFun (realBasis n a) φ :=
    funext (dTest_apply (realBasis n a) φ)
  rw [hfield]
  exact hessFun_apply φ.contDiff b a x

/-- The actual compact second differential yields its literal coordinate expansion. -/
theorem localDdcTest_eq_coordinate_sum {n q : ℕ} {U : Opens (ComplexModel n)}
    (α : 𝓓(U, RealForm n (2 * q))) (hα : ∀ x, α x ∈ formSpan n q)
    (x : ComplexModel n) :
    castForm (by omega : 2 * q + 1 + 1 = 2 * (q + 1)) (localDdcTestCLM α x) =
      ∑ i, ∑ a, ∑ b,
        (-(1 / (4 * Real.pi)) *
          dTest (realBasis n b) (dTest (realBasis n a) (coeffTest α i)) x) •
          ((wedgeLM q (isOneOne_coeffForm a b) (formBasis n q i) :
            formSpan n (q + 1)) : RealForm n (2 * (q + 1))) := by
  conv_lhs => rw [eq_sum_constFormTest α hα, map_sum, _root_.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [localDdcTestCLM_constForm_apply, castForm_wedgeTo _ _ (by omega)]
  rw [← wedgeTo_comm_of_mem_formSpan (formBasis n q i).property
    (smoothDDC (coeffTest α i) x) (by omega) (by omega)]
  have hφ : ContDiffAt ℝ 2 (coeffTest α i) x :=
    (coeffTest α i).contDiff.contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [smoothDDC_eq_sum hφ]
  simp only [wedgeTo_sum_right, wedgeTo_smul_right]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [dTest_dTest_eq_realHessian]
  have hs : realHessian (coeffTest α i) x (realBasis n b) (realBasis n a) =
      realHessian (coeffTest α i) x (realBasis n a) (realBasis n b) := by
    simpa only [realHessian_eq_fderiv] using
      hφ.isSymmSndFDerivAt (by norm_num) (realBasis n b) (realBasis n a)
  rw [hs, coe_wedgeLM_apply]
  rfl

/-- The genuine scalar adjoint test has exactly the literal full differential density. -/
theorem scalarAdjointTest_apply_eq_actual_density {m : ℕ}
    {U : Opens (ComplexModel (m + 1))}
    (α : 𝓓(U, RealForm (m + 1) (2 * m)))
    (hα : ∀ x, α x ∈ formSpan (m + 1) m) (x : ComplexModel (m + 1)) :
    scalarAdjointTest α x = topDensity
      (castForm (by omega : 2 * m + 1 + 1 = 2 * (m + 1)) (localDdcTestCLM α x)) := by
  have h := congrArg (topDensityLM (m + 1)) (localDdcTest_eq_coordinate_sum α hα x)
  simp only [map_sum, map_smul, smul_eq_mul, topDensityLM_apply] at h
  rw [h]
  simp only [scalarAdjointTest, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A true compact scalar test for the literal full differential is internally produced. -/
theorem exists_full_transpose_test {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (T : 𝓓'(U, ℝ)) (α : 𝓓(U, RealForm (m + 1) (2 * m)))
    (hα : ∀ x, α x ∈ formSpan (m + 1) m) :
    ∃ φ : 𝓓(U, ℝ),
      (∀ x, φ x = topDensity (castForm
        (by omega : 2 * m + 1 + 1 = 2 * (m + 1))
        (extDeriv (fun y => localDc α y) x))) ∧
      (∑ i, ddc (ScalarLeviPositiveCurrent.scalarTopCurrent T)
        (formBasis (m + 1) m i) (coeffTest α i)) = T φ := by
  refine ⟨scalarAdjointTest α, ?_, ddc_scalarTopCurrent_full_test_transpose T α⟩
  intro x
  rw [← localDdcTestCLM_apply]
  exact scalarAdjointTest_apply_eq_actual_density α hα x

end SGPT.Foundations.Analysis.Pending.CompactDdcCoordinateExpansion
