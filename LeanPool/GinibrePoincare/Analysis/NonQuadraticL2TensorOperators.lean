/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticL2TensorOperators.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticL2SigmaFiniteDensity

/-! # Concrete coordinate operators on actual product L²
The proved tensor isometry equivalence transports every bounded coordinate
operator to the full product-measure space, including Lebesgue factors. -/

@[expose] public section
open MeasureTheory
open scoped InnerProductSpace TensorProduct
namespace GinibrePoincare
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]

/-- The actual product tensor equivalence agrees with its original finite
sum realization on every algebraic tensor. -/
theorem l2ProductTensorEquiv_coe (x : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
    l2ProductCompletedTensorEquivSigmaFinite
      (x : UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)) = l2ProductTensorMap x := by
  change l2ProductTensorIsometry.toContinuousLinearMap.fromCompletion
    (x : UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)) = _
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- Genuine operator transport onto the actual product-measure space. -/
def l2ProductTransportOperator (T : (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ] (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)) :
    Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  l2ProductCompletedTensorEquivSigmaFinite.toLinearIsometry.toContinuousLinearMap.comp
    (T.completion.comp
        l2ProductCompletedTensorEquivSigmaFinite.symm.toLinearIsometry.toContinuousLinearMap)

/-- Transport genuinely applies the original operator to every algebraic
product vector. -/
theorem l2ProductTransportOperator_tensor (T : (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ] (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2
    ν))
    (x : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
    l2ProductTransportOperator T (l2ProductTensorMap x) = l2ProductTensorMap (T x) := by
  rw [← l2ProductTensorEquiv_coe x]
  change l2ProductCompletedTensorEquivSigmaFinite
    (T.completion (l2ProductCompletedTensorEquivSigmaFinite.symm
      (l2ProductCompletedTensorEquivSigmaFinite
        (x : UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν))))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, ContinuousLinearMap.completion_apply_coe,
    l2ProductTensorEquiv_coe]

/-- Actual bounded first-coordinate operator on the product L² space. -/
def l2ProductLeftOperator (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  l2ProductTransportOperator (TensorProduct.mapL A (ContinuousLinearMap.id ℂ (Lp ℂ 2 ν)))

/-- Actual bounded second-coordinate operator on the product L² space. -/
def l2ProductRightOperator (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :
    Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  l2ProductTransportOperator (TensorProduct.mapL (ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)) B)

theorem l2ProductLeftOperator_pure (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    l2ProductLeftOperator A (l2ProductVector u v) = l2ProductVector (A u) v := by
  change l2ProductTransportOperator _ (l2ProductTensorMap (u ⊗ₜ[ℂ] v)) = _
  rw [l2ProductTransportOperator_tensor, TensorProduct.mapL_tmul]
  rfl

theorem l2ProductRightOperator_pure (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    l2ProductRightOperator B (l2ProductVector u v) = l2ProductVector u (B v) := by
  change l2ProductTransportOperator _ (l2ProductTensorMap (u ⊗ₜ[ℂ] v)) = _
  rw [l2ProductTransportOperator_tensor, TensorProduct.mapL_tmul]
  rfl

/-- Bounded product-space operators are determined by their actual pure
tensor action, using the proved σ-finite tensor realization. -/
theorem l2ProductOperators_ext_on_pure
    (S T : Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 (μ.prod ν))
    (h : ∀ u : Lp ℂ 2 μ, ∀ v : Lp ℂ 2 ν, S (l2ProductVector u v) = T (l2ProductVector u v)) :
    S = T := by
  apply ContinuousLinearMap.ext
  intro F
  obtain ⟨x, rfl⟩ := l2ProductCompletedTensorEquivSigmaFinite.surjective F
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (S.continuous.comp (l2ProductCompletedTensorEquivSigmaFinite (μ := μ) (ν := ν)).continuous)
      (T.continuous.comp (l2ProductCompletedTensorEquivSigmaFinite (μ := μ) (ν := ν)).continuous)
  | ih x =>
    rw [l2ProductTensorEquiv_coe]
    induction x using TensorProduct.inductionOn with
    | tmul u v => exact h u v
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The concrete coordinate operators commute on the whole product L²
space, not merely on separable test functions. -/
theorem l2ProductLeftRight_commute (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :
    (l2ProductLeftOperator A).comp (l2ProductRightOperator B) =
      (l2ProductRightOperator B).comp (l2ProductLeftOperator A) := by
  apply l2ProductOperators_ext_on_pure
  intro u v
  simp only [ContinuousLinearMap.comp_apply, l2ProductLeftOperator_pure,
      l2ProductRightOperator_pure]

/-- Actual first-coordinate transport preserves composition. -/
theorem l2ProductLeftOperator_comp (A B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    l2ProductLeftOperator (ν := ν) (A.comp B) = (l2ProductLeftOperator A).comp
        (l2ProductLeftOperator B) := by
  apply l2ProductOperators_ext_on_pure
  intro u v
  simp only [ContinuousLinearMap.comp_apply, l2ProductLeftOperator_pure]

/-- Actual second-coordinate transport preserves composition. -/
theorem l2ProductRightOperator_comp (A B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :
    l2ProductRightOperator (μ := μ) (A.comp B) = (l2ProductRightOperator A).comp
        (l2ProductRightOperator B) := by
  apply l2ProductOperators_ext_on_pure
  intro u v
  simp only [ContinuousLinearMap.comp_apply, l2ProductRightOperator_pure]

theorem l2ProductLeftOperator_id :
    l2ProductLeftOperator (ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)) = ContinuousLinearMap.id ℂ (Lp ℂ 2
        (μ.prod ν)) := by
  apply l2ProductOperators_ext_on_pure
  intro u v
  simp only [l2ProductLeftOperator_pure, ContinuousLinearMap.id_apply]

theorem l2ProductRightOperator_id :
    l2ProductRightOperator (ContinuousLinearMap.id ℂ (Lp ℂ 2 ν)) = ContinuousLinearMap.id ℂ (Lp ℂ 2
        (μ.prod ν)) := by
  apply l2ProductOperators_ext_on_pure
  intro u v
  simp only [l2ProductRightOperator_pure, ContinuousLinearMap.id_apply]

/-- Pure product vectors separate points of the actual product Hilbert space. -/
theorem l2Product_inner_ext (F G : Lp ℂ 2 (μ.prod ν))
    (h : ∀ u : Lp ℂ 2 μ, ∀ v : Lp ℂ 2 ν,
      ⟪l2ProductVector u v, F⟫_ℂ = ⟪l2ProductVector u v, G⟫_ℂ) : F = G := by
  apply sub_eq_zero.mp
  apply l2Product_eq_zero_of_inner_pure_tensors_sigmaFinite
  intro u v
  rw [inner_sub_right, h u v, sub_self]

/-- Coordinate transport preserves the genuine Hilbert adjoint. -/
theorem l2ProductLeftOperator_adjoint (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    (l2ProductLeftOperator (ν := ν) A).adjoint = l2ProductLeftOperator A.adjoint := by
  apply l2ProductOperators_ext_on_pure
  intro u v
  apply l2Product_inner_ext
  intro a b
  rw [ContinuousLinearMap.adjoint_inner_right, l2ProductLeftOperator_pure,
    l2ProductLeftOperator_pure, l2ProductVector_inner, l2ProductVector_inner,
    ContinuousLinearMap.adjoint_inner_right]

/-- The second coordinate transport also preserves the Hilbert adjoint. -/
theorem l2ProductRightOperator_adjoint (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :
    (l2ProductRightOperator (μ := μ) B).adjoint = l2ProductRightOperator B.adjoint := by
  apply l2ProductOperators_ext_on_pure
  intro u v
  apply l2Product_inner_ext
  intro a b
  rw [ContinuousLinearMap.adjoint_inner_right, l2ProductRightOperator_pure,
    l2ProductRightOperator_pure, l2ProductVector_inner, l2ProductVector_inner,
    ContinuousLinearMap.adjoint_inner_right]

/-- Operator transport retains its sharp bound through completion. -/
theorem l2ProductTransportOperator_bound
    (T : (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ] (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν))
    (F : Lp ℂ 2 (μ.prod ν)) : ‖l2ProductTransportOperator T F‖ ≤ ‖T‖ * ‖F‖ := by
  obtain ⟨x, rfl⟩ := l2ProductCompletedTensorEquivSigmaFinite.surjective F
  change ‖l2ProductCompletedTensorEquivSigmaFinite
    (T.completion (l2ProductCompletedTensorEquivSigmaFinite.symm
      (l2ProductCompletedTensorEquivSigmaFinite x)))‖ ≤ _
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map]
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (continuous_norm.comp T.completion.continuous)
      (continuous_const.mul continuous_norm)
  | ih x =>
    rw [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact T.le_opNorm x

theorem l2ProductTransportOperator_norm_le
    (T : (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ] (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)) :
    ‖l2ProductTransportOperator T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (l2ProductTransportOperator_bound T)

theorem l2ProductLeftOperator_norm_le (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    ‖l2ProductLeftOperator (ν := ν) A‖ ≤ ‖A‖ := by
  apply (l2ProductTransportOperator_norm_le _).trans
  exact (TensorProduct.norm_mapL_le _ _).trans
    ((mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg A)).trans_eq (mul_one
        _))

theorem l2ProductRightOperator_norm_le (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :
    ‖l2ProductRightOperator (μ := μ) B‖ ≤ ‖B‖ := by
  apply (l2ProductTransportOperator_norm_le _).trans
  exact (TensorProduct.norm_mapL_le _ _).trans
    ((mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (norm_nonneg B)).trans_eq (one_mul
        _))

/-- A self-adjoint coordinate operator remains self-adjoint on the actual product. -/
theorem l2ProductLeftOperator_selfadjoint (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hA : A.adjoint = A) : (l2ProductLeftOperator (ν := ν) A).adjoint = l2ProductLeftOperator A :=
        by
  rw [l2ProductLeftOperator_adjoint, hA]

theorem l2ProductRightOperator_selfadjoint (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hB : B.adjoint = B) : (l2ProductRightOperator (μ := μ) B).adjoint = l2ProductRightOperator B :=
        by
  rw [l2ProductRightOperator_adjoint, hB]

/-- Coordinate transport preserves projection idempotence without restricting the domain. -/
theorem l2ProductLeftOperator_idempotent (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hA : A.comp A = A) :
    (l2ProductLeftOperator (ν := ν) A).comp (l2ProductLeftOperator A) = l2ProductLeftOperator A :=
        by
  rw [← l2ProductLeftOperator_comp, hA]

theorem l2ProductRightOperator_idempotent (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hB : B.comp B = B) :
    (l2ProductRightOperator (μ := μ) B).comp (l2ProductRightOperator B) = l2ProductRightOperator B
        := by
  rw [← l2ProductRightOperator_comp, hB]

end
end GinibrePoincare
