/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.XiaoComplexDifferential
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ConstantFormProducts

/-!
# Actual exterior products of arbitrary degree smooth forms

The pointwise product is the existing normalized alternating exterior product.
Its finite-dimensional bilinear map produces actual smooth coefficient fields,
and its real-linear naturality gives the actual tensor transformation law.
-/

@[expose] public section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoComplexProducts

open FirstPass FirstPass.MongeAmpere ProductTestForms ConstantFormProducts
  StronglyPositiveForms LocalProductCurrents ClosedProductCurrents XiaoComplexDifferential

noncomputable section

variable {n p q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The existing exterior product as a continuous bilinear map in any degrees. -/
def exteriorProductCLM (n p q : ℕ) :
    RealForm n p →L[ℝ] RealForm n q →L[ℝ] RealForm n (p + q) :=
  haveI := realForm_finiteDimensional (n := n) p
  haveI := realForm_finiteDimensional (n := n) q
  LinearMap.toContinuousLinearMap
    { toFun := fun A => LinearMap.toContinuousLinearMap (wedgeToBilin n rfl A)
      map_add' := fun A A' => by
        ext B : 1
        simp only [map_add]
      map_smul' := fun c A => by
        ext B : 1
        simp only [map_smul, RingHom.id_apply] }

@[simp] theorem exteriorProductCLM_apply (A : RealForm n p) (B : RealForm n q) :
    exteriorProductCLM n p q A B = coordinateWedge A B := rfl

/-- Smooth tensor fields have an actual smooth exterior product in any degrees. -/
theorem contDiffOn_exteriorProduct {U : Set (ComplexModel n)}
    {A : ComplexModel n → RealForm n p} {B : ComplexModel n → RealForm n q}
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun z => coordinateWedge (A z) (B z)) U :=
  (((exteriorProductCLM n p q).contDiff.comp_contDiffOn hA).clm_apply hB).congr
    fun _ _ => rfl

/-- The genuine global exterior product, without a restriction on either degree. -/
def exteriorProduct (A : SmoothRealForm n M p) (B : SmoothRealForm n M q) :
    SmoothRealForm n M (p + q) where
  coeff e z := coordinateWedge (A.coeff e z) (B.coeff e z)
  smooth e := contDiffOn_exteriorProduct (A.smooth e) (B.smooth e)
  compatible := by
    intro e f z hz v
    have hA : A.coeff e z = (A.coeff f (chartTransition e f z)).compContinuousLinearMap
        (chartTransitionDerivative e f z) := by
      ext u
      exact A.compatible e f z hz u
    have hB : B.coeff e z = (B.coeff f (chartTransition e f z)).compContinuousLinearMap
        (chartTransitionDerivative e f z) := by
      ext u
      exact B.compatible e f z hz u
    rw [hA, hB, ← coordinateWedge_compContinuousLinearMap]
    rfl

@[simp] theorem exteriorProduct_coeff (A : SmoothRealForm n M p) (B : SmoothRealForm n M q)
    (e : ComplexChart n M) (z : ComplexModel n) :
    (exteriorProduct A B).coeff e z = coordinateWedge (A.coeff e z) (B.coeff e z) := rfl

/-- The actual global exterior product as a bilinear map. -/
def exteriorProductLM :
    SmoothRealForm n M p →ₗ[ℝ] SmoothRealForm n M q →ₗ[ℝ] SmoothRealForm n M (p + q) :=
  LinearMap.mk₂ ℝ exteriorProduct
    (fun A A' B => smoothRealForm_ext fun e z =>
      coordinateWedge_add_left (A.coeff e z) (A'.coeff e z) (B.coeff e z))
    (fun c A B => smoothRealForm_ext fun e z =>
      coordinateWedge_smul_left c (A.coeff e z) (B.coeff e z))
    (fun A B B' => smoothRealForm_ext fun e z =>
      coordinateWedge_add_right (A.coeff e z) (B.coeff e z) (B'.coeff e z))
    (fun c A B => smoothRealForm_ext fun e z =>
      coordinateWedge_smul_right c (A.coeff e z) (B.coeff e z))

/-- The generic product has exactly the existing two-form product coefficients. -/
theorem exteriorProduct_eq_wedgeTwo (A : SmoothRealForm n M p) (B : SmoothRealForm n M 2) :
    exteriorProduct A B = wedgeTwo A B := smoothRealForm_ext fun _ _ => rfl

/-- The actual complex structure commutes with the actual global exterior product. -/
theorem complexTwist_exteriorProduct (A : SmoothRealForm n M p) (B : SmoothRealForm n M q) :
    complexTwist (exteriorProduct A B) = exteriorProduct (complexTwist A) (complexTwist B) :=
  smoothRealForm_ext fun e z => coordinateWedge_compContinuousLinearMap
    (modelComplexStructure n) (A.coeff e z) (B.coeff e z)

/-- Actual real `(q,q)` coefficient tensors are geometrically complex invariant. -/
theorem complexTwist_geometricallyEq_of_formSpan (G : SmoothRealForm n M (2 * q))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ formSpan n q) :
    (complexTwist G).GeometricallyEq G := by
  intro e z hz
  change (G.coeff e z).compContinuousLinearMap (modelComplexStructure n) = G.coeff e z
  exact formSpan_le_jInvariant q (hG e z hz)

/-- Strong positivity of actual chart tensors supplies complex invariance. -/
theorem complexTwist_geometricallyEq_of_stronglyPositive (G : SmoothRealForm n M (2 * q))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ spCone q) :
    (complexTwist G).GeometricallyEq G :=
  complexTwist_geometricallyEq_of_formSpan G fun e z hz =>
    mem_formSpan_of_mem_spCone (hG e z hz)

end

end SGPT.Foundations.Analysis.Pending.XiaoComplexProducts
