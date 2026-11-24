/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.CoordinateDensityGeometry

/-!
# Pullback naturality of coordinate wedge powers

For a real-linear map `L : ComplexModel m →L[ℝ] ComplexModel n`, pulling back
real continuous alternating forms along `L` commutes with the genuine exterior
product `coordinateWedge` and hence with the exterior powers
`coordinateWedgePower`.

We also package the standard interleaved real frame `e₀, I e₀, e₁, I e₁, ...`
as a real basis `coordinateRealBasis n`.  Since a top-degree alternating form is
a multiple of the basis determinant, pulling back along a real endomorphism `L`
multiplies the top-power density `actualTopPowerDensity` by `det L`.
-/

@[expose] public section

noncomputable section

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {m n : ℕ}

/-- Explicit alternatization formula for the unreindexed exterior product. -/
theorem coordinateWedgeSum_apply {p q : ℕ}
    (A : (ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ)
    (B : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) (v : Fin p ⊕ Fin q → ComplexModel n) :
    coordinateWedgeSum A B v = (p.factorial * q.factorial : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin p ⊕ Fin q),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * (A (v ∘ σ ∘ Sum.inl) * B (v ∘ σ ∘ Sum.inr)) := by
  unfold coordinateWedgeSum
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  congr 1
  simp only [ContinuousMultilinearMap.alternatization, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    ContinuousAlternatingMap.coe_mk, _root_.sum_apply,
    _root_.smul_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.sum_congr rfl fun σ _ => rfl

/-- The exterior product evaluates through its unreindexed version. -/
theorem coordinateWedge_apply {p q : ℕ}
    (A : (ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ)
    (B : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) (v : Fin (p + q) → ComplexModel n) :
    coordinateWedge A B v = coordinateWedgeSum A B (v ∘ finSumFinEquiv) := rfl

/-- Pullback along a real-linear map commutes with the exterior product. -/
theorem coordinateWedge_compContinuousLinearMap {p q : ℕ}
    (L : ComplexModel m →L[ℝ] ComplexModel n)
    (A : (ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ)
    (B : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :
    (coordinateWedge A B).compContinuousLinearMap L =
      coordinateWedge (A.compContinuousLinearMap L) (B.compContinuousLinearMap L) := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, coordinateWedge_apply,
    coordinateWedgeSum_apply]
  rfl

/-- Evaluating a continuous alternating form transported along an equality of
the number of arguments amounts to reindexing the arguments by `Fin.cast`. -/
theorem cast_continuousAlternatingMap_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] {a b : ℕ} (h : a = b)
    (hT : (E [⋀^Fin a]→L[ℝ] ℝ) = (E [⋀^Fin b]→L[ℝ] ℝ)) (f : E [⋀^Fin a]→L[ℝ] ℝ)
    (v : Fin b → E) :
    cast hT f v = f (v ∘ Fin.cast h) := by
  subst h
  rfl

/-- Unfolding the successor step of `coordinateWedgePower` at an evaluation. -/
theorem coordinateWedgePower_add_two_apply (A : CoordinateRealTwoForm n) (k : ℕ)
    (v : Fin ((k + 2) * 2) → ComplexModel n) :
    coordinateWedgePower A (k + 2) v =
      coordinateWedge (coordinateWedgePower A (k + 1)) A
        (v ∘ Fin.cast (show (k + 1) * 2 + 2 = (k + 2) * 2 by ring)) := by
  rw [coordinateWedgePower.eq_3, eq_mpr_eq_cast, eq_mp_eq_cast, cast_cast]
  exact cast_continuousAlternatingMap_apply _ _ _ _

/-- Pullback along a real-linear map commutes with exterior powers. -/
theorem coordinateWedgePower_compContinuousLinearMap (A : CoordinateRealTwoForm n)
    (L : ComplexModel m →L[ℝ] ComplexModel n) (k : ℕ) :
    coordinateWedgePower (A.compContinuousLinearMap L) k =
      (coordinateWedgePower A k).compContinuousLinearMap L := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => ext v; rfl
    | 1, _ => rfl
    | k + 2, ih =>
      ext v
      rw [coordinateWedgePower_add_two_apply, ih (k + 1) (by omega),
        ContinuousAlternatingMap.compContinuousLinearMap_apply,
        coordinateWedgePower_add_two_apply, ← coordinateWedge_compContinuousLinearMap]
      rfl

variable (n) in
/-- The real basis `e₀, I e₀, e₁, I e₁, ...` of the standard complex model. -/
def coordinateRealBasis : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n) :=
  (Complex.basisOneI.smulTower (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).reindex
    ((Equiv.prodComm _ _).trans finProdFinEquiv)

/-- The basis `coordinateRealBasis n` is the standard frame `coordinateRealFrame`. -/
@[simp] theorem coe_coordinateRealBasis :
    ⇑(coordinateRealBasis n) = coordinateRealFrame := by
  funext i
  obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective i
  simp only [coordinateRealBasis, Module.Basis.reindex_apply, Equiv.symm_trans_apply,
    Equiv.symm_apply_apply, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
    Module.Basis.smulTower_apply, Complex.coe_basisOneI, coordinateRealFrame]
  fin_cases k
  · simp [coordinateVector]
  · simp [coordinateVector]

/-- Pullback of the genuine top power under a real-linear endomorphism multiplies
its standard-frame density by the real determinant. -/
theorem actualTopPowerDensity_compContinuousLinearMap (A : CoordinateRealTwoForm n)
    (L : ComplexModel n →L[ℝ] ComplexModel n) :
    actualTopPowerDensity (A.compContinuousLinearMap L) =
      LinearMap.det (L : ComplexModel n →ₗ[ℝ] ComplexModel n) * actualTopPowerDensity A := by
  set b := coordinateRealBasis n
  have hΦ := (coordinateWedgePower A n).toAlternatingMap.eq_smul_basis_det b
  unfold actualTopPowerDensity
  rw [coordinateWedgePower_compContinuousLinearMap,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, ← coe_coordinateRealBasis]
  change (coordinateWedgePower A n).toAlternatingMap (L ∘ b) =
    _ * (coordinateWedgePower A n).toAlternatingMap b
  rw [hΦ]
  simp only [_root_.smul_apply, smul_eq_mul, Module.Basis.det_self, mul_one]
  rw [show (⇑L ∘ ⇑b) = ⇑(L : ComplexModel n →ₗ[ℝ] ComplexModel n) ∘ ⇑b from rfl,
    Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  ring

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
