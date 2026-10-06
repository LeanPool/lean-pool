/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSlopeMap

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineSlopeMatrix

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Matrix realization of finite affine best-fit slopes

This module represents the finite-solution best-fit slope endomorphism by a
matrix and constructs its inverse only from an explicit bijectivity proof.
Quantitative good-event estimates and slope-family iteration are separate.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- Matrix of the finite-solution best-fit slope endomorphism. -/
@[expose]
noncomputable def finiteAffineBestFitSlopeMatrix
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) : Mat d :=
  LinearMap.toMatrix' (finiteAffineBestFitSlope a k m hkm)

/-- The slope matrix acts with the same column-vector orientation as the
underlying linear map. -/
@[simp] theorem finiteAffineBestFitSlopeMatrix_apply
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (e : Vec d) :
    matVecMul (finiteAffineBestFitSlopeMatrix a k m hkm) e =
      finiteAffineBestFitSlope a k m hkm e := by
  simpa only [matVecMul, finiteAffineBestFitSlopeMatrix] using!
    LinearMap.toMatrix'_mulVec (finiteAffineBestFitSlope a k m hkm) e

/-- The slope matrix has unit determinant exactly when the slope map is
injective. -/
theorem finiteAffineBestFitSlopeMatrix_isUnit_det_iff_injective
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) :
    IsUnit (finiteAffineBestFitSlopeMatrix a k m hkm).det ↔
      Function.Injective (finiteAffineBestFitSlope a k m hkm) := by
  rw [← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.mulVec_injective_iff_isUnit]
  constructor
  · intro h e e' he
    apply h
    change matVecMul (finiteAffineBestFitSlopeMatrix a k m hkm) e =
      matVecMul (finiteAffineBestFitSlopeMatrix a k m hkm) e'
    simpa only [finiteAffineBestFitSlopeMatrix_apply] using he
  · intro h e e' he
    apply h
    change matVecMul (finiteAffineBestFitSlopeMatrix a k m hkm) e =
      matVecMul (finiteAffineBestFitSlopeMatrix a k m hkm) e' at he
    simpa only [finiteAffineBestFitSlopeMatrix_apply] using he

/-- In finite dimension, the determinant gate is equivalently bijectivity of
the finite-solution best-fit slope map. -/
theorem finiteAffineBestFitSlopeMatrix_isUnit_det_iff_bijective
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) :
    IsUnit (finiteAffineBestFitSlopeMatrix a k m hkm).det ↔
      Function.Bijective (finiteAffineBestFitSlope a k m hkm) := by
  rw [finiteAffineBestFitSlopeMatrix_isUnit_det_iff_injective]
  constructor
  · intro hinj
    exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  · intro hbij
    exact hbij.1

/-- The linear equivalence supplied by a proved bijective best-fit slope map.
This declaration is the first inverse-bearing object in the module. -/
@[expose]
noncomputable def finiteAffineBestFitSlopeEquiv
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m)
    (hbij : Function.Bijective (finiteAffineBestFitSlope a k m hkm)) :
    Vec d ≃ₗ[ℝ] Vec d :=
  LinearEquiv.ofBijective (finiteAffineBestFitSlope a k m hkm) hbij

/-- Inverse linear map of a proved bijective finite-solution best-fit slope
map. -/
@[expose]
noncomputable def finiteAffineBestFitSlopeInverseLinearMap
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m)
    (hbij : Function.Bijective (finiteAffineBestFitSlope a k m hkm)) :
    Vec d →ₗ[ℝ] Vec d :=
  (finiteAffineBestFitSlopeEquiv a k m hkm hbij).symm.toLinearMap

/-- Matrix of the proof-gated inverse slope map. -/
@[expose]
noncomputable def finiteAffineBestFitSlopeInverseMatrix
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m)
    (hbij : Function.Bijective (finiteAffineBestFitSlope a k m hkm)) :
    Mat d :=
  LinearMap.toMatrix'
    (finiteAffineBestFitSlopeInverseLinearMap a k m hkm hbij)

/-- The inverse slope matrix acts as the inverse linear map. -/
@[simp] theorem finiteAffineBestFitSlopeInverseMatrix_apply
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m)
    (hbij : Function.Bijective (finiteAffineBestFitSlope a k m hkm))
    (e : Vec d) :
    matVecMul (finiteAffineBestFitSlopeInverseMatrix a k m hkm hbij) e =
      finiteAffineBestFitSlopeInverseLinearMap a k m hkm hbij e := by
  simpa only [matVecMul, finiteAffineBestFitSlopeInverseMatrix] using!
    LinearMap.toMatrix'_mulVec
      (finiteAffineBestFitSlopeInverseLinearMap a k m hkm hbij) e

/-- Applying the slope map after its proof-gated inverse recovers the slope. -/
@[simp] theorem finiteAffineBestFitSlope_apply_inverseMatrix
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m)
    (hbij : Function.Bijective (finiteAffineBestFitSlope a k m hkm))
    (e : Vec d) :
    finiteAffineBestFitSlope a k m hkm
        (matVecMul
          (finiteAffineBestFitSlopeInverseMatrix a k m hkm hbij) e) =
      e := by
  rw [finiteAffineBestFitSlopeInverseMatrix_apply]
  exact
    (finiteAffineBestFitSlopeEquiv a k m hkm hbij).apply_symm_apply e

/-- The slope matrix times its proof-gated inverse matrix is the identity. -/
@[simp] theorem finiteAffineBestFitSlopeMatrix_mul_inverseMatrix
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m)
    (hbij : Function.Bijective (finiteAffineBestFitSlope a k m hkm)) :
    finiteAffineBestFitSlopeMatrix a k m hkm *
        finiteAffineBestFitSlopeInverseMatrix a k m hkm hbij =
      1 := by
  change LinearMap.toMatrix' (finiteAffineBestFitSlope a k m hkm) *
      LinearMap.toMatrix'
          (finiteAffineBestFitSlopeInverseLinearMap a k m hkm hbij) =
    1
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_one]
  apply congrArg LinearMap.toMatrix'
  apply LinearMap.ext
  intro e
  exact
    (finiteAffineBestFitSlopeEquiv a k m hkm hbij).apply_symm_apply e

/-- The proof-gated inverse matrix times the slope matrix is the identity. -/
@[simp] theorem finiteAffineBestFitSlopeInverseMatrix_mul_matrix
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m)
    (hbij : Function.Bijective (finiteAffineBestFitSlope a k m hkm)) :
    finiteAffineBestFitSlopeInverseMatrix a k m hkm hbij *
        finiteAffineBestFitSlopeMatrix a k m hkm =
      1 := by
  change LinearMap.toMatrix'
        (finiteAffineBestFitSlopeInverseLinearMap a k m hkm hbij) *
      LinearMap.toMatrix' (finiteAffineBestFitSlope a k m hkm) =
    1
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_one]
  apply congrArg LinearMap.toMatrix'
  apply LinearMap.ext
  intro e
  exact
    (finiteAffineBestFitSlopeEquiv a k m hkm hbij).symm_apply_apply e

/-- A proof-gated inverse slope matrix also has unit determinant. -/
theorem finiteAffineBestFitSlopeInverseMatrix_isUnit_det
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m)
    (hbij : Function.Bijective (finiteAffineBestFitSlope a k m hkm)) :
    IsUnit (finiteAffineBestFitSlopeInverseMatrix a k m hkm hbij).det := by
  have hinj : Function.Injective
      (finiteAffineBestFitSlopeInverseMatrix a k m hkm hbij).mulVec := by
    intro e e' he
    have hslope := congrArg (finiteAffineBestFitSlope a k m hkm) he
    change finiteAffineBestFitSlope a k m hkm
        (matVecMul
          (finiteAffineBestFitSlopeInverseMatrix a k m hkm hbij) e) =
      finiteAffineBestFitSlope a k m hkm
        (matVecMul
          (finiteAffineBestFitSlopeInverseMatrix a k m hkm hbij) e') at hslope
    simpa only [finiteAffineBestFitSlope_apply_inverseMatrix] using hslope
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)

end

end HighContrast
end HCPolySupport
