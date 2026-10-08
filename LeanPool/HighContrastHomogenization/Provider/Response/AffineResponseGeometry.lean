/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineGeometry
public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffAdaptedMean
public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffBasic
public import LeanPool.HighContrastHomogenization.Provider.Response.DomainBridge

/-!
# High-contrast homogenization: Provider.Response.AffineResponseGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Response averages on an adapted cell

The inverse grid map identifies an adapted cell with its centered reference
cube.  The determinant occurring in the integral change of variables also
occurs in the cell volume, so normalized scalar and vector averages have no
Jacobian factor.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

variable {d : ℕ} {q : Mat d}

/-- The inverse grid map sends an adapted cell to its centered reference cube. -/
theorem matImage_inv_adaptedCell_eq_centeredCube (hq : q.PosDef) (t : ℤ) :
    matImage q⁻¹ (adaptedCell q t) = centeredCube d t := by
  have hdet : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  rw [matImage_adaptedCell, Matrix.nonsing_inv_mul q hdet]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [matVecMul_one] using hy
  · intro hx
    exact ⟨x, hx, matVecMul_one x⟩

/-- An adapted cell is literally the grid image of its reference origin
cube. -/
theorem adaptedCell_eq_matVecMul_image_openCubeSet (q : Mat d) (t : ℤ) :
    adaptedCell q t = matVecMul q '' openCubeSet (originCube d t) := by
  rfl

/-- Pulling the adapted cutoff back by its invertible grid preserves compact
support. -/
theorem adaptedPreYoungCutoff_pullback_hasCompactSupport [NeZero d]
    (hq : q.PosDef) (t : ℤ) :
    HasCompactSupport
      (fun y ↦ Response.adaptedPreYoungCutoff q hq t (matVecMul q y)) := by
  have hdet : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  let e : Vec d ≃ₜ Vec d :=
    { toFun := matVecMul q
      invFun := matVecMul q⁻¹
      left_inv := fun x ↦ by
        rw [matVecMul_mul, Matrix.nonsing_inv_mul q hdet, matVecMul_one]
      right_inv := fun x ↦ by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv q hdet, matVecMul_one]
      continuous_toFun := continuous_matVecMul q
      continuous_invFun := continuous_matVecMul q⁻¹ }
  change HasCompactSupport (Response.adaptedPreYoungCutoff q hq t ∘ e)
  simpa [e, Function.comp_def] using
    (Response.adaptedPreYoungCutoff_hasCompactSupport hq t).comp_homeomorph e

/-- The support of the pulled-back adapted cutoff lies in the reference
origin cube. -/
theorem adaptedPreYoungCutoff_pullback_tsupport_subset_openCubeSet [NeZero d]
    (hq : q.PosDef) (t : ℤ) :
    tsupport (fun y ↦ Response.adaptedPreYoungCutoff q hq t (matVecMul q y)) ⊆
      openCubeSet (originCube d t) := by
  have hdet : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  let e : Vec d ≃ₜ Vec d :=
    { toFun := matVecMul q
      invFun := matVecMul q⁻¹
      left_inv := fun x ↦ by
        rw [matVecMul_mul, Matrix.nonsing_inv_mul q hdet, matVecMul_one]
      right_inv := fun x ↦ by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv q hdet, matVecMul_one]
      continuous_toFun := continuous_matVecMul q
      continuous_invFun := continuous_matVecMul q⁻¹ }
  intro y hy
  have hy' : matVecMul q y ∈ tsupport (Response.adaptedPreYoungCutoff q hq t) := by
    rw [show (fun z ↦ Response.adaptedPreYoungCutoff q hq t (matVecMul q z)) =
      Response.adaptedPreYoungCutoff q hq t ∘ e by rfl,
      tsupport_comp_eq_preimage (Response.adaptedPreYoungCutoff q hq t) e] at hy
    exact hy
  have himage := Response.adaptedPreYoungCutoff_tsupport_subset hq t hy'
  rw [adaptedCell_eq_matVecMul_image_openCubeSet] at himage
  obtain ⟨z, hz, hzy⟩ := himage
  have hzy' : z = y := (Matrix.mulVec_injective_of_isUnit hq.isUnit) hzy
  simpa [hzy'] using hz

/-- A normalized scalar average on an adapted domain is the cube average of
the pullback by the grid map. -/
theorem average_adaptedDomain_eq_cubeAverage_pullback
    (hq : q.PosDef) (t : ℤ) (f : Vec d → ℝ) :
    Book.Ch02.average (Response.adaptedDomain hq t) f =
      cubeAverage (originCube d t) (fun y => f (matVecMul q y)) := by
  have hdet : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  change volumeAverage (adaptedCell q t) f = _
  change volumeAverage (matImage q (centeredCube d t)) f = _
  rw [volumeAverage_matImage hdet]
  · rw [centeredCube,
      ← volumeAverage_cubeSet_originCube_eq_openCubeSet,
      volumeAverage_cubeSet_eq_cubeAverage]
  · exact (isOpen_openCubeSet (originCube d t)).measurableSet

end

end HighContrast
end HCPolySupport
