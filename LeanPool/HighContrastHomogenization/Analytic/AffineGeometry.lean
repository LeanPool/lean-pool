/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.DirichletDomain
public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Definitions
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# High-contrast homogenization: Analytic.AffineGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine geometry and coefficient pullback

An invertible matrix sends a coefficient field to its divergence-form
pullback, sends the corresponding domain to a linear image, and rescales both
volume and unnormalized integrals by its determinant.  The determinant cancels
from normalized averages.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The divergence-form coefficient after the invertible change of variables
`x = L y`. -/
@[expose]
def affineCoefficient (L : Mat d) (_hL : IsUnit L.det) (a : CoeffField d) :
    CoeffField d :=
  fun y => L⁻¹ * a (matVecMul L y) * matTranspose L⁻¹

@[simp] theorem affineCoefficient_apply (L : Mat d) (hL : IsUnit L.det)
    (a : CoeffField d) (y : Vec d) :
    affineCoefficient L hL a y = L⁻¹ * a (matVecMul L y) * matTranspose L⁻¹ :=
  rfl

/-- Transposition commutes with the congruence used by the affine coefficient. -/
theorem matTranspose_affineCoefficient_apply (L : Mat d) (hL : IsUnit L.det)
    (a : CoeffField d) (y : Vec d) :
    matTranspose (affineCoefficient L hL a y) =
      L⁻¹ * matTranspose (a (matVecMul L y)) * matTranspose L⁻¹ := by
  rw [affineCoefficient_apply]
  change Matrix.transpose (L⁻¹ * a (matVecMul L y) * Matrix.transpose L⁻¹) =
    L⁻¹ * Matrix.transpose (a (matVecMul L y)) * Matrix.transpose L⁻¹
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc]

/-- The symmetric part of an affine coefficient is the congruence of the
symmetric part of the original coefficient. -/
theorem symmPart_affineCoefficient_apply (L : Mat d) (hL : IsUnit L.det)
    (a : CoeffField d) (y : Vec d) :
    symmPart (affineCoefficient L hL a y) =
      L⁻¹ * symmPart (a (matVecMul L y)) * matTranspose L⁻¹ := by
  rw [symmPart_eq_smul_add_transpose, symmPart_eq_smul_add_transpose,
    matTranspose_affineCoefficient_apply]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- The skew part of an affine coefficient is the congruence of the skew part
of the original coefficient. -/
theorem skewPart_affineCoefficient_apply (L : Mat d) (hL : IsUnit L.det)
    (a : CoeffField d) (y : Vec d) :
    skewPart (affineCoefficient L hL a y) =
      L⁻¹ * skewPart (a (matVecMul L y)) * matTranspose L⁻¹ := by
  rw [skewPart_eq_smul_sub_transpose, skewPart_eq_smul_sub_transpose,
    matTranspose_affineCoefficient_apply]
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- The right inverse-transpose factor cancels the transformed gradient. -/
theorem affineCoefficient_mul_transpose {L : Mat d} (hL : IsUnit L.det)
    (a : CoeffField d) (y : Vec d) :
    affineCoefficient L hL a y * matTranspose L = L⁻¹ * a (matVecMul L y) := by
  have hLT : IsUnit (matTranspose L).det := by
    simpa [matTranspose] using Matrix.isUnit_det_transpose L hL
  have hinvT : matTranspose L⁻¹ = (matTranspose L)⁻¹ := by
    simpa [matTranspose] using (Matrix.transpose_nonsing_inv (A := L))
  rw [affineCoefficient_apply, hinvT, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hLT, Matrix.mul_one]

/-- Fluxes transform contravariantly under the affine coefficient pullback. -/
theorem affineCoefficient_flux {L : Mat d} (hL : IsUnit L.det)
    (a : CoeffField d) (y ξ : Vec d) :
    matVecMul (affineCoefficient L hL a y) (matVecMul (matTranspose L) ξ) =
      matVecMul L⁻¹ (matVecMul (a (matVecMul L y)) ξ) := by
  rw [matVecMul_mul, affineCoefficient_mul_transpose hL, matVecMul_mul]

/-- The potential--flux pairing is invariant under the dual affine actions. -/
theorem affineCoefficient_energy {L : Mat d} (hL : IsUnit L.det)
    (a : CoeffField d) (y ξ : Vec d) :
    vecDot (matVecMul (matTranspose L) ξ)
        (matVecMul (affineCoefficient L hL a y) (matVecMul (matTranspose L) ξ)) =
      vecDot ξ (matVecMul (a (matVecMul L y)) ξ) := by
  rw [affineCoefficient_flux hL]
  calc
    vecDot (matVecMul (matTranspose L) ξ)
        (matVecMul L⁻¹ (matVecMul (a (matVecMul L y)) ξ)) =
        vecDot (matVecMul L⁻¹ (matVecMul (a (matVecMul L y)) ξ))
          (matVecMul (matTranspose L) ξ) := vecDot_comm _ _
    _ = vecDot
          (matVecMul L (matVecMul L⁻¹ (matVecMul (a (matVecMul L y)) ξ))) ξ :=
        vecDot_matVecMul_transpose _ _ L
    _ = vecDot (matVecMul (a (matVecMul L y)) ξ) ξ := by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
    _ = vecDot ξ (matVecMul (a (matVecMul L y)) ξ) := vecDot_comm _ _

/-! ## Linear images and volume -/

/-- Linear images compose by matrix multiplication. -/
theorem matImage_matImage (M N : Mat d) (U : Set (Vec d)) :
    matImage M (matImage N U) = matImage (M * N) U := by
  simp only [matImage, Set.image_image, ← matVecMul_mul]

/-- Pulling a domain back by `L⁻¹` is the same as taking its preimage by `L`. -/
theorem matImage_inv_eq_preimage {L : Mat d} (hL : IsUnit L.det)
    (U : Set (Vec d)) :
    matImage L⁻¹ U = (fun y : Vec d => matVecMul L y) ⁻¹' U := by
  rw [matImage_eq_preimage (Matrix.isUnit_nonsing_inv_det L hL),
    Matrix.nonsing_inv_nonsing_inv L hL]

/-- An invertible linear image rescales volume by the absolute determinant. -/
theorem volume_matImage (L : Mat d) (U : Set (Vec d)) :
    volume (matImage L U) = ENNReal.ofReal |L.det| * volume U := by
  have hvol := MeasureTheory.Measure.addHaar_image_linearMap
    (μ := (volume : Measure (Vec d))) (Matrix.mulVecLin L) U
  have hdet : LinearMap.det (Matrix.mulVecLin L) = L.det := by
    rw [← Matrix.toLin'_apply']
    exact LinearMap.det_toLin' L
  simpa only [matImage, hdet] using! hvol

/-- The real-valued volume obeys the same determinant scaling. -/
theorem volume_matImage_toReal (L : Mat d) (U : Set (Vec d)) :
    (volume (matImage L U)).toReal = |L.det| * (volume U).toReal := by
  rw [volume_matImage, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg L.det)]

/-- The restricted source volume pushed through an invertible matrix is the
restricted target volume with the inverse Jacobian density. -/
theorem map_restrict_volume_matVecMul {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) :
    Measure.map (matVecMul L) (volume.restrict U) =
      ENNReal.ofReal (|L.det|⁻¹) • volume.restrict (matImage L U) := by
  have hf : Measurable (matVecMul L) := (continuous_matVecMul L).measurable
  have himage : MeasurableSet (matImage L U) := by
    rw [matImage_eq_preimage hL]
    exact hU.preimage (continuous_matVecMul L⁻¹).measurable
  have hpre : (fun x : Vec d => matVecMul L x) ⁻¹' matImage L U = U := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (Matrix.mulVec_injective_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det L).mpr hL) hxy).symm ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := L) hL.ne_zero
  have hfun : (matVecMul L : Vec d → Vec d) = Matrix.toLin' L := by
    funext x
    change Matrix.mulVec L x = Matrix.toLin' L x
    exact (Matrix.toLin'_apply L x).symm
  have hmap' : Measure.map (matVecMul L) volume =
      ENNReal.ofReal (|L.det|⁻¹) • volume := by
    rw [hfun]
    simpa only [abs_inv] using hmap
  calc
    Measure.map (matVecMul L) (volume.restrict U) =
        (Measure.map (matVecMul L) volume).restrict (matImage L U) := by
      rw [Measure.restrict_map hf himage, hpre]
    _ = (ENNReal.ofReal (|L.det|⁻¹) • volume).restrict (matImage L U) := by
      rw [hmap']
    _ = ENNReal.ofReal (|L.det|⁻¹) • volume.restrict (matImage L U) := by
      rw [Measure.restrict_smul]

/-- Bochner integration over a linear image carries the determinant Jacobian. -/
theorem setIntegral_matImage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : Mat d} (hL : IsUnit L.det) {U : Set (Vec d)} (hU : MeasurableSet U)
    (f : Vec d → F) :
    (∫ x in matImage L U, f x ∂volume) =
      |L.det| • ∫ y in U, f (matVecMul L y) ∂volume := by
  let T : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  have hTdet : T.det = L.det := by
    dsimp [T]
    rw [← Matrix.toLin'_apply']
    exact LinearMap.det_toLin' L
  have hderiv : ∀ x ∈ U,
      HasFDerivWithinAt (matVecMul L) T U x := by
    intro x _hx
    exact (T.hasFDerivAt.congr_of_eventuallyEq (by
      filter_upwards with z
      rfl)).hasFDerivWithinAt
  have hinj : Set.InjOn (matVecMul L) U :=
    (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det L).mpr hL)).injOn
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume) (s := U) (f := matVecMul L) (f' := fun _ => T)
    hU hderiv hinj f
  unfold matImage
  rw [hchange]
  simp_rw [hTdet]
  rw [integral_smul]

/-- Normalized scalar averages are unchanged after affine pullback. -/
theorem volumeAverage_matImage {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (f : Vec d → ℝ) :
    volumeAverage (matImage L U) f =
      volumeAverage U (fun y => f (matVecMul L y)) := by
  have hdet : |L.det| ≠ 0 := abs_ne_zero.mpr hL.ne_zero
  unfold volumeAverage
  rw [volume_matImage_toReal, setIntegral_matImage hL hU]
  simp only [smul_eq_mul]
  field_simp [hdet]

/-- A matrix image sends an adapted cell to the cell with the multiplied grid. -/
theorem matImage_adaptedCell (M q : Mat d) (j : ℤ) :
    matImage M (adaptedCell q j) = adaptedCell (M * q) j := by
  simp only [matImage, adaptedCell, Set.image_image, ← matVecMul_mul]

end

end HighContrast
end HCPolySupport
