/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CorrectorDecayRestrictionComposition
public import LeanPool.HighContrastHomogenization.Analytic.AffineFractionalNorm
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneySquareWeights

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.AffineNegOneTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The distortion of the normalized `H¹` test norm under `x = L y`. -/
@[expose]
noncomputable def h1AffineFactor (L : Mat d) : ℝ :=
  max (|L.det| ^ ((2 : ℝ) / (d : ℝ))) (‖matTranspose L‖ ^ 2)

theorem h1AffineFactor_pos {L : Mat d}
    (hL : IsUnit L.det) : 0 < h1AffineFactor L := by
  unfold h1AffineFactor
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos (abs_pos.mpr hL.ne_zero) _)
    (le_max_left _ _)

private theorem h1_value_comp_matVecMul
    {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hU0 : volume U ≠ 0)
    (psi : Vec d → Vec d) :
    volume U ^ (-(2 : ℝ) / (d : ℝ)) *
          eVolumeAverage U
            (fun y ↦ ENNReal.ofReal (vecNormSq (psi (matVecMul L y)))) =
      ENNReal.ofReal (|L.det| ^ ((2 : ℝ) / (d : ℝ))) *
        (volume (matImage L U) ^ (-(2 : ℝ) / (d : ℝ)) *
          eVolumeAverage (matImage L U)
            (fun x ↦ ENNReal.ofReal (vecNormSq (psi x)))) := by
  have hLinv : IsUnit (L⁻¹).det := Matrix.isUnit_nonsing_inv_det L hL
  have hV : MeasurableSet (matImage L U) := measurableSet_matImage hL hU
  have hV0 : volume (matImage L U) ≠ 0 := volume_matImage_ne_zero hL hU0
  have hraw := l2Term_matImage hLinv hV hV0 (1 : ℝ)
    (fun y ↦ psi (matVecMul L y))
  have hinvImage : matImage L⁻¹ (matImage L U) = U :=
    matImage_inv_matImage hL U
  have hcompEnergy :
      (fun y : Vec d ↦ ENNReal.ofReal
        (vecNormSq (psi (matVecMul L (matVecMul L⁻¹ y))))) =
        fun y ↦ ENNReal.ofReal (vecNormSq (psi y)) := by
    funext y
    rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
  have hdet : |(L⁻¹).det| ^ (-(2 * (1 : ℝ)) / (d : ℝ)) =
      |L.det| ^ ((2 : ℝ) / (d : ℝ)) := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv,
      Real.inv_rpow (abs_nonneg L.det)]
    ring_nf
    rw [Real.rpow_neg (abs_nonneg L.det), inv_inv]
  rw [hinvImage, hcompEnergy, hdet] at hraw
  norm_num at hraw ⊢
  exact hraw

private theorem h1_gradient_comp_matVecMul_le
    {L : Mat d} (hL : IsUnit L.det) {U : Set (Vec d)}
    (hU : MeasurableSet U) (psi : Vec d → Vec d)
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) :
    eVolumeAverage U (fun y ↦ ENNReal.ofReal
        (∑ j, vecNormSq
          (smoothGrad (fun z ↦ psi (matVecMul L z) j) y))) ≤
      ENNReal.ofReal (‖matTranspose L‖ ^ 2) *
        eVolumeAverage (matImage L U) (fun x ↦ ENNReal.ofReal
          (∑ j, vecNormSq (smoothGrad (fun z ↦ psi z j) x))) := by
  have hpoint : ∀ y : Vec d,
      (∑ j, vecNormSq
          (smoothGrad (fun z ↦ psi (matVecMul L z) j) y)) ≤
        ‖matTranspose L‖ ^ 2 *
          (∑ j, vecNormSq (smoothGrad (fun z ↦ psi z j) (matVecMul L y))) := by
    intro y
    calc
      _ = ∑ j, vecNormSq
          (matVecMul (matTranspose L)
            (smoothGrad (fun z ↦ psi z j) (matVecMul L y))) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [smoothGrad_comp_matVecMul L (contDiff_pi.mp hpsi j)]
      _ ≤ ∑ j, ‖matTranspose L‖ ^ 2 *
          vecNormSq (smoothGrad (fun z ↦ psi z j) (matVecMul L y)) := by
        exact Finset.sum_le_sum fun j _hj ↦
          vecNormSq_matVecMul_le (matTranspose L)
            (smoothGrad (fun z ↦ psi z j) (matVecMul L y))
      _ = ‖matTranspose L‖ ^ 2 *
          (∑ j, vecNormSq (smoothGrad (fun z ↦ psi z j) (matVecMul L y))) := by
        rw [Finset.mul_sum]
  have havg : eVolumeAverage U (fun y ↦ ENNReal.ofReal
        (∑ j, vecNormSq
          (smoothGrad (fun z ↦ psi (matVecMul L z) j) y))) ≤
      ENNReal.ofReal (‖matTranspose L‖ ^ 2) *
        eVolumeAverage U (fun y ↦ ENNReal.ofReal
          (∑ j, vecNormSq
            (smoothGrad (fun z ↦ psi z j) (matVecMul L y)))) := by
    refine eVolumeAverage_le_const_mul U ENNReal.ofReal_ne_top fun y ↦ ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg ‖matTranspose L‖)]
    exact ENNReal.ofReal_le_ofReal (hpoint y)
  have hchange := eVolumeAverage_matImage hL hU
    (fun x ↦ ENNReal.ofReal
      (∑ j, vecNormSq (smoothGrad (fun z ↦ psi z j) x)))
  rw [hchange]
  exact havg

/-- Pulling an image-domain test back by `L` costs the explicit normalized
`H¹` affine factor. -/
theorem h1NormSq_comp_matVecMul_le
    {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hU0 : volume U ≠ 0)
    (psi : Vec d → Vec d) (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) :
    h1NormSq U (fun y ↦ psi (matVecMul L y)) ≤
      ENNReal.ofReal (h1AffineFactor L) *
        h1NormSq (matImage L U) psi := by
  have hvalue := h1_value_comp_matVecMul hL hU hU0 psi
  have hgradient := h1_gradient_comp_matVecMul_le hL hU psi hpsi
  unfold h1NormSq
  rw [mul_add]
  refine add_le_add ?_ ?_
  · rw [hvalue]
    have hcoef : ENNReal.ofReal (|L.det| ^ ((2 : ℝ) / (d : ℝ))) ≤
        ENNReal.ofReal (h1AffineFactor L) :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    exact (by
      simpa only [mul_comm] using
        (mul_le_mul_right hcoef
          (volume (matImage L U) ^ (-(2 : ℝ) / (d : ℝ)) *
            eVolumeAverage (matImage L U)
              (fun x ↦ ENNReal.ofReal (vecNormSq (psi x))))))
  · exact hgradient.trans
      (by
        have hcoef : ENNReal.ofReal (‖matTranspose L‖ ^ 2) ≤
            ENNReal.ofReal (h1AffineFactor L) :=
          ENNReal.ofReal_le_ofReal (le_max_right _ _)
        simpa only [mul_comm] using
          (mul_le_mul_right hcoef
            (eVolumeAverage (matImage L U) (fun x ↦ ENNReal.ofReal
              (∑ j, vecNormSq (smoothGrad (fun y ↦ psi y j) x))))))

/-- The normalized negative-one norm under an invertible affine image. -/
theorem negOneNorm_matImage_le
    {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hU0 : volume U ≠ 0)
    (F : Vec d → Vec d) :
    negOneNorm (matImage L U) F ≤
      ENNReal.ofReal (Real.sqrt (h1AffineFactor L)) *
        negOneNorm U (fun y ↦ F (matVecMul L y)) := by
  have hK : 0 < h1AffineFactor L := h1AffineFactor_pos hL
  unfold negOneNorm
  apply iSup_le
  rintro ⟨psi, htest, hnorm⟩
  rw [dualPairing_matImage hL hU]
  refine dualPairing_le_negOneNorm_of_h1NormSq_le _ _ hK
    (htest.comp_matVecMul hL) ?_
  exact (h1NormSq_comp_matVecMul_le hL hU hU0 psi
      htest.contDiff).trans
    (by
      simpa only [mul_one] using
        (mul_le_mul_right hnorm
          (ENNReal.ofReal (h1AffineFactor L))))

end

end HighContrast
end HCPolySupport
