/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineFractionalNorm
public import LeanPool.HighContrastHomogenization.Analytic.AffineGeometry
public import LeanPool.HighContrastHomogenization.Analytic.DirichletDomain
public import LeanPool.HighContrastHomogenization.Analytic.ScaledCoeff
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCoefficient
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.ScheduledLocalizationGaugeReduction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Gauge reduction data for the scheduled localization step

The Dirichlet estimate is consumed on the gauge-reduced domain
`Uhat = L⁻¹ U`, where `L` is the square root of the symmetric part of the
comparison matrix.  This module supplies the four pieces of that reduction
which are needed before any localization estimate can be asked for:

* a locally uniformly elliptic source representative of the gauge-reduced,
  skew-centered coefficient;
* positivity of the output distortion factor;
* finiteness of the transported boundary energy;
* the open bounded convex geometry and ball sandwich of `Uhat`.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Ellipticity under an invertible linear pullback -/

private theorem quasiMeasurePreserving_matVecMul_of_isUnitDet
    (L : Mat d) (hL : IsUnit L.det) :
    Measure.QuasiMeasurePreserving (matVecMul L) volume volume := by
  refine ⟨(continuous_matVecMul L).measurable, ?_⟩
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := L) hL.ne_zero
  change Measure.map (Matrix.toLin' L) volume ≪ volume
  rw [hmap]
  exact Measure.smul_absolutelyContinuous

private theorem aestronglyMeasurable_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (affineCoefficient L hL b) volume := by
  have hcomp : AEStronglyMeasurable
      (fun y : Vec d => b (matVecMul L y)) volume :=
    hb.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_matVecMul_of_isUnitDet L hL)
  have hcont : Continuous fun A : Mat d => L⁻¹ * A * matTranspose L⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact hcont.comp_aestronglyMeasurable hcomp

/-- The lower and upper ellipticity constants of a linear pullback. -/
@[expose]
def affineLowerEllipticity (L : Mat d) (lam : ℝ) : ℝ :=
  lam / max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L))

/-- The upper ellipticity constant of a linear pullback. -/
@[expose]
def affineUpperEllipticity (L : Mat d) (Lam : ℝ) : ℝ :=
  max Lam (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam)

theorem affineLowerEllipticity_pos {L : Mat d} {lam : ℝ} (hlam : 0 < lam) :
    0 < affineLowerEllipticity L lam :=
  div_pos hlam (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

theorem affineLowerEllipticity_le_affineUpperEllipticity
    {L : Mat d} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam) :
    affineLowerEllipticity L lam ≤ affineUpperEllipticity L Lam := by
  refine le_trans ?_ (le_max_left _ _)
  exact (div_le_self hlam.le (le_max_left _ _)).trans hle

/-- Uniform ellipticity is carried by an invertible linear pullback, with the
distortion paid by the Frobenius norms of the matrix and of its inverse. -/
theorem isEllipticMatrix_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    {lam Lam : ℝ} {y : Vec d}
    (hb : IsEllipticMatrix lam Lam (b (matVecMul L y))) :
    IsEllipticMatrix (affineLowerEllipticity L lam)
      (affineUpperEllipticity L Lam) (affineCoefficient L hL b y) := by
  let K := max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L))
  let lam' := lam / K
  let Lam' := max Lam (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKone : 1 ≤ K := le_max_left _ _
  have hlam' : 0 < lam' := div_pos hb.1 hK
  have hLT : IsUnit (matTranspose L).det := by
    simpa [matTranspose] using Matrix.isUnit_det_transpose L hL
  change IsEllipticMatrix lam' Lam' (affineCoefficient L hL b y)
  rw [isEllipticMatrix_iff_isEllipticEntryLU]
  refine ⟨hlam', (div_le_self hb.1.le hKone).trans
    (hb.2.1.trans (le_max_left _ _)), ?_, ?_⟩
  · intro x
    let xi := matVecMul (matTranspose L)⁻¹ x
    have hx : matVecMul (matTranspose L) xi = x := by
      rw [show xi = matVecMul (matTranspose L)⁻¹ x from rfl,
        matVecMul_mul, Matrix.mul_nonsing_inv (matTranspose L) hLT]
      exact matVecMul_one x
    have hxnorm : vecNormSq x ≤ K * vecNormSq xi := by
      calc
        vecNormSq x = vecNormSq (matVecMul (matTranspose L) xi) := by rw [hx]
        _ ≤ Book.Ch02.matrixFrobeniusNormSq (matTranspose L) * vecNormSq xi :=
          Book.Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq _ _
        _ ≤ K * vecNormSq xi :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (vecNormSq_nonneg xi)
    have hscaled : lam' * vecNormSq x ≤ lam * vecNormSq xi := by
      calc
        lam' * vecNormSq x ≤ lam' * (K * vecNormSq xi) :=
          mul_le_mul_of_nonneg_left hxnorm hlam'.le
        _ = lam * vecNormSq xi := by
          dsimp only [lam']
          field_simp
    calc
      lam' * vecNormSq x ≤ lam * vecNormSq xi := hscaled
      _ ≤ vecDot xi (matVecMul (b (matVecMul L y)) xi) := hb.2.2.1 xi
      _ = vecDot x (matVecMul (affineCoefficient L hL b y) x) := by
        rw [← affineCoefficient_energy hL b y xi, hx]
  · intro x
    let xi := matVecMul (matTranspose L)⁻¹ x
    have hx : matVecMul (matTranspose L) xi = x := by
      rw [show xi = matVecMul (matTranspose L)⁻¹ x from rfl,
        matVecMul_mul, Matrix.mul_nonsing_inv (matTranspose L) hLT]
      exact matVecMul_one x
    have himage :=
      ((isEllipticMatrix_iff_isEllipticEntryLU
        (b (matVecMul L y))).mp hb).2.2.2 xi
    have hnormInv : 0 ≤ Book.Ch02.matrixFrobeniusNormSq L⁻¹ :=
      Book.Ch02.matrixFrobeniusNormSq_nonneg L⁻¹
    have henergy : 0 ≤ vecDot xi (matVecMul (b (matVecMul L y)) xi) :=
      (mul_nonneg hb.1.le (vecNormSq_nonneg xi)).trans (hb.2.2.1 xi)
    calc
      vecNormSq (matVecMul (affineCoefficient L hL b y) x) =
          vecNormSq (matVecMul L⁻¹ (matVecMul (b (matVecMul L y)) xi)) := by
        rw [← hx, affineCoefficient_flux hL]
      _ ≤ Book.Ch02.matrixFrobeniusNormSq L⁻¹ *
          vecNormSq (matVecMul (b (matVecMul L y)) xi) :=
        Book.Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq _ _
      _ ≤ Book.Ch02.matrixFrobeniusNormSq L⁻¹ *
          (Lam * vecDot xi (matVecMul (b (matVecMul L y)) xi)) :=
        mul_le_mul_of_nonneg_left himage hnormInv
      _ = (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam) *
          vecDot xi (matVecMul (b (matVecMul L y)) xi) := by ring
      _ ≤ Lam' * vecDot xi (matVecMul (b (matVecMul L y)) xi) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) henergy
      _ = Lam' * vecDot x (matVecMul (affineCoefficient L hL b y) x) := by
        rw [← affineCoefficient_energy hL b y xi, hx]

theorem aeElliptic_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d} {lam Lam : ℝ}
    (hb : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) :
    ∀ᵐ y ∂volume, IsEllipticMatrix (affineLowerEllipticity L lam)
      (affineUpperEllipticity L Lam) (affineCoefficient L hL b y) := by
  have hqmp := quasiMeasurePreserving_matVecMul_of_isUnitDet L hL
  filter_upwards [hqmp.tendsto_ae hb] with y hy
  exact isEllipticMatrix_affineCoefficient L hL hy

/-! ## The gauge-reduced source field -/

/-- Local uniform ellipticity is carried by an invertible linear pullback: the
ball of a given radius is served by the constants of a ball of proportional
radius, with the distortion paid by the Frobenius norms. -/
theorem isAELocallyUniformlyElliptic_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b) :
    IsAELocallyUniformlyElliptic (affineCoefficient L hL b) := by
  intro R hR
  obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
    hb.comp_matVecMul L (quasiMeasurePreserving_matVecMul_of_isUnitDet L hL) R hR
  refine ⟨affineLowerEllipticity L lam, affineUpperEllipticity L Lam,
    affineLowerEllipticity_pos hlam,
    affineLowerEllipticity_le_affineUpperEllipticity hlam hle, ?_⟩
  filter_upwards [hell] with y hy hyb
  exact isEllipticMatrix_affineCoefficient L hL (hy hyb)

/-- A globally measurable, locally uniformly elliptic field has a locally
uniformly elliptic source representative after any invertible linear
pullback. -/
theorem exists_affineCoefficientSource
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    (hbmeas : AEStronglyMeasurable b volume)
    (hbEll : IsAELocallyUniformlyElliptic b) :
    ∃ aSource : Source.AKL.Field d,
      AEUniformlyEllipticField aSource ∧
        (⇑aSource : CoeffField d) =ᵐ[volume] affineCoefficient L hL b := by
  have hmeas : AEStronglyMeasurable (affineCoefficient L hL b) volume :=
    aestronglyMeasurable_affineCoefficient L hL hbmeas
  refine ⟨AEEqFun.mk (affineCoefficient L hL b) hmeas, ?_,
    AEEqFun.coeFn_mk (affineCoefficient L hL b) hmeas⟩
  exact (isAELocallyUniformlyElliptic_affineCoefficient L hL hbEll).congr
    (AEEqFun.coeFn_mk (affineCoefficient L hL b) hmeas).symm

/-- The gauge-reduced, skew-centered rescaled coefficient of the scheduled
estimate has a locally uniformly elliptic source representative. -/
theorem exists_gaugeReducedSource
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) (aSample : CoeffSpace d) :
    ∃ aSource : Source.AKL.Field d,
      AEUniformlyEllipticField aSource ∧
        (⇑aSource : CoeffField d) =ᵐ[volume]
          affineCoefficient (matSqrt (symmPart abar)) (isUnit_det_matSqrt hS)
            (fun x => scaledCoeff epsilon aSample x - skewPart abar) := by
  have hskew : IsSkewMat (skewPart abar) := matTranspose_skewPart abar
  have hcenterEll : IsAELocallyUniformlyElliptic
      (fun x => scaledCoeff epsilon aSample x - skewPart abar) := by
    intro R hR
    obtain ⟨lam, Lam, hlam, hle, hEll⟩ :=
      isAELocallyUniformlyElliptic_scaledCoeff hEpsilon aSample R hR
    refine ⟨lam, Response.skewShiftUpper lam Lam (skewPart abar), hlam,
      Response.le_skewShiftUpper hlam hle (skewPart abar), ?_⟩
    filter_upwards [hEll] with x hx hxb
    exact Response.isEllipticMatrix_sub_skew (hx hxb) hskew
  have hcenterMeas : AEStronglyMeasurable
      (fun x => scaledCoeff epsilon aSample x - skewPart abar) volume :=
    (aestronglyMeasurable_scaledCoeff hEpsilon aSample).sub
      aestronglyMeasurable_const
  exact exists_affineCoefficientSource (matSqrt (symmPart abar))
    (isUnit_det_matSqrt hS) hcenterMeas hcenterEll

/-! ## Distortion factor and transported boundary energy -/

/-- The boundary energy transported by a constant matrix stays finite. -/
theorem hsNormSq_matVecMul_ne_top (M : Mat d) (V : Set (Vec d)) (s : ℝ)
    {F : Vec d → Vec d} (hF : hsNormSq V s F ≠ ⊤) :
    hsNormSq V s (fun x => matVecMul M (F x)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (hsNormSq_matVecMul_le M V s F)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF

end

end HighContrast
end HCPolySupport
