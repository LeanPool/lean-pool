/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineNormalization
public import LeanPool.HighContrastHomogenization.Analytic.ScaledCoeff
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCoefficient
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions
public import LeanPool.HighContrastHomogenization.Support.Probability.RegCoeffField.EllipticSet

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.AffineCoeffFamily

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine coefficient families

An invertible linear change of variables sends one globally measurable, locally
uniformly elliptic coefficient representative to another such representative:
the ball of a given radius is served by the constants of a ball of proportional
radius.  Using that same representative on every open triadic cube, with the
constants of a ball containing the cube, produces the compatible coefficient
family required by the deterministic comparison.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

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
  have hcomp : AEStronglyMeasurable (fun y : Vec d => b (matVecMul L y)) volume :=
    hb.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_matVecMul_of_isUnitDet L hL)
  have hcont : Continuous fun A : Mat d => L⁻¹ * A * matTranspose L⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact hcont.comp_aestronglyMeasurable hcomp

private theorem isEllipticMatrix_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    {lam Lam : ℝ} {y : Vec d}
    (hb : IsEllipticMatrix lam Lam (b (matVecMul L y))) :
    IsEllipticMatrix
      (lam / max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L)))
      (max
        Lam
        (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam))
      (affineCoefficient L hL b y) := by
  let K := max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L))
  let lam' := lam / K
  let Lam' := max Lam (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKone : 1 ≤ K := le_max_left _ _
  have hlam' : 0 < lam' := div_pos hb.1 hK
  have hLT : IsUnit (matTranspose L).det := by
    simpa [matTranspose] using Matrix.isUnit_det_transpose L hL
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
        _ ≤ K * vecNormSq xi := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (vecNormSq_nonneg xi)
    have hscaled : lam' * vecNormSq x ≤ lam * vecNormSq xi := by
      calc
        lam' * vecNormSq x ≤ lam' * (K * vecNormSq xi) :=
          mul_le_mul_of_nonneg_left hxnorm hlam'.le
        _ = lam * vecNormSq xi := by
          dsimp [lam', K]
          field_simp [hK.ne']
    calc
      lam' * vecNormSq x ≤ lam * vecNormSq xi := hscaled
      _ ≤ vecDot xi (matVecMul (b (matVecMul L y)) xi) := hb.2.2.1 xi
      _ = vecDot x
          (matVecMul (affineCoefficient L hL b y) x) := by
        rw [← affineCoefficient_energy hL b y xi, hx]
  · intro x
    let xi := matVecMul (matTranspose L)⁻¹ x
    have hx : matVecMul (matTranspose L) xi = x := by
      rw [show xi = matVecMul (matTranspose L)⁻¹ x from rfl,
        matVecMul_mul, Matrix.mul_nonsing_inv (matTranspose L) hLT]
      exact matVecMul_one x
    have himage :=
      ((isEllipticMatrix_iff_isEllipticEntryLU (b (matVecMul L y))).mp hb).2.2.2 xi
    have hnormInv : 0 ≤ Book.Ch02.matrixFrobeniusNormSq L⁻¹ :=
      Book.Ch02.matrixFrobeniusNormSq_nonneg L⁻¹
    have henergy : 0 ≤ vecDot xi (matVecMul (b (matVecMul L y)) xi) :=
      (mul_nonneg hb.1.le (vecNormSq_nonneg xi)).trans (hb.2.2.1 xi)
    calc
      vecNormSq
          (matVecMul (affineCoefficient L hL b y) x) =
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
      _ = Lam' * vecDot x
          (matVecMul (affineCoefficient L hL b y) x) := by
        rw [← affineCoefficient_energy hL b y xi, hx]

private theorem isAELocallyUniformlyElliptic_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b) :
    IsAELocallyUniformlyElliptic (affineCoefficient L hL b) := by
  intro R hR
  obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
    hb.comp_matVecMul L (quasiMeasurePreserving_matVecMul_of_isUnitDet L hL) R hR
  have hK : 0 < max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L)) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨lam / max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L)),
    max Lam (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam), div_pos hlam hK,
    (div_le_self hlam.le (le_max_left _ _)).trans (hle.trans (le_max_left _ _)),
    ?_⟩
  filter_upwards [hell] with y hy hyb
  exact isEllipticMatrix_affineCoefficient L hL (hy hyb)

/-- A globally measurable, locally uniformly elliptic field produces a
compatible Chapter 3 coefficient family after any invertible linear pullback:
each cube reads the constants of a ball containing it. -/
theorem exists_affineCoeffFamily
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    (hbmeas : AEStronglyMeasurable b volume)
    (hbEll : IsAELocallyUniformlyElliptic b) :
    ∃ aL : Book.Ch03.CoeffFamily d,
      ∀ Q : TriadicCube d,
        (aL.coeffOn Q).toCoeffField = affineCoefficient L hL b := by
  classical
  have hmeas := aestronglyMeasurable_affineCoefficient L hL hbmeas
  choose lam Lam hlam hle hell using fun Q : TriadicCube d =>
    (isAELocallyUniformlyElliptic_affineCoefficient L hL hbEll
      ).exists_ae_isEllipticMatrix_of_isBounded
      (isBoundedDomain_openCubeSet Q).isBounded
  let aL : Book.Ch03.CoeffFamily d :=
    { coeffOn := fun Q =>
        { toCoeffField := affineCoefficient L hL b
          lam := lam Q
          Lam := Lam Q
          lam_pos := hlam Q
          lam_le_Lam := hle Q
          aeStronglyMeasurable := by
            intro i j
            have hentry : AEStronglyMeasurable
                (fun x : Vec d => affineCoefficient L hL b x i j) volume :=
              (continuous_id.matrix_elem i j).comp_aestronglyMeasurable hmeas
            refine hentry.restrict.congr ?_
            filter_upwards [ae_restrict_mem (Book.Ch02.cubeDomain Q).measurableSet]
              with x hx
            change x ∈ openCubeSet Q at hx
            simp [restrictCoeffField, hx]
          aeElliptic := by
            filter_upwards [ae_restrict_of_ae (hell Q),
              ae_restrict_mem (Book.Ch02.cubeDomain Q).measurableSet] with x hx hxQ
            exact hx hxQ }
      restrictsTo_of_subset := by
        intro Q R _hRQ
        exact Filter.EventuallyEq.rfl }
  exact ⟨aL, fun Q => rfl⟩

end

end HighContrast
end HCPolySupport
