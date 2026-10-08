/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.AffineLiouvilleGrowth
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffinePullbackCoeffSpaceEquiv
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.AffineLiouvilleClass

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Liouville-class covariance under invertible affine maps

The coefficient ellipticity calculation is the representative-level form of
the packaged affine-pullback coefficient construction.  It supplies the
reverse local-Sobolev transport without adding a second ellipticity premise.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

private theorem affinePullback_quasiMeasurePreserving
    (L : Mat d) (hL : IsUnit L.det) :
    Measure.QuasiMeasurePreserving (matVecMul L) volume volume := by
  refine ⟨(continuous_matVecMul L).measurable, ?_⟩
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := L) hL.ne_zero
  change Measure.map (Matrix.toLin' L) volume ≪ volume
  rw [hmap]
  exact Measure.smul_absolutelyContinuous

/-- Pointwise ellipticity is preserved by an invertible divergence-form
pullback, with fixed transformed constants. -/
theorem isEllipticMatrix_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    {lam Lam : ℝ} {y : Vec d}
    (hb : IsEllipticMatrix lam Lam (b (matVecMul L y))) :
    IsEllipticMatrix
      (lam / max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L)))
      (max Lam (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam))
      (affineCoefficient L hL b y) := by
  let K := max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L))
  let lam' := lam / K
  let Lam' := max Lam (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam)
  have hK : 0 < K := zero_lt_one.trans_le (le_max_left _ _)
  have hKone : 1 ≤ K := le_max_left _ _
  have hlam' : 0 < lam' := div_pos hb.1 hK
  have hLT : IsUnit (matTranspose L).det := by
    simpa only [matTranspose] using Matrix.isUnit_det_transpose L hL
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
        _ ≤ Book.Ch02.matrixFrobeniusNormSq (matTranspose L) *
            vecNormSq xi :=
          Book.Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq
            _ _
        _ ≤ K * vecNormSq xi :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (vecNormSq_nonneg xi)
    have hscaled : lam' * vecNormSq x ≤ lam * vecNormSq xi := by
      calc
        lam' * vecNormSq x ≤ lam' * (K * vecNormSq xi) :=
          mul_le_mul_of_nonneg_left hxnorm hlam'.le
        _ = lam * vecNormSq xi := by
          dsimp only [lam', K]
          field_simp [hK.ne']
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
      ((isEllipticMatrix_iff_isEllipticEntryLU (b (matVecMul L y))).mp hb).2.2.2 xi
    have hnormInv : 0 ≤ Book.Ch02.matrixFrobeniusNormSq L⁻¹ :=
      Book.Ch02.matrixFrobeniusNormSq_nonneg L⁻¹
    have henergy : 0 ≤ vecDot xi (matVecMul (b (matVecMul L y)) xi) :=
      (mul_nonneg hb.1.le (vecNormSq_nonneg xi)).trans (hb.2.2.1 xi)
    calc
      vecNormSq (matVecMul (affineCoefficient L hL b y) x) =
          vecNormSq (matVecMul L⁻¹
            (matVecMul (b (matVecMul L y)) xi)) := by
        rw [← hx, affineCoefficient_flux hL]
      _ ≤ Book.Ch02.matrixFrobeniusNormSq L⁻¹ *
          vecNormSq (matVecMul (b (matVecMul L y)) xi) :=
        Book.Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq
          _ _
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

/-- Local uniform ellipticity transports through the affine coefficient field:
the ball of radius `R` is served by the transformed constants of a ball whose
radius absorbs the matrix. -/
theorem isAELocallyUniformlyElliptic_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b) :
    IsAELocallyUniformlyElliptic (affineCoefficient L hL b) := by
  intro R hR
  obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
    hb.comp_matVecMul L (affinePullback_quasiMeasurePreserving L hL) R hR
  have hKone : (1 : ℝ) ≤ max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L)) :=
    le_max_left _ _
  refine ⟨lam / max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L)),
    max Lam (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam),
    div_pos hlam (zero_lt_one.trans_le hKone),
    (div_le_self hlam.le hKone).trans (hle.trans (le_max_left _ _)), ?_⟩
  filter_upwards [hell] with y hy hyb
  exact isEllipticMatrix_affineCoefficient L hL (hy hyb)

private theorem affinePulledValue_inverse
    {L : Mat d} (hL : IsUnit L.det) (v : Vec d → ℝ) :
    (fun x ↦ (fun y ↦ v (matVecMul L y)) (matVecMul L⁻¹ x)) = v := by
  funext x
  change v (matVecMul L (matVecMul L⁻¹ x)) = v x
  rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]

private theorem affinePulledGradient_inverse
    {L : Mat d} (hL : IsUnit L.det) (Dv : Vec d → Vec d) :
    (fun x ↦ matVecMul (matTranspose L⁻¹)
      ((fun y ↦ matVecMul (matTranspose L) (Dv (matVecMul L y)))
        (matVecMul L⁻¹ x))) = Dv := by
  funext x
  change matVecMul (matTranspose L⁻¹)
      (matVecMul (matTranspose L)
        (Dv (matVecMul L (matVecMul L⁻¹ x)))) = Dv x
  have hx : matVecMul L (matVecMul L⁻¹ x) = x := by
    rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
  rw [hx]
  have hLT : IsUnit (matTranspose L).det := by
    simpa only [matTranspose] using Matrix.isUnit_det_transpose L hL
  have hinvT : matTranspose L⁻¹ = (matTranspose L)⁻¹ := by
    simpa only [matTranspose] using Matrix.transpose_nonsing_inv (A := L)
  rw [hinvT, matVecMul_mul, Matrix.nonsing_inv_mul _ hLT, matVecMul_one]

/-- Full Liouville membership is equivalent before and after an invertible
affine pullback. -/
theorem memLiouvilleClass_affinePullback_iff
    {L : Mat d} (hL : IsUnit L.det)
    {b : CoeffField d} {theta : ℝ}
    (hb : IsAELocallyUniformlyElliptic b)
    (v : Vec d → ℝ) (Dv : Vec d → Vec d) :
    MemLiouvilleClass b theta v Dv ↔
      MemLiouvilleClass (affineCoefficient L hL b) theta
        (fun y ↦ v (matVecMul L y))
        (fun y ↦ matVecMul (matTranspose L) (Dv (matVecMul L y))) := by
  constructor
  · rintro ⟨hlocal, hweak, hgrowth⟩
    refine ⟨memH1sLoc_affinePullback hL hb hlocal, ?_,
      liouvilleGrowth_affinePullback hL hgrowth⟩
    have hweak' := (isWeakSolutionOn_affinePullback_iff hL
      (U := Set.univ) MeasurableSet.univ b Dv).mp hweak
    simpa only [matImage_inv_eq_preimage hL, preimage_univ] using hweak'
  · intro hpull
    let bL : CoeffField d := affineCoefficient L hL b
    let hLinv : IsUnit (L⁻¹).det := Matrix.isUnit_nonsing_inv_det L hL
    have hbL : IsAELocallyUniformlyElliptic bL :=
      isAELocallyUniformlyElliptic_affineCoefficient L hL hb
    have hlocalBack := memH1sLoc_affinePullback hLinv hbL hpull.1
    have hgrowthBack := liouvilleGrowth_affinePullback hLinv hpull.2.2
    have hweakBack := (isWeakSolutionOn_affinePullback_iff hLinv
      (U := Set.univ) MeasurableSet.univ bL
      (fun y ↦ matVecMul (matTranspose L) (Dv (matVecMul L y)))).mp hpull.2.1
    have hcoeff : affineCoefficient L⁻¹ hLinv bL = b := by
      funext x
      exact affineCoefficient_inv_affineCoefficient L hL b x
    have hvalue := affinePulledValue_inverse hL v
    have hgrad := affinePulledGradient_inverse hL Dv
    rw [hvalue, hgrad] at hlocalBack
    rw [hcoeff] at hlocalBack
    rw [hvalue] at hgrowthBack
    rw [matImage_inv_eq_preimage hLinv, preimage_univ, hcoeff,
      hgrad] at hweakBack
    exact ⟨hlocalBack, hweakBack, hgrowthBack⟩

end

end Root
end HighContrast
end HCPolySupport
