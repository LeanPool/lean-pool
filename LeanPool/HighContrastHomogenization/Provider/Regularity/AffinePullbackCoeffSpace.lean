/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AffineCoeffFamily

/-!
# High-contrast homogenization: Provider.Regularity.AffinePullbackCoeffSpace

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine pullback of a qualitative coefficient sample

An invertible divergence-form pullback is packaged on the existing
`CoeffSpace` carrier by its literal measurable representative.  The
characterization theorem exposes that representative almost everywhere.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem affinePullback_quasiMeasurePreserving
    (L : Mat d) (hL : IsUnit L.det) :
    Measure.QuasiMeasurePreserving (matVecMul L) volume volume := by
  refine ⟨(continuous_matVecMul L).measurable, ?_⟩
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := L) hL.ne_zero
  change Measure.map (Matrix.toLin' L) volume ≪ volume
  rw [hmap]
  exact Measure.smul_absolutelyContinuous

private theorem affinePullback_aestronglyMeasurable
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (affineCoefficient L hL b) volume := by
  have hcomp : AEStronglyMeasurable
      (fun y : Vec d ↦ b (matVecMul L y)) volume :=
    hb.comp_quasiMeasurePreserving
      (affinePullback_quasiMeasurePreserving L hL)
  have hcont : Continuous fun A : Mat d ↦
      L⁻¹ * A * matTranspose L⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact hcont.comp_aestronglyMeasurable hcomp

private theorem affinePullback_isEllipticMatrix
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
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
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

/-- The literal affine pullback of one qualitative coefficient sample. -/
@[expose]
noncomputable def affinePullbackCoeffSpace
    (L : Mat d) (hL : IsUnit L.det) (a : CoeffSpace d) : CoeffSpace d := by
  let f : CoeffField d := affineCoefficient L hL (⇑a.1)
  let hf : AEStronglyMeasurable f volume :=
    affinePullback_aestronglyMeasurable L hL a.1.aestronglyMeasurable
  refine ⟨AEEqFun.mk f hf, ?_⟩
  intro R hR
  obtain ⟨lam, Lam, hlam, hle, hEll⟩ :=
    (a.2.comp_matVecMul L (affinePullback_quasiMeasurePreserving L hL)) R hR
  refine ⟨lam / max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L)),
    max Lam (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam),
    div_pos hlam (lt_of_lt_of_le zero_lt_one (le_max_left _ _)),
    (div_le_self hlam.le (le_max_left _ _)).trans
      (hle.trans (le_max_left _ _)), ?_⟩
  filter_upwards [AEEqFun.coeFn_mk f hf, hEll] with y hfy hy hyb
  rw [hfy]
  exact affinePullback_isEllipticMatrix L hL (hy hyb)

/-- The packaged sample has exactly the divergence-form pullback as its a.e.
representative. -/
theorem affinePullbackCoeffSpace_ae
    (L : Mat d) (hL : IsUnit L.det) (a : CoeffSpace d) :
    (⇑(affinePullbackCoeffSpace L hL a).1 : CoeffField d) =ᵐ[volume]
      affineCoefficient L hL (⇑a.1) := by
  unfold affinePullbackCoeffSpace
  exact AEEqFun.coeFn_mk _ _

/-- Affine pullback respects almost-everywhere equality of coefficient
representatives. -/
theorem affineCoefficient_congr_ae
    (L : Mat d) (hL : IsUnit L.det) {a b : CoeffField d}
    (hab : a =ᵐ[volume] b) :
    affineCoefficient L hL a =ᵐ[volume] affineCoefficient L hL b := by
  have hpull := (affinePullback_quasiMeasurePreserving L hL).tendsto_ae hab
  filter_upwards [hpull] with y hy
  unfold affineCoefficient
  rw [hy]

end

end HighContrast
end HCPolySupport
