/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHattedCarrier
public import LeanPool.HighContrastHomogenization.Provider.Persistence.AdaptedPersistence
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationClosure
public import LeanPool.HighContrastHomogenization.Provider.Response.RandomAdaptedResponseCompactInsertion
public import LeanPool.HighContrastHomogenization.Provider.Response.RandomAdaptedResponseDefectBridge
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.ReferenceIntermediate

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastProfileDefectCap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Calibrated profile defects from the hatted mean dilation

The canonical Schur recentering uses the unshifted metric loads in the profile
defects.  The opposite shifts occur only when constant-skew covariance rewrites
the resulting terminal calls back to the original coefficient field.

This file isolates the last algebraic input needed for the two defect caps.  If
the fine adapted mean is bounded by the coarse adapted mean with the dilation
predicted by the hatted-carrier drop, response-load calibration turns that
matrix comparison into dimension-only bounds for both profile defects.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem toFullBlockVec_pair (u v : Vec d) :
    toFullBlockVec ((u, v) : BlockVec d) = Sum.elim u v := by
  funext i
  cases i <;> rfl

/-- The two canonical profile defects are controlled by the hatted-carrier
drop once the corresponding fine-to-coarse mean dilation is known.  The
terminal intrinsic smallness is written in precisely the form needed to bound
the calibrated load energy by an absolute constant. -/
theorem calibratedProfileDefects_le_of_hattedMeanDilation
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {qGrid : Mat d} (hgrid : IsRoundedGrid l qGrid)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hfins : HasFiniteAdaptedMean P qGrid s)
    (hfint : HasFiniteAdaptedMean P qGrid t)
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hEtform : toFullBlockMat (adaptedMean P qGrid t) =
      schurBlock S SStar K)
    (hsmall : 6 * (blockContrast (adaptedMean P qGrid t) - 1) ≤ 1)
    (hupper :
      toFullBlockMat (adaptedMean P qGrid s) ≤
        (1 + 4 * (d : ℝ) *
            (adaptedHattedContrast P qGrid s -
              adaptedHattedContrast P qGrid t)) •
          toFullBlockMat (adaptedMean P qGrid t))
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    let h0 := Response.responseSkew K
    let p := Response.centeredResponseLoadP S SStar K e
    let r := Response.centeredResponseLoadQ S SStar K e
    Response.profilePrimalResponseDefect P (Recurrence.posDef_of_isRoundedGrid hgrid)
          h0 (Response.is_skew_mat_response_skew K) s t p r ≤
        16 * (d : ℝ) *
          (adaptedHattedContrast P qGrid s -
            adaptedHattedContrast P qGrid t) ∧
      Response.profileAdjointResponseDefect P (Recurrence.posDef_of_isRoundedGrid hgrid)
          h0 (Response.is_skew_mat_response_skew K) s t p r ≤
        16 * (d : ℝ) *
          (adaptedHattedContrast P qGrid s -
            adaptedHattedContrast P qGrid t) := by
  let Es : FullBlockMat d := toFullBlockMat (adaptedMean P qGrid s)
  let Et : FullBlockMat d := toFullBlockMat (adaptedMean P qGrid t)
  let h0 : Mat d := Response.responseSkew K
  let p : Vec d := Response.centeredResponseLoadP S SStar K e
  let r : Vec d := Response.centeredResponseLoadQ S SStar K e
  let G0 : FullBlockMat d := fullBlockShear h0
  let Ethat : FullBlockMat d := G0ᴴ * Et * G0
  let Eshat : FullBlockMat d := G0ᴴ * Es * G0
  let rSym : Mat d := Response.responseSymmetric K
  let B : Mat d := Response.centeredResponseBlock S SStar K
  let m : Mat d := Response.centeredResponseMetric S SStar K
  let theta : ℝ := canonImbalance Et
  let drop : ℝ := adaptedHattedContrast P qGrid s -
    adaptedHattedContrast P qGrid t
  let rd : ℝ := 1 + 4 * (d : ℝ) * drop
  have hdrop0 : 0 ≤ drop := by
    dsimp only [drop]
    exact sub_nonneg.mpr
      (adaptedHattedContrast_le hstat hgrid hls hst hfins hfint)
  have hrd : 1 ≤ rd := by
    dsimp only [rd]
    exact le_add_of_nonneg_right (by positivity)
  have hEsPos : Es.PosDef := by
    dsimp only [Es]
    exact Recurrence.posDef_toFullBlockMat_adaptedMean hgrid s hfins
  have hEtPos : Et.PosDef := by
    dsimp only [Et]
    exact Recurrence.posDef_toFullBlockMat_adaptedMean hgrid t hfint
  have hmean : Et ≤ Es := by
    dsimp only [Et, Es]
    exact Recurrence.toFullBlockMat_adaptedMean_le hstat hgrid hls hst hfins hfint
  have hhatTS : Ethat ≤ Eshat := by
    dsimp only [Ethat, Eshat]
    exact conj_le_conj G0 hmean
  have hhatUpper : Eshat ≤ rd • Ethat := by
    have hconj := conj_le_conj G0 hupper
    dsimp only [Eshat, Ethat, Es, Et, G0, rd, drop]
    simpa only [Response.conj_smul] using hconj
  have hEthatPos : Ethat.PosDef := by
    dsimp only [Ethat, G0]
    exact posDef_conj hEtPos (isUnit_fullBlockShear h0)
  have hEtSharp : fullBlockSharp Et ≤ Et := by
    dsimp only [Et]
    exact Persistence.fullBlockSharp_toFullBlockMat_adaptedMean_le hgrid t hfint
  have hthetaOne : 1 ≤ theta := by
    dsimp only [theta]
    exact Persistence.one_le_canonImbalance hEtPos hEtSharp
  have hthetaPos : 0 < theta := one_pos.trans_le hthetaOne
  have hEtLe : Et ≤ theta • fullBlockSharp Et := by
    dsimp only [theta]
    rw [canonImbalance_eq hEtPos]
    exact le_relSize_smul hEtPos.posSemidef
      (posDef_fullBlockSharp hEtPos)
  have hBle : B ≤ theta • SStar := by
    have hEtLe' : schurBlock S SStar K ≤
        theta • fullBlockSharp (schurBlock S SStar K) := by
      rw [← hEtform]
      exact hEtLe
    have hraw := Response.responseBlock_le_smul hS hStar
      (r := rSym) (B := B) (c := theta) rfl rfl
      hEtLe'
    simpa only [B, rSym, Response.centeredResponseBlock,
      Response.responseSymmetric] using hraw
  have hloadSum :
      Sum.elim (-p) r ⬝ᵥ Ethat *ᵥ Sum.elim (-p) r +
          Sum.elim p r ⬝ᵥ Ethat *ᵥ Sum.elim p r ≤
        4 * Real.sqrt theta := by
    have hraw := Response.load_sum_le hS hStar
      (Et := Et) (Ehat := Ethat) (G0 := G0)
      (r := rSym) (B := B) (m := m) (g0 := h0) (h := h0)
      (p := p) (q := r) (e := e) (theta := theta)
      (by simpa only [Et] using hEtform) rfl rfl rfl rfl rfl rfl rfl rfl
      he hthetaPos hBle
    simpa only [sub_self, Matrix.zero_mulVec, add_zero] using hraw
  have hminus0 :
      0 ≤ Sum.elim (-p) r ⬝ᵥ Ethat *ᵥ Sum.elim (-p) r :=
    Response.quadratic_nonneg hEthatPos.posSemidef _
  have hplus0 :
      0 ≤ Sum.elim p r ⬝ᵥ Ethat *ᵥ Sum.elim p r :=
    Response.quadratic_nonneg hEthatPos.posSemidef _
  have hminusLoad :
      Sum.elim (-p) r ⬝ᵥ Ethat *ᵥ Sum.elim (-p) r ≤
        4 * Real.sqrt theta := by
    linarith only [hloadSum, hplus0]
  have hplusLoad :
      Sum.elim p r ⬝ᵥ Ethat *ᵥ Sum.elim p r ≤
        4 * Real.sqrt theta := by
    linarith only [hloadSum, hminus0]
  have hrawMinus := (Response.defect_bounds hEthatPos.posSemidef hhatTS
    hrd hhatUpper (Sum.elim (-p) r) hminusLoad).2
  have hrawPlus := (Response.defect_bounds hEthatPos.posSemidef hhatTS
    hrd hhatUpper (Sum.elim p r) hplusLoad).2
  have htauMinus :
      Response.profilePrimalResponseDefect P
          (Recurrence.posDef_of_isRoundedGrid hgrid) h0
          (Response.is_skew_mat_response_skew K) s t p r ≤
        2 * (rd - 1) * Real.sqrt theta := by
    rw [Response.profilePrimalResponseDefect_identity
      (Recurrence.posDef_of_isRoundedGrid hgrid)
      (Response.is_skew_mat_response_skew K) hfins hfint]
    simpa only [Ethat, Eshat, Et, Es, G0, h0,
      Response.profileRecenteredMean, toFullBlockMat_blockMatMul,
      toFullBlockMat_blockMatTranspose_conj, toFullBlockMat_blockG,
      Recurrence.toFullBlockMat_blockSub,
      blockVecDot_blockMatVecMul_eq_dotProduct, Matrix.mul_assoc,
      Matrix.sub_mulVec, dotProduct_sub, one_div,
      toFullBlockVec_pair] using hrawMinus
  have htauPlus :
      Response.profileAdjointResponseDefect P
          (Recurrence.posDef_of_isRoundedGrid hgrid) h0
          (Response.is_skew_mat_response_skew K) s t p r ≤
        2 * (rd - 1) * Real.sqrt theta := by
    rw [Response.profile_adjoint_response_defect_eq_recentered_quadratic
      (Recurrence.posDef_of_isRoundedGrid hgrid)
      (Response.is_skew_mat_response_skew K) hfins hfint]
    simpa only [Ethat, Eshat, Et, Es, G0, h0,
      Response.profileRecenteredMean, toFullBlockMat_blockMatMul,
      toFullBlockMat_blockMatTranspose_conj, toFullBlockMat_blockG,
      blockVecDot_blockMatVecMul_eq_dotProduct, Matrix.mul_assoc,
      one_div, toFullBlockVec_pair] using hrawPlus
  have hthetaBound : theta ≤ 2 := by
    have hsymm := Recurrence.isSymmetricBlockMat_adaptedMean P qGrid t
    have hpos := Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid t hfint
    have hsharp := Persistence.blockSharp_adaptedMean_le hgrid t hfint
    have hraw := Initialization.kappaRef_le_one_add_six_mul_refContrast_sub_one
      hsymm hpos hsharp
    rw [kappaRef_eq_canonImbalance hsymm hpos] at hraw
    have hcanon : theta ≤
        1 + 6 * (blockContrast (adaptedMean P qGrid t) - 1) := by
      simpa only [theta, Et, refContrast] using hraw
    linarith only [hcanon, hsmall]
  have hsqrt : Real.sqrt theta ≤ 2 := by
    have hsqrtTheta : Real.sqrt theta ≤ Real.sqrt 2 :=
      Real.sqrt_le_sqrt hthetaBound
    have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg 2]
    exact hsqrtTheta.trans hsqrtTwo
  have hfactor0 : 0 ≤ 8 * (d : ℝ) * drop := by positivity
  have hfactor :
      8 * (d : ℝ) * drop * Real.sqrt theta ≤
        16 * (d : ℝ) * drop := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt hfactor0
    nlinarith only [hmul]
  have hrdEq : 2 * (rd - 1) * Real.sqrt theta =
      8 * (d : ℝ) * drop * Real.sqrt theta := by
    dsimp only [rd]
    ring
  dsimp only
  constructor
  · exact htauMinus.trans (by rw [hrdEq]; exact hfactor)
  · exact htauPlus.trans (by rw [hrdEq]; exact hfactor)

end

end HCPolySupport.HighContrast.Quenched
