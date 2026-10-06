/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastGoodQuads
public import LeanPool.HighContrastHomogenization.Provider.Bridge.ComparisonMatrixRows
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewHistory
public import Mathlib.Tactic.NoncommRing

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastMeanDilation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fine-to-coarse dilation from the hatted contrast drop

The positive adapted-mean increment is measured in the coarse Schur geometry.
Its two diagonal trace gaps are linear in the hatted drop.  The coupling term is
quadratic, by the good-quadratics estimate, and is absorbed in the perturbative
range.  This yields the full-block dilation used by the calibrated profile
defects.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem trace_fromBlocks (A B C D : Mat d) :
    Matrix.trace (Matrix.fromBlocks A B C D : FullBlockMat d) =
      Matrix.trace A + Matrix.trace D := by
  simp only [Matrix.trace, Fintype.sum_sum_type, Matrix.diag_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

private theorem inv_fromBlocks_diagonal {A D : Mat d}
    (hA : IsUnit A.det) (hD : IsUnit D.det) :
    (Matrix.fromBlocks A 0 0 D : FullBlockMat d)⁻¹ =
      Matrix.fromBlocks A⁻¹ 0 0 D⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.fromBlocks_multiply, Matrix.mul_nonsing_inv _ hA,
    Matrix.mul_nonsing_inv _ hD]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  exact Matrix.fromBlocks_one

private theorem trace_inv_mul_sub_eq_schur_gaps
    {C F : BlockMat d}
    (hCsymm : IsSymmetricBlockMat C) (hCpos : BlockPosDef C)
    (hFsymm : IsSymmetricBlockMat F) (hFpos : BlockPosDef F) :
    Matrix.trace
        ((toFullBlockMat C)⁻¹ * (toFullBlockMat F - toFullBlockMat C)) =
      Matrix.trace
          ((schurSigma F - schurSigma C) * (schurSigma C)⁻¹) +
        Matrix.trace
          ((F.lowerRight - C.lowerRight) * C.lowerRight⁻¹) +
        Matrix.trace
          ((schurSkew F - schurSkew C)ᴴ * F.lowerRight *
            (schurSkew F - schurSkew C) * (schurSigma C)⁻¹) := by
  let SC : Mat d := schurSigma C
  let SF : Mat d := schurSigma F
  let RC : Mat d := C.lowerRight
  let RF : Mat d := F.lowerRight
  let KC : Mat d := schurSkew C
  let KF : Mat d := schurSkew F
  let D : Mat d := KF - KC
  let G : FullBlockMat d := fullBlockShear KC
  have hSC : SC.PosDef := by
    dsimp only [SC]
    have hfull := posDef_toFullBlockMat hCsymm hCpos
    have hstar : (schurSigmaStar C).PosDef :=
      (posDef_lowerRight hCsymm hCpos).inv
    apply posDef_of_posDef_schurBlock hstar
    rw [← Initialization.toFullBlockMat_eq_schurBlock hCsymm hCpos]
    exact hfull
  have hRC : RC.PosDef := by
    dsimp only [RC]
    exact posDef_lowerRight hCsymm hCpos
  have hRF : RF.PosDef := by
    dsimp only [RF]
    exact posDef_lowerRight hFsymm hFpos
  have hSCdet : IsUnit SC.det := isUnit_det_of_posDef hSC
  have hRCdet : IsUnit RC.det := isUnit_det_of_posDef hRC
  have hRFdet : IsUnit RF.det := isUnit_det_of_posDef hRF
  have hCform : toFullBlockMat C = schurBlock SC RC⁻¹ KC := by
    simpa only [SC, RC, KC, schurSigmaStar] using
      Initialization.toFullBlockMat_eq_schurBlock hCsymm hCpos
  have hFform : toFullBlockMat F = schurBlock SF RF⁻¹ KF := by
    simpa only [SF, RF, KF, schurSigmaStar] using
      Initialization.toFullBlockMat_eq_schurBlock hFsymm hFpos
  have hCcong : Gᴴ * toFullBlockMat C * G =
      Matrix.fromBlocks SC 0 0 RC := by
    rw [hCform]
    change (fullBlockShear KC)ᴴ * schurBlock SC RC⁻¹ KC *
      fullBlockShear KC = _
    rw [Response.schurBlock_conj_shear, sub_self, Response.schurBlock_zero,
      Matrix.nonsing_inv_nonsing_inv _ hRCdet]
  have hFcong : Gᴴ * toFullBlockMat F * G =
      Matrix.fromBlocks (SF + Dᴴ * RF * D) (-(Dᴴ * RF))
        (-(RF * D)) RF := by
    rw [hFform]
    change (fullBlockShear KC)ᴴ * schurBlock SF RF⁻¹ KF *
      fullBlockShear KC = _
    rw [Response.schurBlock_conj_shear]
    change schurBlock SF RF⁻¹ D = _
    rw [schurBlock_eq, Matrix.nonsing_inv_nonsing_inv _ hRFdet]
  have hinv := Response.trace_inv_mul_skewBlockCongr KC (blockSub F C) C
  rw [Response.blockSub_skewBlockCongr, Recurrence.toFullBlockMat_blockSub] at hinv
  simp only [Response.toFullBlockMat_skewBlockCongr] at hinv
  dsimp only [G] at hCcong hFcong
  rw [hCcong, hFcong,
    inv_fromBlocks_diagonal hSCdet hRCdet] at hinv
  rw [Recurrence.toFullBlockMat_blockSub] at hinv
  have hcalc :
      Matrix.trace
          ((Matrix.fromBlocks SC⁻¹ 0 0 RC⁻¹ : FullBlockMat d) *
            (Matrix.fromBlocks (SF + Dᴴ * RF * D) (-(Dᴴ * RF))
                (-(RF * D)) RF - Matrix.fromBlocks SC 0 0 RC)) =
        Matrix.trace ((SF - SC) * SC⁻¹) +
          Matrix.trace ((RF - RC) * RC⁻¹) +
          Matrix.trace (Dᴴ * RF * D * SC⁻¹) := by
    have hsub :
        Matrix.fromBlocks (SF + Dᴴ * RF * D) (-(Dᴴ * RF))
              (-(RF * D)) RF - Matrix.fromBlocks SC 0 0 RC =
          (Matrix.fromBlocks (SF + Dᴴ * RF * D - SC) (-(Dᴴ * RF))
              (-(RF * D)) (RF - RC) : FullBlockMat d) := by
      ext i j
      cases i <;> cases j <;> simp
    rw [hsub, Matrix.fromBlocks_multiply, trace_fromBlocks]
    simp only [Matrix.zero_mul, add_zero, zero_add]
    have htop :
        Matrix.trace (SC⁻¹ * (SF + Dᴴ * RF * D - SC)) =
          Matrix.trace ((SF - SC) * SC⁻¹) +
            Matrix.trace (Dᴴ * RF * D * SC⁻¹) := by
      rw [show SC⁻¹ * (SF + Dᴴ * RF * D - SC) =
          SC⁻¹ * (SF - SC) + SC⁻¹ * (Dᴴ * RF * D) by
            noncomm_ring,
        Matrix.trace_add, Matrix.trace_mul_comm SC⁻¹ (SF - SC),
        Matrix.trace_mul_comm SC⁻¹ (Dᴴ * RF * D)]
    rw [htop, Matrix.trace_mul_comm RC⁻¹ (RF - RC)]
    ring
  rw [hcalc] at hinv
  simpa only [SC, SF, RC, RF, KC, KF, D] using hinv.symm

/-- In the perturbative range, the hatted-carrier drop controls the complete
fine adapted mean in the geometry of the coarse adapted mean. -/
theorem adaptedMean_le_hattedContrast_dilation
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    {j p : ℤ} (hlj : l ≤ j) (hjp : j ≤ p)
    (hfinj : HasFiniteAdaptedMean P q j)
    (hfinp : HasFiniteAdaptedMean P q p)
    (hsmall :
      (d : ℝ) *
          (adaptedHattedContrast P q j - adaptedHattedContrast P q p) ≤ 1) :
    toFullBlockMat (adaptedMean P q j) ≤
      (1 + 4 * (d : ℝ) *
          (adaptedHattedContrast P q j - adaptedHattedContrast P q p)) •
        toFullBlockMat (adaptedMean P q p) := by
  let C : BlockMat d := adaptedMean P q p
  let F : BlockMat d := adaptedMean P q j
  let D : Mat d := schurSkew F - schurSkew C
  let QS : Mat d := schurSigma F - schurSigma C
  let QR : Mat d := F.lowerRight - C.lowerRight
  let b : ℝ :=
    ‖matSqrt C.lowerRight⁻¹ * F.lowerRight *
        matSqrt C.lowerRight⁻¹ - 1‖
  let x : ℝ := Matrix.trace (QS * (schurSigma C)⁻¹)
  let y : ℝ := Matrix.trace (QR * C.lowerRight⁻¹)
  let z : ℝ := Matrix.trace (Dᴴ * F.lowerRight * D * (schurSigma C)⁻¹)
  let delta : ℝ :=
    (d : ℝ) *
      (adaptedHattedContrast P q j - adaptedHattedContrast P q p)
  have hCsymm : IsSymmetricBlockMat C := by
    dsimp only [C]
    exact Recurrence.isSymmetricBlockMat_adaptedMean P q p
  have hCpos : BlockPosDef C := by
    dsimp only [C]
    exact Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid p hfinp
  have hFsymm : IsSymmetricBlockMat F := by
    dsimp only [F]
    exact Recurrence.isSymmetricBlockMat_adaptedMean P q j
  have hFpos : BlockPosDef F := by
    dsimp only [F]
    exact Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid j hfinj
  have hCF : BlockMatLoewnerLE C F := by
    dsimp only [C, F]
    exact Recurrence.adaptedMean_le hstat hgrid hlj hjp hfinj hfinp
  have hCfull : (toFullBlockMat C).PosDef :=
    posDef_toFullBlockMat hCsymm hCpos
  have hCright : C.lowerRight.PosDef := posDef_lowerRight hCsymm hCpos
  have hFright : F.lowerRight.PosDef := posDef_lowerRight hFsymm hFpos
  have hCsigma : (schurSigma C).PosDef := by
    have hstar : (schurSigmaStar C).PosDef := hCright.inv
    apply posDef_of_posDef_schurBlock hstar
    rw [← Initialization.toFullBlockMat_eq_schurBlock hCsymm hCpos]
    exact hCfull
  have hFsigma : (schurSigma F).PosDef := by
    have hstar : (schurSigmaStar F).PosDef := hFright.inv
    apply posDef_of_posDef_schurBlock hstar
    rw [← Initialization.toFullBlockMat_eq_schurBlock hFsymm hFpos]
    exact posDef_toFullBlockMat hFsymm hFpos
  have hright : C.lowerRight ≤ F.lowerRight :=
    Initialization.le_of_matLoewnerLE hCright.isHermitian hFright.isHermitian
      (matLoewnerLE_lowerRight_of_blockMatLoewnerLE hCF)
  have hsigma : schurSigma C ≤ schurSigma F := by
    apply Initialization.le_of_matLoewnerLE hCsigma.isHermitian hFsigma.isHermitian
    refine (matLoewnerLE_schurSigma_skewCorrectedForm
      hCpos (schurSkew F)).trans ?_
    have hfixed := matLoewnerLE_skewCorrectedForm_of_blockMatLoewnerLE
      hCsymm hCpos hFsymm hFpos hCF (schurSkew F)
    simpa only [skewCorrectedForm, sub_self, Matrix.transpose_zero,
      Matrix.zero_mul, Matrix.mul_zero, add_zero] using hfixed
  have hQS : QS.PosSemidef := by
    dsimp only [QS]
    exact Matrix.le_iff.mp hsigma
  have hQR : QR.PosSemidef := by
    dsimp only [QR]
    exact Matrix.le_iff.mp hright
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact PortableHistory.trace_mul_nonneg hQS hCsigma.inv.posSemidef
  have hy0 : 0 ≤ y := by
    dsimp only [y]
    exact PortableHistory.trace_mul_nonneg hQR hCright.inv.posSemidef
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta]
    exact mul_nonneg (by positivity)
      (sub_nonneg.mpr
        (adaptedHattedContrast_le hstat hgrid hlj hjp hfinj hfinp))
  have hdiag : x + y ≤ delta := by
    simpa only [C, F, QS, QR, x, y, delta] using!
      schur_trace_gaps_le_hattedContrast_drop
        hCsymm hCpos hFsymm hFpos hCF
          (Persistence.blockSharp_adaptedMean_le hgrid p hfinp)
  have hxdelta : x ≤ delta := by
    linarith only [hdiag, hy0]
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    exact norm_nonneg _
  have hgood := normalized_schur_norm_gaps_le_hattedContrast_drop
    hCsymm hCpos hFsymm hFpos hCF
      (Persistence.blockSharp_adaptedMean_le hgrid p hfinp)
  have hgood' :
      ‖matSqrt (schurSigma C)⁻¹ * schurSigma F *
            matSqrt (schurSigma C)⁻¹ - 1‖ + b ≤ delta := by
    simpa only [C, F, b, delta, adaptedHattedContrast] using hgood
  have hbdelta : b ≤ delta := by
    have hnorm0 :
        0 ≤ ‖matSqrt (schurSigma C)⁻¹ * schurSigma F *
            matSqrt (schurSigma C)⁻¹ - 1‖ := norm_nonneg _
    linarith only [hgood', hnorm0]
  have hrightScale : F.lowerRight ≤ (1 + b) • C.lowerRight := by
    let N : Mat d := matSqrt C.lowerRight⁻¹ * F.lowerRight *
      matSqrt C.lowerRight⁻¹
    have hone : (1 : Mat d) ≤ N := Recurrence.one_le_normalize hCright hright
    have hgap : (N - 1).PosSemidef := Matrix.le_iff.mp hone
    have hgaple : N - 1 ≤ b • (1 : Mat d) := by
      dsimp only [b, N]
      exact le_norm_smul_one hgap
    have hNle : N ≤ (1 + b) • (1 : Mat d) := by
      refine Matrix.le_iff.mpr ?_
      have hps := Matrix.le_iff.mp hgaple
      have hrw : (1 + b) • (1 : Mat d) - N =
          b • (1 : Mat d) - (N - 1) := by
        rw [add_smul, one_smul]
        abel
      rwa [hrw]
    apply (conj_normalize hCright (1 + b)).mpr
    simpa only [N] using hNle
  have hquad := schurSkew_diff_quad_le_lowerRight_norm_gap
    hCsymm hCpos hFsymm hFpos hCF
  change Dᴴ * C.lowerRight * D ≤ b • QS at hquad
  have hDF : Dᴴ * F.lowerRight * D ≤
      ((1 + b) * b) • QS := by
    have hfirst := conj_le_conj D hrightScale
    have hfirst' : Dᴴ * F.lowerRight * D ≤
        (1 + b) • (Dᴴ * C.lowerRight * D) := by
      simpa only [Matrix.mul_smul, Matrix.smul_mul] using hfirst
    have hsecond := smul_le_smul_of_le (by positivity : 0 ≤ 1 + b) hquad
    have hsecond' : (1 + b) • (Dᴴ * C.lowerRight * D) ≤
        ((1 + b) * b) • QS := by
      simpa only [smul_smul] using hsecond
    exact hfirst'.trans hsecond'
  have hzBound : z ≤ ((1 + b) * b) * x := by
    have htrace := PortableHistory.trace_mul_le_trace_mul hCsigma.inv.posSemidef hDF
    dsimp only [z, x]
    calc
      Matrix.trace (Dᴴ * F.lowerRight * D * (schurSigma C)⁻¹) =
          Matrix.trace ((schurSigma C)⁻¹ *
            (Dᴴ * F.lowerRight * D)) := Matrix.trace_mul_comm _ _
      _ ≤ Matrix.trace ((schurSigma C)⁻¹ *
          (((1 + b) * b) • QS)) := htrace
      _ = ((1 + b) * b) * Matrix.trace (QS * (schurSigma C)⁻¹) := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
          Matrix.trace_mul_comm]
  have hbOne : b ≤ 1 := hbdelta.trans hsmall
  have honeb : 1 + b ≤ 2 := by linarith only [hbOne]
  have hbx : b * x ≤ delta * delta :=
    mul_le_mul hbdelta hxdelta hx0 hdelta0
  have hprod : (1 + b) * (b * x) ≤ 2 * (delta * delta) :=
    mul_le_mul honeb hbx (mul_nonneg hb0 hx0) (by norm_num)
  have hdeltaSq : delta * delta ≤ delta := by
    nlinarith only [hdelta0, hsmall]
  have hzTwo : z ≤ 2 * delta := by
    calc
      z ≤ ((1 + b) * b) * x := hzBound
      _ = (1 + b) * (b * x) := by ring
      _ ≤ 2 * (delta * delta) := hprod
      _ ≤ 2 * delta := mul_le_mul_of_nonneg_left hdeltaSq (by norm_num)
  have htraceEq := trace_inv_mul_sub_eq_schur_gaps
    hCsymm hCpos hFsymm hFpos
  change Matrix.trace
      ((toFullBlockMat C)⁻¹ * (toFullBlockMat F - toFullBlockMat C)) =
        x + y + z at htraceEq
  have htraceBound :
      Matrix.trace
          ((toFullBlockMat C)⁻¹ *
            (toFullBlockMat F - toFullBlockMat C)) ≤ 4 * delta := by
    rw [htraceEq]
    linarith only [hdiag, hzTwo, hdelta0]
  have hmean : toFullBlockMat F ≤
      (1 + Matrix.trace
          ((toFullBlockMat C)⁻¹ *
            (toFullBlockMat F - toFullBlockMat C))) •
        toFullBlockMat C :=
    Bridge.matrix_le_terminal_trace_sub hCfull
      (Recurrence.toFullBlockMat_adaptedMean_le
        hstat hgrid hlj hjp hfinj hfinp)
  have hscale :
      (1 + Matrix.trace
          ((toFullBlockMat C)⁻¹ *
            (toFullBlockMat F - toFullBlockMat C))) •
          toFullBlockMat C ≤
        (1 + 4 * delta) • toFullBlockMat C :=
    Persistence.smul_le_smul_of_le_right hCfull.posSemidef
      (by simpa only [add_comm] using add_le_add_left htraceBound 1)
  simpa only [C, F, delta, mul_assoc] using hmean.trans hscale

end

end HCPolySupport.HighContrast.Quenched
