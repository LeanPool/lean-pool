/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTraceBridge

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastGoodQuads

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Good quadratic control for ordered Schur data

The change of the Schur coupling between two ordered positive blocks is
controlled by the product of their two normalized diagonal gaps.  Together
with the hatted trace drop, this gives a dimension-sharp linear bound for all
three normalized Schur gaps.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem good_quad_scalar {a qC qF qS : ℝ}
    (ha : 0 < a) (hqC : 0 ≤ qC)
    (hscale : qF ≤ (1 + a) * qC)
    (hshear : ((1 + a) / a) ^ (2 : ℕ) * qC ≤
      qS + (1 - (1 + a) / a) ^ (2 : ℕ) * qF) :
    qC ≤ a * qS := by
  have hweighted :
      (1 - (1 + a) / a) ^ (2 : ℕ) * qF ≤
        (1 - (1 + a) / a) ^ (2 : ℕ) * ((1 + a) * qC) :=
    mul_le_mul_of_nonneg_left hscale (sq_nonneg _)
  have hcoeff :
      (((1 + a) / a) ^ (2 : ℕ) -
          (1 - (1 + a) / a) ^ (2 : ℕ) * (1 + a)) * qC ≤ qS := by
    nlinarith only [hshear, hweighted]
  have hidentity :
      ((1 + a) / a) ^ (2 : ℕ) -
          (1 - (1 + a) / a) ^ (2 : ℕ) * (1 + a) =
        (1 + a) / a := by
    field_simp
    ring
  rw [hidentity] at hcoeff
  have hmul := mul_le_mul_of_nonneg_left hcoeff ha.le
  have hcancel : a * ((1 + a) / a * qC) = (1 + a) * qC := by
    field_simp
  rw [hcancel] at hmul
  have haq : 0 ≤ a * qC := mul_nonneg ha.le hqC
  nlinarith only [hmul, haq]

private theorem posDef_schurSigma_of_blockPosDef {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : BlockPosDef H) :
    (schurSigma H).PosDef := by
  have hfull : (toFullBlockMat H).PosDef :=
    posDef_toFullBlockMat hsymm hpos
  have hstar : (schurSigmaStar H).PosDef :=
    (posDef_lowerRight hsymm hpos).inv
  have hform : toFullBlockMat H =
      schurBlock (schurSigma H) (schurSigmaStar H) (schurSkew H) :=
    Initialization.toFullBlockMat_eq_schurBlock hsymm hpos
  apply posDef_of_posDef_schurBlock hstar
  rwa [← hform]

private theorem schurSigma_le_of_blockMatLoewnerLE
    {C F : BlockMat d}
    (hCsymm : IsSymmetricBlockMat C) (hCpos : BlockPosDef C)
    (hFsymm : IsSymmetricBlockMat F) (hFpos : BlockPosDef F)
    (hCF : BlockMatLoewnerLE C F) : schurSigma C ≤ schurSigma F := by
  have hCsigma := posDef_schurSigma_of_blockPosDef hCsymm hCpos
  have hFsigma := posDef_schurSigma_of_blockPosDef hFsymm hFpos
  apply Initialization.le_of_matLoewnerLE hCsigma.isHermitian hFsigma.isHermitian
  refine (matLoewnerLE_schurSigma_skewCorrectedForm
    hCpos (schurSkew F)).trans ?_
  have hfixed := matLoewnerLE_skewCorrectedForm_of_blockMatLoewnerLE
    hCsymm hCpos hFsymm hFpos hCF (schurSkew F)
  simpa only [skewCorrectedForm, sub_self, Matrix.transpose_zero,
    Matrix.zero_mul, Matrix.mul_zero, add_zero] using hfixed

/-- If the lower-right fine block is at most `1 + a` times the coarse one,
then the coarse-normalized square of the Schur-coupling change is at most `a`
times the upper Schur gap. -/
theorem schurSkew_diff_quad_le_of_lowerRight_le
    {C F : BlockMat d}
    (hCsymm : IsSymmetricBlockMat C) (hCpos : BlockPosDef C)
    (hFsymm : IsSymmetricBlockMat F) (hFpos : BlockPosDef F)
    (hCF : BlockMatLoewnerLE C F) {a : ℝ} (ha : 0 < a)
    (hscale : F.lowerRight ≤ (1 + a) • C.lowerRight) :
    (schurSkew F - schurSkew C)ᴴ * C.lowerRight *
        (schurSkew F - schurSkew C) ≤
      a • (schurSigma F - schurSigma C) := by
  let D : Mat d := schurSkew F - schurSkew C
  let QC : Mat d := Dᴴ * C.lowerRight * D
  let QF : Mat d := Dᴴ * F.lowerRight * D
  let QS : Mat d := schurSigma F - schurSigma C
  have hCright : C.lowerRight.PosDef := posDef_lowerRight hCsymm hCpos
  have hFright : F.lowerRight.PosDef := posDef_lowerRight hFsymm hFpos
  have hsigma : schurSigma C ≤ schurSigma F :=
    schurSigma_le_of_blockMatLoewnerLE hCsymm hCpos hFsymm hFpos hCF
  have hQC : QC.PosSemidef :=
    hCright.posSemidef.conjTranspose_mul_mul_same D
  have hQF : QF.PosSemidef :=
    hFright.posSemidef.conjTranspose_mul_mul_same D
  have hQS : QS.PosSemidef := Matrix.le_iff.mp hsigma
  have hQscale : QF ≤ (1 + a) • QC := by
    have hconj := conj_le_conj D hscale
    simp only [Matrix.mul_smul, Matrix.smul_mul] at hconj
    exact hconj
  let eta : ℝ := (1 + a) / a
  have hshear := schurSkew_diff_shear_inequality
    hCsymm hCpos hFsymm hFpos hCF eta
  change eta ^ (2 : ℕ) • QC ≤ QS +
    (1 - eta) ^ (2 : ℕ) • QF at hshear
  change QC ≤ a • QS
  apply Initialization.le_of_dotProduct_mulVec_le hQC.isHermitian
    (hQS.smul ha.le).isHermitian
  intro x
  let qC : ℝ := x ⬝ᵥ QC *ᵥ x
  let qF : ℝ := x ⬝ᵥ QF *ᵥ x
  let qS : ℝ := x ⬝ᵥ QS *ᵥ x
  have hqC : 0 ≤ qC := hQC.dotProduct_mulVec_nonneg x
  have hqscale := Initialization.dotProduct_mulVec_le_of_le hQscale x
  have hqshear := Initialization.dotProduct_mulVec_le_of_le hshear x
  have hqscale' : qF ≤ (1 + a) * qC := by
    simpa only [qF, qC, Matrix.smul_mulVec, dotProduct_smul,
      star_trivial, smul_eq_mul] using hqscale
  have hqshear' : eta ^ (2 : ℕ) * qC ≤
      qS + (1 - eta) ^ (2 : ℕ) * qF := by
    simpa only [qC, qF, qS, Matrix.smul_mulVec, Matrix.add_mulVec,
      dotProduct_smul, dotProduct_add, star_trivial, smul_eq_mul] using hqshear
  have hscalar := good_quad_scalar ha hqC hqscale'
    (by simpa only [eta] using hqshear')
  simpa only [qC, qS, Matrix.smul_mulVec, dotProduct_smul,
    star_trivial, smul_eq_mul] using hscalar

private theorem lowerRight_le_one_add_norm_gap_smul
    {C F : BlockMat d}
    (hCsymm : IsSymmetricBlockMat C) (hCpos : BlockPosDef C)
    (hFsymm : IsSymmetricBlockMat F) (hFpos : BlockPosDef F)
    (hCF : BlockMatLoewnerLE C F) :
    F.lowerRight ≤
      (1 + ‖matSqrt C.lowerRight⁻¹ * F.lowerRight *
        matSqrt C.lowerRight⁻¹ - 1‖) • C.lowerRight := by
  have hCright : C.lowerRight.PosDef := posDef_lowerRight hCsymm hCpos
  have hFright : F.lowerRight.PosDef := posDef_lowerRight hFsymm hFpos
  have hright : C.lowerRight ≤ F.lowerRight :=
    Initialization.le_of_matLoewnerLE hCright.isHermitian hFright.isHermitian
      (matLoewnerLE_lowerRight_of_blockMatLoewnerLE hCF)
  let P : Mat d := matSqrt C.lowerRight⁻¹ * F.lowerRight *
    matSqrt C.lowerRight⁻¹
  let a : ℝ := ‖P - 1‖
  have hone : (1 : Mat d) ≤ P := Recurrence.one_le_normalize hCright hright
  have hgap : (P - 1).PosSemidef := Matrix.le_iff.mp hone
  have hgaple : P - 1 ≤ a • (1 : Mat d) := le_norm_smul_one hgap
  have hPle : P ≤ (1 + a) • (1 : Mat d) := by
    refine Matrix.le_iff.mpr ?_
    have hps := Matrix.le_iff.mp hgaple
    have hrw : (1 + a) • (1 : Mat d) - P =
        a • (1 : Mat d) - (P - 1) := by
      rw [add_smul, one_smul]
      abel
    rwa [hrw]
  apply (conj_normalize hCright (1 + a)).mpr
  simpa only [P, a] using hPle

/-- The optimized shear estimate, including the zero-gap endpoint.  Its
coefficient is exactly the lower-right normalized spectral gap. -/
theorem schurSkew_diff_quad_le_lowerRight_norm_gap
    {C F : BlockMat d}
    (hCsymm : IsSymmetricBlockMat C) (hCpos : BlockPosDef C)
    (hFsymm : IsSymmetricBlockMat F) (hFpos : BlockPosDef F)
    (hCF : BlockMatLoewnerLE C F) :
    (schurSkew F - schurSkew C)ᴴ * C.lowerRight *
        (schurSkew F - schurSkew C) ≤
      ‖matSqrt C.lowerRight⁻¹ * F.lowerRight *
          matSqrt C.lowerRight⁻¹ - 1‖ •
        (schurSigma F - schurSigma C) := by
  let D : Mat d := schurSkew F - schurSkew C
  let QC : Mat d := Dᴴ * C.lowerRight * D
  let QS : Mat d := schurSigma F - schurSigma C
  let a : ℝ := ‖matSqrt C.lowerRight⁻¹ * F.lowerRight *
    matSqrt C.lowerRight⁻¹ - 1‖
  have hCright : C.lowerRight.PosDef := posDef_lowerRight hCsymm hCpos
  have hFright : F.lowerRight.PosDef := posDef_lowerRight hFsymm hFpos
  have hright : C.lowerRight ≤ F.lowerRight :=
    Initialization.le_of_matLoewnerLE hCright.isHermitian hFright.isHermitian
      (matLoewnerLE_lowerRight_of_blockMatLoewnerLE hCF)
  have hsigma : schurSigma C ≤ schurSigma F :=
    schurSigma_le_of_blockMatLoewnerLE hCsymm hCpos hFsymm hFpos hCF
  have hQC : QC.PosSemidef :=
    hCright.posSemidef.conjTranspose_mul_mul_same D
  have hQS : QS.PosSemidef := Matrix.le_iff.mp hsigma
  have hscale := lowerRight_le_one_add_norm_gap_smul
    hCsymm hCpos hFsymm hFpos hCF
  change F.lowerRight ≤ (1 + a) • C.lowerRight at hscale
  change QC ≤ a • QS
  by_cases ha0 : a = 0
  · have hFC : F.lowerRight ≤ C.lowerRight := by
      simpa only [ha0, add_zero, one_smul] using hscale
    have hrightEq : F.lowerRight = C.lowerRight :=
      le_antisymm hFC hright
    rw [ha0, zero_smul]
    apply Initialization.le_of_dotProduct_mulVec_le hQC.isHermitian
      Matrix.isHermitian_zero
    intro x
    let qC : ℝ := x ⬝ᵥ QC *ᵥ x
    let qS : ℝ := x ⬝ᵥ QS *ᵥ x
    have hqS : 0 ≤ qS := hQS.dotProduct_mulVec_nonneg x
    simp only [Matrix.zero_mulVec, dotProduct_zero]
    change qC ≤ 0
    refine le_of_forall_pos_le_add fun eps heps => ?_
    let delta : ℝ := eps / (qS + 1)
    have hden : 0 < qS + 1 := by linarith only [hqS]
    have hdelta : 0 < delta := div_pos heps hden
    have hself : F.lowerRight ≤ (1 + delta) • C.lowerRight := by
      rw [hrightEq]
      refine Matrix.le_iff.mpr ?_
      have hps := hCright.posSemidef.smul hdelta.le
      have hrw : (1 + delta) • C.lowerRight - C.lowerRight =
          delta • C.lowerRight := by
        rw [add_smul, one_smul]
        abel
      rwa [hrw]
    have hquad := schurSkew_diff_quad_le_of_lowerRight_le
      hCsymm hCpos hFsymm hFpos hCF hdelta hself
    change QC ≤ delta • QS at hquad
    have hx := Initialization.dotProduct_mulVec_le_of_le hquad x
    have hx' : qC ≤ delta * qS := by
      simpa only [qC, qS, Matrix.smul_mulVec, dotProduct_smul,
        star_trivial, smul_eq_mul] using hx
    have hfrac : delta * qS ≤ eps := by
      have hqSle : qS ≤ qS + 1 := by
        linarith only [(zero_le_one : (0 : ℝ) ≤ 1)]
      have hdelta0 : 0 ≤ delta := hdelta.le
      calc
        delta * qS ≤ delta * (qS + 1) :=
          mul_le_mul_of_nonneg_left hqSle hdelta0
        _ = eps := by
          dsimp only [delta]
          field_simp
    simpa only [zero_add] using hx'.trans hfrac
  · have ha : 0 < a := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha0)
    exact schurSkew_diff_quad_le_of_lowerRight_le
      hCsymm hCpos hFsymm hFpos hCF ha hscale

/-- The normalized change of the Schur coupling is bounded by the hatted
carrier drop.  Together with `normalized_schur_norm_gaps_le_hattedContrast_drop`
this is the full good-quadratics estimate. -/
theorem normalized_schurSkew_diff_le_hattedContrast_drop
    [NeZero d] {C F : BlockMat d}
    (hCsymm : IsSymmetricBlockMat C) (hCpos : BlockPosDef C)
    (hFsymm : IsSymmetricBlockMat F) (hFpos : BlockPosDef F)
    (hCF : BlockMatLoewnerLE C F)
    (hCsharp : BlockMatLoewnerLE (blockSharp C) C) :
    ‖matSqrt C.lowerRight * (schurSkew F - schurSkew C) *
        matSqrt (schurSigma C)⁻¹‖ ≤
      (d : ℝ) * (hattedContrast F - hattedContrast C) := by
  let D : Mat d := schurSkew F - schurSkew C
  let R : Mat d := matSqrt C.lowerRight
  let T : Mat d := matSqrt (schurSigma C)⁻¹
  let N : Mat d := R * D * T
  let QC : Mat d := Dᴴ * C.lowerRight * D
  let QS : Mat d := schurSigma F - schurSigma C
  let MS : Mat d := T * QS * T
  let a : ℝ := ‖matSqrt C.lowerRight⁻¹ * F.lowerRight *
    matSqrt C.lowerRight⁻¹ - 1‖
  let b : ℝ := ‖matSqrt (schurSigma C)⁻¹ * schurSigma F *
    matSqrt (schurSigma C)⁻¹ - 1‖
  have hCright : C.lowerRight.PosDef := posDef_lowerRight hCsymm hCpos
  have hCsigma : (schurSigma C).PosDef :=
    posDef_schurSigma_of_blockPosDef hCsymm hCpos
  have hsigma : schurSigma C ≤ schurSigma F :=
    schurSigma_le_of_blockMatLoewnerLE hCsymm hCpos hFsymm hFpos hCF
  have hQS : QS.PosSemidef := Matrix.le_iff.mp hsigma
  have hMS : MS.PosSemidef := posSemidef_normalize hQS hCsigma
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hquad := schurSkew_diff_quad_le_lowerRight_norm_gap
    hCsymm hCpos hFsymm hFpos hCF
  change QC ≤ a • QS at hquad
  have hRsymm : Rᴴ = R :=
    (matSqrt_spec hCright.posSemidef).1.isHermitian
  have hTsymm : Tᴴ = T :=
    (matSqrt_spec hCsigma.inv.posSemidef).1.isHermitian
  have hRR : R * R = C.lowerRight :=
    (matSqrt_spec hCright.posSemidef).2
  have hNN : Nᴴ * N = T * QC * T := by
    simp only [N, Matrix.conjTranspose_mul, hRsymm, hTsymm]
    simp only [QC]
    rw [← hRR]
    noncomm_ring
  have hMSform : MS =
      matSqrt (schurSigma C)⁻¹ * schurSigma F *
        matSqrt (schurSigma C)⁻¹ - 1 := by
    simp only [MS, QS, T, Matrix.mul_sub, Matrix.sub_mul]
    rw [matSqrt_inv_conj hCsigma]
  have hconj : Nᴴ * N ≤ a • MS := by
    have h := conj_le_conj' hTsymm hquad
    simp only [Matrix.mul_smul, Matrix.smul_mul] at h
    rwa [hNN]
  have hnormsq : ‖N‖ * ‖N‖ ≤ a * b := by
    have hnorm := norm_le_norm_of_le
      (Matrix.posSemidef_conjTranspose_mul_self N) (hMS.smul ha) hconj
    rw [Matrix.l2_opNorm_conjTranspose_mul_self, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha, hMSform] at hnorm
    exact hnorm
  have hNbound : ‖N‖ ≤ a + b := by
    have habSquare : 0 ≤ (a - b) ^ (2 : ℕ) := sq_nonneg _
    have hN0 : 0 ≤ ‖N‖ := norm_nonneg _
    nlinarith only [hnormsq, habSquare, hN0, ha, hb]
  have hdiag := normalized_schur_norm_gaps_le_hattedContrast_drop
    hCsymm hCpos hFsymm hFpos hCF hCsharp
  have hab : a + b ≤
      (d : ℝ) * (hattedContrast F - hattedContrast C) := by
    simpa only [a, b, add_comm] using hdiag
  change ‖N‖ ≤ _
  exact hNbound.trans hab

/-- The three normalized Schur gaps satisfy the source good-quadratics bound:
the sum of the two diagonal gaps and the coupling gap are each charged to the
same hatted carrier drop. -/
theorem normalized_schur_good_quads_le_hattedContrast_drop
    [NeZero d] {C F : BlockMat d}
    (hCsymm : IsSymmetricBlockMat C) (hCpos : BlockPosDef C)
    (hFsymm : IsSymmetricBlockMat F) (hFpos : BlockPosDef F)
    (hCF : BlockMatLoewnerLE C F)
    (hCsharp : BlockMatLoewnerLE (blockSharp C) C) :
    max
        (‖matSqrt (schurSigma C)⁻¹ * schurSigma F *
              matSqrt (schurSigma C)⁻¹ - 1‖ +
          ‖matSqrt C.lowerRight⁻¹ * F.lowerRight *
              matSqrt C.lowerRight⁻¹ - 1‖)
        ‖matSqrt C.lowerRight * (schurSkew F - schurSkew C) *
            matSqrt (schurSigma C)⁻¹‖ ≤
      (d : ℝ) * (hattedContrast F - hattedContrast C) := by
  exact max_le
    (normalized_schur_norm_gaps_le_hattedContrast_drop
      hCsymm hCpos hFsymm hFpos hCF hCsharp)
    (normalized_schurSkew_diff_le_hattedContrast_drop
      hCsymm hCpos hFsymm hFpos hCF hCsharp)

/-- Good quadratics on one rounded adapted grid, with the later scale as the
coarse normalization. -/
theorem adaptedMean_normalized_schur_good_quads_le_hattedContrast_drop
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j p : ℤ} (hlj : l ≤ j) (hjp : j ≤ p)
    (hintj : HasFiniteAdaptedMean P q j)
    (hintp : HasFiniteAdaptedMean P q p) :
    max
        (‖matSqrt (schurSigma (adaptedMean P q p))⁻¹ *
              schurSigma (adaptedMean P q j) *
              matSqrt (schurSigma (adaptedMean P q p))⁻¹ - 1‖ +
          ‖matSqrt (adaptedMean P q p).lowerRight⁻¹ *
              (adaptedMean P q j).lowerRight *
              matSqrt (adaptedMean P q p).lowerRight⁻¹ - 1‖)
        ‖matSqrt (adaptedMean P q p).lowerRight *
            (schurSkew (adaptedMean P q j) -
              schurSkew (adaptedMean P q p)) *
            matSqrt (schurSigma (adaptedMean P q p))⁻¹‖ ≤
      (d : ℝ) *
        (adaptedHattedContrast P q j - adaptedHattedContrast P q p) := by
  apply normalized_schur_good_quads_le_hattedContrast_drop
  · exact Recurrence.isSymmetricBlockMat_adaptedMean P q p
  · exact Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq p hintp
  · exact Recurrence.isSymmetricBlockMat_adaptedMean P q j
  · exact Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq j hintj
  · exact Recurrence.adaptedMean_le hP hq hlj hjp hintj hintp
  · exact Persistence.blockSharp_adaptedMean_le hq p hintp

end

end HCPolySupport.HighContrast.Quenched
