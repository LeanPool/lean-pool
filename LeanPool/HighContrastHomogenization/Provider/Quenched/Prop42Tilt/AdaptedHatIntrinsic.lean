/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHattedCarrier
public import LeanPool.HighContrastHomogenization.Provider.Persistence.AdaptedPersistence
public import LeanPool.HighContrastHomogenization.Provider.Entry.ContrastBridge
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationSchur
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.SchurHelpers

/-!
# High-contrast homogenization: Provider.Quenched.Prop42Tilt.AdaptedHatIntrinsic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Intrinsic contrast from the hatted trace carrier

For a positive doubled block above its sharp, the intrinsic contrast is bounded
by a quadratic polynomial in the trace gap

`u = tr (σ σ₍⁻¹) - d`.

The quadratic term is necessary at unrestricted contrast.  The proof uses the
sharp ordering after a fixed Schur shear and therefore introduces no smallness
assumption.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-- A sharp-ordered positive block has intrinsic contrast controlled by its
unnormalized hatted trace gap. -/
theorem blockContrast_sub_one_le_traceGap_polynomial [NeZero d]
    {F : BlockMat d} (hsymm : IsSymmetricBlockMat F)
    (hpos : Book.Ch02.BlockPosDef F)
    (hsharp : BlockMatLoewnerLE (blockSharp F) F) :
    blockContrast F - 1 ≤
      (5 / 4 : ℝ) *
          (Matrix.trace (schurSigma F * F.lowerRight) - d) +
        (1 / 4 : ℝ) *
          (Matrix.trace (schurSigma F * F.lowerRight) - d) ^ 2 := by
  have : Nonempty (Fin d) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  let S : Mat d := schurSigma F
  let SStar : Mat d := schurSigmaStar F
  let K : Mat d := schurSkew F
  let T : Mat d := F.lowerRight
  let t : ℝ := relSize S SStar
  let u : ℝ := Matrix.trace (S * T) - d
  have hFfull : (toFullBlockMat F).PosDef :=
    posDef_toFullBlockMat hsymm hpos
  have hTpd : T.PosDef := posDef_lowerRight hsymm hpos
  have hdet : IsUnit F.lowerRight.det := isUnit_det_lowerRight hpos
  have hStarPd : SStar.PosDef := by
    simpa only [SStar, schurSigmaStar, T] using hTpd.inv
  have hform : toFullBlockMat F = schurBlock S SStar K := by
    simpa only [S, SStar, K] using Initialization.toFullBlockMat_eq_schurBlock hsymm hpos
  have hSchurPd : (schurBlock S SStar K).PosDef := by
    rw [← hform]
    exact hFfull
  have hSPd : S.PosDef := posDef_of_posDef_schurBlock hStarPd hSchurPd
  have hsharpFull : (toFullBlockMat (blockSharp F)).PosDef := by
    rw [toFullBlockMat_blockSharp]
    exact posDef_fullBlockSharp hFfull
  have hsharpSymm : IsSymmetricBlockMat (blockSharp F) :=
    isSymmetricBlockMat_of_posSemidef hsharpFull.posSemidef
  have hle : fullBlockSharp (schurBlock S SStar K) ≤ schurBlock S SStar K := by
    have h := le_of_blockMatLoewnerLE hsharpSymm hsymm hsharp
    rw [toFullBlockMat_blockSharp, hform] at h
    exact h
  have hsharpForm : fullBlockSharp (schurBlock S SStar K) =
      schurBlock SStar S (-Kᴴ) :=
    fullBlockSharp_schurBlock hSPd hStarPd
  have hconj := conj_le_conj (fullBlockShear K) hle
  rw [hsharpForm, Response.schurBlock_conj_shear,
    Response.schurBlock_conj_shear] at hconj
  have h11 := toBlocks₁₁_mono hconj
  have hKS :
      (K + Kᴴ)ᴴ * S⁻¹ * (K + Kᴴ) ≤ S - SStar := by
    have hneg : -Kᴴ - K = -(K + Kᴴ) := by abel
    rw [hneg, sub_self] at h11
    have h11' :
        SStar + (K + Kᴴ)ᴴ * S⁻¹ * (K + Kᴴ) ≤ S := by
      simpa only [toBlocks₁₁_schurBlock, Matrix.conjTranspose_neg, Matrix.neg_mul,
        Matrix.mul_neg, neg_neg, Matrix.zero_mul, Matrix.mul_zero, add_zero]
        using h11
    exact (le_sub_iff_add_le).mpr (by simpa [add_comm] using h11')
  have hStarLe : SStar ≤ S := by
    simpa only [S, SStar] using
      Initialization.schurSigmaStar_le_schurSigma hsymm hpos hsharp
  have ht1 : 1 ≤ t := by
    have hmono := relSize_mono_left hStarPd.posSemidef hSPd.posSemidef
      hStarPd hStarLe
    rw [relSize_self_eq_one hStarPd] at hmono
    exact hmono
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hTStar : SStar⁻¹ = T := by
    simpa only [SStar, T] using schurSigmaStar_inv F hdet
  let X : Mat d := matSqrt SStar⁻¹ * S * matSqrt SStar⁻¹
  have hXpd : X.PosDef := by
    simpa only [X] using posDef_normalize hSPd hStarPd
  have hOneX : (1 : Mat d) ≤ X := by
    have h := conj_le_conj (matSqrt SStar⁻¹) hStarLe
    rw [conjTranspose_matSqrt_inv hStarPd,
      matSqrt_inv_conj hStarPd] at h
    simpa only [X] using h
  have hrootSq : matSqrt SStar⁻¹ * matSqrt SStar⁻¹ = SStar⁻¹ :=
    (matSqrt_spec hStarPd.inv.posSemidef).2
  have htraceX : Matrix.trace X = Matrix.trace (S * T) := by
    calc
      Matrix.trace X =
          Matrix.trace (matSqrt SStar⁻¹ *
            (matSqrt SStar⁻¹ * S)) := by
              change Matrix.trace
                (matSqrt SStar⁻¹ * S * matSqrt SStar⁻¹) = _
              rw [Matrix.trace_mul_comm
                (matSqrt SStar⁻¹ * S) (matSqrt SStar⁻¹)]
      _ = Matrix.trace ((matSqrt SStar⁻¹ *
            matSqrt SStar⁻¹) * S) :=
        congrArg Matrix.trace (Matrix.mul_assoc _ _ _).symm
      _ = Matrix.trace (S * SStar⁻¹) := by
            rw [hrootSq, Matrix.trace_mul_comm]
      _ = Matrix.trace (S * T) := by rw [hTStar]
  have hu0 : 0 ≤ u := by
    have h := PortableHistory.trace_sub_one_nonneg hOneX
    rw [Matrix.trace_sub, htraceX, Matrix.trace_one] at h
    simpa only [u, Fintype.card_fin] using h
  have htGap : t ≤ 1 + u := by
    have h := PortableHistory.norm_le_one_add_trace_sub_one hXpd hOneX
    rw [Matrix.trace_sub, htraceX, Matrix.trace_one] at h
    simpa only [t, relSize, X, u, Fintype.card_fin] using h
  have hSle : S ≤ t • SStar := le_relSize_smul hSPd.posSemidef hStarPd
  have hTle : T ≤ t • S⁻¹ := by
    have hscaledPd : (t • SStar).PosDef := hStarPd.smul htpos
    have hinv : (t • SStar)⁻¹ = t⁻¹ • T := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        mul_inv_cancel₀ htpos.ne', one_smul, ← hTStar,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hStarPd)]
    have hstep := inv_le_inv_of_le hSPd hscaledPd hSle
    rw [hinv] at hstep
    have h := smul_le_smul_of_le (c := t) htpos.le hstep
    rwa [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul] at h
  have hKSterm :
      (K + Kᴴ)ᴴ * T * (K + Kᴴ) ≤
        (t * (t - 1)) • SStar := by
    have hfirst := conj_le_conj (K + Kᴴ) hTle
    have hfirst' :
        (K + Kᴴ)ᴴ * T * (K + Kᴴ) ≤
          t • ((K + Kᴴ)ᴴ * S⁻¹ * (K + Kᴴ)) := by
      simpa only [Matrix.mul_smul, Matrix.smul_mul] using hfirst
    have hsecond := smul_le_smul_of_le htpos.le hKS
    have hgap : S - SStar ≤ (t - 1) • SStar := by
      refine Matrix.le_iff.mpr ?_
      have hle := Matrix.le_iff.mp hSle
      have hrw : (t - 1) • SStar - (S - SStar) = t • SStar - S := by
        rw [sub_smul, one_smul]
        abel
      rwa [hrw]
    have hthird := smul_le_smul_of_le htpos.le hgap
    refine hfirst'.trans (hsecond.trans ?_)
    simpa only [smul_smul] using hthird
  let r : Mat d := (2 : ℝ)⁻¹ • (K + Kᴴ)
  let h : Mat d := (2 : ℝ)⁻¹ • (K - Kᴴ)
  have hrterm : rᴴ * T * r ≤
      ((t * (t - 1)) / 4) • SStar := by
    have hscaled := smul_le_smul_of_le (c := (4 : ℝ)⁻¹)
      (by norm_num) hKSterm
    have heq : rᴴ * T * r =
        (4 : ℝ)⁻¹ • ((K + Kᴴ)ᴴ * T * (K + Kᴴ)) := by
      change ((2 : ℝ)⁻¹ • (K + Kᴴ))ᴴ * T *
        ((2 : ℝ)⁻¹ • (K + Kᴴ)) = _
      simp only [Matrix.conjTranspose_smul, star_trivial,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      norm_num
    have hrhs : (4 : ℝ)⁻¹ • ((t * (t - 1)) • SStar) =
        ((t * (t - 1)) / 4) • SStar := by
      rw [smul_smul]
      congr 1
      ring
    calc
      rᴴ * T * r =
          (4 : ℝ)⁻¹ • ((K + Kᴴ)ᴴ * T * (K + Kᴴ)) := heq
      _ ≤ (4 : ℝ)⁻¹ • ((t * (t - 1)) • SStar) := hscaled
      _ = ((t * (t - 1)) / 4) • SStar := hrhs
  have hcorr : S + rᴴ * T * r ≤
      (t + (t * (t - 1)) / 4) • SStar := by
    have hsum := add_le_add hSle hrterm
    simpa only [add_smul] using hsum
  have hhskew : IsSkewMat h := by
    change IsSkewMat ((2 : ℝ)⁻¹ • (K - Kᴴ))
    rw [IsSkewMat, ← conjTranspose_eq_matTranspose,
      Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    rw [show Kᴴ - K = -(K - Kᴴ) by abel, smul_neg]
  have hdiff : K - h = r := by
    change K - (2 : ℝ)⁻¹ • (K - Kᴴ) =
      (2 : ℝ)⁻¹ • (K + Kᴴ)
    module
  have htheta : blockContrast F ≤ t + (t * (t - 1)) / 4 := by
    refine blockContrast_le (by nlinarith only [ht1]) hhskew ?_
    rw [← conjTranspose_eq_matTranspose, hdiff]
    simpa only [S, SStar, T] using Initialization.matLoewnerLE_of_le hcorr
  dsimp only [u, S, T] at hu0 htGap ⊢
  nlinarith only [htheta, ht1, htGap, hu0]

/-- The generic trace-gap polynomial specialized to the adapted hatted
contrast. -/
theorem adaptedContrast_sub_one_le_hatted_polynomial [NeZero d]
    {P : MeasureTheory.Measure (CoeffSpace d)} [MeasureTheory.IsProbabilityMeasure P]
    {l r : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    (hfin : HasFiniteAdaptedMean P q r) :
    blockContrast (adaptedMean P q r) - 1 ≤
      (5 / 4 : ℝ) * (d : ℝ) * (adaptedHattedContrast P q r - 1) +
        (1 / 4 : ℝ) * ((d : ℝ) * (adaptedHattedContrast P q r - 1)) ^ 2 := by
  have hsymm := Recurrence.isSymmetricBlockMat_adaptedMean P q r
  have hpos := Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq r hfin
  have hraw := blockContrast_sub_one_le_traceGap_polynomial
    hsymm hpos
    (Persistence.blockSharp_adaptedMean_le hq r hfin)
  have htrace :
      Matrix.trace
          (schurSigma (adaptedMean P q r) * (adaptedMean P q r).lowerRight) - d =
        (d : ℝ) * (adaptedHattedContrast P q r - 1) := by
    rw [adaptedHattedContrast,
      hattedContrast_eq_trace_lowerRight_mul hsymm hpos,
      Matrix.trace_mul_comm]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
    field_simp
  rw [htrace] at hraw
  simpa only [mul_assoc] using hraw

/-- The canonical adapted hatted carrier is at least one on a finite rounded
adapted mean. -/
theorem one_le_adaptedHattedContrast_of_rounded [NeZero d]
    {P : MeasureTheory.Measure (CoeffSpace d)} [MeasureTheory.IsProbabilityMeasure P]
    {l r : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    (hfin : HasFiniteAdaptedMean P q r) :
    1 ≤ adaptedHattedContrast P q r := by
  let E : BlockMat d := adaptedMean P q r
  have hsymm : IsSymmetricBlockMat E :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q r
  have hpos : Book.Ch02.BlockPosDef E :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq r hfin
  have hsharp : BlockMatLoewnerLE (blockSharp E) E :=
    Persistence.blockSharp_adaptedMean_le hq r hfin
  have hstarle : schurSigmaStar E ≤ schurSigma E :=
    Initialization.schurSigmaStar_le_schurSigma hsymm hpos hsharp
  have hRpd : E.lowerRight.PosDef := posDef_lowerRight hsymm hpos
  have htrace : Matrix.trace (E.lowerRight * schurSigmaStar E) ≤
      Matrix.trace (E.lowerRight * schurSigma E) :=
    PortableHistory.trace_mul_le_trace_mul hRpd.posSemidef hstarle
  have hdet : IsUnit E.lowerRight.det := isUnit_det_lowerRight hpos
  have hleft : Matrix.trace (E.lowerRight * schurSigmaStar E) = d := by
    rw [schurSigmaStar, Matrix.mul_nonsing_inv _ hdet, Matrix.trace_one]
    simp only [Fintype.card_fin]
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hscaled := mul_le_mul_of_nonneg_left htrace (inv_nonneg.mpr hdpos.le)
  rw [hleft, inv_mul_cancel₀ hdpos.ne'] at hscaled
  rw [adaptedHattedContrast,
    hattedContrast_eq_trace_lowerRight_mul hsymm hpos]
  simpa only [E] using hscaled

end

end Quenched
end HighContrast
end HCPolySupport
