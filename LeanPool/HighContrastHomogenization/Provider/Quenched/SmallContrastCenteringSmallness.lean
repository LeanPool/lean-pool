/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHattedCarrier
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRecenteredSharp
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSymmetricSkew
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCalibrationAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Response.RandomAdaptedResponseCompactInsertion

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCenteringSmallness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The smallness clauses for the centering estimate

The two matrix smallness hypotheses and the two trace bounds consumed by the
generic centering estimate, derived from the hatted contrast of the annealed
block alone: the normalized Schur excess has trace `d·(hat − 1)` and is
positive semidefinite, so the diagonal gap is `ε`-small in the Loewner order;
the recentered sharp order and the symmetric-skew bound make the symmetric
skew coordinate `ε/2`-small in the same normalized sense.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The gap trace in normalized form. -/
theorem trace_gap_eq_trace_centeredResponseX {S SStar : Mat d}
    (hStar : SStar.PosDef) :
    Matrix.trace ((S - SStar) * SStar⁻¹) =
      Matrix.trace (Response.centeredResponseX S SStar) := by
  set N : Mat d := matSqrt SStar⁻¹ with hN
  have hNN : N * N = SStar⁻¹ := (matSqrt_spec hStar.inv.posSemidef).2
  have hunit : N * SStar * N = 1 := by
    have h := Response.matSqrt_mul_inv_mul_matSqrt hStar.inv
    simpa only [← hN, Matrix.nonsing_inv_nonsing_inv SStar
      (isUnit_det_of_posDef hStar)] using h
  calc
    Matrix.trace ((S - SStar) * SStar⁻¹) =
        Matrix.trace ((S - SStar) * (N * N)) := by rw [hNN]
    _ = Matrix.trace (N * ((S - SStar) * N)) := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    _ = Matrix.trace (Response.centeredResponseX S SStar) := by
        congr 1
        have hexp : N * ((S - SStar) * N) = N * S * N - N * SStar * N := by
          rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
            Matrix.mul_assoc]
        rw [hexp, hunit, Response.centeredResponseX, ← hN]

/-- The Loewner form of the diagonal gap from its trace. -/
theorem gap_le_smul_of_trace {S SStar : Mat d}
    (hStar : SStar.PosDef) (horder : SStar ≤ S) {eps : ℝ}
    (htr : Matrix.trace (Response.centeredResponseX S SStar) ≤ eps) :
    S - SStar ≤ eps • SStar := by
  set N : Mat d := matSqrt SStar⁻¹ with hN
  have hNN : N * N = SStar⁻¹ := (matSqrt_spec hStar.inv.posSemidef).2
  have hNherm : Nᴴ = N := (matSqrt_spec hStar.inv.posSemidef).1.isHermitian
  have hNunit : IsUnit N.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hStar.inv)
  have hNinvherm : (N⁻¹)ᴴ = N⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hNherm]
  have hXpsd := Response.centeredResponseX_posSemidef hStar horder
  have hXle : Response.centeredResponseX S SStar ≤
      Matrix.trace (Response.centeredResponseX S SStar) • (1 : Mat d) :=
    psd_le_smul_one hXpsd fun x => psd_quad_le_trace hXpsd x
  have hsmul1Herm : ∀ c : ℝ, (c • (1 : Mat d)).IsHermitian := fun c => by
    show (c • (1 : Mat d))ᴴ = c • (1 : Mat d)
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
  have hXle2 : Response.centeredResponseX S SStar ≤ eps • (1 : Mat d) := by
    refine le_trans hXle (Initialization.le_of_dotProduct_mulVec_le
      (hsmul1Herm _) (hsmul1Herm _) fun x => ?_)
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right htr (dotProduct_self_nonneg' x)
  have hXeq : Response.centeredResponseX S SStar = N * S * N - 1 := by
    rw [Response.centeredResponseX, ← hN]
  have hconj := conj_le_conj' (C := N⁻¹) hNinvherm hXle2
  rw [hXeq] at hconj
  have hstarinv : N⁻¹ * N⁻¹ = SStar := by
    rw [← Matrix.mul_inv_rev, hNN,
      Matrix.nonsing_inv_nonsing_inv SStar (isUnit_det_of_posDef hStar)]
  have hL : N⁻¹ * (N * S * N - 1) * N⁻¹ = S - SStar := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    have h1 : N⁻¹ * (N * S * N) * N⁻¹ = S := by
      calc
        N⁻¹ * (N * S * N) * N⁻¹ = N⁻¹ * N * S * (N * N⁻¹) := by
          noncomm_ring
        _ = S := by
          rw [Matrix.nonsing_inv_mul N hNunit,
            Matrix.mul_nonsing_inv N hNunit, Matrix.one_mul,
            Matrix.mul_one]
    have h2 : N⁻¹ * (1 : Mat d) * N⁻¹ = SStar := by
      rw [Matrix.mul_one, hstarinv]
    rw [h1, h2]
  have hR : N⁻¹ * (eps • (1 : Mat d)) * N⁻¹ = eps • SStar := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hstarinv]
  rw [hL, hR] at hconj
  exact hconj

/-- **The smallness supply for the centering estimate.**  From the annealed
block's Schur representation and the hatted-contrast bound
`d·(hat − 1) ≤ ε` alone: the diagonal order, the two Loewner smallness
clauses, and the two trace bounds, exactly as the generic centering estimate
consumes them. -/
theorem centering_smallness_supply [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Book.Ch02.Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K)
    {eps : ℝ} (hpos : 0 < eps)
    (htr : (d : ℝ) * (schurHattedContrast S SStar - 1) ≤ eps) :
    SStar ≤ S ∧
    S - SStar ≤ eps • SStar ∧
    Response.responseSymmetric K * SStar⁻¹ * Response.responseSymmetric K ≤
      (eps ^ 2 / 4) • SStar ∧
    Matrix.trace ((S - SStar) * SStar⁻¹) ≤ eps ∧
    Matrix.trace (Response.responseSymmetric K * SStar⁻¹ *
      Response.responseSymmetric K * SStar⁻¹) ≤ (d : ℝ) * eps ^ 2 / 4 := by
  have horder : SStar ≤ S :=
    Response.annealed_schurStar_le_schur U hint hS hStar hE
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have htrX : Matrix.trace (Response.centeredResponseX S SStar) ≤ eps := by
    rw [schurHattedContrast_sub_one_eq_trace_centeredResponseX S SStar]
      at htr
    rwa [← mul_assoc, mul_inv_cancel₀ hd0, one_mul] at htr
  have hgapM : S - SStar ≤ eps • SStar :=
    gap_le_smul_of_trace hStar horder htrX
  have htrGap : Matrix.trace ((S - SStar) * SStar⁻¹) ≤ eps := by
    rw [trace_gap_eq_trace_centeredResponseX hStar]
    exact htrX
  -- the recentered sharp order in flattened Schur form
  have hE2 : toFullBlockMat (Response.skewBlockCongr (Response.responseSkew K)
      (annealedBlock P (U : Set (Vec d)))) =
      schurBlock S SStar (Response.responseSymmetric K) := by
    have h := toFullBlockMat_skewBlockCongr_of_schurBlock
      (Response.responseSkew K) hE
    rwa [Response.sub_responseSkew] at h
  have hvol : 0 < (volume (U : Set (Vec d))).toReal :=
    ENNReal.toReal_pos (U.isDomain.isOpen.measure_pos volume U.nonempty).ne'
      U.isDomain.volume_lt_top.ne
  have hposA : BlockPosDef (Response.skewBlockCongr (Response.responseSkew K)
      (annealedBlock P (U : Set (Vec d)))) :=
    Response.blockPosDef_skewBlockCongr
      (Sharp.blockPosDef_annealedBlock_of_volume_pos U.isDomain hvol hint)
  have hsymA : IsSymmetricBlockMat (Response.skewBlockCongr (Response.responseSkew K)
      (annealedBlock P (U : Set (Vec d)))) :=
    Response.isSymmetricBlockMat_skewBlockCongr
      (Recurrence.isSymmetricBlockMat_annealedBlock P (U : Set (Vec d)))
  have hsharpA := blockSharp_skewBlockCongr_annealedBlock_le U hint
    (Response.responseSkew K) (Response.is_skew_mat_response_skew K)
  have hfull := fullBlockSharp_le_of_blockMatLoewnerLE hsymA hposA hsharpA
  rw [hE2] at hfull
  -- the symmetric-skew smallness at `θ = 1 + ε`
  have hsmulHermStar : ∀ c : ℝ, (c • SStar).IsHermitian := fun c => by
    show (c • SStar)ᴴ = c • SStar
    rw [Matrix.conjTranspose_smul, hStar.isHermitian.eq, star_trivial]
  have hS_le : S ≤ (1 + eps) • SStar := by
    refine Initialization.le_of_dotProduct_mulVec_le hS.isHermitian
      (hsmulHermStar (1 + eps)) fun x => ?_
    have h := Initialization.dotProduct_mulVec_le_of_le hgapM x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul] at h
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    linarith only [h]
  have hskew0 := symmetricSchurSkew_conj_le_of_sharp_le hS hStar
    (Response.responseSymmetric_isHermitian K) hfull
    (show (1 : ℝ) < 1 + eps by linarith only [hpos]) hS_le
  rw [Response.responseSymmetric_isHermitian] at hskew0
  have hscal : (1 + eps - 1) ^ 2 / 4 = eps ^ 2 / 4 := by ring
  rw [hscal] at hskew0
  -- the skew trace bound
  have htrSkew : Matrix.trace (Response.responseSymmetric K * SStar⁻¹ *
      Response.responseSymmetric K * SStar⁻¹) ≤ (d : ℝ) * eps ^ 2 / 4 := by
    have h := PortableHistory.trace_mul_le_trace_mul hStar.inv.posSemidef hskew0
    have hrhs : Matrix.trace (SStar⁻¹ * ((eps ^ 2 / 4) • SStar)) =
        (d : ℝ) * eps ^ 2 / 4 := by
      rw [Matrix.mul_smul, Matrix.trace_smul,
        Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hStar),
        Matrix.trace_one, smul_eq_mul, Fintype.card_fin]
      ring
    calc
      Matrix.trace (Response.responseSymmetric K * SStar⁻¹ *
          Response.responseSymmetric K * SStar⁻¹) =
          Matrix.trace (SStar⁻¹ * (Response.responseSymmetric K * SStar⁻¹ *
            Response.responseSymmetric K)) := Matrix.trace_mul_comm _ _
      _ ≤ Matrix.trace (SStar⁻¹ * ((eps ^ 2 / 4) • SStar)) := h
      _ = (d : ℝ) * eps ^ 2 / 4 := hrhs
  exact ⟨horder, hgapM, hskew0, htrGap, htrSkew⟩

end

end HCPolySupport.HighContrast.Quenched
