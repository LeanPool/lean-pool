/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakEnergyTail
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenterVariance
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileSkewMeasurability

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastAdjointMirrors

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adjoint mirrors: bad energy and centering variance

The adjoint sides of the bad-event optimizer energy and of the centering
variance, by the same source-envelope and single-cell-variance routes as the
primal sides; the adjoint state is the sign-congruent primal state at the
transposed sample, so every bound transports through the sign congruence
with the plus load in place of the minus load.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory Set

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The adjoint centering variance** at the recentered samples is bounded
by the terminal single-cell fluctuation carrier in the adapted-mean
normalization. -/
theorem profileAdjointCenterVariance_le_variance
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {m : Mat d} (hm : m.PosDef) {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t)
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P q t))
    (h0 : Mat d) (hh0 : IsSkewMat h0) (p r : Vec d) :
    Response.profileAdjointCenterVariance P m hq t
        (fun a => a.subSkew h0 hh0) p r ≤
      ENNReal.ofReal
          (Response.diagonalWeakMetricFactor m
              (Response.skewBlockCongr h0 (adaptedMean P q t)) *
            Response.diagonalWeakLoadPlus
              (Response.skewBlockCongr h0 (adaptedMean P q t)) p r) *
        scaleVariance P q (adaptedMean P q t) t := by
  classical
  have hEsym : IsSymmetricBlockMat (adaptedMean P q t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hEhatsym : IsSymmetricBlockMat
      (Response.skewBlockCongr h0 (adaptedMean P q t)) :=
    Response.isSymmetricBlockMat_skewBlockCongr (g := h0) hEsym
  have hEhatpd : Book.Ch02.BlockPosDef
      (Response.skewBlockCongr h0 (adaptedMean P q t)) :=
    Response.blockPosDef_skewBlockCongr (g := h0) hEt
  set C : ℝ := Response.diagonalWeakMetricFactor m
      (Response.skewBlockCongr h0 (adaptedMean P q t)) *
    Response.diagonalWeakLoadPlus
      (Response.skewBlockCongr h0 (adaptedMean P q t)) p r with hC
  have hC0 : 0 ≤ C :=
    mul_nonneg (Response.diagonalWeakMetricFactor_nonneg m _)
      (Response.diagonalWeakLoadPlus_nonneg _ p r)
  set Z : CoeffSpace d → ℝ := fun a =>
    schattenSize 2
      (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
      (adaptedMean P q t)
    with hZ
  have hZ0 : ∀ a, 0 ≤ Z a := fun a =>
    Recurrence.zero_le_schattenNorm
      (isSymmetricBlockMat_normalizedBlock (F := adaptedMean P q t)
        (isSymmetricBlockMat_blockSub
          (isSymmetricBlockMat_coarseBlock _ _) hEsym)) _
  have hZmeas : AEStronglyMeasurable Z P := by
    rw [hZ]
    refine Transport.aestronglyMeasurable_schattenSize (by exact even_two)
      (fun a => isSymmetricBlockMat_blockSub
        (isSymmetricBlockMat_coarseBlock _ _) hEsym) ?_
    intro α β
    have hmA : AEStronglyMeasurable
        (fun a : CoeffSpace d ↦
          toFullBlockMat (coarseBlock (adaptedCell q t) a) α β) P :=
      Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq t α β
    have h := hmA.sub
      (aestronglyMeasurable_const
        (b := toFullBlockMat (adaptedMean P q t) α β))
    simpa only [Recurrence.toFullBlockMat_blockSub_apply] using! h
  -- the pathwise Lipschitz bound
  have hpoint : ∀ a, ENNReal.ofReal
      (Real.sqrt (Response.metricBlockNormSq m
        (Response.blockCellAverage (adaptedCell q t)
          (Response.diagonalWeakAdjointState hq t (a.subSkew h0 hh0) p r) -
          Response.profileAdjointCenter P hq t
            (fun b => b.subSkew h0 hh0) p r))) ≤
      ENNReal.ofReal C * ENNReal.ofReal (Z a) := by
    intro a
    have hAsym : IsSymmetricBlockMat (coarseBlock (adaptedCell q t) a) :=
      isSymmetricBlockMat_coarseBlock _ a
    have hAhatsym : IsSymmetricBlockMat
        (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q t) a)) :=
      Response.isSymmetricBlockMat_skewBlockCongr (g := h0) hAsym
    have hAadsym : IsSymmetricBlockMat
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul
            (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q t) a))
            (blockDiag 1 (-1)))) :=
      Response.isSymmetricBlockMat_adjointSign_congr hAhatsym
    have hEadsym : IsSymmetricBlockMat
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul (Response.skewBlockCongr h0 (adaptedMean P q t))
            (blockDiag 1 (-1)))) :=
      Response.isSymmetricBlockMat_adjointSign_congr hEhatsym
    have hEadpd : Book.Ch02.BlockPosDef
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul (Response.skewBlockCongr h0 (adaptedMean P q t))
            (blockDiag 1 (-1)))) :=
      Response.blockPosDef_adjointSign_congr hEhatpd
    have hsample : coarseBlock (adaptedCell q t) (a.subSkew h0 hh0) =
        Response.skewBlockCongr h0 (coarseBlock (adaptedCell q t) a) := by
      simpa only [Response.adaptedDomain_carrier] using
        Response.coarseBlock_subSkew (Response.adaptedDomain hq t) a h0 hh0
    have htranspose :
        coarseBlock (adaptedCell q t) (a.subSkew h0 hh0).transpose =
        blockMatMul (blockDiag 1 (-1))
          (blockMatMul
            (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q t) a))
            (blockDiag 1 (-1))) := by
      have hraw := Response.coarseBlock_transpose (a.subSkew h0 hh0)
        (Response.adaptedDomain hq t)
      simpa only [Response.adaptedDomain_carrier, hsample] using hraw
    have hreal := Response.sqrt_metricBlockNormSq_responseAverage_sub_le hm
      hAadsym hEadsym hEadpd p r
    rw [← Response.blockSub_adjointSign_congr, Response.blockSize_adjointSign_congr,
      Response.diagonalWeakMetricFactor_adjoint, Response.diagonalWeakLoadMinus_adjoint,
      ← Response.blockSub_skewBlockCongr, Response.blockSize_skewBlockCongr]
      at hreal
    rw [Response.diagonalWeakAdjointState_eq,
      Response.blockCellAverage_diagonalWeakState_eq_response hq t
        (a.subSkew h0 hh0).transpose p r,
      htranspose, Response.profileAdjointCenter_subSkew_eq hq t hint h0 hh0 p r]
    rw [← ENNReal.ofReal_mul hC0]
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_trans hreal ?_
    rw [hC]
    have hsize : blockSize
        (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
        (adaptedMean P q t) ≤ Z a := by
      rw [hZ]
      exact PortableHistory.blockSize_le_schattenSize
        (isSymmetricBlockMat_blockSub hAsym hEsym) hEsym hEt
        (by norm_num)
    exact mul_le_mul_of_nonneg_left hsize
      (mul_nonneg (Response.diagonalWeakMetricFactor_nonneg m _)
        (Response.diagonalWeakLoadPlus_nonneg _ p r))
  -- assemble
  calc
    Response.profileAdjointCenterVariance P m hq t
        (fun a => a.subSkew h0 hh0) p r ≤
        eLpNorm (fun a => ENNReal.ofReal C * ENNReal.ofReal (Z a)) 2 P := by
      refine eLpNorm_mono_enorm ?_ fun a => ?_
      · exact (ENNReal.measurable_ofReal.comp_aemeasurable
          (Response.AEMeasurable.sqrt_metricBlockNormSq_sub_const
            (Response.aemeasurable_blockCellAverage_diagonalWeakAdjointState_subSkew
              hq t h0 hh0 p r) m _)).aestronglyMeasurable
      simp only [enorm_eq_self]
      exact hpoint a
    _ ≤ ENNReal.ofReal C *
        eLpNorm (fun a => ENNReal.ofReal (Z a)) 2 P :=
      Response.eLpNorm_ofReal_mul_le
        (ENNReal.measurable_ofReal.comp_aemeasurable
          hZmeas.aemeasurable).aestronglyMeasurable C 2
    _ = ENNReal.ofReal C * scaleVariance P q (adaptedMean P q t) t := by
      congr 1
      have heq : eLpNorm (fun a => ENNReal.ofReal (Z a)) 2 P =
          eLpNorm Z 2 P := by
        have hZofReal : AEStronglyMeasurable (fun a => ENNReal.ofReal (Z a)) P :=
          (ENNReal.measurable_ofReal.comp_aemeasurable
            hZmeas.aemeasurable).aestronglyMeasurable
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hZofReal,
          eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hZmeas]
        congr 1
        refine lintegral_congr fun a => ?_
        congr 1
        simp only [enorm_eq_self]
        rw [Real.enorm_eq_ofReal (hZ0 a)]
      rw [heq]
      simp only [hZ]
      rfl

end

end HCPolySupport.HighContrast.Quenched
