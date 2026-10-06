/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceMomentDeepened

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSingleCellVarianceAbstract

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The single-cell variance at abstract envelopes

The single-cell reference variance with **both** envelope inputs abstract:
the pathwise coarse-block envelope `cPt·NSS^g·E` and the mean envelope
`c1·E`, at an arbitrary normalized source variable and scale.  The
burn-split (dimensional) constants instantiate directly: no boundary
constant, no grid-norm exponent in the statement.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder ENNReal

noncomputable section

variable {d : ℕ}

/-- **The single-cell variance at abstract envelopes.** -/
theorem scaleVariance_le_of_envelopes [NeZero d]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {n : Mat d} (hn : n.PosDef)
    (k : ℤ)
    (hintk : HasFiniteAdaptedMean P (roundedGrid l n) k)
    (F : BlockMat d) (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {S' : CoeffSpace d → ℝ} (w : ℤ)
    {cPt : ℝ} (hcPt0 : 0 ≤ cPt)
    (hpt' : ∀ᵐ a ∂P,
      BlockMatLoewnerLE (coarseBlock (adaptedCell (roundedGrid l n) k) a)
        (blockScale (cPt * normalizedSourceScale S' w a ^ g) E))
    {c1 mu2 : ℝ} (hc1Pt : cPt ≤ c1) (hmu20 : 0 ≤ mu2)
    (hmean : BlockMatLoewnerLE (adaptedMean P (roundedGrid l n) k)
      (blockScale c1 E))
    (hmom : ∫⁻ a, ENNReal.ofReal
        (normalizedSourceScale S' w a ^ ((2 : ℕ) : ℝ)) ∂P ≤
      ENNReal.ofReal mu2) :
    scaleVariance P (roundedGrid l n) F k ≤
      ENNReal.ofReal
        ((2 * d : ℝ) ^ (2 : ℝ)⁻¹ * blockSize E F * (2 * c1) *
          Real.sqrt mu2) := by
  classical
  have hq : (roundedGrid l n).PosDef := Recurrence.posDef_roundedGrid hl hn
  have hc10 : (0 : ℝ) ≤ c1 := le_trans hcPt0 hc1Pt
  have hbS0 : 0 ≤ blockSize E F :=
    PortableHistory.blockSize_nonneg hdag.refBlock_isSymm hFsym hFpd
  set c0 : ℝ := (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * blockSize E F * (2 * c1)
    with hc0
  have hc00 : 0 ≤ c0 := by
    rw [hc0]
    have h2d : (0 : ℝ) ≤ (2 * d : ℝ) ^ (2 : ℝ)⁻¹ :=
      Real.rpow_nonneg (by positivity) _
    positivity
  -- the pointwise Schatten bound
  have hpt : ∀ᵐ a ∂P,
      schattenSize 2
        (blockSub (coarseBlock (adaptedCell (roundedGrid l n) k) a)
          (adaptedMean P (roundedGrid l n) k)) F ≤
      c0 * normalizedSourceScale S' w a ^ g := by
    filter_upwards [hpt'] with a hcellenv
    have hApd : Book.Ch02.BlockPosDef
        (coarseBlock (adaptedCell (roundedGrid l n) k) a) :=
      Recurrence.blockPosDef_coarseBlock_adaptedCell hq k a
    have hAsym : IsSymmetricBlockMat
        (coarseBlock (adaptedCell (roundedGrid l n) k) a) :=
      isSymmetricBlockMat_coarseBlock _ a
    have hAmSym : IsSymmetricBlockMat
        (adaptedMean P (roundedGrid l n) k) :=
      Recurrence.isSymmetricBlockMat_adaptedMean P _ k
    have hAmPd : Book.Ch02.BlockPosDef
        (adaptedMean P (roundedGrid l n) k) :=
      Recurrence.blockPosDef_adaptedMean hq k hintk
    have hnss1 : 1 ≤ normalizedSourceScale S' w a :=
      one_le_normalizedSourceScale S' _ a
    have hnssg1 : 1 ≤ normalizedSourceScale S' w a ^ g :=
      Real.one_le_rpow hnss1 hg.1
    have hs0 : (0 : ℝ) ≤ cPt * normalizedSourceScale S' w a ^ g :=
      mul_nonneg hcPt0 (by linarith only [hnssg1])
    have hsand := Transport.schattenSize_blockSub_le_of_bounds (Q := 2)
      (by norm_num) hAsym (posDef_toFullBlockMat hAsym hApd).posSemidef
      hAmSym (posDef_toFullBlockMat hAmSym hAmPd).posSemidef
      hdag.refBlock_isSymm hFsym hFpd hs0 hc10 hcellenv hmean
    refine le_trans hsand ?_
    have hsum : cPt * normalizedSourceScale S' w a ^ g + c1 ≤
        2 * c1 * normalizedSourceScale S' w a ^ g := by
      have h1 : cPt * normalizedSourceScale S' w a ^ g ≤
          c1 * normalizedSourceScale S' w a ^ g :=
        mul_le_mul_of_nonneg_right hc1Pt (by linarith only [hnssg1])
      have h2 : c1 ≤ c1 * normalizedSourceScale S' w a ^ g := by
        nlinarith only [hnssg1, hc10]
      nlinarith only [h1, h2]
    calc
      (2 * d : ℝ) ^ (2 : ℝ)⁻¹ *
          (blockSize E F *
            (cPt * normalizedSourceScale S' w a ^ g + c1)) ≤
          (2 * d : ℝ) ^ (2 : ℝ)⁻¹ *
            (blockSize E F *
              (2 * c1 * normalizedSourceScale S' w a ^ g)) := by
        refine mul_le_mul_of_nonneg_left ?_
          (Real.rpow_nonneg (by positivity) _)
        exact mul_le_mul_of_nonneg_left hsum hbS0
      _ = c0 * normalizedSourceScale S' w a ^ g := by
        rw [hc0]
        ring
  -- integrate the square
  have hf0 : ∀ a, 0 ≤ schattenSize 2
      (blockSub (coarseBlock (adaptedCell (roundedGrid l n) k) a)
        (adaptedMean P (roundedGrid l n) k)) F := by
    intro a
    rw [schattenSize]
    exact Recurrence.zero_le_schattenNorm
      (isSymmetricBlockMat_normalizedBlock
        (isSymmetricBlockMat_blockSub
          (isSymmetricBlockMat_coarseBlock _ a)
          (Recurrence.isSymmetricBlockMat_adaptedMean P _ k))) 2
  have hfm : AEStronglyMeasurable (fun a => schattenSize 2
      (blockSub (coarseBlock (adaptedCell (roundedGrid l n) k) a)
        (adaptedMean P (roundedGrid l n) k)) F) P := by
    refine Transport.aestronglyMeasurable_schattenSize (by exact even_two)
      (fun a => isSymmetricBlockMat_blockSub (isSymmetricBlockMat_coarseBlock _ a)
        (Recurrence.isSymmetricBlockMat_adaptedMean P _ k)) ?_
    intro α β
    have hmA : AEStronglyMeasurable
        (fun a : CoeffSpace d ↦
          toFullBlockMat (coarseBlock (adaptedCell (roundedGrid l n) k) a) α β) P :=
      Recurrence.hasMeasurableCoarseBlock_adaptedCell P
        (Recurrence.posDef_roundedGrid hl hn) k α β
    have h := hmA.sub
      (aestronglyMeasurable_const
        (b := toFullBlockMat (adaptedMean P (roundedGrid l n) k) α β))
    simpa only [Recurrence.toFullBlockMat_blockSub_apply] using! h
  rw [scaleVariance]
  refine le_of_sq_le_sq ?_
  rw [eLpNorm_two_real_sq hf0 hfm]
  have hmono : (∫⁻ a, ENNReal.ofReal
      (schattenSize 2
        (blockSub (coarseBlock (adaptedCell (roundedGrid l n) k) a)
          (adaptedMean P (roundedGrid l n) k)) F ^ 2) ∂P) ≤
      ∫⁻ a, ENNReal.ofReal (c0 ^ 2 *
        normalizedSourceScale S' w a ^ ((2 : ℕ) : ℝ)) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hpt] with a ha
    refine ENNReal.ofReal_le_ofReal ?_
    have hnss1 : 1 ≤ normalizedSourceScale S' w a :=
      one_le_normalizedSourceScale S' _ a
    have hsq : schattenSize 2
        (blockSub (coarseBlock (adaptedCell (roundedGrid l n) k) a)
          (adaptedMean P (roundedGrid l n) k)) F ^ 2 ≤
        (c0 * normalizedSourceScale S' w a ^ g) ^ 2 :=
      pow_le_pow_left₀ (hf0 a) ha 2
    refine hsq.trans ?_
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hcollapse : (normalizedSourceScale S' w a ^ g) ^
        (2 : ℕ) = normalizedSourceScale S' w a ^ (g * 2) := by
      rw [← Real.rpow_natCast
        (normalizedSourceScale S' w a ^ g) 2,
        ← Real.rpow_mul (by linarith only [hnss1])]
      norm_num
    rw [hcollapse]
    refine Real.rpow_le_rpow_of_exponent_le hnss1 ?_
    push_cast
    linarith only [hg.2]
  refine le_trans hmono ?_
  have hsplit : (∫⁻ a, ENNReal.ofReal (c0 ^ 2 *
      normalizedSourceScale S' w a ^ ((2 : ℕ) : ℝ)) ∂P) =
      ENNReal.ofReal (c0 ^ 2) *
        ∫⁻ a, ENNReal.ofReal
          (normalizedSourceScale S' w a ^ ((2 : ℕ) : ℝ)) ∂P := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun a => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
  rw [hsplit]
  calc
    ENNReal.ofReal (c0 ^ 2) *
        (∫⁻ a, ENNReal.ofReal
          (normalizedSourceScale S' w a ^ ((2 : ℕ) : ℝ)) ∂P) ≤
        ENNReal.ofReal (c0 ^ 2) * ENNReal.ofReal mu2 :=
      mul_le_mul' le_rfl hmom
    _ = ENNReal.ofReal (c0 * Real.sqrt mu2) ^ 2 := by
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_pow
          (mul_nonneg hc00 (Real.sqrt_nonneg _))]
      congr 1
      rw [mul_pow c0 (Real.sqrt mu2) 2,
        Real.sq_sqrt hmu20]
    _ = ENNReal.ofReal
        ((2 * d : ℝ) ^ (2 : ℝ)⁻¹ * blockSize E F * (2 * c1) *
          Real.sqrt mu2) ^ 2 := by
      rw [hc0]

end

end HCPolySupport.HighContrast.Quenched
