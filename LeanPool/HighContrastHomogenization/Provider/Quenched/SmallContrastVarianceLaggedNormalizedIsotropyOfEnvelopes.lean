/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceLagged
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVarianceAbstract

/-!
# High-contrast homogenization:
Provider.Quenched.SmallContrastVarianceLaggedNormalizedIsotropyOfEnvelopes

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The lagged variance at a parametrized normalizing block, abstract moments

The isotropy-block lagged variance replacement with the mean-envelope and
second-moment values of the normalized source scale as hypotheses — the
corrected (deepened) moment interface at the opaque-carrier variant.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

theorem scaleVariance_le_lagged_normalized_of_block_of_envelopes [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef)
    (hgrid : IsRoundedGrid l (roundedGrid l n))
    {j p : ℤ} (hlj : l ≤ j) (hjp : j ≤ p)
    {Sj SStarj Kj : Mat d} (hSj : Sj.PosDef) (hStarj : SStarj.PosDef)
    (hformj : toFullBlockMat (adaptedMean P (roundedGrid l n) j) =
      schurBlock Sj SStarj Kj)
    {Sp SStarp Kp : Mat d} (hSp : Sp.PosDef) (hStarp : SStarp.PosDef)
    (hformp : toFullBlockMat (adaptedMean P (roundedGrid l n) p) =
      schurBlock Sp SStarp Kp)
    {epsj epsp : ℝ}
    (hposj : 0 < epsj) (hepsj1 : epsj ≤ 1)
    (htrj : (d : ℝ) * (schurHattedContrast Sj SStarj - 1) ≤ epsj)
    (hposp : 0 < epsp) (hepsp1 : epsp ≤ 1)
    (htrp : (d : ℝ) * (schurHattedContrast Sp SStarp - 1) ≤ epsp)
    (hdropSmall : 4 * (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid l n) j -
        adaptedHattedContrast P (roundedGrid l n) p) ≤ 1)
    {Gc : ℕ}
    {S' : CoeffSpace d → ℝ} {cPt : ℝ} (hcPt0 : 0 ≤ cPt)
    (hpt' : ∀ᵐ a ∂P,
      BlockMatLoewnerLE (coarseBlock (adaptedCell (roundedGrid l n) j) a)
        (blockScale (cPt *
          normalizedSourceScale S' (j + (Gc : ℤ) - 1) a ^ g) E))
    {cE mu2 : ℝ} (hcEPt : cPt ≤ cE) (hcE1 : 1 ≤ cE) (hmu20 : 0 ≤ mu2)
    (hmean : BlockMatLoewnerLE (adaptedMean P (roundedGrid l n) j)
      (blockScale cE E))
    (hmom : ∫⁻ a, ENNReal.ofReal
        (normalizedSourceScale S' (j + (Gc : ℤ) - 1) a ^ ((2 : ℕ) : ℝ)) ∂P ≤
      ENNReal.ofReal mu2)
    {kapB : ℝ} (hkapB0 : 0 ≤ kapB)
    (hbSmeanp : blockSize E (adaptedMean P (roundedGrid l n) p) ≤ kapB)
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {cN : ℝ} (hcN1 : 1 ≤ cN)
    (hmeanpF2 : toFullBlockMat (adaptedMean P (roundedGrid l n) p) ≤
      cN •
        toFullBlockMat F)
    {Csub : ℝ} (hCsub : 0 < Csub)
    (hsubdiv : ∀ (j' p' : ℤ), l ≤ j' → j' ≤ p' →
      ∃ Z : Finset (Fin d → ℤ),
        (↑Z : Set (Fin d → ℤ)) =
            {w | adaptedCellCenter (roundedGrid l n) j' w ∈
              adaptedCell (roundedGrid l n) p'} ∧
          Z.card = 3 ^ (d * (p' - j').toNat) ∧ Z.Nonempty ∧
          lqSchattenSize P 2
              (fun a ↦ blockSub
                (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
                  ∑ w ∈ Z,
                    toFullBlockMat
                      (coarseBlock (adaptedCellAt (roundedGrid l n) j' w)
                        a)))
                (adaptedMean P (roundedGrid l n) j'))
                (adaptedMean P (roundedGrid l n) p') ≤
            ENNReal.ofReal
                (Csub * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) *
              lqSchattenSize P 2
                (fun a ↦ blockSub
                  (coarseBlock (adaptedCell (roundedGrid l n) j') a)
                  (adaptedMean P (roundedGrid l n) j'))
                (adaptedMean P (roundedGrid l n) p')) :
    scaleVariance P (roundedGrid l n) F p ≤
      ENNReal.ofReal
        (Real.sqrt (2 * d) * cN *
          ((2 + 4 * (1 + 4 * (d : ℝ) *
              (adaptedHattedContrast P (roundedGrid l n) j -
                adaptedHattedContrast P (roundedGrid l n) p)) ^ 2) *
            (Csub * ((3 ^ (d * (p - j).toNat) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) *
              ((2 * d : ℝ) ^ (2 : ℝ)⁻¹ * kapB *
                (2 * cE) *
                Real.sqrt (mu2))) +
          4 * (1 + 4 * (d : ℝ) *
              (adaptedHattedContrast P (roundedGrid l n) j -
                adaptedHattedContrast P (roundedGrid l n) p)) ^ 2 *
            (36 * epsj) +
          4 * (d : ℝ) *
            (adaptedHattedContrast P (roundedGrid l n) j -
              adaptedHattedContrast P (roundedGrid l n) p))) := by
  classical
  set q : Mat d := roundedGrid l n with hqdef
  have hq : q.PosDef := Recurrence.posDef_roundedGrid hl hn
  have hintj : HasFiniteAdaptedMean P q j :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq j).1
  have hintp : HasFiniteAdaptedMean P q p :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq p).1
  have hmeanpsym := Recurrence.isSymmetricBlockMat_adaptedMean P q p
  have hmeanppd : Book.Ch02.BlockPosDef (adaptedMean P q p) :=
    Recurrence.blockPosDef_adaptedMean hq p hintp
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hbC0 : 0 < boundaryConst Cd g n :=
    Transport.zero_lt_boundaryConst (by linarith only [hCd1]) hg.2 hn
  have hCK1 : (1 : ℝ) ≤ cE := hcE1
  -- the subdivision and its concentration
  obtain ⟨Z, hZ, hZcard, hZne, hZbound⟩ := hsubdiv j p hlj hjp
  -- shorthand for the drop
  set drop : ℝ := adaptedHattedContrast P q j -
    adaptedHattedContrast P q p with hdropdef
  have hdropnn : 0 ≤ drop := by
    rw [hdropdef]
    exact sub_nonneg.mpr (adaptedHattedContrast_le hstat hgrid hlj hjp
      hintj hintp)
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  set c1 : ℝ := 2 + 4 * (1 + 4 * (d : ℝ) * drop) ^ 2 with hc1def
  set c2 : ℝ := 4 * (1 + 4 * (d : ℝ) * drop) ^ 2 * (36 * epsj) with hc2def
  have hc10 : 0 ≤ c1 := by
    rw [hc1def]
    positivity
  have hc20 : 0 ≤ c2 := by
    rw [hc2def]
    have h0 : 0 ≤ epsj := hposj.le
    positivity
  have hK0 : 0 ≤ c2 + 4 * (d : ℝ) * drop := by
    have h := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hd0)
      hdropnn
    linarith only [hc20, h]
  -- the pathwise scalar function and its majorant
  have hgmeas := aemeasurable_blockSize_subdivisionDefect hq j Z
    (Recurrence.isSymmetricBlockMat_adaptedMean P q j) hmeanpsym hmeanppd
    (P := P)
  have hpath : ∀ a : CoeffSpace d,
      schattenSize 2
        (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p))
        F ≤
      Real.sqrt (2 * d) * cN *
        (c1 * blockSize
          (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
            ∑ w ∈ Z,
              toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
            (adaptedMean P q j)) (adaptedMean P q p) +
          (c2 + 4 * (d : ℝ) * drop)) := by
    intro a
    have hXsym : IsSymmetricBlockMat
        (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p)) :=
      isSymmetricBlockMat_blockSub
        (isSymmetricBlockMat_coarseBlock _ a) hmeanpsym
    -- Schatten to size in the reference normalization
    have h1 := PortableHistory.schattenSize_le_blockSize hXsym hFsym hFpd
      (by norm_num : (0 : ℝ) < 2)
    -- reference size to mean size
    have hbs0 : 0 ≤ blockSize
        (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p))
        (adaptedMean P q p) :=
      PortableHistory.blockSize_nonneg hXsym hmeanpsym hmeanppd
    have hsand := PortableHistory.blockSize_sandwich hXsym hmeanpsym hmeanppd
    have hup2 : toFullBlockMat
        (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p)) ≤
        (blockSize
          (blockSub (coarseBlock (adaptedCell q p) a)
            (adaptedMean P q p)) (adaptedMean P q p) *
          cN) •
          toFullBlockMat F := by
      refine hsand.1.trans ?_
      have h := smul_le_smul_of_nonneg_left hmeanpF2 hbs0
      rwa [smul_smul] at h
    have hlo2 : (-(blockSize
        (blockSub (coarseBlock (adaptedCell q p) a)
          (adaptedMean P q p)) (adaptedMean P q p) *
        cN)) •
        toFullBlockMat F ≤
        toFullBlockMat
          (blockSub (coarseBlock (adaptedCell q p) a)
            (adaptedMean P q p)) := by
      refine le_trans ?_ hsand.2
      have h := smul_le_smul_of_nonneg_left hmeanpF2 hbs0
      rw [smul_smul] at h
      have h2 := neg_le_neg h
      rw [← neg_smul, ← neg_smul] at h2
      exact h2
    have h2 : blockSize
        (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p))
        F ≤
        blockSize
          (blockSub (coarseBlock (adaptedCell q p) a)
            (adaptedMean P q p)) (adaptedMean P q p) *
          cN := by
      refine PortableHistory.blockSize_le_of_sandwich hXsym hFsym hFpd
        (mul_nonneg hbs0 (by linarith only [hcN1])) hup2 ?_
      exact hlo2
    -- the pathwise wrapper
    have h3 := blockSize_variance_replacement_pathwise hstat hgrid hlj
      hjp hintj hintp hSj hStarj hformj hSp hStarp hformp hposj.le
      hepsj1 htrj hposp hepsp1 htrp hposj hdropSmall hZ hZne a
    have hsq2d : (2 * d : ℝ) ^ (2 : ℝ)⁻¹ ≤ Real.sqrt (2 * d) := by
      refine le_of_eq ?_
      rw [Real.sqrt_eq_rpow, one_div]
    have hbsF20 : 0 ≤ blockSize
        (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p))
        F :=
      PortableHistory.blockSize_nonneg hXsym hFsym hFpd
    calc schattenSize 2
            (blockSub (coarseBlock (adaptedCell q p) a)
              (adaptedMean P q p))
            F ≤
          (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * blockSize
            (blockSub (coarseBlock (adaptedCell q p) a)
              (adaptedMean P q p)) F := h1
      _ ≤ Real.sqrt (2 * d) * blockSize
          (blockSub (coarseBlock (adaptedCell q p) a)
            (adaptedMean P q p)) F :=
        mul_le_mul_of_nonneg_right hsq2d hbsF20
      _ ≤ Real.sqrt (2 * d) *
          (blockSize
            (blockSub (coarseBlock (adaptedCell q p) a)
              (adaptedMean P q p)) (adaptedMean P q p) *
            cN) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (2 * d) *
          ((c1 * blockSize
            (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
              ∑ w ∈ Z,
                toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
              (adaptedMean P q j)) (adaptedMean P q p) +
            (c2 + 4 * (d : ℝ) * drop)) * cN) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        refine mul_le_mul_of_nonneg_right ?_
          (by linarith only [hcN1])
        rw [hc1def, hc2def, hdropdef]
        calc blockSize
                (blockSub (coarseBlock (adaptedCell q p) a)
                  (adaptedMean P q p)) (adaptedMean P q p) ≤ _ := h3
          _ = _ := by ring
      _ = Real.sqrt (2 * d) * cN *
          (c1 * blockSize
            (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
              ∑ w ∈ Z,
                toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
              (adaptedMean P q j)) (adaptedMean P q p) +
            (c2 + 4 * (d : ℝ) * drop)) := by ring
  -- integrate
  have hschat0 : ∀ a : CoeffSpace d, 0 ≤ schattenSize 2
      (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p))
      F := by
    intro a
    rw [schattenSize]
    exact Recurrence.zero_le_schattenNorm
      (isSymmetricBlockMat_normalizedBlock
        (isSymmetricBlockMat_blockSub
          (isSymmetricBlockMat_coarseBlock _ a) hmeanpsym)) 2
  have hα0 : (0 : ℝ) ≤ Real.sqrt (2 * d) * cN :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith only [hcN1])
  rw [scaleVariance]
  have hmono : eLpNorm
      (fun a => schattenSize 2
        (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p))
        F) 2 P ≤
      eLpNorm
        (fun a => Real.sqrt (2 * d) * cN * c1 *
          blockSize
            (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
              ∑ w ∈ Z,
                toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
              (adaptedMean P q j)) (adaptedMean P q p) +
          Real.sqrt (2 * d) * cN *
            (c2 + 4 * (d : ℝ) * drop)) 2 P := by
    have hXm : AEStronglyMeasurable (fun a => schattenSize 2
        (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p)) F) P := by
      refine Transport.aestronglyMeasurable_schattenSize (by exact even_two)
        (fun a => isSymmetricBlockMat_blockSub
          (isSymmetricBlockMat_coarseBlock _ _) hmeanpsym) ?_
      intro α β
      have hmA : AEStronglyMeasurable
          (fun a : CoeffSpace d ↦
            toFullBlockMat (coarseBlock (adaptedCell q p) a) α β) P :=
        Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq p α β
      have hm := hmA.sub
        (aestronglyMeasurable_const
          (b := toFullBlockMat (adaptedMean P q p) α β))
      simpa only [Recurrence.toFullBlockMat_blockSub_apply] using! hm
    refine eLpNorm_mono_real hXm fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hschat0 a)]
    have h := hpath a
    calc schattenSize 2
            (blockSub (coarseBlock (adaptedCell q p) a)
              (adaptedMean P q p))
            F ≤ _ := h
      _ = _ := by ring
  refine le_trans hmono ?_
  have hmeas1 : AEStronglyMeasurable
      (fun a => Real.sqrt (2 * d) * cN * c1 *
        blockSize
          (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
            ∑ w ∈ Z,
              toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
            (adaptedMean P q j)) (adaptedMean P q p)) P := by
    exact ((hgmeas.const_mul
      (Real.sqrt (2 * d) * cN * c1))).aestronglyMeasurable
  have hadd := eLpNorm_add_le
    (f := fun a => Real.sqrt (2 * d) * cN * c1 *
      blockSize
        (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z,
            toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
          (adaptedMean P q j)) (adaptedMean P q p))
    (g := fun _ : CoeffSpace d =>
      Real.sqrt (2 * d) * cN * (c2 + 4 * (d : ℝ) * drop))
    (μ := P) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine le_trans hadd ?_
  -- the constant piece
  have hconstpiece : eLpNorm
      (fun _ : CoeffSpace d =>
        Real.sqrt (2 * d) * cN *
          (c2 + 4 * (d : ℝ) * drop)) 2 P =
      ENNReal.ofReal
        (Real.sqrt (2 * d) * cN *
          (c2 + 4 * (d : ℝ) * drop)) := by
    rw [eLpNorm_const _ (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by
        have h : (P Set.univ) = 1 := measure_univ
        intro hP0
        rw [hP0] at h
        simp at h)]
    rw [measure_univ]
    simp only [ENNReal.one_rpow, mul_one]
    rw [Real.enorm_eq_ofReal (mul_nonneg hα0 hK0)]
  -- the concentration piece
  have hsmulpiece : eLpNorm
      (fun a => Real.sqrt (2 * d) * cN * c1 *
        blockSize
          (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
            ∑ w ∈ Z,
              toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
            (adaptedMean P q j)) (adaptedMean P q p)) 2 P =
      ENNReal.ofReal
          (Real.sqrt (2 * d) * cN * c1) *
        eLpNorm
          (fun a => blockSize
            (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
              ∑ w ∈ Z,
                toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
              (adaptedMean P q j)) (adaptedMean P q p)) 2 P := by
    have heq : (fun a => Real.sqrt (2 * d) * cN *
        c1 * blockSize
          (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
            ∑ w ∈ Z,
              toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
            (adaptedMean P q j)) (adaptedMean P q p)) =
        (Real.sqrt (2 * d) * cN * c1) •
          fun a => blockSize
            (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
              ∑ w ∈ Z,
                toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
              (adaptedMean P q j)) (adaptedMean P q p) := by
      funext a
      rw [Pi.smul_apply, smul_eq_mul]
    rw [heq, eLpNorm_const_smul]
    congr 1
    rw [Real.enorm_eq_ofReal (mul_nonneg hα0 hc10)]
  rw [hconstpiece, hsmulpiece]
  -- bound the concentration factor
  have hgs : eLpNorm
      (fun a => blockSize
        (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z,
            toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
          (adaptedMean P q j)) (adaptedMean P q p)) 2 P ≤
      lqSchattenSize P 2
        (fun a => blockSub
          (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
            ∑ w ∈ Z,
              toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
          (adaptedMean P q j)) (adaptedMean P q p) := by
    rw [lqSchattenSize,
      show (ENNReal.ofReal 2) = (2 : ℝ≥0∞) from by
        rw [ENNReal.ofReal_ofNat]]
    refine eLpNorm_mono_real hgmeas.aestronglyMeasurable fun a => ?_
    have hsubsym : IsSymmetricBlockMat
        (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z,
            toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
          (adaptedMean P q j)) := by
      refine isSymmetricBlockMat_blockSub ?_
        (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
      refine isSymmetricBlockMat_of_posSemidef ?_
      rw [toFullBlockMat_ofFullBlockMat]
      refine Matrix.PosSemidef.smul ?_ (by positivity : (0 : ℝ) ≤ _)
      refine Matrix.posSemidef_sum Z fun w hw => ?_
      exact (posDef_toFullBlockMat
        (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q j w a)
        (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq j w a)).posSemidef
    rw [Real.norm_eq_abs, abs_of_nonneg
      (PortableHistory.blockSize_nonneg hsubsym hmeanpsym hmeanppd)]
    exact PortableHistory.blockSize_le_schattenSize hsubsym hmeanpsym hmeanppd
      (by norm_num)
  -- the single-cell bound at the mean normalization
  have hsingle : lqSchattenSize P 2
      (fun a => blockSub (coarseBlock (adaptedCell q j) a)
        (adaptedMean P q j)) (adaptedMean P q p) ≤
      ENNReal.ofReal
        ((2 * d : ℝ) ^ (2 : ℝ)⁻¹ * kapB *
          (2 * cE) *
          Real.sqrt (mu2)) := by
    have h := scaleVariance_le_of_envelopes hg hdag hl hn
      j hintj (adaptedMean P q p) hmeanpsym hmeanppd
      (j + (Gc : ℤ) - 1) hcPt0 hpt' hcEPt hmu20 hmean hmom
    have hbridge : lqSchattenSize P 2
        (fun a => blockSub (coarseBlock (adaptedCell q j) a)
          (adaptedMean P q j)) (adaptedMean P q p) =
        scaleVariance P q (adaptedMean P q p) j := by
      rw [lqSchattenSize, scaleVariance,
        show (ENNReal.ofReal 2) = (2 : ℝ≥0∞) from by
          rw [ENNReal.ofReal_ofNat]]
    rw [hbridge]
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2d : (0 : ℝ) ≤ (2 * d : ℝ) ^ (2 : ℝ)⁻¹ :=
      Real.rpow_nonneg (by positivity) _
    have hfac : (0 : ℝ) ≤ 2 * cE := by
      linarith only [hCK1]
    have hs2 : (0 : ℝ) ≤ Real.sqrt (mu2) :=
      Real.sqrt_nonneg _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbSmeanp h2d) hfac) hs2
  -- assemble
  have hchain := le_trans hgs (hZbound.trans
    (mul_le_mul' le_rfl hsingle))
  have hMsc0 : (0 : ℝ) ≤ (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * kapB *
      (2 * cE) * Real.sqrt (mu2) := by
    have h2d : (0 : ℝ) ≤ (2 * d : ℝ) ^ (2 : ℝ)⁻¹ :=
      Real.rpow_nonneg (by positivity) _
    have hCK0 : (0 : ℝ) ≤ cE := by linarith only [hCK1]
    have hs2 : (0 : ℝ) ≤ Real.sqrt (mu2) :=
      Real.sqrt_nonneg _
    positivity
  have hcs0 : (0 : ℝ) ≤ Csub * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹) :=
    mul_nonneg hCsub.le (Real.rpow_nonneg (by positivity) _)
  calc ENNReal.ofReal
        (Real.sqrt (2 * d) * cN * c1) *
        eLpNorm
          (fun a => blockSize
            (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
              ∑ w ∈ Z,
                toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
              (adaptedMean P q j)) (adaptedMean P q p)) 2 P +
        ENNReal.ofReal
          (Real.sqrt (2 * d) * cN *
            (c2 + 4 * (d : ℝ) * drop)) ≤
      ENNReal.ofReal
          (Real.sqrt (2 * d) * cN * c1) *
        (ENNReal.ofReal (Csub * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) *
          ENNReal.ofReal
            ((2 * d : ℝ) ^ (2 : ℝ)⁻¹ * kapB *
              (2 * cE) *
              Real.sqrt (mu2))) +
        ENNReal.ofReal
          (Real.sqrt (2 * d) * cN *
            (c2 + 4 * (d : ℝ) * drop)) :=
        add_le_add (mul_le_mul' le_rfl hchain) le_rfl
    _ = ENNReal.ofReal
        (Real.sqrt (2 * d) * cN *
          (c1 * (Csub * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹) *
            ((2 * d : ℝ) ^ (2 : ℝ)⁻¹ * kapB *
              (2 * cE) *
              Real.sqrt (mu2))) +
          c2 + 4 * (d : ℝ) * drop)) := by
      rw [← ENNReal.ofReal_mul hcs0, ← ENNReal.ofReal_mul
        (mul_nonneg hα0 hc10),
        ← ENNReal.ofReal_add
          (mul_nonneg (mul_nonneg hα0 hc10)
            (mul_nonneg hcs0 hMsc0))
          (mul_nonneg hα0 hK0)]
      congr 1
      ring
    _ ≤ _ := by
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [hZcard, hc1def, hc2def, hdropdef]

end

end HCPolySupport.HighContrast.Quenched
