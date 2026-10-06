/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnSplitDeepened
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceLaggedNormalizedIsotropyOfEnvelopes

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEntrySupplySplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-split entry supply at a parametrized normalizer

The free-threshold entry supply at the **burn-split frame**: the dagger is
the enlarged-source datum, the pathwise input is the mesoscale ceiling, and
past the burn-in every constant is dimensional — the supply value is
`(2d)^{1/2}·(κ_𝐄·4)·8·√2`, with no boundary constant and no grid-norm
power.  This is the print's frame discipline (the printed argument, 8446-8455):
the geometry rides only in the burn depth, which is a scale threshold.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The burn-split entry supply.** -/
theorem entry_lagged_variance_supply_of_block_split [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {lAl : ℤ} (hl : (kZero d : ℤ) ≤ lAl)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {mAl : Mat d} (hn : mAl.PosDef)
    (hgrid : IsRoundedGrid lAl (roundedGrid lAl mAl))
    {Gacc : ℕ}
    (hqnorm : ‖roundedGrid lAl mAl‖ * Real.sqrt d ≤ (3 : ℝ) ^ Gacc)
    (hDbc : boundaryConst Cd g mAl ≤ (3 : ℝ) ^ (Gacc + 1 : ℕ))
    (hmeso : ∀ᵐ a ∂P, ∀ m : ℤ, S a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m →
      ∀ w : Fin d → ℤ, standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale
            ((3 : ℝ) ^ (g * max ((m : ℝ) - 2 * ((Gacc + 1 : ℕ) : ℝ) -
              (k : ℝ)) 0)) E))
    {sKw : ℤ} (hsKw : growthBar K ≤ (3 : ℝ) ^ sKw)
    {jb p t : ℤ} (hjb : lAl ≤ jb) (hjbp : jb ≤ p) (hpt : p ≤ t)
    (hsKjb : sKw ≤ jb)
    (M : ℕ)
    (hburn : 1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
      (3 : ℝ) ^ ((M : ℝ) *
        ((jb + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ)))
    (hsmjb : (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) jb - 1) ≤ 1 / 2)
    (hsmp : (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) p - 1) ≤ 1 / 2)
    (hdropB : 4 * (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) jb -
        adaptedHattedContrast P (roundedGrid lAl mAl) t) ≤ 1)
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    (henvF : BlockMatLoewnerLE (adaptedMean P (roundedGrid lAl mAl) p) F)
    {Csub : ℝ} (hCsub : 0 < Csub)
    (hsubdiv : ∀ (j' p' : ℤ), lAl ≤ j' → j' ≤ p' →
      ∃ Z : Finset (Fin d → ℤ),
        (↑Z : Set (Fin d → ℤ)) =
            {w | adaptedCellCenter (roundedGrid lAl mAl) j' w ∈
              adaptedCell (roundedGrid lAl mAl) p'} ∧
          Z.card = 3 ^ (d * (p' - j').toNat) ∧ Z.Nonempty ∧
          lqSchattenSize P 2
              (fun a ↦ blockSub
                (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
                  ∑ w ∈ Z,
                    toFullBlockMat
                      (coarseBlock
                        (adaptedCellAt (roundedGrid lAl mAl) j' w) a)))
                (adaptedMean P (roundedGrid lAl mAl) j'))
                (adaptedMean P (roundedGrid lAl mAl) p') ≤
            ENNReal.ofReal
                (Csub * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) *
              lqSchattenSize P 2
                (fun a ↦ blockSub
                  (coarseBlock (adaptedCell (roundedGrid lAl mAl) j') a)
                  (adaptedMean P (roundedGrid lAl mAl) j'))
                (adaptedMean P (roundedGrid lAl mAl) p')) :
    scaleVariance P (roundedGrid lAl mAl)
        F p ≤
      ENNReal.ofReal
        (Real.sqrt (2 * d) * 1 *
          ((2 + 4 * (1 + 4 * (d : ℝ) *
              (adaptedHattedContrast P (roundedGrid lAl mAl) jb -
                adaptedHattedContrast P (roundedGrid lAl mAl) p)) ^ 2) *
            (Csub *
              ((3 ^ (d * (p - jb).toNat) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) *
              ((2 * d : ℝ) ^ (2 : ℝ)⁻¹ *
                (kappaRef E * 4) * (2 * (4 : ℝ)) *
                Real.sqrt 2)) +
          4 * (1 + 4 * (d : ℝ) *
              (adaptedHattedContrast P (roundedGrid lAl mAl) jb -
                adaptedHattedContrast P (roundedGrid lAl mAl) p)) ^ 2 *
            (36 * ((d : ℝ) *
              (adaptedHattedContrast P (roundedGrid lAl mAl) jb - 1) +
              (1 / 2) *
                (3 : ℝ) ^ (-(((p - jb).toNat : ℕ) : ℝ)))) +
          4 * (d : ℝ) *
            (adaptedHattedContrast P (roundedGrid lAl mAl) jb -
              adaptedHattedContrast P (roundedGrid lAl mAl) p))) := by
  classical
  have hq : (roundedGrid lAl mAl).PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hd1 : 1 ≤ d := by omega
  have hintjb : HasFiniteAdaptedMean P (roundedGrid lAl mAl) jb :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq jb).1
  have hintp : HasFiniteAdaptedMean P (roundedGrid lAl mAl) p :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq p).1
  have hintt : HasFiniteAdaptedMean P (roundedGrid lAl mAl) t :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq t).1
  have hEjb : BlockPosDef (adaptedMean P (roundedGrid lAl mAl) jb) :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq jb).2
  have hEp : BlockPosDef (adaptedMean P (roundedGrid lAl mAl) p) :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq p).2
  -- Schur data at the two scales
  have hfulljb : (toFullBlockMat
      (adaptedMean P (roundedGrid lAl mAl) jb)).PosDef :=
    posDef_toFullBlockMat
      (Recurrence.isSymmetricBlockMat_adaptedMean P _ jb) hEjb
  have hfullp : (toFullBlockMat
      (adaptedMean P (roundedGrid lAl mAl) p)).PosDef :=
    posDef_toFullBlockMat
      (Recurrence.isSymmetricBlockMat_adaptedMean P _ p) hEp
  obtain ⟨Sj, SStarj, Kj, hSj, hStarj, hformj⟩ := exists_schurBlock hfulljb
  obtain ⟨Sp, SStarp, Kp, hSp, hStarp, hformp⟩ := exists_schurBlock hfullp
  -- the hatted identifications
  have hhatjb : schurHattedContrast Sj SStarj =
      adaptedHattedContrast P (roundedGrid lAl mAl) jb :=
    (hattedContrast_eq_schurHattedContrast hStarj hformj).symm
  have hhatp : schurHattedContrast Sp SStarp =
      adaptedHattedContrast P (roundedGrid lAl mAl) p :=
    (hattedContrast_eq_schurHattedContrast hStarp hformp).symm
  have hhat1jb : 1 ≤ adaptedHattedContrast P (roundedGrid lAl mAl) jb :=
    one_le_adaptedHattedContrast_of_rounded hgrid hintjb
  have hhat1p : 1 ≤ adaptedHattedContrast P (roundedGrid lAl mAl) p :=
    one_le_adaptedHattedContrast_of_rounded hgrid hintp
  -- the two smallness packs
  set epsj : ℝ := (d : ℝ) *
    (adaptedHattedContrast P (roundedGrid lAl mAl) jb - 1) +
    (1 / 2) * (3 : ℝ) ^ (-(((p - jb).toNat : ℕ) : ℝ)) with hepsjdef
  have hepsj0 : 0 < epsj := by
    rw [hepsjdef]
    have h1 : (0 : ℝ) ≤ (d : ℝ) *
        (adaptedHattedContrast P (roundedGrid lAl mAl) jb - 1) :=
      mul_nonneg (Nat.cast_nonneg d) (by linarith only [hhat1jb])
    have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(((p - jb).toNat : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    linarith only [h1, h2]
  have hepsj1 : epsj ≤ 1 := by
    rw [hepsjdef]
    have h2 : (3 : ℝ) ^ (-(((p - jb).toNat : ℕ) : ℝ)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      simp only [Left.neg_nonpos_iff, Nat.cast_nonneg]
    linarith only [hsmjb, h2]
  have htrj : (d : ℝ) * (schurHattedContrast Sj SStarj - 1) ≤ epsj := by
    rw [hhatjb, hepsjdef]
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((p - jb).toNat : ℕ) : ℝ)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    linarith only [h2]
  set epsp : ℝ := (d : ℝ) *
    (adaptedHattedContrast P (roundedGrid lAl mAl) p - 1) + 1 / 2
    with hepspdef
  have hepsp0 : 0 < epsp := by
    rw [hepspdef]
    have h1 : (0 : ℝ) ≤ (d : ℝ) *
        (adaptedHattedContrast P (roundedGrid lAl mAl) p - 1) :=
      mul_nonneg (Nat.cast_nonneg d) (by linarith only [hhat1p])
    linarith only [h1]
  have hepsp1 : epsp ≤ 1 := by
    rw [hepspdef]
    linarith only [hsmp]
  have htrp : (d : ℝ) * (schurHattedContrast Sp SStarp - 1) ≤ epsp := by
    rw [hhatp, hepspdef]
    linarith only []
  -- the drop smallness
  have hhattp : adaptedHattedContrast P (roundedGrid lAl mAl) t ≤
      adaptedHattedContrast P (roundedGrid lAl mAl) p :=
    adaptedHattedContrast_le hstat hgrid (le_trans hjb hjbp) hpt
      hintp hintt
  have hdropSmall : 4 * (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) jb -
        adaptedHattedContrast P (roundedGrid lAl mAl) p) ≤ 1 := by
    have h1 : 4 * (d : ℝ) *
        (adaptedHattedContrast P (roundedGrid lAl mAl) jb -
          adaptedHattedContrast P (roundedGrid lAl mAl) p) ≤
        4 * (d : ℝ) *
        (adaptedHattedContrast P (roundedGrid lAl mAl) jb -
          adaptedHattedContrast P (roundedGrid lAl mAl) t) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith only [hhattp]
    linarith only [h1, hdropB]
  -- the base-scale enclosure
  have hcellsub : ∀ k : ℤ, adaptedCell (roundedGrid lAl mAl) k ⊆
      centeredCube d (k + ((Gacc + 1 : ℕ) : ℤ)) := by
    intro k
    refine (Selection.adaptedCell_subset_centeredCube_add hd1 hqnorm).trans
      (Window.centeredCube_mono ?_)
    omega
  have hDjb : 0 ≤ jb + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw := by omega
  -- the comparability at the current scale
  have hDp : 0 ≤ p + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw := by omega
  -- the collapsed burn-split envelopes at the two scales
  have hcolljb := adaptedMean_le_scaled_burnsplit_collapsed hd hg hdag
    hmeso hl hCd hn hDbc hsKw jb M hDjb hburn (hcellsub jb) hintjb
  have hcollp := adaptedMean_le_scaled_burnsplit_collapsed hd hg hdag
    hmeso hl hCd hn hDbc hsKw p M hDp
    (burn_condition_mono hjbp hburn) (hcellsub p) hintp
  -- the comparability at the collapsed constant
  obtain ⟨hkap1, hcomp⟩ := terminal_reference_comparability_of_c1
    hd hdag hl hn p hintp (by norm_num : (1 : ℝ) ≤ (4 : ℝ)) hcollp
  have hkap0 : (0 : ℝ) ≤ kappaRef E * 4 := by linarith only [hkap1]
  have hbSmeanp : blockSize E (adaptedMean P (roundedGrid lAl mAl) p) ≤
      kappaRef E * 4 := by
    refine Transport.blockSize_le_of_blockMatLoewnerLE_blockScale
      hdag.refBlock_isSymm
      (posDef_toFullBlockMat hdag.refBlock_isSymm
        hdag.refBlock_posDef).posSemidef
      (Recurrence.isSymmetricBlockMat_adaptedMean P _ p) hEp hkap0 ?_
    intro X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
    have h := hcomp X
    linarith only [h]
  have hmeanpF2 : toFullBlockMat (adaptedMean P (roundedGrid lAl mAl) p) ≤
      (1 : ℝ) • toFullBlockMat F := by
    have h1 := le_of_blockMatLoewnerLE
      (Recurrence.isSymmetricBlockMat_adaptedMean P _ p) hFsym henvF
    rw [one_smul]
    exact h1
  -- the pathwise burn-split envelope at the base cell
  have hpt' : ∀ᵐ a ∂P,
      BlockMatLoewnerLE
        (coarseBlock (adaptedCell (roundedGrid lAl mAl) jb) a)
        (blockScale ((2 : ℝ) *
          normalizedSourceScale S (jb + ((Gacc + 1 : ℕ) : ℤ) - 1) a ^ g)
          E) := by
    filter_upwards [coarseBlock_adaptedCell_burnsplit_nss hd hg
      hdag.refBlock_posDef hmeso hl hCd hn hDbc jb] with a ha
    exact ha (hcellsub jb)
  exact scaleVariance_le_lagged_normalized_of_block_of_envelopes hd hg hdag
    hstat hl hCd hn hgrid hjb hjbp hSj hStarj hformj hSp hStarp hformp
    hepsj0 hepsj1 htrj hepsp0 hepsp1 htrp hdropSmall
    (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) hpt'
    (by norm_num : (2 : ℝ) ≤ (4 : ℝ)) (by norm_num : (1 : ℝ) ≤ (4 : ℝ))
    (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) hcolljb
    (lintegral_nss_sq_collapsed hdag hsKw jb M hDjb hburn)
    hkap0 hbSmeanp hFsym hFpd (le_refl (1 : ℝ)) hmeanpF2 hCsub hsubdiv

end

end HCPolySupport.HighContrast.Quenched
