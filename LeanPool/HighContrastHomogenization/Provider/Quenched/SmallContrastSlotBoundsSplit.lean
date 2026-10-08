/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupplySplit

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSlotBoundsSplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-split slots at a parametrized normalizer

The shallow and deep slot bounds at the burn-split supply: the supply
value `supplyMscSplit d E = (2d)^{1/2}·(κ_𝐄·4)·8·√2` carries no boundary
constant and no grid-norm power.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The burn-split supply value: dimensional up to `κ_𝐄`. -/
@[expose]
def supplyMscSplit (d : ℕ) (E : BlockMat d) : ℝ :=
  (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * (kappaRef E * 4) * (2 * (4 : ℝ)) * Real.sqrt 2

theorem supplyMscSplit_nonneg (d : ℕ) (E : BlockMat d) :
    0 ≤ supplyMscSplit d E := by
  have hkapRef : 0 ≤ kappaRef E := Transport.zero_le_kappaRef E
  rw [supplyMscSplit]
  have h2d : (0 : ℝ) ≤ (2 * d : ℝ) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  positivity

/-- **The shallow slot, at a parametrized normalizer.** -/
theorem entry_supply_slot_bound_of_block_split [NeZero d]
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
                (adaptedMean P (roundedGrid lAl mAl) p'))
    (hdropP : 4 * (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) jb -
        adaptedHattedContrast P (roundedGrid lAl mAl) p) ≤ 1) :
    scaleVariance P (roundedGrid lAl mAl)
        F p ≤
      ENNReal.ofReal
        (slotSourceValue d Csub (supplyMscSplit d E)
            ((p - jb).toNat) +
          slotBaseCoefficient d *
            hatExcessAt P (roundedGrid lAl mAl) jb) := by
  classical
  have hq : (roundedGrid lAl mAl).PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hfinjb : HasFiniteAdaptedMean P (roundedGrid lAl mAl) jb :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq jb).1
  have hfinp : HasFiniteAdaptedMean P (roundedGrid lAl mAl) p :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq p).1
  -- the drop is nonnegative and below four times the base excess
  have hmono : adaptedHattedContrast P (roundedGrid lAl mAl) p ≤
      adaptedHattedContrast P (roundedGrid lAl mAl) jb :=
    adaptedHattedContrast_le hstat hgrid hjb hjbp hfinjb hfinp
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hc0 : (0 : ℝ) ≤ 4 * (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) jb -
        adaptedHattedContrast P (roundedGrid lAl mAl) p) := by
    have hsub : (0 : ℝ) ≤ adaptedHattedContrast P (roundedGrid lAl mAl) jb -
        adaptedHattedContrast P (roundedGrid lAl mAl) p :=
      sub_nonneg.mpr hmono
    have : (0 : ℝ) ≤ 4 * (d : ℝ) := by linarith only [hd0]
    exact mul_nonneg this hsub
  have honep : (1 : ℝ) ≤ adaptedHattedContrast P (roundedGrid lAl mAl) p :=
    one_le_adaptedHattedContrast_of_rounded hgrid hfinp
  have hY0 : (0 : ℝ) ≤ (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) jb - 1) := by
    have h1 : (1 : ℝ) ≤ adaptedHattedContrast P (roundedGrid lAl mAl) jb :=
      one_le_adaptedHattedContrast_of_rounded hgrid hfinjb
    exact mul_nonneg hd0 (by linarith only [h1])
  have hcY : 4 * (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) jb -
        adaptedHattedContrast P (roundedGrid lAl mAl) p) ≤
      4 * ((d : ℝ) *
        (adaptedHattedContrast P (roundedGrid lAl mAl) jb - 1)) := by
    have hle : adaptedHattedContrast P (roundedGrid lAl mAl) jb -
        adaptedHattedContrast P (roundedGrid lAl mAl) p ≤
        adaptedHattedContrast P (roundedGrid lAl mAl) jb - 1 := by
      linarith only [honep]
    have h4d : (0 : ℝ) ≤ 4 * (d : ℝ) := by linarith only [hd0]
    have := mul_le_mul_of_nonneg_left hle h4d
    linarith only [this]
  have hMsc0 : 0 ≤ supplyMscSplit d E :=
    supplyMscSplit_nonneg d E
  refine le_trans (entry_lagged_variance_supply_of_block_split hd hg hdag
    hstat hl hCd hn hgrid hqnorm hDbc hmeso hsKw hjb hjbp hpt hsKjb
    M hburn hsmjb hsmp hdropB hFsym hFpd henvF hCsub hsubdiv)
    (ENNReal.ofReal_le_ofReal ?_)
  rw [hatExcessAt, supplyMscSplit]
  exact supply_value_slot_bound d hc0 hdropP hcY hCsub.le
    (by rw [← supplyMscSplit]; exact hMsc0) hY0

/-- **The deep slot, at a parametrized normalizer.** -/
theorem entry_supply_deep_slot_bound_of_block_split [NeZero d]
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
    {p t : ℤ} (hlp : lAl ≤ p) (hpt : p ≤ t) (hsKp : sKw ≤ p)
    (M : ℕ)
    (hburn : 1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
      (3 : ℝ) ^ ((M : ℝ) *
        ((p + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ)))
    {delta : ℝ}
    (hsmp : hatExcessAt P (roundedGrid lAl mAl) p ≤ delta)
    (hdelta2 : delta ≤ 1 / 2)
    (hdropB : 4 * (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) p -
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
        (slotSourceValue d Csub (supplyMscSplit d E) 0 +
          slotBaseCoefficient d * delta) := by
  classical
  have hsmp' : (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) p - 1) ≤ 1 / 2 := by
    have := le_trans hsmp hdelta2
    rw [hatExcessAt] at this
    exact this
  have hdropP : 4 * (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) p -
        adaptedHattedContrast P (roundedGrid lAl mAl) p) ≤ 1 := by
    have : adaptedHattedContrast P (roundedGrid lAl mAl) p -
        adaptedHattedContrast P (roundedGrid lAl mAl) p = 0 := by ring
    rw [this]
    norm_num
  have hbase := entry_supply_slot_bound_of_block_split hd hg hdag hstat hl
    hCd hn hgrid hqnorm hDbc hmeso hsKw hlp (le_refl p) hpt hsKp
    M hburn hsmp' hsmp' hdropB hFsym hFpd henvF hCsub hsubdiv hdropP
  have hlag : (p - p).toNat = 0 := by simp
  rw [hlag] at hbase
  refine le_trans hbase (ENNReal.ofReal_le_ofReal ?_)
  have hcoef : 0 ≤ slotBaseCoefficient d := slotBaseCoefficient_nonneg d
  have := mul_le_mul_of_nonneg_left hsmp hcoef
  linarith only [this]


end

end HCPolySupport.HighContrast.Quenched
