/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotBoundsSplit

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastHvarFamilySplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-split variance family at a parametrized normalizer

The variance family at the burn-split slot bounds: the family values carry
`supplyMscSplit d E` — dimensional up to `κ_𝐄`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The variance family, at a parametrized normalizer.** -/
theorem hvar_family_of_account_of_block_split [NeZero d] (hd : 2 ≤ d) {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
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
    {t : ℤ} {Hw : ℕ} {jb : ℤ}
    (hstart : lAl ≤ t - (Hw : ℤ)) (hsKstart : sKw ≤ t - (Hw : ℤ))
    (hjbstart : t - (Hw : ℤ) ≤ jb) (hjbt : jb ≤ t)
    (M : ℕ)
    (hburnStart : 1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
      (3 : ℝ) ^ ((M : ℝ) *
        (((t - (Hw : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ)))
    {delta : ℝ} (hdelta4 : delta ≤ 1 / 4)
    (hsm : ∀ k : ℤ, lAl ≤ k → k ≤ t →
      hatExcessAt P (roundedGrid lAl mAl) k ≤ delta)
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    (henvFam : ∀ j : ℕ, j ≤ Hw →
      BlockMatLoewnerLE
        (adaptedMean P (roundedGrid lAl mAl) (t - (j : ℤ))) F)
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
    ∀ j : ℕ, j ≤ Hw →
      scaleVariance P (roundedGrid lAl mAl)
          F (t - (j : ℤ)) ≤
        ENNReal.ofReal
          (slotFamilyValue d Csub (supplyMscSplit d E) delta
            (hatExcessAt P (roundedGrid lAl mAl) jb) ((t - jb).toNat) j) := by
  classical
  intro j hj
  have hq : (roundedGrid lAl mAl).PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  set q : Mat d := roundedGrid lAl mAl with hqdef
  set p : ℤ := t - (j : ℤ) with hpdef
  have hjZ : (j : ℤ) ≤ (Hw : ℤ) := by exact_mod_cast hj
  have hlp : lAl ≤ p := by rw [hpdef]; omega
  have hpt : p ≤ t := by rw [hpdef]; omega
  have hsKp : sKw ≤ p := by rw [hpdef]; omega
  have hFjb0 : 0 ≤ hatExcessAt P q jb :=
    hatExcessAt_nonneg hgrid
      (finite_adaptedMean_of_coarseEllipticityDagger hdag hq jb).1
  -- the drop-smallness clauses, from `δ ≤ 1/4`
  have hdropAt : ∀ x y : ℤ, lAl ≤ x → x ≤ t →
      4 * (d : ℝ) * (adaptedHattedContrast P q x -
        adaptedHattedContrast P q y) ≤ 1 := by
    intro x y hlx hxt
    have hdr := hat_drop_le_hatExcess (P := P) (q := q) (j := x) (p := y) hgrid
      (finite_adaptedMean_of_coarseEllipticityDagger hdag hq y).1
    have hsmx := hsm x hlx hxt
    have h4 : 4 * (d : ℝ) * (adaptedHattedContrast P q x -
        adaptedHattedContrast P q y) =
        4 * ((d : ℝ) * (adaptedHattedContrast P q x -
          adaptedHattedContrast P q y)) := by ring
    rw [h4]
    have : (d : ℝ) * (adaptedHattedContrast P q x -
        adaptedHattedContrast P q y) ≤ delta := le_trans hdr hsmx
    linarith only [this, hdelta4]
  -- the half-smallness clauses
  have hhalf : ∀ x : ℤ, lAl ≤ x → x ≤ t →
      (d : ℝ) * (adaptedHattedContrast P q x - 1) ≤ 1 / 2 := by
    intro x hlx hxt
    have h := hsm x hlx hxt
    rw [hatExcessAt] at h
    linarith only [h, hdelta4]
  rcases le_or_gt j (t - jb).toNat with hshallow | hdeep
  · -- shallow leg: the supply at the base `j_b`
    have hjbp : jb ≤ p := by
      rw [hpdef]
      have : (j : ℤ) ≤ t - jb := by
        have := Int.toNat_of_nonneg (a := t - jb) (by omega)
        omega
      omega
    have hlagcast : (p - jb).toNat = (t - jb).toNat - j := by
      rw [hpdef]
      omega
    have hburnjb := burn_condition_mono hjbstart hburnStart
    have hbase := entry_supply_slot_bound_of_block_split hd hg hdag hstat
      hl hCd hn hgrid hqnorm hDbc hmeso hsKw (by omega : lAl ≤ jb)
      hjbp hpt (by omega : sKw ≤ jb) M hburnjb
      (hhalf jb (by omega) hjbt) (hhalf p hlp hpt)
      (hdropAt jb t (by omega) hjbt) hFsym hFpd (henvFam j hj) hCsub hsubdiv
      (hdropAt jb p (by omega) hjbt)
    refine le_trans hbase (ENNReal.ofReal_le_ofReal ?_)
    rw [slotFamilyValue, slotSourceSeq, ite_eq_left hshallow, hlagcast]
  · -- deep leg: the supply at the leg's own scale
    have hburnp := burn_condition_mono
      (by rw [hpdef]; omega : t - (Hw : ℤ) ≤ p) hburnStart
    have hbase := entry_supply_deep_slot_bound_of_block_split hd hg hdag
      hstat hl hCd hn hgrid hqnorm hDbc hmeso hsKw hlp hpt hsKp
      M hburnp (hsm p hlp hpt)
      (by linarith only [hdelta4]) (hdropAt p t hlp hpt)
      hFsym hFpd (henvFam j hj) hCsub hsubdiv
    refine le_trans hbase (ENNReal.ofReal_le_ofReal ?_)
    rw [slotFamilyValue, slotSourceSeq, ite_eq_right (by omega), deepSlotConstant]
    have hpos : 0 ≤ slotBaseCoefficient d * hatExcessAt P q jb :=
      mul_nonneg (slotBaseCoefficient_nonneg d) hFjb0
    linarith only [hpos]

end

end HCPolySupport.HighContrast.Quenched
