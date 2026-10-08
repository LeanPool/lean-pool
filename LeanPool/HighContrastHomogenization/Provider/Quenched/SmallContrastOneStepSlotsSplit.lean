/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionStep
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAnnealedEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridCells
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSkewCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowOscillationSum
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowAtCenters
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTerminalComparability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanDropCarrier
public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowAccount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAlignedGeometry
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupply
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOneStepHub
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAbsorptionChoice
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryCapsIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHvarFamily
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceLagged
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOneStepEntryIsotropyAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanSlotConversionAt
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMomentCollapse
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceMomentDeepened
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHvarFamilySplit

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastOneStepSlotsSplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-split one-step estimate with its slots

The released one-step estimate with the slot family at the burn-split
supply `supplyMscSplit d E`; the weak-cap branch keeps its availability
threshold unchanged.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

/-- **The one-step estimate with slots, at the caller's mean conversion.** -/
theorem exists_one_step_with_slots_of_block_at_level_conv_split (d : ℕ) (hd : 2 ≤ d) :
    ∃ (Cpre : ℝ) (H : ℕ) (eta : ℝ), 1 ≤ Cpre ∧ 4 ≤ H ∧ 0 < eta ∧
      ∀ {g : ℝ}, g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
        {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ},
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        HCPoly.Frozen.IsStationaryLaw P →
      ∀ {lAl : ℤ}, (kZero d : ℤ) ≤ lAl →
      ∀ {Cd : ℝ}, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
      ∀ {mAl : Mat d}, mAl.PosDef →
      IsRoundedGrid lAl (roundedGrid lAl mAl) →
      ∀ {Gacc : ℕ},
        ‖roundedGrid lAl mAl‖ * Real.sqrt d ≤ (3 : ℝ) ^ Gacc →
      boundaryConst Cd g mAl ≤ (3 : ℝ) ^ (Gacc + 1 : ℕ) →
      (∀ᵐ a ∂P, ∀ m : ℤ, S a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m →
        ∀ w : Fin d → ℤ, standardCellCenter k w ∈ centeredCube d m →
          BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
            (blockScale
              ((3 : ℝ) ^ (g * max ((m : ℝ) - 2 * ((Gacc + 1 : ℕ) : ℝ) -
                (k : ℝ)) 0)) E)) →
      ∀ {rho : ℝ}, 0 < rho → rho < 1 → g ≤ rho →
      ∀ {s t : ℤ}, s ≤ t → t = s + (H : ℤ) → lAl ≤ s →
      ∀ (Hw : ℕ), lAl ≤ t - (Hw : ℤ) →
      ∀ {sKw : ℤ}, growthBar K ≤ (3 : ℝ) ^ sKw → sKw ≤ t - (Hw : ℤ) →
      sourceMomentTwo K ≤
        (3 : ℝ) ^ ((t - (Hw : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - sKw) →
      ∀ (M : ℕ),
      (1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
          growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
        (3 : ℝ) ^ ((M : ℝ) *
          (((t - (Hw : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) →
      ∀ {jb : ℤ}, t - (Hw : ℤ) ≤ jb → jb ≤ t →
      ∀ {delta : ℝ}, 0 ≤ delta → delta ≤ 1 / 9 →
      (∀ k : ℤ, lAl ≤ k → k ≤ t →
        hatExcessAt P (roundedGrid lAl mAl) k ≤ delta) →
      ∀ {Csub : ℝ}, 0 < Csub →
      (∀ (j' p' : ℤ), lAl ≤ j' → j' ≤ p' →
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
                  (adaptedMean P (roundedGrid lAl mAl) p')) →
      ∀ {k0 : ℤ} {cIso : ℝ}, 0 ≤ cIso →
      (∀ k : ℤ, k0 ≤ k → k ≤ s →
        ∀ w ∈ Response.alignedIndex (roundedGrid lAl mAl) k s,
          BlockMatLoewnerLE
            (annealedBlock P (adaptedCellAt (roundedGrid lAl mAl) k w))
            (blockScale (1 + cIso) E)) →
      ∀ {cDeep : ℝ},
      capsDeepConstant Cd g mAl (Gacc + 1) k0 s t ≤ cDeep →
      ∀ {F : BlockMat d}, IsSymmetricBlockMat F → BlockPosDef F →
      ∀ {cF : ℝ}, 0 ≤ cF → F = blockScale cF E →
      (∀ j : ℕ, j ≤ Hw →
        BlockMatLoewnerLE
          (adaptedMean P (roundedGrid lAl mAl) (t - (j : ℤ))) F) →
      ∀ {kapE : ℝ}, 1 ≤ kapE →
      (∀ X : BlockVec d,
        blockVecDot X (blockMatVecMul E X) ≤
          kapE * blockVecDot X
            (blockMatVecMul (adaptedMean P (roundedGrid lAl mAl) t) X)) →
      ∀ {R lev : ℝ}, 1 ≤ R → 1 ≤ lev →
      (∀ᵐ a ∂P,
        Response.diagonalWeakMaximum rho (roundedGrid lAl mAl) t F a ≤
          ENNReal.ofReal (R *
            ((max 1 (3 * S a *
              (3 : ℝ) ^ (-((t : ℝ) + ((Gacc + 1 : ℕ) : ℝ))))) ^ g / 2))) →
      ∀ {S0 SStar0 K0 : Mat d}, S0.PosDef → SStar0.PosDef →
      toFullBlockMat (adaptedMean P (roundedGrid lAl mAl) t) =
        schurBlock S0 SStar0 K0 →
      0 < hatExcessAt P (roundedGrid lAl mAl) t →
        adaptedHattedContrast P (roundedGrid lAl mAl) t - 1 ≤
          4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
                (16 * (d : ℝ) *
                  (adaptedHattedContrast P (roundedGrid lAl mAl) s -
                    adaptedHattedContrast P (roundedGrid lAl mAl) t)) +
              rowValue2Isotropy d (rowSplitConstant cIso cDeep) kapE
                (hatExcessAt P (roundedGrid lAl mAl) t) +
              weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
            (Response.maxGroupConstantAtLevel lev) (Response.energyGoodConstantAtLevel lev) P
              mAl (Response.responseSkew K0) F
                (loadScaleOfScalar cF (kapE)) mAl
                rho Hw
                (R ^ 4 * badMomentMajorant K
                  (t + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw)) (R / 2) lev
                t lAl
                (fun j => slotFamilyValue d Csub
                  (supplyMscSplit d E) delta
                  (hatExcessAt P (roundedGrid lAl mAl) jb)
                  ((t - jb).toNat) j)
                (slotFamilyValue d Csub (supplyMscSplit d E) delta
                  (hatExcessAt P (roundedGrid lAl mAl) jb)
                  ((t - jb).toNat) 0)
                (meanDrop2ValueIsotropy P lAl cF mAl E F t)
                (meanSlotConversionAt d cF kapE *
                  slotFamilyValue d Csub (supplyMscSplit d E) delta
                    (hatExcessAt P (roundedGrid lAl mAl) jb)
                    ((t - jb).toNat) 0)) +
            2 * ((3 * (d : ℝ) + 4) *
              hatExcessAt P (roundedGrid lAl mAl) t ^ 2) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cpre, H, eta, hCpre, hH4, heta, hstep⟩ :=
    exists_account_one_step_entry_of_block_at_level d hd
  refine ⟨Cpre, H, eta, hCpre, hH4, heta, ?_⟩
  intro g hg P hP E Ψ K S hdag hstat lAl hl Cd hCd mAl hn hgrid Gacc hqnorm
    hDbc hmeso rho hrho0 hrho1 hrhog s t hst hteq hlAlS Hw hstart sKw hsKw hsKrange
    hentryStart M hburnStart jb hjbstart hjbt delta hdelta0 hdelta9 hsm
    Csub hCsub hsubdiv
    k0 cIso hcIso hiso cDeep hcDeep F hFsym hFpd cF hcF0 hFeq henvFam kapE
    hkapE1 hcompE R lev hR1 hlev henvMax
    S0 SStar0 K0 hS0 hStar0 hform hpos
  let : IsProbabilityMeasure P := hP
  have hq : (roundedGrid lAl mAl).PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hlt : lAl ≤ t := by omega
  have hdelta4 : delta ≤ 1 / 4 := by linarith only [hdelta9]
  have hkap0 : (0 : ℝ) ≤ kapE := by linarith only [hkapE1]
  set q : Mat d := roundedGrid lAl mAl with hqdef
  set Msc : ℝ := supplyMscSplit d E with hMscdef
  set Fjb : ℝ := hatExcessAt P q jb with hFjbdef
  set J : ℕ := (t - jb).toNat with hJdef
  -- the slot family
  have hMsc0 : 0 ≤ Msc := supplyMscSplit_nonneg d E
  have hFjb0 : 0 ≤ Fjb :=
    hatExcessAt_nonneg hgrid
      (finite_adaptedMean_of_coarseEllipticityDagger hdag hq jb).1
  have hVnn : ∀ j : ℕ, 0 ≤ slotFamilyValue d Csub Msc delta Fjb J j :=
    fun j => slotFamilyValue_nonneg d hCsub.le hMsc0 hdelta0 hFjb0 J j
  have hvar := hvar_family_of_account_of_block_split hd hg hdag hstat hl
    hCd hn hgrid hqnorm hDbc hmeso hsKw hstart hsKrange hjbstart
    hjbt M hburnStart hdelta4 hsm hFsym hFpd henvFam hCsub hsubdiv
  have hvart : scaleVariance P q F t ≤
      ENNReal.ofReal (slotFamilyValue d Csub Msc delta Fjb J 0) := by
    have h := hvar 0 (Nat.zero_le Hw)
    have hz : t - ((0 : ℕ) : ℤ) = t := by omega
    rwa [hz] at h
  have hsKt : sKw ≤ t := by omega
  have hentryT : sourceMomentTwo K ≤
      (3 : ℝ) ^ (t + ((Gacc + 1 : ℕ) : ℤ) - sKw) := by
    refine le_trans hentryStart ?_
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have henvT : BlockMatLoewnerLE (adaptedMean P q t) F := by
    have h := henvFam 0 (Nat.zero_le Hw)
    have hz : t - ((0 : ℕ) : ℤ) = t := by omega
    rwa [hz] at h
  have hEt : BlockPosDef (adaptedMean P q t) :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq t).2
  have hXm : AEStronglyMeasurable (fun a => schattenSize 2
      (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
      (adaptedMean P q t)) P := by
    refine Transport.aestronglyMeasurable_schattenSize (by exact even_two)
      (fun a => isSymmetricBlockMat_blockSub (isSymmetricBlockMat_coarseBlock _ a)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q t)) ?_
    intro α β
    have hmA : AEStronglyMeasurable
        (fun a : CoeffSpace d ↦ toFullBlockMat (coarseBlock (adaptedCell q t) a) α β) P :=
      Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq t α β
    have h := hmA.sub
      (aestronglyMeasurable_const (b := toFullBlockMat (adaptedMean P q t) α β))
    simpa only [Recurrence.toFullBlockMat_blockSub_apply] using! h
  have hvmean := entry_supply_mean_slot_bound_at (E := E) hEt hFsym hFpd hcF0
    hkap0 hFeq hcompE hvart hXm
  -- the smallness pack
  obtain ⟨heps1, hsmallC, hdropAll⟩ :=
    account_smallness_pack hgrid
      (fun k => (finite_adaptedMean_of_coarseEllipticityDagger hdag hq k).1)
      hlt hdelta9 hsm
  have htr : (d : ℝ) * (schurHattedContrast S0 SStar0 - 1) ≤
      hatExcessAt P q t := by
    have hid : hattedContrast (adaptedMean P q t) =
        schurHattedContrast S0 SStar0 :=
      hattedContrast_eq_schurHattedContrast hStar0 hform
    rw [hatExcessAt, adaptedHattedContrast, hid]
  have hblocksAll : ∀ k : ℤ, lAl ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k) :=
    fun k _ _ => finite_adaptedMean_of_coarseEllipticityDagger hdag hq k
  have hdrop : (d : ℝ) *
      (adaptedHattedContrast P q s - adaptedHattedContrast P q t) ≤ 1 :=
    hdropAll s t hlAlS hst
  have hdropSmall : ∀ j : ℕ, j ≤ Hw → (d : ℝ) *
      (adaptedHattedContrast P q (t - (j : ℤ)) -
        adaptedHattedContrast P q t) ≤ 1 := by
    intro j hj
    have hjZ : (j : ℤ) ≤ (Hw : ℤ) := by exact_mod_cast hj
    exact hdropAll (t - (j : ℤ)) t (by omega) (by omega)
  have hVmean0 : 0 ≤ meanSlotConversionAt d cF kapE *
      slotFamilyValue d Csub Msc delta Fjb J 0 :=
    mul_nonneg (meanSlotConversionAt_nonneg d hcF0 hkap0) (hVnn 0)
  exact hstep hg hdag hstat hl hCd hn hgrid hqnorm hrho0 hrho1 hrhog hst hteq
    hlAlS Hw hstart hsKw hsKrange hentryT hblocksAll hS0 hStar0 hform hpos
    heps1 htr hsmallC hdrop hdropSmall hcIso hiso hcDeep hFsym hFpd hcF0 hFeq
    henvT hkapE1 hcompE hR1 hlev henvMax
    (fun j _ => hVnn j) (hVnn 0) hVmean0
    (fun j hj => hvar j hj) hvart hvmean

end

end HCPolySupport.HighContrast.Quenched
