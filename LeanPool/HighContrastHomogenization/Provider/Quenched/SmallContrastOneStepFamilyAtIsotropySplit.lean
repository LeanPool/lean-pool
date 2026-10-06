/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowAccount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAbsorptionChoice
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAlignedGeometry
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAnnealedEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryCapsIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupply
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionStep
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHvarFamily
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastIsotropyPack
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastLoadScalePiFree
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanDropCarrier
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanSlotConversionAt
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMomentCollapse
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOneStepEntryIsotropyAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOneStepFamilySplit
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOneStepHub
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRealClauses
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowAtCenters
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSharpLineAtJb
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceMomentDeepened
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTerminalComparability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceLagged
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridCells
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowOscillationSum
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSkewCarriers

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastOneStepFamilyAtIsotropySplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-split one-step family at the isotropy carriers

The Tier-A-discharged family producer at the burn-split supply
`supplyMscSplit d E`: the isotropy pack's discharges as given, the
mesoscale ceiling and burn depth as hypotheses, the slot family
dimensional up to `κ_𝐄`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

/-- **The one-step family at the isotropy carriers, at every admissible base
index.**  The recursion family as the print proves it (every depth in the
window), at the pack's own carriers; the shifted instantiation is the member
`jb := shiftedBaseIndex ns`. -/
theorem exists_one_step_family_at_isotropy_var_at_level_conv_family_split (d : ℕ)
    (hd : 2 ≤ d) :
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
      ∀ (Hw : ℕ → ℕ),
      ∀ {sKw : ℤ}, growthBar K ≤ (3 : ℝ) ^ sKw →
      ∀ {delta : ℝ}, 0 ≤ delta → delta ≤ 1 / 9 →
      (∀ k : ℤ, lAl ≤ k → hatExcessAt P (roundedGrid lAl mAl) k ≤ delta) →
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
      ∀ {N₀ ns : ℕ},
        H + 1 ≤ ns →
        lAl ≤ (N₀ : ℤ) + ((ns - H : ℕ) : ℤ) →
        (∀ n : ℕ, ns ≤ n → lAl ≤ (N₀ : ℤ) + (n : ℤ) - ((Hw n : ℕ) : ℤ)) →
        (∀ n : ℕ, ns ≤ n → sKw ≤ (N₀ : ℤ) + (n : ℤ) - ((Hw n : ℕ) : ℤ)) →
        (∀ n : ℕ, ns ≤ n → sourceMomentTwo K ≤ (3 : ℝ) ^
          (((N₀ : ℤ) + (n : ℤ) - ((Hw n : ℕ) : ℤ)) +
            ((Gacc + 1 : ℕ) : ℤ) - sKw)) →
      ∀ (M : ℕ),
        (∀ n : ℕ, ns ≤ n →
          1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
              growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
            (3 : ℝ) ^ ((M : ℝ) *
              ((((N₀ : ℤ) + (n : ℤ) - ((Hw n : ℕ) : ℤ)) +
                ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) →
      ∀ (jb : ℕ → ℕ),
        (∀ n : ℕ, ns ≤ n →
          ((N₀ : ℤ) + (n : ℤ)) - ((Hw n : ℕ) : ℤ) ≤
            (N₀ : ℤ) + ((jb n : ℕ) : ℤ)) →
        (∀ n : ℕ, ns ≤ n → jb n ≤ n) →
      ∀ {sigma cEnt : ℝ}, refContrast E - 1 ≤ sigma → 0 ≤ sigma → 0 < cEnt →
      nearIdentityDefect cEnt sigma < 1 →
      0 ≤ euclideanEntryThreshold K (cEnt / 2) sKw →
      lAl ≤ isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw →
      (∀ n : ℕ, ns ≤ n →
        isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw ≤ (N₀ : ℤ) + (n : ℤ) - ((Hw n : ℕ) : ℤ)) →
      sourceMomentTwo K ≤ (3 : ℝ) ^
        (isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw + ((Gacc + 1 : ℕ) : ℤ) - sKw) →
      ∀ {cDeep : ℝ},
      (∀ n : ℕ, ns ≤ n →
        capsDeepConstant Cd g mAl (Gacc + 1) (isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw)
          ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) ((N₀ : ℤ) + (n : ℤ)) ≤ cDeep) →
      ∀ {R lev : ℝ}, 1 ≤ R → 1 ≤ lev →
      (∀ n : ℕ, ns ≤ n → ∀ᵐ a ∂P,
        Response.diagonalWeakMaximum rho (roundedGrid lAl mAl)
            ((N₀ : ℤ) + (n : ℤ))
            (isotropyReference (nearIdentityDefect cEnt sigma) E) a ≤
          ENNReal.ofReal (R *
            ((max 1 (3 * S a *
              (3 : ℝ) ^ (-((((N₀ : ℤ) + (n : ℤ) : ℤ) : ℝ) +
                ((Gacc + 1 : ℕ) : ℝ))))) ^ g / 2))) →
      ∀ (S0 SStar0 K0 : ℕ → Mat d),
        (∀ m : ℕ, (S0 m).PosDef) → (∀ m : ℕ, (SStar0 m).PosDef) →
        (∀ m : ℕ, toFullBlockMat
            (adaptedMean P (roundedGrid lAl mAl) ((N₀ : ℤ) + (m : ℤ))) =
          schurBlock (S0 m) (SStar0 m) (K0 m)) →
      ∀ n : ℕ, ns ≤ n →
        0 < hatExcessAt P (roundedGrid lAl mAl) ((N₀ : ℤ) + (n : ℤ)) →
        adaptedHattedContrast P (roundedGrid lAl mAl) ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
          4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
                (16 * (d : ℝ) *
                  (adaptedHattedContrast P (roundedGrid lAl mAl) ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                    adaptedHattedContrast P (roundedGrid lAl mAl) ((N₀ : ℤ) + (n : ℤ)))) +
              rowValue2Isotropy d (rowSplitConstant (nearIdentityDefect cEnt sigma) cDeep) (isotropyKap2 (nearIdentityDefect cEnt sigma))
                (hatExcessAt P (roundedGrid lAl mAl) ((N₀ : ℤ) + (n : ℤ))) +
              weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
            (Response.maxGroupConstantAtLevel lev) (Response.energyGoodConstantAtLevel lev) P mAl (Response.responseSkew (K0 n))
                (isotropyReference (nearIdentityDefect cEnt sigma) E)
                (loadScaleOfScalar (1 + nearIdentityDefect cEnt sigma) (isotropyKap2 (nearIdentityDefect cEnt sigma))) mAl
                rho (Hw n)
                (R ^ 4 * badMomentMajorant K
                  (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
                (R / 2) lev
                ((N₀ : ℤ) + (n : ℤ)) lAl
                (fun j => slotFamilyValue d Csub
                  (supplyMscSplit d E) delta
                  (hatExcessAt P (roundedGrid lAl mAl)
                    ((N₀ : ℤ) + ((jb n : ℕ) : ℤ)))
                  ((((N₀ : ℤ) + (n : ℤ)) -
                    ((N₀ : ℤ) + ((jb n : ℕ) : ℤ))).toNat) j)
                (slotFamilyValue d Csub (supplyMscSplit d E) delta
                  (hatExcessAt P (roundedGrid lAl mAl)
                    ((N₀ : ℤ) + ((jb n : ℕ) : ℤ)))
                  ((((N₀ : ℤ) + (n : ℤ)) -
                    ((N₀ : ℤ) + ((jb n : ℕ) : ℤ))).toNat) 0)
                (meanDrop2ValueIsotropy P lAl (1 + nearIdentityDefect cEnt sigma) mAl E (isotropyReference (nearIdentityDefect cEnt sigma) E) ((N₀ : ℤ) + (n : ℤ)))
                (meanSlotConversionAt d (1 + nearIdentityDefect cEnt sigma)
                    (isotropyKap2 (nearIdentityDefect cEnt sigma)) *
                  slotFamilyValue d Csub (supplyMscSplit d E) delta
                    (hatExcessAt P (roundedGrid lAl mAl)
                      ((N₀ : ℤ) + ((jb n : ℕ) : ℤ)))
                    ((((N₀ : ℤ) + (n : ℤ)) -
                      ((N₀ : ℤ) + ((jb n : ℕ) : ℤ))).toNat) 0)) +
            2 * ((3 * (d : ℝ) + 4) *
              hatExcessAt P (roundedGrid lAl mAl) ((N₀ : ℤ) + (n : ℤ)) ^ 2) := by
  obtain ⟨Cpre, H, eta, hCpre1, hH4, heta, hfam⟩ :=
    exists_one_step_family_of_block_var_at_level_conv_family_split d hd
  refine ⟨Cpre, H, eta, hCpre1, hH4, heta, ?_⟩
  intro g hg P hP E Ψ K S hdag hstat lAl hl Cd hCd mAl hmAl hgrid Gacc
    hqnorm hDbc hmeso rho hrho0 hrho1 hrhog Hw sKw hsKw delta hdelta0 hdelta9 hray Csub hCsub
    hsubdiv N₀ ns hHns hlAlS hlAlWn hsKwn hsrcn M hburnn jb hjbn hjble
    sigma cEnt hsigma hsigma0
    hcEnt hsmall hkEnt0 hlsplit hsplitns hentry0 cDeep hcDeep R lev hR1 hlev
    henvMax
  have := hP
  have : NeZero d := ⟨by omega⟩
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hcIso0 : (0 : ℝ) ≤ nearIdentityDefect cEnt sigma :=
    nearIdentityDefect_nonneg hcEnt.le hsigma0
  have hisoAll := hiso_of_isotropySplit hd hg hdag hstat hl hCd hmAl hqnorm
    hsKw hsigma hsigma0 hcEnt hkEnt0 hlsplit hentry0
  have hcar := isotropy_carriers_of_isotropySplit hd hg hdag hstat hl hCd hmAl
    hqnorm hsKw hsigma hsigma0 hcEnt hsmall hkEnt0 hentry0
  have hiso : ∀ n : ℕ, ns ≤ n → ∀ k : ℤ,
      isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw ≤ k → k ≤ (N₀ : ℤ) + ((n - H : ℕ) : ℤ) →
      ∀ w ∈ Response.alignedIndex (roundedGrid lAl mAl) k
          ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)),
        BlockMatLoewnerLE
          (annealedBlock P (adaptedCellAt (roundedGrid lAl mAl) k w))
          (blockScale (1 + nearIdentityDefect cEnt sigma) E) :=
    fun _ _ k hk _ w _ => hisoAll k hk w
  have henvFam : ∀ n : ℕ, ns ≤ n → ∀ j : ℕ, j ≤ Hw n →
      BlockMatLoewnerLE
        (adaptedMean P (roundedGrid lAl mAl)
          (((N₀ : ℤ) + (n : ℤ)) - (j : ℤ)))
        (isotropyReference (nearIdentityDefect cEnt sigma) E) := by
    intro n hn j hj
    refine (hcar (((N₀ : ℤ) + (n : ℤ)) - (j : ℤ)) ?_).1
    have hjZ : (j : ℤ) ≤ ((Hw n : ℕ) : ℤ) := by exact_mod_cast hj
    have := hsplitns n hn
    omega
  have hcompE : ∀ n : ℕ, ns ≤ n → ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        isotropyKap2 (nearIdentityDefect cEnt sigma) * blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid lAl mAl)
            ((N₀ : ℤ) + (n : ℤ))) X) := by
    intro n hn X
    have hge : isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw ≤ (N₀ : ℤ) + (n : ℤ) := by
      have := hsplitns n hn
      have hHw0 : (0 : ℤ) ≤ ((Hw n : ℕ) : ℤ) := Int.natCast_nonneg _
      omega
    have h := (hcar ((N₀ : ℤ) + (n : ℤ)) hge).2 X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h
    linarith only [h]
  exact hfam hg hdag hstat hl hCd hmAl hgrid hqnorm hDbc hmeso
    hrho0 hrho1 hrhog Hw hsKw
    hdelta0 hdelta9 hray hCsub hsubdiv hHns hlAlS hlAlWn hsKwn hsrcn M hburnn
    jb hjbn hjble
    hcIso0 hiso hcDeep
    (isSymmetricBlockMat_isotropyReference _ hdag.refBlock_isSymm)
    (blockPosDef_isotropyReference hcIso0 hdag.refBlock_posDef)
    (by linarith only [hcIso0]) rfl henvFam
    (one_le_isotropyKap2 hcIso0 hsmall) hcompE hR1 hlev henvMax

/-- **The split one-step family at the cadence consumer's minimum base.**
The generation window is specialized to `n - ns`, the base index to
`min n m`, and the zero-excess endpoint is included. -/
theorem exists_one_step_family_at_isotropy_var_at_level_conv_family_min (d : ℕ)
    (hd : 2 ≤ d) :
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
      ∀ {sKw : ℤ}, growthBar K ≤ (3 : ℝ) ^ sKw →
      ∀ {delta : ℝ}, 0 ≤ delta → delta ≤ 1 / 9 →
      (∀ k : ℤ, lAl ≤ k → hatExcessAt P (roundedGrid lAl mAl) k ≤ delta) →
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
      ∀ {N₀ ns : ℕ},
        H + 1 ≤ ns →
        lAl ≤ (N₀ : ℤ) + ((ns - H : ℕ) : ℤ) →
        (∀ n : ℕ, ns ≤ n →
          lAl ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) →
        (∀ n : ℕ, ns ≤ n →
          sKw ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) →
        (∀ n : ℕ, ns ≤ n → sourceMomentTwo K ≤ (3 : ℝ) ^
          (((N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) +
            ((Gacc + 1 : ℕ) : ℤ) - sKw)) →
      ∀ (M : ℕ),
        (∀ n : ℕ, ns ≤ n →
          1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
              growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
            (3 : ℝ) ^ ((M : ℝ) *
              ((((N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) +
                ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) →
      ∀ {sigma cEnt : ℝ}, refContrast E - 1 ≤ sigma → 0 ≤ sigma → 0 < cEnt →
      nearIdentityDefect cEnt sigma < 1 →
      0 ≤ euclideanEntryThreshold K (cEnt / 2) sKw →
      lAl ≤ isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw →
      (∀ n : ℕ, ns ≤ n →
        isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw ≤
          (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) →
      sourceMomentTwo K ≤ (3 : ℝ) ^
        (isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw +
          ((Gacc + 1 : ℕ) : ℤ) - sKw) →
      ∀ {cDeep : ℝ},
      (∀ n : ℕ, ns ≤ n →
        capsDeepConstant Cd g mAl (Gacc + 1)
          (isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw)
          ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) ((N₀ : ℤ) + (n : ℤ)) ≤ cDeep) →
      ∀ {R lev : ℝ}, 1 ≤ R → 1 ≤ lev →
      (∀ n : ℕ, ns ≤ n → ∀ᵐ a ∂P,
        Response.diagonalWeakMaximum rho (roundedGrid lAl mAl)
            ((N₀ : ℤ) + (n : ℤ))
            (isotropyReference (nearIdentityDefect cEnt sigma) E) a ≤
          ENNReal.ofReal (R *
            ((max 1 (3 * S a *
              (3 : ℝ) ^ (-((((N₀ : ℤ) + (n : ℤ) : ℤ) : ℝ) +
                ((Gacc + 1 : ℕ) : ℝ))))) ^ g / 2))) →
      ∀ (S0 SStar0 K0 : ℕ → Mat d),
        (∀ m : ℕ, (S0 m).PosDef) → (∀ m : ℕ, (SStar0 m).PosDef) →
        (∀ m : ℕ, toFullBlockMat
            (adaptedMean P (roundedGrid lAl mAl) ((N₀ : ℤ) + (m : ℤ))) =
          schurBlock (S0 m) (SStar0 m) (K0 m)) →
      ∀ m : ℕ, ns ≤ m → ∀ n : ℕ, ns ≤ n →
        adaptedHattedContrast P (roundedGrid lAl mAl)
            ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
          4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
                (16 * (d : ℝ) *
                  (adaptedHattedContrast P (roundedGrid lAl mAl)
                      ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                    adaptedHattedContrast P (roundedGrid lAl mAl)
                      ((N₀ : ℤ) + (n : ℤ)))) +
              rowValue2Isotropy d
                (rowSplitConstant (nearIdentityDefect cEnt sigma) cDeep)
                (isotropyKap2 (nearIdentityDefect cEnt sigma))
                (hatExcessAt P (roundedGrid lAl mAl)
                  ((N₀ : ℤ) + (n : ℤ))) +
              weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
                (Response.maxGroupConstantAtLevel lev)
                (Response.energyGoodConstantAtLevel lev) P mAl
                (Response.responseSkew (K0 n))
                (isotropyReference (nearIdentityDefect cEnt sigma) E)
                (loadScaleOfScalar (1 + nearIdentityDefect cEnt sigma)
                  (isotropyKap2 (nearIdentityDefect cEnt sigma))) mAl rho
                (n - ns)
                (R ^ 4 * badMomentMajorant K
                  (((N₀ : ℤ) + (n : ℤ)) +
                    ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
                (R / 2) lev ((N₀ : ℤ) + (n : ℤ)) lAl
                (fun j => slotFamilyValue d Csub (supplyMscSplit d E) delta
                  (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
                  (n - min n m) j)
                (slotFamilyValue d Csub (supplyMscSplit d E) delta
                  (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
                  (n - min n m) 0)
                (meanDrop2ValueIsotropy P lAl (1 + nearIdentityDefect cEnt sigma)
                  mAl E (isotropyReference (nearIdentityDefect cEnt sigma) E)
                  ((N₀ : ℤ) + (n : ℤ)))
                (meanSlotConversionAt d (1 + nearIdentityDefect cEnt sigma)
                    (isotropyKap2 (nearIdentityDefect cEnt sigma)) *
                  slotFamilyValue d Csub (supplyMscSplit d E) delta
                    (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
                    (n - min n m) 0)) +
            2 * ((3 * (d : ℝ) + 4) *
              hatExcessAt P (roundedGrid lAl mAl)
                ((N₀ : ℤ) + (n : ℤ)) ^ 2) := by
  obtain ⟨Cpre, H, eta, hCpre1, hH4, heta, hfam⟩ :=
    exists_one_step_family_at_isotropy_var_at_level_conv_family_split d hd
  refine ⟨Cpre, H, eta, hCpre1, hH4, heta, ?_⟩
  intro g hg P hP E Ψ K S hdag hstat lAl hl Cd hCd mAl hmAl hgrid Gacc
    hqnorm hDbc hmeso rho hrho0 hrho1 hrhog sKw hsKw delta hdelta0 hdelta9
    hray Csub hCsub hsubdiv N₀ ns hHns hlAlS hlAlWn hsKwn hsrcn M hburnn
    sigma cEnt hsigma hsigma0 hcEnt hsmall hkEnt0 hlsplit hsplitns hentry0
    cDeep hcDeep R lev hR1 hlev henvMax S0 SStar0 K0 hS0 hStar0 hform
    m hm n hn
  have := hP
  have : NeZero d := ⟨by omega⟩
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  by_cases hpos : 0 < hatExcessAt P (roundedGrid lAl mAl)
      ((N₀ : ℤ) + (n : ℤ))
  · have hjb1 : ∀ n' : ℕ, ns ≤ n' →
        (N₀ : ℤ) + (n' : ℤ) - ((n' - ns : ℕ) : ℤ) ≤
          (N₀ : ℤ) + ((min n' m : ℕ) : ℤ) := by
      intro n' hn'
      have hmin : ns ≤ min n' m := le_min hn' hm
      omega
    have hjb2 : ∀ n' : ℕ, ns ≤ n' → min n' m ≤ n' :=
      fun n' _ => min_le_left _ _
    have hprod := hfam hg hdag hstat hl hCd hmAl hgrid hqnorm hDbc hmeso
      hrho0 hrho1 hrhog (fun k => k - ns) hsKw hdelta0 hdelta9 hray hCsub
      hsubdiv hHns hlAlS hlAlWn hsKwn hsrcn M hburnn (fun k => min k m)
      hjb1 hjb2 hsigma hsigma0 hcEnt hsmall hkEnt0 hlsplit hsplitns hentry0
      (cDeep := cDeep) hcDeep (R := R) (lev := lev) hR1 hlev henvMax
      S0 SStar0 K0 hS0 hStar0 hform
      n hn hpos
    have hcast : (((N₀ : ℤ) + (n : ℤ)) -
        ((N₀ : ℤ) + ((min n m : ℕ) : ℤ))).toNat = n - min n m := by
      omega
    rw [hcast] at hprod
    exact hprod
  · have hqpd : (roundedGrid lAl mAl).PosDef :=
      Recurrence.posDef_of_isRoundedGrid hgrid
    have hx0 : hatExcessAt P (roundedGrid lAl mAl)
        ((N₀ : ℤ) + (n : ℤ)) = 0 :=
      le_antisymm (not_lt.mp hpos)
        (hatExcessAt_nonneg hgrid
          (finite_adaptedMean_of_coarseEllipticityDagger hdag hqpd _).1)
    have haHC1 : adaptedHattedContrast P (roundedGrid lAl mAl)
        ((N₀ : ℤ) + (n : ℤ)) = 1 := by
      rw [hatExcessAt] at hx0
      have hd0 : (d : ℝ) ≠ 0 := by
        have hdpos : (0 : ℝ) < (d : ℝ) := by
          exact_mod_cast (by omega : 0 < d)
        exact ne_of_gt hdpos
      rcases mul_eq_zero.mp hx0 with h | h
      · exact absurd h hd0
      · linarith only [h]
    have hhat1 : 1 ≤ adaptedHattedContrast P (roundedGrid lAl mAl)
        ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) :=
      one_le_adaptedHattedContrast_of_rounded hgrid
        (finite_adaptedMean_of_coarseEllipticityDagger hdag hqpd _).1
    have hrow00 : rowValue2Isotropy d
        (rowSplitConstant (nearIdentityDefect cEnt sigma) cDeep)
        (isotropyKap2 (nearIdentityDefect cEnt sigma)) 0 = 0 := by
      rw [rowValue2Isotropy]
      ring
    rw [hx0, haHC1, hrow00]
    have hweak0 : (0 : ℝ) ≤ weakValueBoundSharpIsotropyAt
        (Response.recentConstantAtLevel lev) (Response.maxGroupConstantAtLevel lev)
        (Response.energyGoodConstantAtLevel lev) P mAl
        (Response.responseSkew (K0 n))
        (isotropyReference (nearIdentityDefect cEnt sigma) E)
        (loadScaleOfScalar (1 + nearIdentityDefect cEnt sigma)
          (isotropyKap2 (nearIdentityDefect cEnt sigma))) mAl rho
        (n - ns)
        (R ^ 4 * badMomentMajorant K
          (((N₀ : ℤ) + (n : ℤ)) +
            ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
        (R / 2) lev ((N₀ : ℤ) + (n : ℤ)) lAl
        (fun j => slotFamilyValue d Csub (supplyMscSplit d E) delta
          (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
          (n - min n m) j)
        (slotFamilyValue d Csub (supplyMscSplit d E) delta
          (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
          (n - min n m) 0)
        (meanDrop2ValueIsotropy P lAl (1 + nearIdentityDefect cEnt sigma)
          mAl E (isotropyReference (nearIdentityDefect cEnt sigma) E)
          ((N₀ : ℤ) + (n : ℤ)))
        (meanSlotConversionAt d (1 + nearIdentityDefect cEnt sigma)
            (isotropyKap2 (nearIdentityDefect cEnt sigma)) *
          slotFamilyValue d Csub (supplyMscSplit d E) delta
            (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
            (n - min n m) 0) := by
      rw [weakValueBoundSharpIsotropyAt]
      exact sq_nonneg _
    have ht1 : (0 : ℝ) ≤ (3 / 2 + 1 / (4 * eta)) *
        (16 * (d : ℝ) *
          (adaptedHattedContrast P (roundedGrid lAl mAl)
            ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) - 1)) := by
      have hc0 : (0 : ℝ) ≤ 3 / 2 + 1 / (4 * eta) := by positivity
      have hin : (0 : ℝ) ≤ 16 * (d : ℝ) *
          (adaptedHattedContrast P (roundedGrid lAl mAl)
            ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) - 1) := by
        have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        nlinarith only [hhat1, hd0]
      exact mul_nonneg hc0 hin
    have hsum0 : (0 : ℝ) ≤ 4 * Cpre := by linarith only [hCpre1]
    nlinarith only [ht1, hweak0, hsum0]

end

end HCPolySupport.HighContrast.Quenched
