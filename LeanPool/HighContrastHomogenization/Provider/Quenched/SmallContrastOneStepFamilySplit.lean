/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOneStepSlotsSplit

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastOneStepFamilySplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-split one-step family at every admissible base index

The recursion family with the slot family at `supplyMscSplit d E` under
the burn-in condition — the choice function quantified before the
generation.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

/-- **The one-step family at a growing window, at every admissible base
index.**  The choice function is quantified before the generation. -/
theorem exists_one_step_family_of_block_var_at_level_conv_family_split (d : ℕ)
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
        (∀ n : ℕ, ns ≤ n →
          lAl ≤ (N₀ : ℤ) + (n : ℤ) - ((Hw n : ℕ) : ℤ)) →
        (∀ n : ℕ, ns ≤ n →
          sKw ≤ (N₀ : ℤ) + (n : ℤ) - ((Hw n : ℕ) : ℤ)) →
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
      ∀ {k0 : ℤ} {cIso : ℝ}, 0 ≤ cIso →
      (∀ n : ℕ, ns ≤ n → ∀ k : ℤ, k0 ≤ k →
        k ≤ (N₀ : ℤ) + ((n - H : ℕ) : ℤ) →
        ∀ w ∈ Response.alignedIndex (roundedGrid lAl mAl) k
            ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)),
          BlockMatLoewnerLE
            (annealedBlock P (adaptedCellAt (roundedGrid lAl mAl) k w))
            (blockScale (1 + cIso) E)) →
      ∀ {cDeep : ℝ},
      (∀ n : ℕ, ns ≤ n →
        capsDeepConstant Cd g mAl (Gacc + 1) k0
          ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) ((N₀ : ℤ) + (n : ℤ)) ≤ cDeep) →
      ∀ {F : BlockMat d}, IsSymmetricBlockMat F → BlockPosDef F →
      ∀ {cF : ℝ}, 0 ≤ cF → F = blockScale cF E →
      (∀ n : ℕ, ns ≤ n → ∀ j : ℕ, j ≤ Hw n →
        BlockMatLoewnerLE
          (adaptedMean P (roundedGrid lAl mAl)
            (((N₀ : ℤ) + (n : ℤ)) - (j : ℤ))) F) →
      ∀ {kapE : ℝ}, 1 ≤ kapE →
      (∀ n : ℕ, ns ≤ n → ∀ X : BlockVec d,
        blockVecDot X (blockMatVecMul E X) ≤
          kapE * blockVecDot X
            (blockMatVecMul (adaptedMean P (roundedGrid lAl mAl)
              ((N₀ : ℤ) + (n : ℤ))) X)) →
      ∀ {R lev : ℝ}, 1 ≤ R → 1 ≤ lev →
      (∀ n : ℕ, ns ≤ n → ∀ᵐ a ∂P,
        Response.diagonalWeakMaximum rho (roundedGrid lAl mAl)
            ((N₀ : ℤ) + (n : ℤ)) F a ≤
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
              rowValue2Isotropy d (rowSplitConstant cIso cDeep) kapE
                (hatExcessAt P (roundedGrid lAl mAl) ((N₀ : ℤ) + (n : ℤ))) +
              weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
            (Response.maxGroupConstantAtLevel lev) (Response.energyGoodConstantAtLevel lev) P mAl (Response.responseSkew (K0 n)) F
                (loadScaleOfScalar cF (kapE)) mAl
                rho (Hw n)
                (R ^ 4 * badMomentMajorant K
                  (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw)) (R / 2) lev
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
                (meanDrop2ValueIsotropy P lAl cF mAl E F ((N₀ : ℤ) + (n : ℤ)))
                (meanSlotConversionAt d cF kapE *
                  slotFamilyValue d Csub (supplyMscSplit d E) delta
                    (hatExcessAt P (roundedGrid lAl mAl)
                      ((N₀ : ℤ) + ((jb n : ℕ) : ℤ)))
                    ((((N₀ : ℤ) + (n : ℤ)) -
                      ((N₀ : ℤ) + ((jb n : ℕ) : ℤ))).toNat) 0)) +
            2 * ((3 * (d : ℝ) + 4) *
              hatExcessAt P (roundedGrid lAl mAl) ((N₀ : ℤ) + (n : ℤ)) ^ 2) := by
  obtain ⟨Cpre, H, eta, hCpre1, hH4, heta, hchain⟩ :=
    exists_one_step_with_slots_of_block_at_level_conv_split d hd
  refine ⟨Cpre, H, eta, hCpre1, hH4, heta, ?_⟩
  intro g hg P hP E Ψ K S hdag hstat lAl hl Cd hCd mAl hmAl hgrid Gacc
    hqnorm hDbc hmeso rho hrho0 hrho1 hrhog Hw sKw hsKw delta hdelta0 hdelta9 hray Csub hCsub
    hsubdiv N₀ ns hHns hlAlS hlAlWn hsKwn hsrcn M hburnn jb hjbn hjble k0
    cIso hcIso hiso
    cDeep hcDeep F hFsym hFpd cF hcF0 hFeq henvFam kapE hkapE1 hcompE R lev hR1 hlev
    henvMax S0 SStar0 K0 hS0 hSStar0 hform n hn hposn
  have hHn : H ≤ n := by omega
  have hcast : ((n - H : ℕ) : ℤ) = (n : ℤ) - (H : ℤ) := by
    exact Nat.cast_sub hHn
  have hst : (N₀ : ℤ) + ((n - H : ℕ) : ℤ) ≤ (N₀ : ℤ) + (n : ℤ) := by omega
  have hteq : ((N₀ : ℤ) + (n : ℤ)) =
      ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) + (H : ℤ) := by omega
  have hcastns : ((ns - H : ℕ) : ℤ) = (ns : ℤ) - (H : ℤ) := by
    exact Nat.cast_sub (by omega : H ≤ ns)
  have hnZ : (ns : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hlAlSn : lAl ≤ (N₀ : ℤ) + ((n - H : ℕ) : ℤ) := by omega
  have hfloor : ∀ k : ℤ, lAl ≤ k → k ≤ (N₀ : ℤ) + (n : ℤ) →
      hatExcessAt P (roundedGrid lAl mAl) k ≤ delta := fun k hk _ => hray k hk
  have hjb2 : (N₀ : ℤ) + ((jb n : ℕ) : ℤ) ≤ (N₀ : ℤ) + (n : ℤ) := by
    have := hjble n hn
    have hc : ((jb n : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast this
    omega
  exact hchain hg hdag hstat hl hCd hmAl hgrid hqnorm hDbc hmeso
    hrho0 hrho1 hrhog
    hst hteq hlAlSn (Hw n) (hlAlWn n hn) hsKw (hsKwn n hn) (hsrcn n hn)
    M (hburnn n hn) (hjbn n hn) hjb2 hdelta0 hdelta9 hfloor hCsub hsubdiv hcIso
    (hiso n hn) (hcDeep n hn) hFsym hFpd hcF0 hFeq (henvFam n hn) hkapE1
    (hcompE n hn) hR1 hlev (henvMax n hn) (hS0 n) (hSStar0 n) (hform n) hposn

end

end HCPolySupport.HighContrast.Quenched
