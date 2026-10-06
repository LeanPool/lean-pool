/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryCapsIsotropyAtLevel

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastOneStepEntryIsotropyAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The account's one-step entry estimate at a released split level

The hub applied at the released caps: the weak slot is the released sharp weak
value and every other slot is the pinned one.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

/-- **The account's one-step entry estimate, at a released split level.** -/
theorem exists_account_one_step_entry_of_block_at_level (d : ℕ) (hd : 2 ≤ d) :
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
      ∀ {rho : ℝ}, 0 < rho → rho < 1 → g ≤ rho →
      ∀ {s t : ℤ}, s ≤ t → t = s + (H : ℤ) → lAl ≤ s →
      ∀ (Hw : ℕ), lAl ≤ t - (Hw : ℤ) →
      ∀ {sKw : ℤ}, growthBar K ≤ (3 : ℝ) ^ sKw → sKw ≤ t - (Hw : ℤ) →
      sourceMomentTwo K ≤ (3 : ℝ) ^ (t + ((Gacc + 1 : ℕ) : ℤ) - sKw) →
      (∀ k : ℤ, lAl ≤ k → k ≤ t →
        HasFiniteAdaptedMean P (roundedGrid lAl mAl) k ∧
          BlockPosDef (adaptedMean P (roundedGrid lAl mAl) k)) →
      ∀ {S0 SStar0 K0 : Mat d}, S0.PosDef → SStar0.PosDef →
      toFullBlockMat (adaptedMean P (roundedGrid lAl mAl) t) =
        schurBlock S0 SStar0 K0 →
      ∀ {eps : ℝ}, 0 < eps → eps ≤ 1 →
      (d : ℝ) * (schurHattedContrast S0 SStar0 - 1) ≤ eps →
      6 * (blockContrast (adaptedMean P (roundedGrid lAl mAl) t) - 1) ≤
        1 →
      (d : ℝ) * (adaptedHattedContrast P (roundedGrid lAl mAl) s -
        adaptedHattedContrast P (roundedGrid lAl mAl) t) ≤ 1 →
      (∀ j : ℕ, j ≤ Hw → (d : ℝ) *
        (adaptedHattedContrast P (roundedGrid lAl mAl) (t - (j : ℤ)) -
          adaptedHattedContrast P (roundedGrid lAl mAl) t) ≤ 1) →
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
      BlockMatLoewnerLE (adaptedMean P (roundedGrid lAl mAl) t) F →
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
      ∀ {V : ℕ → ℝ} {V0 Vmean : ℝ},
      (∀ j : ℕ, j ≤ Hw → 0 ≤ V j) → 0 ≤ V0 → 0 ≤ Vmean →
      (∀ j : ℕ, j ≤ Hw →
        scaleVariance P (roundedGrid lAl mAl)
          F (t - (j : ℤ)) ≤
          ENNReal.ofReal (V j)) →
      scaleVariance P (roundedGrid lAl mAl)
        F t ≤
        ENNReal.ofReal V0 →
      scaleVariance P (roundedGrid lAl mAl)
        (adaptedMean P (roundedGrid lAl mAl) t) t ≤
        ENNReal.ofReal Vmean →
      adaptedHattedContrast P (roundedGrid lAl mAl) t - 1 ≤
        4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
            (16 * (d : ℝ) *
              (adaptedHattedContrast P (roundedGrid lAl mAl) s -
                adaptedHattedContrast P (roundedGrid lAl mAl) t)) +
          rowValue2Isotropy d (rowSplitConstant cIso cDeep) kapE eps +
          weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
            (Response.maxGroupConstantAtLevel lev) (Response.energyGoodConstantAtLevel lev) P mAl (Response.responseSkew K0) F
            (loadScaleOfScalar cF (kapE)) mAl rho Hw
            (R ^ 4 * badMomentMajorant K (t + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw)) (R / 2) lev
            t lAl V V0 (meanDrop2ValueIsotropy P lAl cF mAl E F t) Vmean) +
        2 * ((3 * (d : ℝ) + 4) * eps ^ 2) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cpre, hCpre, hhub⟩ := exists_hatted_one_step_of_profile_caps d
  obtain ⟨H, eta, hH4, heta, habsorb⟩ := exists_absorption_lag_choice hCpre
  refine ⟨Cpre, H, eta, hCpre, hH4, heta, ?_⟩
  intro g hg P hP E Ψ K S hdag hstat lAl hl Cd hCd mAl hn hgrid Gacc
    hqnorm rho hrho0 hrho1 hrhog s t hst hteq hlAlS Hw hstart sKw hsKw
    hsKrange hentry hblocksAll S0 SStar0 K0 hS0 hStar0 hform eps hpos
    heps1 htr hsmall hdrop hdropSmall k0 cIso hcIso hiso cDeep hcDeep F hFsym
    hFpd cF hcF0 hFeq henvF kapE hkapE1 hcompE R lev hR1 hlev henvMax V V0 Vmean hV hV0 hVmean hvar hvart hvmean
  -- the derived comparability constant is nonnegative
  have hq : (roundedGrid lAl mAl).PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hd1 : 1 ≤ d := by omega
  have hcellsubT : adaptedCell (roundedGrid lAl mAl) t ⊆
      centeredCube d (t + ((Gacc + 1 : ℕ) : ℤ)) := by
    refine (Selection.adaptedCell_subset_centeredCube_add hd1 hqnorm).trans
      (Window.centeredCube_mono ?_)
    omega
  have hDeltaT : 0 ≤ t + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw := by
    have h1 : sKw ≤ t := le_trans hsKrange (by omega)
    omega
  have hkap0 : (0 : ℝ) ≤ kapE := by linarith only [hkapE1]
  -- the value nonnegativities
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hcDeep0 : (0 : ℝ) ≤ cDeep :=
    le_trans (capsDeepConstant_nonneg hCd1 hg hn (Gacc + 1) k0 s t) hcDeep
  have hL0 : 0 ≤ rowValue2Isotropy d (rowSplitConstant cIso cDeep) kapE eps := by
    rw [rowValue2Isotropy]
    refine mul_nonneg (rowSplitConstant_nonneg hcIso hcDeep0) ?_
    exact mul_nonneg hkap0 (by positivity)
  have hW0 : 0 ≤ weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
            (Response.maxGroupConstantAtLevel lev) (Response.energyGoodConstantAtLevel lev) P mAl (Response.responseSkew K0) F
      (loadScaleOfScalar cF (kapE)) mAl rho Hw
      (R ^ 4 * badMomentMajorant K (t + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw)) (R / 2) lev
      t lAl V V0 (meanDrop2ValueIsotropy P lAl cF mAl E F t) Vmean := by
    rw [weakValueBoundSharpIsotropyAt]
    exact sq_nonneg _
  -- the sharp caps at the account
  have hcaps := account_profile_caps_entry_of_block_at_level hd hg hdag hstat hl hCd hn
    hgrid hqnorm hrho0 hrho1 hst Hw hstart hsKw hsKrange hentry hS0
    hStar0 hform hpos heps1 htr hdropSmall hcIso hiso hcDeep hFsym hFpd hcF0
    hFeq henvF hkapE1 hcompE hR1 hlev henvMax hV hV0 hVmean hvar hvart hvmean
  -- the hub
  exact hhub hstat hdag hn rfl hgrid hlAlS H hteq hblocksAll hS0 hStar0
    hform hsmall hdrop heta hL0 hW0 habsorb hcaps

end

end HCPolySupport.HighContrast.Quenched
