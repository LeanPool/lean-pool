/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryCapsIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCapsBundleEntryIsotropyAtLevel

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEntryCapsIsotropyAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The account's entry caps at a released split level

The account-side caps bundle with its two weak quantities read against the
released sharp weak value.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The account's entry caps, at a released split level.** -/
theorem account_profile_caps_entry_of_block_at_level [NeZero d]
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
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    {s t : ℤ} (hst : s ≤ t) (Hw : ℕ) (hstart : lAl ≤ t - (Hw : ℤ))
    {sKw : ℤ} (hsKw : growthBar K ≤ (3 : ℝ) ^ sKw)
    (hsKrange : sKw ≤ t - (Hw : ℤ))
    (hentry : sourceMomentTwo K ≤
      (3 : ℝ) ^ (t + ((Gacc + 1 : ℕ) : ℤ) - sKw))
    {S0 SStar0 K0 : Mat d} (hS0 : S0.PosDef) (hStar0 : SStar0.PosDef)
    (hform : toFullBlockMat (adaptedMean P (roundedGrid lAl mAl) t) =
      schurBlock S0 SStar0 K0)
    {eps : ℝ} (hpos : 0 < eps) (heps1 : eps ≤ 1)
    (htr : (d : ℝ) * (schurHattedContrast S0 SStar0 - 1) ≤ eps)
    (hdropSmall : ∀ j : ℕ, j ≤ Hw → (d : ℝ) *
      (adaptedHattedContrast P (roundedGrid lAl mAl) (t - (j : ℤ)) -
        adaptedHattedContrast P (roundedGrid lAl mAl) t) ≤ 1)
    {k0 : ℤ} {cIso : ℝ} (hcIso : 0 ≤ cIso)
    (hiso : ∀ k : ℤ, k0 ≤ k → k ≤ s →
      ∀ w ∈ Response.alignedIndex (roundedGrid lAl mAl) k s,
        BlockMatLoewnerLE
          (annealedBlock P (adaptedCellAt (roundedGrid lAl mAl) k w))
          (blockScale (1 + cIso) E))
    {cDeep : ℝ}
    (hcDeep : capsDeepConstant Cd g mAl (Gacc + 1) k0 s t ≤ cDeep)
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {cF : ℝ} (hcF0 : 0 ≤ cF) (hFeq : F = blockScale cF E)
    (henvF : BlockMatLoewnerLE (adaptedMean P (roundedGrid lAl mAl) t) F)
    {kapE : ℝ} (hkapE1 : 1 ≤ kapE)
    (hcompE : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kapE * blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid lAl mAl) t) X))
    {R lev : ℝ} (hR1 : 1 ≤ R) (hlev : 1 ≤ lev)
    (henvMax : ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid lAl mAl) t F a ≤
        ENNReal.ofReal (R *
          ((max 1 (3 * S a * (3 : ℝ) ^ (-((t : ℝ) + ((Gacc + 1 : ℕ) : ℝ))))) ^ g / 2)))
    {V : ℕ → ℝ} {V0 Vmean : ℝ}
    (hV : ∀ j : ℕ, j ≤ Hw → 0 ≤ V j) (hV0 : 0 ≤ V0) (hVmean : 0 ≤ Vmean)
    (hvar : ∀ j : ℕ, j ≤ Hw →
      scaleVariance P (roundedGrid lAl mAl)
        F (t - (j : ℤ)) ≤
        ENNReal.ofReal (V j))
    (hvart : scaleVariance P (roundedGrid lAl mAl)
      F t ≤ ENNReal.ofReal V0)
    (hvmean : scaleVariance P (roundedGrid lAl mAl)
      (adaptedMean P (roundedGrid lAl mAl) t) t ≤
      ENNReal.ofReal Vmean) :
    ∀ e : Vec d, e ⬝ᵥ e = 1 →
      Response.profilePrimalHattedEarlierRow P (roundedGrid lAl mAl)
          (Response.responseSkew K0) s
          (Response.profilePrimalCenter P
            (Recurrence.posDef_of_isRoundedGrid hgrid) t
            (fun a ↦ a.subSkew (Response.responseSkew K0)
              (Response.is_skew_mat_response_skew K0))
            (Response.centeredResponseLoadP S0 SStar0 K0 e)
            (Response.centeredResponseLoadQ S0 SStar0 K0 e)).1
          (Response.profilePrimalCenter P
            (Recurrence.posDef_of_isRoundedGrid hgrid) t
            (fun a ↦ a.subSkew (Response.responseSkew K0)
              (Response.is_skew_mat_response_skew K0))
            (Response.centeredResponseLoadP S0 SStar0 K0 e)
            (Response.centeredResponseLoadQ S0 SStar0 K0 e)).2 ≤
        ENNReal.ofReal (rowValue2Isotropy d (rowSplitConstant cIso cDeep)
          kapE eps) ∧
      Response.profileAdjointHattedEarlierRow P (roundedGrid lAl mAl)
          (Response.responseSkew K0) s
          (Response.profileAdjointCenter P
            (Recurrence.posDef_of_isRoundedGrid hgrid) t
            (fun a ↦ a.subSkew (Response.responseSkew K0)
              (Response.is_skew_mat_response_skew K0))
            (Response.centeredResponseLoadP S0 SStar0 K0 e)
            (Response.centeredResponseLoadQ S0 SStar0 K0 e)).1
          (Response.profileAdjointCenter P
            (Recurrence.posDef_of_isRoundedGrid hgrid) t
            (fun a ↦ a.subSkew (Response.responseSkew K0)
              (Response.is_skew_mat_response_skew K0))
            (Response.centeredResponseLoadP S0 SStar0 K0 e)
            (Response.centeredResponseLoadQ S0 SStar0 K0 e)).2 ≤
        ENNReal.ofReal (rowValue2Isotropy d (rowSplitConstant cIso cDeep)
          kapE eps) ∧
      Response.profilePrimalWeakQuantity P mAl
          (Recurrence.posDef_of_isRoundedGrid hgrid) t
          (fun a ↦ a.subSkew (Response.responseSkew K0)
            (Response.is_skew_mat_response_skew K0))
          (Response.centeredResponseLoadP S0 SStar0 K0 e)
          (Response.centeredResponseLoadQ S0 SStar0 K0 e) ≤
        ENNReal.ofReal
          (weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
            (Response.maxGroupConstantAtLevel lev) (Response.energyGoodConstantAtLevel lev) P mAl (Response.responseSkew K0) F
            (loadScaleOfScalar cF (kapE)) mAl rho Hw
            (R ^ 4 * badMomentMajorant K (t + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw)) (R / 2) lev t lAl
            V V0 (meanDrop2ValueIsotropy P lAl cF mAl E F t) Vmean) ∧
      Response.profileAdjointWeakQuantity P mAl
          (Recurrence.posDef_of_isRoundedGrid hgrid) t
          (fun a ↦ a.subSkew (Response.responseSkew K0)
            (Response.is_skew_mat_response_skew K0))
          (Response.centeredResponseLoadP S0 SStar0 K0 e)
          (Response.centeredResponseLoadQ S0 SStar0 K0 e) ≤
        ENNReal.ofReal
          (weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
            (Response.maxGroupConstantAtLevel lev) (Response.energyGoodConstantAtLevel lev) P mAl (Response.responseSkew K0) F
            (loadScaleOfScalar cF (kapE)) mAl rho Hw
            (R ^ 4 * badMomentMajorant K (t + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw)) (R / 2) lev t lAl
            V V0 (meanDrop2ValueIsotropy P lAl cF mAl E F t) Vmean) ∧
      (1 / 2 : ℝ) *
          |vecDot
            (fun i ↦ ∫ a, averageGradient
              (Response.adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
              ((a.subSkew (Response.responseSkew K0)
                (Response.is_skew_mat_response_skew K0)).coeffOn
                  (Response.adaptedDomain
                    (Recurrence.posDef_of_isRoundedGrid hgrid) t))
              (Response.centeredResponseOptimizer
                (Response.adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
                (a.subSkew (Response.responseSkew K0)
                  (Response.is_skew_mat_response_skew K0))
                (Response.centeredResponseLoadP S0 SStar0 K0 e)
                (Response.centeredResponseLoadQ S0 SStar0 K0 e)) i ∂P)
            (fun i ↦ ∫ a, averageFlux
              (Response.adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
              ((a.subSkew (Response.responseSkew K0)
                (Response.is_skew_mat_response_skew K0)).coeffOn
                  (Response.adaptedDomain
                    (Recurrence.posDef_of_isRoundedGrid hgrid) t))
              (Response.centeredResponseOptimizer
                (Response.adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
                (a.subSkew (Response.responseSkew K0)
                  (Response.is_skew_mat_response_skew K0))
                (Response.centeredResponseLoadP S0 SStar0 K0 e)
                (Response.centeredResponseLoadQ S0 SStar0 K0 e)) i ∂P)| ≤
        (3 * (d : ℝ) + 4) * eps ^ 2 ∧
      (1 / 2 : ℝ) *
          |vecDot
            (fun i ↦ ∫ a, averageGradient
              (Response.adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
              ((a.subSkew (Response.responseSkew K0)
                (Response.is_skew_mat_response_skew K0)).transpose.coeffOn
                  (Response.adaptedDomain
                    (Recurrence.posDef_of_isRoundedGrid hgrid) t))
              (Response.centeredAdjointOptimizer
                (Response.adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
                (a.subSkew (Response.responseSkew K0)
                  (Response.is_skew_mat_response_skew K0))
                (Response.centeredResponseLoadP S0 SStar0 K0 e)
                (Response.centeredResponseLoadQ S0 SStar0 K0 e)) i ∂P)
            (fun i ↦ ∫ a, averageFlux
              (Response.adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
              ((a.subSkew (Response.responseSkew K0)
                (Response.is_skew_mat_response_skew K0)).transpose.coeffOn
                  (Response.adaptedDomain
                    (Recurrence.posDef_of_isRoundedGrid hgrid) t))
              (Response.centeredAdjointOptimizer
                (Response.adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
                (a.subSkew (Response.responseSkew K0)
                  (Response.is_skew_mat_response_skew K0))
                (Response.centeredResponseLoadP S0 SStar0 K0 e)
                (Response.centeredResponseLoadQ S0 SStar0 K0 e)) i ∂P)| ≤
        (3 * (d : ℝ) + 4) * eps ^ 2 := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hq : (roundedGrid lAl mAl).PosDef :=
    Recurrence.posDef_of_isRoundedGrid hgrid
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hbC0 : 0 < boundaryConst Cd g mAl :=
    Transport.zero_lt_boundaryConst (by linarith only [hCd1]) hg.2 hn
  have hCK1 : (1 : ℝ) ≤ sourceMomentOne K := one_le_sourceMomentOne
  have hfinAll : ∀ k : ℤ,
      HasFiniteAdaptedMean P (roundedGrid lAl mAl) k := fun k =>
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq k).1
  have hEt : Book.Ch02.BlockPosDef
      (adaptedMean P (roundedGrid lAl mAl) t) :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag hq t).2
  -- geometry
  have hgeomS := aligned_hgeom_of_grid_norm hd1 hq hqnorm hst
  have hgeomT := aligned_hgeom_of_grid_norm hd1 hq hqnorm
    (le_refl t)
  have hcellsub : ∀ k : ℤ, adaptedCell (roundedGrid lAl mAl) k ⊆
      centeredCube d (k + ((Gacc + 1 : ℕ) : ℤ)) := by
    intro k
    refine (Selection.adaptedCell_subset_centeredCube_add hd1 hqnorm).trans
      (Window.centeredCube_mono ?_)
    omega
  -- the exponent normalization
  have hexpo : ∀ k : ℤ,
      (3 : ℝ) ^ (g * (((k + ((Gacc + 1 : ℕ) : ℤ) : ℤ) : ℝ) - (k : ℝ))) =
      (3 : ℝ) ^ (g * (((Gacc + 1 : ℕ) : ℝ))) := by
    intro k
    congr 1
    congr 1
    push_cast
    ring
  -- the terminal comparability at the clean constant
  have hDeltaT : 0 ≤ t + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw := by
    have h1 : sKw ≤ t := le_trans hsKrange (by omega)
    omega
  have hkap0 : (0 : ℝ) ≤ kapE := by linarith only [hkapE1]
  have hcomp := hcompE
  have hbSF2 : 0 ≤ blockSize E F :=
    PortableHistory.blockSize_nonneg hdag.refBlock_isSymm hFsym hFpd
  have h3G0 : (0 : ℝ) ≤ (3 : ℝ) ^ (g * ((Gacc + 1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hDr0 : ∀ j : ℕ, j ≤ Hw →
      0 ≤ meanDrop2ValueIsotropy P lAl cF mAl E F t j := by
    intro j hj
    rw [meanDrop2ValueIsotropy]
    have hdrop0 : 0 ≤
        adaptedHattedContrast P (roundedGrid lAl mAl) (t - (j : ℤ)) -
          adaptedHattedContrast P (roundedGrid lAl mAl) t := by
      refine sub_nonneg.mpr (adaptedHattedContrast_le hstat hgrid ?_
        (by omega) (hfinAll _) (hfinAll _))
      have h1 : lAl ≤ t - (Hw : ℤ) := hstart
      have h2 : (j : ℤ) ≤ (Hw : ℤ) := by exact_mod_cast hj
      omega
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have h4d : (0 : ℝ) ≤ 4 * (d : ℝ) * (adaptedHattedContrast P
        (roundedGrid lAl mAl) (t - (j : ℤ)) -
        adaptedHattedContrast P (roundedGrid lAl mAl) t) :=
      mul_nonneg (by linarith only [hd0]) hdrop0
    exact mul_nonneg (mul_nonneg h4d hcF0) hbSF2
  have henvT : BlockMatLoewnerLE
      (adaptedMean P (roundedGrid lAl mAl) t) (blockScale cF E) := by
    rw [← hFeq]
    exact henvF
  -- the mean drops
  have hdropC : ∀ j : ℕ, j ≤ Hw →
      blockSize (blockSub
        (adaptedMean P (roundedGrid lAl mAl) (t - (j : ℤ)))
        (adaptedMean P (roundedGrid lAl mAl) t))
        F ≤
      meanDrop2ValueIsotropy P lAl cF mAl E F t j := by
    intro j hj
    have hlj : lAl ≤ t - (j : ℤ) := by
      have h1 : (j : ℤ) ≤ (Hw : ℤ) := by exact_mod_cast hj
      omega
    have h := blockSize_meanDrop_le hstat hgrid hlj (by omega)
      (hfinAll _) (hfinAll _) (hdropSmall j hj) hdag.refBlock_isSymm hcF0
      henvT hFsym hFpd
    refine h.trans (le_of_eq ?_)
    rw [meanDrop2ValueIsotropy]
  -- assemble through the bundle
  have hbundle := profile_caps_bundle_entry_of_block_at_level (G := Gacc + 1)
    (kap := kapE) (F := F) (cF := cF) (R := R) (k0 := k0) (cIso := cIso)
    (Dr := meanDrop2ValueIsotropy P lAl cF mAl E F t)
    hd hg hdag hstat hl hCd hn hgrid
    hrho0 hrho1 hst Hw hstart hgeomS hsKw hDeltaT
    (by
      have h1 : t + ((Gacc + 1 : ℕ) : ℤ) - sKw =
          t + (((Gacc + 1 : ℕ) : ℤ)) - sKw := rfl
      exact hentry) hfinAll hEt hS0
    hStar0 hform hpos heps1 htr hkap0 hcomp
    hcIso hiso hFsym hFpd hcF0 hFeq hR1 hlev henvMax
    hV hV0 hDr0 hVmean hvar hvart hdropC hvmean
  intro e he
  obtain ⟨hr1, hr2, hw1, hw2, hc1, hc2⟩ := hbundle e he
  have hmono : rowValue2Isotropy d
      (rowSplitConstant cIso (capsDeepConstant Cd g mAl (Gacc + 1) k0 s t))
      kapE eps ≤ rowValue2Isotropy d (rowSplitConstant cIso cDeep) kapE eps :=
    rowValue2Isotropy_mono hkap0 (rowSplitConstant_mono hcDeep)
  exact ⟨le_trans hr1 (ENNReal.ofReal_le_ofReal hmono),
    le_trans hr2 (ENNReal.ofReal_le_ofReal hmono), hw1, hw2, hc1, hc2⟩

end

end HCPolySupport.HighContrast.Quenched
