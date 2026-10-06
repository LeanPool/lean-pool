/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCapsBundleEntryIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValueSharpIsotropyAtLevel

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCapsBundleEntryIsotropyAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The entry caps bundle at a released split level

The six-clause bundle with its two weak quantities read against the released
sharp weak value.  The four row and centering clauses are level-free and are
the pinned ones.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The entry caps bundle, at a released split level.** -/
theorem profile_caps_bundle_entry_of_block_at_level [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {lAl : ℤ} (hl : (kZero d : ℤ) ≤ lAl)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {mAl : Mat d} (hn : mAl.PosDef)
    (hgrid : IsRoundedGrid lAl (roundedGrid lAl mAl))
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    {s t : ℤ} (hst : s ≤ t) (Hw : ℕ) (hstart : lAl ≤ t - (Hw : ℤ))
    {G : ℕ}
    (hgeomS : ∀ k : ℤ, k ≤ s →
      ∀ w ∈ Response.alignedIndex (roundedGrid lAl mAl) k s,
        adaptedCellAt (roundedGrid lAl mAl) k w ⊆
          centeredCube d (t + (G : ℤ)))
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    (hentry : sourceMomentTwo K ≤ (3 : ℝ) ^ (t + (G : ℤ) - sK))
    (hintAll : ∀ k : ℤ, HasFiniteAdaptedMean P (roundedGrid lAl mAl) k)
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid lAl mAl) t))
    {S0 SStar0 K0 : Mat d} (hS0 : S0.PosDef) (hStar0 : SStar0.PosDef)
    (hform : toFullBlockMat (adaptedMean P (roundedGrid lAl mAl) t) =
      schurBlock S0 SStar0 K0)
    {eps : ℝ} (hpos : 0 < eps) (heps1 : eps ≤ 1)
    (htr : (d : ℝ) * (schurHattedContrast S0 SStar0 - 1) ≤ eps)
    {kap : ℝ} (hkap0 : 0 ≤ kap)
    (hcomp : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kap * blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid lAl mAl) t) X))
    {k0 : ℤ} {cIso : ℝ} (hcIso : 0 ≤ cIso)
    (hiso : ∀ k : ℤ, k0 ≤ k → k ≤ s →
      ∀ w ∈ Response.alignedIndex (roundedGrid lAl mAl) k s,
        BlockMatLoewnerLE
          (annealedBlock P (adaptedCellAt (roundedGrid lAl mAl) k w))
          (blockScale (1 + cIso) E))
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {cF : ℝ} (hcF0 : 0 ≤ cF) (hFeq : F = blockScale cF E)
    {R lev : ℝ} (hR1 : 1 ≤ R) (hlev : 1 ≤ lev)
    (henvMax : ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid lAl mAl) t F a ≤
        ENNReal.ofReal (R *
          ((max 1 (3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))))) ^ g / 2)))
    {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    (hV : ∀ j : ℕ, j ≤ Hw → 0 ≤ V j) (hV0 : 0 ≤ V0)
    (hDr0 : ∀ j : ℕ, j ≤ Hw → 0 ≤ Dr j)
    (hVmean : 0 ≤ Vmean)
    (hvar : ∀ j : ℕ, j ≤ Hw →
      scaleVariance P (roundedGrid lAl mAl)
        F (t - (j : ℤ)) ≤
        ENNReal.ofReal (V j))
    (hvart : scaleVariance P (roundedGrid lAl mAl)
      F t ≤ ENNReal.ofReal V0)
    (hdrop : ∀ j : ℕ, j ≤ Hw →
      blockSize (blockSub
        (adaptedMean P (roundedGrid lAl mAl) (t - (j : ℤ)))
        (adaptedMean P (roundedGrid lAl mAl) t))
        F ≤ Dr j)
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
        ENNReal.ofReal (rowValue2Isotropy d
          (rowSplitConstant cIso (capsDeepConstant Cd g mAl G k0 s t))
          kap eps) ∧
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
        ENNReal.ofReal (rowValue2Isotropy d
          (rowSplitConstant cIso (capsDeepConstant Cd g mAl G k0 s t))
          kap eps) ∧
      Response.profilePrimalWeakQuantity P mAl
          (Recurrence.posDef_of_isRoundedGrid hgrid) t
          (fun a ↦ a.subSkew (Response.responseSkew K0)
            (Response.is_skew_mat_response_skew K0))
          (Response.centeredResponseLoadP S0 SStar0 K0 e)
          (Response.centeredResponseLoadQ S0 SStar0 K0 e) ≤
        ENNReal.ofReal
          (weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
            (Response.maxGroupConstantAtLevel lev) (Response.energyGoodConstantAtLevel lev) P mAl (Response.responseSkew K0) F
            (loadScaleOfScalar cF kap) mAl rho Hw
            (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) (R / 2) lev t lAl
            V V0 Dr Vmean) ∧
      Response.profileAdjointWeakQuantity P mAl
          (Recurrence.posDef_of_isRoundedGrid hgrid) t
          (fun a ↦ a.subSkew (Response.responseSkew K0)
            (Response.is_skew_mat_response_skew K0))
          (Response.centeredResponseLoadP S0 SStar0 K0 e)
          (Response.centeredResponseLoadQ S0 SStar0 K0 e) ≤
        ENNReal.ofReal
          (weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
            (Response.maxGroupConstantAtLevel lev) (Response.energyGoodConstantAtLevel lev) P mAl (Response.responseSkew K0) F
            (loadScaleOfScalar cF kap) mAl rho Hw
            (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) (R / 2) lev t lAl
            V V0 Dr Vmean) ∧
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
  intro e he
  have hq : (roundedGrid lAl mAl).PosDef :=
    Recurrence.posDef_of_isRoundedGrid hgrid
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hbC0 : 0 < boundaryConst Cd g mAl :=
    Transport.zero_lt_boundaryConst (by linarith only [hCd1]) hg.2 hn
  have hCK1 : (1 : ℝ) ≤ sourceMomentOne K := one_le_sourceMomentOne
  have hrows := caps_bundle_entry_rows_isotropy hd hg hdag hl hCd hn hgrid hsK t
    hDelta hentry hst hgeomS hcIso hiso (hintAll t) hS0 hStar0 hform hpos
    heps1 htr hkap0 hcomp e he
  -- the two weak quantities
  have hweakm := profilePrimalWeakQuantity_le_weakValueSharp_of_block_at_level
    hg hdag hstat hl hn hgrid hn hrho0 hrho1 t Hw hstart
    hFsym hFpd hcF0 hFeq hR1 hlev henvMax hsK hDelta
    hintAll hEt hS0 hStar0 hform hpos heps1 htr hkap0 hcomp hV hV0 hDr0
    hVmean hvar hvart hdrop hvmean e he
  have hweakp := profileAdjointWeakQuantity_le_weakValueSharp_of_block_at_level
    hg hdag hstat hl hn hgrid hn hrho0 hrho1 t Hw hstart
    hFsym hFpd hcF0 hFeq hR1 hlev henvMax hsK hDelta
    hintAll hEt hS0 hStar0 hform hpos heps1 htr hkap0 hcomp hV hV0 hDr0
    hVmean hvar hvart hdrop hvmean e he
  -- the centering caps
  have hcent := centering_caps_at_terminal hq t (hintAll t) hS0 hStar0 hform
    hpos heps1 htr e he
  exact ⟨hrows.1, hrows.2, hweakm, hweakp, hcent.1, hcent.2⟩

end

end HCPolySupport.HighContrast.Quenched
