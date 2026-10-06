/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnSplitNssEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMomentCollapse

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBurnSplitDeepened

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-split deepened mean envelope and its collapse

The clause-2 chain at the burn-split frame: the mean of an enclosed cell
is dominated by the reference at `2·(deepened first moment of the
enlarged source)`, hence by the **absolute constant `4`** past the
burn-in — no boundary constant, no grid-norm power.  The comparability is
restated at an abstract collapsed coefficient, so the burn-split constant
feeds it directly.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder ENNReal

noncomputable section

variable {d : ℕ}

/-- **The burn-split deepened mean envelope.**  The window height is
`G + 1`, matching the moment interface. -/
theorem adaptedMean_le_scaled_burnsplit [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ' : ℝ → ℝ} {K' : ℝ} {Sh : CoeffSpace d → ℝ}
    (hdag' : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ' K' Sh)
    {G : ℕ}
    (hmeso : ∀ᵐ a ∂P, ∀ m : ℤ, Sh a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m →
      ∀ w : Fin d → ℤ, standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale
            ((3 : ℝ) ^ (g * max ((m : ℝ) - 2 * ((G + 1 : ℕ) : ℝ) -
              (k : ℝ)) 0)) E))
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef)
    (hD : boundaryConst Cd g n ≤ (3 : ℝ) ^ (G + 1 : ℕ))
    {sKw : ℤ} (hsKw : growthBar K' ≤ (3 : ℝ) ^ sKw)
    (k : ℤ) (M : ℕ)
    (hDk : 0 ≤ k + ((G + 1 : ℕ) : ℤ) - 1 - sKw)
    (hsub : adaptedCell (roundedGrid l n) k ⊆
      centeredCube d (k + ((G + 1 : ℕ) : ℤ)))
    (hint : HasFiniteAdaptedMean P (roundedGrid l n) k) :
    BlockMatLoewnerLE (adaptedMean P (roundedGrid l n) k)
      (blockScale
        (2 * (1 + (3 : ℝ) ^
            (-((M : ℝ) * ((k + ((G + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) *
          (1 + 2 * ((1 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K')) *
            growthBar K' ^ IndependentSums.natTriangular (1 + M)))) E) := by
  classical
  have hquadE : ∀ X : BlockVec d,
      0 ≤ blockVecDot X (blockMatVecMul E X) := by
    intro X
    by_cases hX : X = 0
    · subst X
      simp [blockMatVecMul, blockVecDot, vecDot]
    · exact (hdag'.refBlock_posDef X hX).le
  -- the deepened first moment at the window top
  have hVSle := integral_normalizedSourceScale_deepened hdag' hsKw M hDk
  rw [show sKw + (k + ((G + 1 : ℕ) : ℤ) - 1 - sKw) =
      k + ((G + 1 : ℕ) : ℤ) - 1 from by ring] at hVSle
  have hsK' : growthBar K' ≤ (3 : ℝ) ^ (k + ((G + 1 : ℕ) : ℤ) - 1) := by
    refine hsKw.trans ?_
    refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) ?_
    omega
  -- the pathwise envelope, weakened to the first power
  have hscalar : ∀ᵐ a ∂P,
      ∀ X : BlockVec d,
        blockVecDot X (blockMatVecMul
          (coarseBlock (adaptedCell (roundedGrid l n) k) a) X) ≤
        2 * normalizedSourceScale Sh (k + ((G + 1 : ℕ) : ℤ) - 1) a *
          blockVecDot X (blockMatVecMul E X) := by
    filter_upwards [coarseBlock_adaptedCell_burnsplit_nss hd hg
      hdag'.refBlock_posDef hmeso hl hCd hn hD k] with a henv
    intro X
    have hcell := henv hsub X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hcell
    have hnss1 : 1 ≤ normalizedSourceScale Sh
        (k + ((G + 1 : ℕ) : ℤ) - 1) a :=
      one_le_normalizedSourceScale Sh _ a
    have hgle : normalizedSourceScale Sh
        (k + ((G + 1 : ℕ) : ℤ) - 1) a ^ g ≤
        normalizedSourceScale Sh (k + ((G + 1 : ℕ) : ℤ) - 1) a := by
      calc
        normalizedSourceScale Sh (k + ((G + 1 : ℕ) : ℤ) - 1) a ^ g ≤
            normalizedSourceScale Sh (k + ((G + 1 : ℕ) : ℤ) - 1) a ^
              (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnss1 hg.2.le
        _ = normalizedSourceScale Sh (k + ((G + 1 : ℕ) : ℤ) - 1) a :=
          Real.rpow_one _
    have hstep : 2 * normalizedSourceScale Sh
        (k + ((G + 1 : ℕ) : ℤ) - 1) a ^ g *
        blockVecDot X (blockMatVecMul E X) ≤
        2 * normalizedSourceScale Sh (k + ((G + 1 : ℕ) : ℤ) - 1) a *
          blockVecDot X (blockMatVecMul E X) := by
      refine mul_le_mul_of_nonneg_right ?_ (hquadE X)
      exact mul_le_mul_of_nonneg_left hgle (by norm_num)
    linarith only [hcell, hstep]
  -- integrate
  have hint' : HasIntegrableCoarseBlock P
      (adaptedCell (roundedGrid l n) k) := hint
  simp only [adaptedMean]
  intro X
  have hid := blockVecDot_blockMatVecMul_annealedBlock hint' X
  rw [hid, Sharp.blockVecDot_blockMatVecMul_blockScale]
  have hquadX := hquadE X
  have hint1 : Integrable
      (fun a => blockVecDot X (blockMatVecMul
        (coarseBlock (adaptedCell (roundedGrid l n) k) a) X)) P :=
    integrable_blockVecDot_coarseBlock hint' X
  have hint2 : Integrable
      (fun a => 2 * normalizedSourceScale Sh
          (k + ((G + 1 : ℕ) : ℤ) - 1) a *
        blockVecDot X (blockMatVecMul E X)) P := by
    have h := ((integrable_normalizedSourceScale hdag' hsK').const_mul
      2).mul_const (blockVecDot X (blockMatVecMul E X))
    refine h.congr (_root_.Filter.Eventually.of_forall fun a => ?_)
    ring
  have hmono := integral_mono_ae hint1 hint2 (by
    filter_upwards [hscalar] with a ha using ha X)
  have hsplit : ∫ a, 2 * normalizedSourceScale Sh
      (k + ((G + 1 : ℕ) : ℤ) - 1) a *
      blockVecDot X (blockMatVecMul E X) ∂P =
      2 * (∫ a, normalizedSourceScale Sh
          (k + ((G + 1 : ℕ) : ℤ) - 1) a ∂P) *
        blockVecDot X (blockMatVecMul E X) := by
    rw [show (fun a => 2 * normalizedSourceScale Sh
        (k + ((G + 1 : ℕ) : ℤ) - 1) a *
        blockVecDot X (blockMatVecMul E X)) =
        fun a => 2 * (normalizedSourceScale Sh
          (k + ((G + 1 : ℕ) : ℤ) - 1) a *
          blockVecDot X (blockMatVecMul E X)) from by
      funext a
      ring]
    rw [integral_const_mul, integral_mul_const]
    ring
  have hbound : ∫ a, blockVecDot X (blockMatVecMul
      (coarseBlock (adaptedCell (roundedGrid l n) k) a) X) ∂P ≤
      2 * (1 + (3 : ℝ) ^
          (-((M : ℝ) * ((k + ((G + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) *
        (1 + 2 * ((1 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K')) *
          growthBar K' ^ IndependentSums.natTriangular (1 + M))) *
        blockVecDot X (blockMatVecMul E X) := by
    refine le_trans hmono ?_
    rw [hsplit]
    calc
      2 * (∫ a, normalizedSourceScale Sh
          (k + ((G + 1 : ℕ) : ℤ) - 1) a ∂P) *
          blockVecDot X (blockMatVecMul E X) ≤
          2 * (1 + (3 : ℝ) ^
              (-((M : ℝ) *
                ((k + ((G + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) *
            (1 + 2 * ((1 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K')) *
              growthBar K' ^ IndependentSums.natTriangular (1 + M))) *
            blockVecDot X (blockMatVecMul E X) := by
        refine mul_le_mul_of_nonneg_right ?_ hquadX
        exact mul_le_mul_of_nonneg_left hVSle (by norm_num)
      _ = _ := rfl
  linarith only [hbound]

/-- **The collapsed burn-split mean envelope**: past the burn-in the
coefficient is the absolute constant `4`. -/
theorem adaptedMean_le_scaled_burnsplit_collapsed [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ' : ℝ → ℝ} {K' : ℝ} {Sh : CoeffSpace d → ℝ}
    (hdag' : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ' K' Sh)
    {G : ℕ}
    (hmeso : ∀ᵐ a ∂P, ∀ m : ℤ, Sh a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m →
      ∀ w : Fin d → ℤ, standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale
            ((3 : ℝ) ^ (g * max ((m : ℝ) - 2 * ((G + 1 : ℕ) : ℝ) -
              (k : ℝ)) 0)) E))
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef)
    (hD : boundaryConst Cd g n ≤ (3 : ℝ) ^ (G + 1 : ℕ))
    {sKw : ℤ} (hsKw : growthBar K' ≤ (3 : ℝ) ^ sKw)
    (k : ℤ) (M : ℕ)
    (hDk : 0 ≤ k + ((G + 1 : ℕ) : ℤ) - 1 - sKw)
    (hburnk : 1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K')) *
        growthBar K' ^ IndependentSums.natTriangular (2 + M) ≤
      (3 : ℝ) ^ ((M : ℝ) *
        ((k + ((G + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ)))
    (hsub : adaptedCell (roundedGrid l n) k ⊆
      centeredCube d (k + ((G + 1 : ℕ) : ℤ)))
    (hint : HasFiniteAdaptedMean P (roundedGrid l n) k) :
    BlockMatLoewnerLE (adaptedMean P (roundedGrid l n) k)
      (blockScale (4 : ℝ) E) := by
  have hquadE : ∀ X : BlockVec d,
      0 ≤ blockVecDot X (blockMatVecMul E X) := by
    intro X
    by_cases hX : X = 0
    · subst X
      simp [blockMatVecMul, blockVecDot, vecDot]
    · exact (hdag'.refBlock_posDef X hX).le
  have henv := adaptedMean_le_scaled_burnsplit hd hg hdag' hmeso hl
    hCd hn hD hsKw k M hDk hsub hint
  have hd0 : (0 : ℝ) ≤ (3 : ℝ) ^
      (-((M : ℝ) * ((k + ((G + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) := by
    positivity
  have hm := mul_le_mul_of_nonneg_left
    (crudeMoment_mono_order (K := K') M) hd0
  have hexc := deepened_excess_le_one (Gacc := G) (sKw := sKw) (w := k)
    hburnk
  have hcoefle : 2 * (1 + (3 : ℝ) ^
      (-((M : ℝ) * ((k + ((G + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) *
      (1 + 2 * ((1 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K')) *
        growthBar K' ^ IndependentSums.natTriangular (1 + M))) ≤
      (4 : ℝ) := by
    linarith only [hm, hexc]
  exact fun X => le_trans (henv X)
    (blockScale_loewner_mono hquadE hcoefle X)

/-- **The comparability at an abstract collapsed coefficient.** -/
theorem terminal_reference_comparability_of_c1 [NeZero d]
    (hd : 2 ≤ d) {g : ℝ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {n : Mat d} (hn : n.PosDef)
    (t : ℤ)
    (hint : HasFiniteAdaptedMean P (roundedGrid l n) t)
    {c1 : ℝ} (hc11 : 1 ≤ c1)
    (hmean : BlockMatLoewnerLE (adaptedMean P (roundedGrid l n) t)
      (blockScale c1 E)) :
    (1 : ℝ) ≤ kappaRef E * c1 ∧
    ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kappaRef E * c1 *
          blockVecDot X
            (blockMatVecMul (adaptedMean P (roundedGrid l n) t) X) := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hq : (roundedGrid l n).PosDef := Recurrence.posDef_roundedGrid hl hn
  have hc1pos : 0 < c1 := lt_of_lt_of_le zero_lt_one hc11
  -- symmetry and positivity of the two sides
  have hEsymm := hdag.refBlock_isSymm
  have hEpd := hdag.refBlock_posDef
  have hmeanSymm : IsSymmetricBlockMat (adaptedMean P (roundedGrid l n) t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P _ t
  have hmeanPd : Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid l n) t) :=
    Recurrence.blockPosDef_adaptedMean hq t hint
  have hscaleSymm : IsSymmetricBlockMat (blockScale c1 E) :=
    isSymmetricBlockMat_blockScale c1 hEsymm
  have hscalePd : Book.Ch02.BlockPosDef (blockScale c1 E) :=
    Transport.blockPosDef_blockScale hc1pos hEpd
  -- the sharp chain
  have hanti := blockMatLoewnerLE_blockSharp_of_le hmeanSymm hscaleSymm
    hmeanPd hscalePd hmean
  rw [blockSharp_blockScale hEsymm hEpd hc1pos] at hanti
  have hself : BlockMatLoewnerLE
      (blockSharp (adaptedMean P (roundedGrid l n) t))
      (adaptedMean P (roundedGrid l n) t) := by
    simpa only [adaptedMean] using
      Sharp.blockSharp_annealedBlock_le_of_nonempty
        (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t)
        (Recurrence.adaptedCell_nonempty (roundedGrid l n) t) hint
  have hkR := Initialization.blockMatLoewnerLE_reference_kappaRef_blockSharp hEsymm hEpd
  have hkR1 : 1 ≤ kappaRef E :=
    Initialization.one_le_kappaRef hEsymm hEpd
      (Initialization.blockMatLoewnerLE_blockSharp_reference hdag)
  have hkap1 : (1 : ℝ) ≤ kappaRef E * c1 := by
    have h := mul_le_mul hkR1 hc11 (by norm_num)
      (by linarith only [hkR1])
    linarith only [h]
  refine ⟨hkap1, ?_⟩
  intro X
  have h1 := hkR X
  have h2 := hanti X
  have h3 := hself X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h1 h2
  have hb : blockVecDot X (blockMatVecMul (blockSharp E) X) ≤
      c1 * blockVecDot X (blockMatVecMul
        (blockSharp (adaptedMean P (roundedGrid l n) t)) X) := by
    have h2' : c1⁻¹ * blockVecDot X (blockMatVecMul (blockSharp E) X) ≤
        blockVecDot X (blockMatVecMul
          (blockSharp (adaptedMean P (roundedGrid l n) t)) X) := by
      linarith only [h2]
    have hmul := mul_le_mul_of_nonneg_left h2' hc1pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc1pos.ne', one_mul] at hmul
  have hkR0 : (0 : ℝ) ≤ kappaRef E := by linarith only [hkR1]
  have hchain : blockVecDot X (blockMatVecMul E X) ≤
      kappaRef E * (c1 * blockVecDot X (blockMatVecMul
        (blockSharp (adaptedMean P (roundedGrid l n) t)) X)) := by
    have h1' : blockVecDot X (blockMatVecMul E X) ≤
        kappaRef E * blockVecDot X (blockMatVecMul (blockSharp E) X) := by
      linarith only [h1]
    exact le_trans h1' (mul_le_mul_of_nonneg_left hb hkR0)
  have hlast : kappaRef E * (c1 * blockVecDot X (blockMatVecMul
      (blockSharp (adaptedMean P (roundedGrid l n) t)) X)) ≤
      kappaRef E * c1 * blockVecDot X
        (blockMatVecMul (adaptedMean P (roundedGrid l n) t) X) := by
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg hkR0 hc1pos.le)
    linarith only [h3]
  exact le_trans hchain hlast

end

end HCPolySupport.HighContrast.Quenched
