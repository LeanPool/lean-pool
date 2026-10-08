/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop211Cost
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop211CellRenormalization
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedContrastAntitone
public import LeanPool.HighContrastHomogenization.Provider.Quenched.BlockScaleGeometry

/-!
# High-contrast homogenization: Provider.Quenched.Prop211Rebase

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The one-time coarse-ellipticity rebase

This is the unit-range specialization of the renormalization of the
coarse-ellipticity assumptions.  All numerical parameters are selected before
the probability law.  The law-dependent choice is only the triadic bracket of
the original polynomial base and the entry generation supplied by the entry
theorem.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory

noncomputable section


private theorem rebased_reference_aspect_bound (d : ℕ)
    {g delta : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    {mEnt q : ℕ} (hqLow : (2 + aspectRatio E * K) ^ 2 ≤ (3 : ℝ) ^ (q : ℤ))
    (hbase0 : 0 < (2 + aspectRatio E * K))
    (hAhatSymm : IsSymmetricBlockMat (annealedBlock P (centeredCube d ((mEnt + q) : ℤ))))
    (hAhatPos : Book.Ch02.BlockPosDef (annealedBlock P (centeredCube d ((mEnt + q) : ℤ))))
    (hKle : K ≤ (2 + aspectRatio E * K))
    (hAspect : 1 ≤ aspectRatio E)
    : (((1 + 6 * K ^ 2 * (3 : ℝ) ^ (-((mEnt + q) : ℤ))) ^ g) ≤ (7 : ℝ) ^ g) ∧
    (0 < ((1 + 6 * K ^ 2 * (3 : ℝ) ^ (-((mEnt + q) : ℤ))) ^ g)) ∧
    (aspectRatio (annealedBlock P (centeredCube d ((mEnt + q) : ℤ))) ≤ ((1 + 6 * K ^ 2 * (3 : ℝ) ^
      (-((mEnt + q) : ℤ))) ^ g) ^ 2 * aspectRatio E) ∧
    (aspectRatio (blockScale (1 + delta) (annealedBlock P (centeredCube d ((mEnt + q) : ℤ)))) ≤ ((1
      + delta) ^ 2 * ((7 : ℝ) ^ g) ^ 2) * aspectRatio E) ∧
    (1 ≤ ((1 + delta) ^ 2 * ((7 : ℝ) ^ g) ^ 2)) := by
  classical
  let Casp : ℝ := (1 + delta) ^ 2 * ((7 : ℝ) ^ g) ^ 2
  let base : ℝ := 2 + aspectRatio E * K
  let inner : ℕ := mEnt + q
  let Ahat : BlockMat d := annealedBlock P (centeredCube d (inner : ℤ))
  let Ebase : BlockMat d := blockScale (1 + delta) Ahat
  have hAhatUpper := Entry.annealedBlock_centeredCube_le_blockScale hdag (inner : ℤ)
  let cA : ℝ := (1 + 6 * K ^ 2 * (3 : ℝ) ^ (-(inner : ℤ))) ^ g
  have hcA : cA ≤ (7 : ℝ) ^ g := by
    have hKsq : K ^ 2 ≤ (3 : ℝ) ^ (inner : ℤ) := by
      have hK0 : 0 ≤ K := (le_of_lt hdag.one_lt_growthWitness).trans' (by norm_num)
      have hKsqBase : K ^ 2 ≤ base ^ 2 := by
        nlinarith only [hK0, hbase0.le, hKle]
      exact (hKsqBase.trans hqLow).trans
          (zpow_le_zpow_right₀ (by norm_num) (by dsimp only [inner]; omega))
    have hratio : K ^ 2 * (3 : ℝ) ^ (-(inner : ℤ)) ≤ 1 := by
      rw [zpow_neg]
      exact mul_inv_le_one_of_le₀ hKsq (by positivity)
    have hinside : 1 + 6 * K ^ 2 * (3 : ℝ) ^ (-(inner : ℤ)) ≤ 7 := by
      nlinarith only [hratio]
    dsimp only [cA]
    exact Real.rpow_le_rpow (by positivity) hinside hg.1
  have hcApos : 0 < cA := by dsimp only [cA]; positivity
  have hAhatAspect : aspectRatio Ahat ≤ cA ^ 2 * aspectRatio E := by
    have hscaledSymm := isSymmetricBlockMat_blockScale cA hdag.refBlock_isSymm
    have hscaledPos : Book.Ch02.BlockPosDef (blockScale cA E) := by
      intro X hX
      rw [blockVecDot_blockMatVecMul_blockScale]
      exact mul_pos hcApos (hdag.refBlock_posDef X hX)
    have hmono := aspectRatio_mono hAhatSymm hAhatPos hscaledSymm hscaledPos
      (by simpa only [Ahat, cA, inner, Nat.cast_add] using hAhatUpper)
    rwa [aspectRatio_blockScale hcApos E] at hmono
  have hAspectBound : aspectRatio Ebase ≤ Casp * aspectRatio E := by
    rw [show Ebase = blockScale (1 + delta) Ahat by rfl,
      aspectRatio_blockScale (by linarith only [hdelta.1]) Ahat]
    have hsquare := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hcApos.le hcA 2)
      (sq_nonneg (1 + delta))
    dsimp only [Casp]
    exact (mul_le_mul_of_nonneg_left hAhatAspect (sq_nonneg (1 + delta))).trans <| by
      nlinarith only [hsquare, hAspect]
  have hCasp : 1 ≤ Casp := by
    have hdeltaOne : 1 ≤ 1 + delta := by linarith only [hdelta.1]
    have hseven : 1 ≤ (7 : ℝ) ^ g := Real.one_le_rpow (by norm_num) hg.1
    have hdeltaSq : 1 ≤ (1 + delta) ^ 2 := one_le_pow₀ hdeltaOne
    have hsevenSq : 1 ≤ ((7 : ℝ) ^ g) ^ 2 := one_le_pow₀ hseven
    dsimp only [Casp]
    exact one_le_mul_of_one_le_of_one_le hdeltaSq hsevenSq
  exact ⟨hcA, hcApos, hAhatAspect, hAspectBound, hCasp⟩

private theorem rebasing_cell_gain_bound (d : ℕ)
    [NeZero d] {g : ℝ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    : (unitRangeCellGain d g E ≤ (192 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d *
    (1 + unitRangeRenormShift d)) * (2 + aspectRatio E * K)) := by
  classical
  let G0 : ℝ := 192 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d *
    (1 + unitRangeRenormShift d)
  let base : ℝ := 2 + aspectRatio E * K
  have hGainBound : unitRangeCellGain d g E ≤ G0 * base := by
    have hkappa := Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag
    have haspectBase : aspectRatio E ≤ base := by
      have hK1 : 1 ≤ K := le_of_lt hdag.one_lt_growthWitness
      have hAspect : 0 ≤ aspectRatio E :=
        zero_le_one.trans (one_le_aspectRatio_of_coarseEllipticityDagger hdag)
      dsimp only [base]
      nlinarith only [hK1, hAspect]
    have hkbase : kappaRef E ≤ 6 * base :=
      hkappa.trans (mul_le_mul_of_nonneg_left haspectBase (by norm_num))
    have hfactor : 0 < 32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d *
        (1 + unitRangeRenormShift d) := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
      have hs : 0 ≤ unitRangeRenormShift d := unitRangeRenormShift_nonneg d
      have hs1 : 0 < 1 + unitRangeRenormShift d := by linarith only [hs]
      have hpowg : 0 < (3 : ℝ) ^ g := by positivity
      have hfr : 0 < frThreshold d := frThreshold_pos d
      positivity
    rw [unitRangeCellGain]
    dsimp only [G0]
    have hmul := mul_le_mul_of_nonneg_left hkbase hfactor.le
    nlinarith only [hmul]
  exact hGainBound

private theorem rebased_block_contrast_bound (d : ℕ)
    [NeZero d] {g : ℝ}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    {cSc cStar delta : ℝ} {mEnt q : ℕ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hsmall : annealedContrast P (mEnt : ℤ) - 1 ≤ cStar)
    (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1)
    (hcal : (1 + delta) ^ 2 * (1 + cStar) ≤ 1 + cSc)
    (hAhatSymm : IsSymmetricBlockMat (annealedBlock P (centeredCube d ((mEnt + q) : ℤ))))
    (hAhatPos : Book.Ch02.BlockPosDef (annealedBlock P (centeredCube d ((mEnt + q) : ℤ))))
    : (blockContrast (annealedBlock P (centeredCube d ((mEnt + q) : ℤ))) ≤ 1 + cStar) ∧
    (blockContrast (blockScale (1 + delta) (annealedBlock P (centeredCube d ((mEnt + q) : ℤ)))) ≤ 1
      + cSc) := by
  classical
  let inner : ℕ := mEnt + q
  let Ahat : BlockMat d := annealedBlock P (centeredCube d (inner : ℤ))
  let Ebase : BlockMat d := blockScale (1 + delta) Ahat
  have hcontrastInner : blockContrast Ahat ≤ 1 + cStar := by
    have hmono := annealedContrast_antitone hstat hdag
      (show mEnt ≤ inner by dsimp only [inner]; omega)
    change annealedContrast P (inner : ℤ) ≤ 1 + cStar
    linarith only [hmono, hsmall]
  have hcontrastBase : blockContrast Ebase ≤ 1 + cSc := by
    have hscale := blockContrast_blockScale_le hAhatSymm hAhatPos
      (by linarith only [hdelta.1] : 0 < 1 + delta)
    dsimp only [Ebase] at hscale ⊢
    exact hscale.trans <| (mul_le_mul_of_nonneg_left hcontrastInner
      (sq_nonneg (1 + delta))).trans hcal
  exact ⟨hcontrastInner, hcontrastBase⟩

private theorem rebasing_cell_threshold_certificate (d : ℕ)
    [NeZero d] {g : ℝ} {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    (hstat : HCPoly.Frozen.IsStationaryLaw P) (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    {mEnt A D q : ℕ} {T delta : ℝ} (hT : 1 ≤ T)
    (hTthr : Real.log 2 ≤ frGaugeConst d * T ^ 2 *
      ((3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g)) - 1))
    (hinner : ((mEnt + ((A + D + 1) * q)) : ℤ) - (((A + D) * q) : ℤ) = ((mEnt + q) : ℤ))
    (hhalf : (Psi ((3 : ℝ) ^ ((mEnt + q) : ℤ)))⁻¹ ≤ 1 / 2)
    (hTbase : T ≤ renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g) delta
      (unitRangeCellGain d g E) ((A + D) * q) (A * q))
    (hl0 : 1 ≤ renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g) delta
      (unitRangeCellGain d g E) ((A + D) * q) (A * q))
    : (Real.log 2 ≤ frGaugeConst d *
      renormBase g ((d : ℝ) / 2) ((d : ℝ) / 2 - g) delta
        (unitRangeCellGain d g E) ((A + D) * q) (A * q) ^ 2 *
        ((3 : ℝ) ^ (2 * ((d : ℝ) / 2 - g)) - 1)) ∧
    (HasCellRenormalization P S (annealedBlock P (centeredCube d ((mEnt + q) : ℤ))) g ((d : ℝ) / 2)
      (unitRangeCellGain d g E) (mEnt + ((A + D + 1) * q)) ((A + D) * q) (A * q)) := by
  classical
  let mu : ℝ := (d : ℝ) / 2 - g
  let h : ℕ := A * q
  let l0 : ℕ := (A + D) * q
  let inner : ℕ := mEnt + q
  let nBase : ℕ := mEnt + ((A + D + 1) * q)
  let Ahat : BlockMat d := annealedBlock P (centeredCube d (inner : ℤ))
  have hthr : Real.log 2 ≤ frGaugeConst d *
      renormBase g ((d : ℝ) / 2) mu delta
        (unitRangeCellGain d g E) l0 h ^ 2 *
        ((3 : ℝ) ^ (2 * mu) - 1) := by
    have hren : T ≤ renormBase g ((d : ℝ) / 2) mu delta
        (unitRangeCellGain d g E) l0 h := hTbase
    have hsq := sq_le_sq₀ (zero_le_one.trans hT)
      (zero_le_one.trans hl0) |>.2 hren
    have hfac : 0 ≤ frGaugeConst d * ((3 : ℝ) ^ (2 * mu) - 1) := by
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      by_contra hneg
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg
        (le_of_lt (lt_of_not_ge hneg)) (sq_nonneg T)
      nlinarith only [hTthr, hlog, hnonpos]
    have hmul := mul_le_mul_of_nonneg_right hsq hfac
    nlinarith only [hTthr, hmul]
  have hcell : HasCellRenormalization P S Ahat g ((d : ℝ) / 2)
      (unitRangeCellGain d g E) nBase l0 h := by
    have hn0 : 0 ≤ (nBase : ℤ) - (l0 : ℤ) := by
      dsimp only [nBase, l0]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      rw [hinner]
      positivity
    have hhl0 : h ≤ l0 + 1 := by
      dsimp only [h, l0]
      have hAD : A ≤ A + D := Nat.le_add_right A D
      exact (Nat.mul_le_mul_right q hAD).trans (Nat.le_add_right _ 1)
    simpa only [Ahat, inner, nBase, l0, Nat.cast_add, Nat.cast_mul, Nat.cast_one, hinner] using
      hasCellRenormalization_unitRangeCellGain_of_frozen hstat hunit hdag hn0 hhl0
        (by simpa only [nBase, l0, Nat.cast_add, Nat.cast_mul, Nat.cast_one, hinner] using hhalf)
  exact ⟨hthr, hcell⟩
/-- The one-time rebase provider used by the annealed-to-quenched step. -/
theorem exists_prop211_rebase_provider (d : ℕ) (hd : 2 ≤ d) :
    ∀ {cSc g cStar Centry : ℝ},
      cStar ∈ Set.Ioo (0 : ℝ) cSc →
      g ∈ Set.Ico (0 : ℝ) 1 → 0 < Centry →
      ∃ Crebase : ℝ, 0 < Crebase ∧ Centry ≤ Crebase ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d)
          (Psi : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          HCPoly.Frozen.IsStationaryLaw P →
          HCPoly.Frozen.IsUnitRangeLaw P →
          HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
          (∃ mEnt : ℕ,
            (mEnt : ℤ) ≤
              ⌈Centry * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
            annealedContrast P (mEnt : ℤ) - 1 ≤ cStar ∧
            (3 : ℝ) ^ mEnt ≤
              3 * (2 + aspectRatio E * K) ^ Centry) →
          ∃ (nBase : ℕ) (Pbase : Measure (CoeffSpace d))
            (gBase : ℝ) (Ebase : BlockMat d) (PsiBase : ℝ → ℝ)
            (Kbase : ℝ) (Sbase : CoeffSpace d → ℝ),
            gBase = (1 + g) / 2 ∧
            IsProbabilityMeasure Pbase ∧
            HCPoly.Frozen.IsStationaryLaw Pbase ∧
            HCPoly.Frozen.IsUnitRangeLaw Pbase ∧
            HCPoly.Frozen.CoarseEllipticityDagger
              Pbase gBase Ebase PsiBase Kbase Sbase ∧
            annealedContrast Pbase 0 - 1 ≤ cStar ∧
            blockContrast Ebase ≤ 1 + cSc ∧
            (∀ j : ℕ,
              annealedContrast Pbase (j : ℤ) =
                annealedContrast P ((nBase + j : ℕ) : ℤ)) ∧
            (∀ j : ℕ,
              annealedBlock Pbase (centeredCube d (j : ℤ)) =
                annealedBlock P
                  (centeredCube d ((nBase + j : ℕ) : ℤ))) ∧
            (3 : ℝ) ^ nBase ≤
              (2 + aspectRatio E * K) ^ Crebase ∧
            2 + aspectRatio Ebase * Kbase ≤
              (2 + aspectRatio E * K) ^ Crebase := by
  have : NeZero d := ⟨by omega⟩
  intro cSc g cStar Centry hcStar hg hCentry
  let rho : ℝ := (1 + g) / 2
  let mu : ℝ := (d : ℝ) / 2 - g
  have hdiff : 0 < rho - g := by
    dsimp only [rho]
    linarith only [hg.2]
  have hmu : 0 < mu := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp only [mu]
    linarith only [hdR, hg.2]
  have hrho : rho ∈ Set.Ico (0 : ℝ) 1 := by
    dsimp only [rho]
    constructor <;> linarith only [hg.1, hg.2]
  obtain ⟨delta, hdelta, hcal⟩ := exists_rebase_enlargement hcStar
  let G0 : ℝ := 192 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d *
    (1 + unitRangeRenormShift d)
  have hG0 : 0 < G0 := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    have hshift : 0 ≤ unitRangeRenormShift d := unitRangeRenormShift_nonneg d
    have hshift1 : 0 < 1 + unitRangeRenormShift d := by
      linarith only [hshift]
    have hpowg : 0 < (3 : ℝ) ^ g := by positivity
    have hfr : 0 < frThreshold d := frThreshold_pos d
    dsimp only [G0]
    positivity
  obtain ⟨T, A, D, B, hT, hTthr, hA, hAcoef, hAburn,
      hD, hDcoef, hDgain, hB, hBbuffer⟩ :=
    exists_renormalization_parameters d hdiff hmu hdelta.1 hdelta.2 hG0
  let Kfix : ℝ := frPoweredGrowthWitness d mu
  let eK : ℝ := 2 * (1 + 4 * (B : ℝ) + Real.logb 3 Kfix)
  let Casp : ℝ := (1 + delta) ^ 2 * ((7 : ℝ) ^ g) ^ 2
  let Cgen : ℝ := 1 + Centry + 4 * ((A + D + 1 : ℕ) : ℝ)
  let Cref : ℝ := 2 + Real.logb 3 Casp + eK
  let Crebase : ℝ := max 1 (max Centry (max Cgen Cref))
  have hCrebase : 0 < Crebase :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hCentryCrebase : Centry ≤ Crebase :=
    (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨Crebase, hCrebase, hCentryCrebase, ?_⟩
  intro P E Psi K S hprob hstat hunit hdag hentry
  let : IsProbabilityMeasure P := hprob
  let base : ℝ := 2 + aspectRatio E * K
  have hbase : 3 ≤ base := by
    simpa only [base] using three_le_rebaseBase hdag
  have hbase0 : 0 < base := lt_of_lt_of_le (by norm_num) hbase
  obtain ⟨mEnt, -, hsmall, hmEntCost⟩ := hentry
  obtain ⟨q, hqLow, hqHigh⟩ := Entry.exists_pow_three_bracket
    (sq_nonneg base)
  obtain ⟨hq, hqCost⟩ := pow_three_bracket_sq_le_four hbase hqLow hqHigh
  let h : ℕ := A * q
  let l0 : ℕ := (A + D) * q
  let b : ℕ := B * q
  let inner : ℕ := mEnt + q
  let nBase : ℕ := mEnt + ((A + D + 1) * q)
  let Ahat : BlockMat d := annealedBlock P (centeredCube d (inner : ℤ))
  let Ebase : BlockMat d := blockScale (1 + delta) Ahat
  let Pbase : Measure (CoeffSpace d) := triadicRebasedLaw nBase P
  let : IsProbabilityMeasure Pbase :=
    isProbabilityMeasure_triadicRebasedLaw nBase P
  let PsiBase : ℝ → ℝ := renormalizedCombinedGauge d nBase b mu Psi
  let Kbase : ℝ := renormalizedCombinedGrowthWitness d b mu K
  let Sbase : CoeffSpace d → ℝ := rebasedPullbackSource nBase
    (renormalizedCombinedSource S Ahat delta rho h nBase)
  have hinner : (nBase : ℤ) - (l0 : ℤ) = (inner : ℤ) := by
    simp only [nBase, l0, inner]
    push_cast
    ring
  have hhalf : (Psi ((3 : ℝ) ^ (inner : ℤ)))⁻¹ ≤ 1 / 2 :=
    inv_gauge_at_entry_add_bracket_le_half hdag hqLow
  have hAhatSymm : IsSymmetricBlockMat Ahat := by
    exact isSymmetricBlockMat_annealedBlock P _
  have hAhatPos : Book.Ch02.BlockPosDef Ahat := by
    exact blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag _
  have hGainPos : 0 < unitRangeCellGain d g E :=
    unitRangeCellGain_pos hdag.refBlock_isSymm hdag.refBlock_posDef
      (Initialization.blockMatLoewnerLE_blockSharp_reference hdag)
  have hGainBound :=
    rebasing_cell_gain_bound d hdag
  have hl0Exp : g - (d : ℝ) / 2 +
      mu * ((l0 : ℝ) - (h : ℝ)) =
        mu * ((D * q : ℕ) : ℝ) - mu := by
    dsimp only [mu, l0, h]
    push_cast
    ring
  have hbaseOne : 1 ≤ base := by linarith only [hbase]
  have hbaseSq : base ≤ base ^ 2 := by nlinarith only [hbaseOne]
  have hbaseq : base ≤ (3 : ℝ) ^ (q : ℤ) := hbaseSq.trans hqLow
  have hDpow : G0 * T / delta * base ≤
      (3 : ℝ) ^ (mu * ((D * q : ℕ) : ℝ) - mu) :=
    mul_base_le_rpow_mul_index hmu hq hDcoef hDgain hbase0.le hbaseq
  have hTbase : T ≤ renormBase g ((d : ℝ) / 2) mu delta
      (unitRangeCellGain d g E) l0 h :=
    T_le_renormBase_of_gain_bound hT hdelta.1 hGainPos hGainBound hDpow hl0Exp
  have hl0 : 1 ≤ renormBase g ((d : ℝ) / 2) mu delta
      (unitRangeCellGain d g E) l0 h :=
    hT.trans hTbase
  obtain ⟨hthr, hcell⟩ :=
    rebasing_cell_threshold_certificate d hdag hstat hunit hT
      hTthr hinner hhalf hTbase hl0
  have hb1 : 1 ≤ b := by
    dsimp only [b]
    exact Nat.mul_pos hB hq
  have hh1 : 1 ≤ h := by
    dsimp only [h]
    exact Nat.mul_pos hA hq
  have hbuf : Real.log (2 * renormCellCount d h) ≤
      frGaugeConst d * ((3 : ℝ) ^ (2 * mu * (b : ℝ)) - 1) := by
    simpa only [h, b] using renorm_buffer_of_multiplier hmu hA hq hBbuffer
  have href : BlockMatLoewnerLE E (blockScale (2 * kappaRef E) Ahat) := by
    simpa only [Ahat] using
      blockMatLoewnerLE_blockScale_annealedBlock_reference hdag (inner : ℤ)
        (hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag _)
        hhalf
  have hburn : 2 * kappaRef E ≤
      (1 + delta) * (3 : ℝ) ^ ((rho - g) * (h : ℝ)) := by
    have hkappa := Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag
    have haspectBase : aspectRatio E ≤ base := by
      have hK1 : 1 ≤ K := le_of_lt hdag.one_lt_growthWitness
      have hAspect : 0 ≤ aspectRatio E :=
        zero_le_one.trans (one_le_aspectRatio_of_coarseEllipticityDagger hdag)
      dsimp only [base]
      nlinarith only [hK1, hAspect]
    have hkbase : kappaRef E ≤ 6 * base :=
      hkappa.trans (mul_le_mul_of_nonneg_left haspectBase (by norm_num))
    simpa only [h] using kappa_burn_of_multiplier hdelta.1 hq
      hAcoef hAburn hbase0.le hbaseq hkbase
  have hdagBase : HCPoly.Frozen.CoarseEllipticityDagger
      Pbase rho Ebase PsiBase Kbase Sbase := by
    have hgr : g ≤ rho := by linarith only [hdiff]
    exact coarseEllipticityDagger_rebased_of_renormalization hdag hAhatSymm
      hAhatPos hdelta.1.le rfl hmu hgr
      hrho hGainPos hl0 hthr hcell hb1 hh1 hbuf href hburn
  obtain ⟨hcontrastInner, hcontrastBase⟩ :=
    rebased_block_contrast_bound d hdag hstat hsmall
      hdelta hcal hAhatSymm hAhatPos
  have hnCost0 : (3 : ℝ) ^ nBase ≤ base ^ Cgen := by
    dsimp only [nBase, Cgen]
    exact rebase_generation_cost hbase hmEntCost hqCost
  have hnCost : (3 : ℝ) ^ nBase ≤ base ^ Crebase :=
    hnCost0.trans (Real.rpow_le_rpow_of_exponent_le
      (by linarith only [hbase] : 1 ≤ base)
      ((le_max_left Cgen Cref).trans (le_max_right Centry _)
        |>.trans (le_max_right 1 _)))
  have hKle : K ≤ base := by
    have hAspect : 1 ≤ aspectRatio E := one_le_aspectRatio_of_coarseEllipticityDagger hdag
    dsimp only [base]
    nlinarith only [hAspect, hdag.one_lt_growthWitness]
  have hKcost : Kbase ≤ base ^ eK := by
    simpa only [Kbase, b, eK, Kfix] using
      renormalizedCombinedGrowthWitness_le_rpow d hmu hbase hKle hqCost
  have hAspect : 1 ≤ aspectRatio E := one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hAhatUpper := Entry.annealedBlock_centeredCube_le_blockScale hdag (inner : ℤ)
  let cA : ℝ := (1 + 6 * K ^ 2 * (3 : ℝ) ^ (-(inner : ℤ))) ^ g
  obtain ⟨hcA, hcApos, hAhatAspect, hAspectBound, hCasp⟩ :=
    rebased_reference_aspect_bound d hg hdelta hdag hqLow hbase0 hAhatSymm hAhatPos hKle hAspect
  have hAspectNew : 1 ≤ aspectRatio Ebase :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdagBase
  have hKbaseOne : 1 ≤ Kbase := by
    dsimp only [Kbase]
    exact one_le_combinedGrowthWitness _ _
  have hrefCost0 : 2 + aspectRatio Ebase * Kbase ≤ base ^ Cref := by
    dsimp only [Cref]
    exact rebase_reference_cost hbase hAspect
      (by dsimp only [base]; nlinarith only [hAspect, hdag.one_lt_growthWitness])
      hCasp hAspectNew hKbaseOne hAspectBound hKcost
  have hrefCost : 2 + aspectRatio Ebase * Kbase ≤ base ^ Crebase :=
    hrefCost0.trans (Real.rpow_le_rpow_of_exponent_le
      (by linarith only [hbase] : 1 ≤ base)
      ((le_max_right Cgen Cref).trans (le_max_right Centry _)
        |>.trans (le_max_right 1 _)))
  refine ⟨nBase, Pbase, rho, Ebase, PsiBase, Kbase, Sbase, rfl,
    isProbabilityMeasure_triadicRebasedLaw nBase P,
    stationaryLaw_triadicRebasedLaw hstat nBase,
    unitRangeLaw_triadicRebasedLaw hunit nBase, hdagBase, ?_, hcontrastBase,
    ?_, ?_, ?_, ?_⟩
  · exact annealedContrast_triadicRebasedLaw_zero_sub_one_le_of_le hstat hdag
      (show mEnt ≤ nBase by dsimp only [nBase]; omega) hsmall
  · intro j
    simpa only [Pbase, add_comm] using! annealedContrast_triadicRebasedLaw nBase P (j : ℤ)
  · intro j
    simpa only [Pbase, add_comm] using! annealedBlock_triadicRebasedLaw nBase P (j : ℤ)
  · simpa only [base] using hnCost
  · simpa only [base] using hrefCost

end

end HCPolySupport.HighContrast.Quenched
