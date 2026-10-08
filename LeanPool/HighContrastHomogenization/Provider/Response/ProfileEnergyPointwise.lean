/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileEnergyCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseAnnealed

/-!
# High-contrast homogenization: Provider.Response.ProfileEnergyPointwise

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Pointwise optimizer-energy bounds from the complete maximum

The terminal cell is one of the terms of the all-scale maximum.  Its response
block is consequently below `(1 + M_t) E_t` in quadratic form, which controls
the canonical optimizer energy.  The coefficient-transpose assertion follows
from the signed block congruence and retains its independent load.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02

open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The square of the response-energy load. -/
theorem sq_profileEnergyLoad {L : ℝ} {p q : Vec d} :
    profileEnergyLoad L p q ^ 2 = L ^ 2 + |vecDot p q| := by
  rw [profileEnergyLoad_eq, Real.sq_sqrt]
  exact add_nonneg (sq_nonneg L) (abs_nonneg _)

/-- The terminal maximum controls the primal optimizer energy. -/
theorem sq_diagonalWeakEnergy_le_maximum
    {rho : ℝ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) :
    diagonalWeakEnergy hq t a p r ^ 2 ≤
      (1 + (diagonalWeakMaximum rho q t E a).toReal) *
          diagonalWeakLoadMinus E p r ^ 2 +
        2 * |vecDot p r| := by
  let A : BlockMat d := adaptedResponse q t 0 a
  let X : BlockVec d := (-p, r)
  let M : ℝ := (diagonalWeakMaximum rho q t E a).toReal
  have hcenter : adaptedCellCenter q t (0 : Fin d → ℤ) ∈ adaptedCell q t := by
    rw [Recurrence.adaptedCellCenter_mem_adaptedCell_iff hq (le_refl t)]
    intro i
    simp
  have hw : (0 : Fin d → ℤ) ∈ alignedIndex q t t :=
    (mem_alignedIndex_iff hq (le_refl t)).mpr hcenter
  have hexcess : blockExcess A E ≤ M := by
    have h := weighted_excess_le_diagonalWeakMaximum_toReal hq hE hEpd
      (le_refl t) hw hfinite
    simpa only [Int.cast_sub, sub_self, mul_zero, neg_zero, Real.rpow_zero,
      one_mul, A, M] using h
  have hAsym : IsSymmetricBlockMat A :=
    Recurrence.isSymmetricBlockMat_adaptedResponse q t 0 a
  have hApsd : (toFullBlockMat A).PosSemidef :=
    (posDef_toFullBlockMat hAsym
      (Recurrence.blockPosDef_adaptedResponse hq t 0 a)).posSemidef
  have hsize : blockSize A E ≤ 1 + M :=
    (blockSize_le_one_add_blockExcess hAsym hApsd hE hEpd).trans
      (by linarith only [hexcess])
  have hup := (PortableHistory.blockSize_sandwich hAsym hE hEpd).1
  have hup' : toFullBlockMat A ≤
      toFullBlockMat (blockScale (blockSize A E) E) := by
    rw [toFullBlockMat_blockScale]
    exact hup
  have hquadHalf := blockMatLoewnerLE_of_le hup' X
  have hquad : blockVecDot X (blockMatVecMul A X) ≤
      blockSize A E * blockVecDot X (blockMatVecMul E X) := by
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hquadHalf
    linarith only [hquadHalf]
  have hEquad0 : 0 ≤ blockVecDot X (blockMatVecMul E X) := by
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    exact (posDef_toFullBlockMat hE hEpd).posSemidef.dotProduct_mulVec_nonneg _
  have hquad' : blockVecDot X (blockMatVecMul A X) ≤
      (1 + M) * blockVecDot X (blockMatVecMul E X) :=
    hquad.trans (mul_le_mul_of_nonneg_right hsize hEquad0)
  have henergy : diagonalWeakEnergy hq t a p r ^ 2 =
      blockVecDot X (blockMatVecMul A X) - 2 * vecDot p r := by
    have hJenergy := responseJ_eq_sq_diagonalWeakEnergy hq t a p r
    have hJblock := responseJ_eq_coarseBlock (adaptedDomain hq t) a p r
    rw [hJenergy] at hJblock
    have hAeq : coarseBlock (adaptedCell q t) a = A := by
      dsimp only [A, adaptedResponse]
      rw [PortableHistory.adaptedCellAt_zero]
    change (1 / 2 : ℝ) * diagonalWeakEnergy hq t a p r ^ 2 =
      (1 / 2 : ℝ) * blockVecDot ((-p, r) : BlockVec d)
        (blockMatVecMul (coarseBlock (adaptedCell q t) a) ((-p, r) : BlockVec d)) -
          vecDot p r at hJblock
    rw [hAeq] at hJblock
    change (1 / 2 : ℝ) * diagonalWeakEnergy hq t a p r ^ 2 =
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul A X) - vecDot p r at hJblock
    linarith only [hJblock]
  rw [henergy, sq_diagonalWeakLoadMinus hE hEpd]
  change blockVecDot X (blockMatVecMul A X) - 2 * vecDot p r ≤
    (1 + M) * blockVecDot X (blockMatVecMul E X) + 2 * |vecDot p r|
  have habs := neg_le_abs (vecDot p r)
  linarith only [hquad', habs]

/-- The same terminal maximum controls the coefficient-transpose optimizer
energy with its separate plus load. -/
theorem sq_diagonalWeakAdjointEnergy_le_maximum
    {rho : ℝ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) :
    diagonalWeakAdjointEnergy hq t a p r ^ 2 ≤
      (1 + (diagonalWeakMaximum rho q t E a).toReal) *
          diagonalWeakLoadPlus E p r ^ 2 +
        2 * |vecDot p r| := by
  let Ead := blockMatMul (blockDiag 1 (-1))
    (blockMatMul E (blockDiag 1 (-1)))
  have hEad : IsSymmetricBlockMat Ead :=
    isSymmetricBlockMat_adjointSign_congr hE
  have hEadpd : BlockPosDef Ead := blockPosDef_adjointSign_congr hEpd
  have hMad : diagonalWeakMaximum rho q t Ead a.transpose =
      diagonalWeakMaximum rho q t E a :=
    diagonalWeakMaximum_adjoint rho hq t E a
  have hfinitead : diagonalWeakMaximum rho q t Ead a.transpose ≠ ⊤ := by
    rw [hMad]
    exact hfinite
  have hmain := sq_diagonalWeakEnergy_le_maximum hq hEad hEadpd
    (a := a.transpose) p r hfinitead
  rw [hMad, diagonalWeakLoadMinus_adjoint E p r] at hmain
  exact hmain

/-- On the bad event the primal energy costs one square root of the maximum. -/
theorem diagonalWeakEnergy_le_sqrt_two_mul_bad
    {rho : ℝ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hbad : (1 : ℝ≥0∞) < diagonalWeakMaximum rho q t E a) :
    diagonalWeakEnergy hq t a p r ≤
      Real.sqrt 2 * Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
        profileEnergyLoad (diagonalWeakLoadMinus E p r) p r := by
  let M : ℝ := (diagonalWeakMaximum rho q t E a).toReal
  let L : ℝ := diagonalWeakLoadMinus E p r
  let Lambda : ℝ := profileEnergyLoad L p r
  have hM : 1 < M := by
    exact (ENNReal.toReal_lt_toReal (by simp) hfinite).2 hbad
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  have hdot : 0 ≤ |vecDot p r| := abs_nonneg _
  have hsq := sq_diagonalWeakEnergy_le_maximum hq hE hEpd p r hfinite
  have hmajor : diagonalWeakEnergy hq t a p r ^ 2 ≤ 2 * M * Lambda ^ 2 := by
    rw [sq_profileEnergyLoad]
    calc
      diagonalWeakEnergy hq t a p r ^ 2 ≤
          (1 + M) * L ^ 2 + 2 * |vecDot p r| := hsq
      _ ≤ 2 * M * (L ^ 2 + |vecDot p r|) := by
        have hML : (1 + M) * L ^ 2 ≤ 2 * M * L ^ 2 := by
          exact mul_le_mul_of_nonneg_right (by linarith only [hM]) hL2
        have hMd : 2 * |vecDot p r| ≤ 2 * M * |vecDot p r| := by
          exact mul_le_mul_of_nonneg_right (by linarith only [hM]) hdot
        linarith only [hML, hMd]
  have hrootM0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hLambda0 : 0 ≤ Lambda := profileEnergyLoad_nonneg L p r
  have hrhs0 : 0 ≤ Real.sqrt 2 * Real.sqrt M * Lambda :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hrootM0) hLambda0
  rw [show diagonalWeakEnergy hq t a p r =
      Real.sqrt (diagonalWeakEnergy hq t a p r ^ 2) by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (diagonalWeakEnergy_nonneg hq t a p r)]]
  refine (Real.sqrt_le_sqrt hmajor).trans_eq ?_
  rw [show 2 * M * Lambda ^ 2 =
      (Real.sqrt 2 * Real.sqrt M * Lambda) ^ 2 by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
          Real.sq_sqrt (by linarith only [hM])],
    Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs0]

/-- On the good event the primal energy is bounded by its deterministic load. -/
theorem diagonalWeakEnergy_le_sqrt_two_mul_good
    {rho : ℝ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (p r : Vec d)
    (hgood : diagonalWeakMaximum rho q t E a ≤ (1 : ℝ≥0∞)) :
    diagonalWeakEnergy hq t a p r ≤
      Real.sqrt 2 * profileEnergyLoad (diagonalWeakLoadMinus E p r) p r := by
  have hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) hgood
  let M : ℝ := (diagonalWeakMaximum rho q t E a).toReal
  let L : ℝ := diagonalWeakLoadMinus E p r
  let Lambda : ℝ := profileEnergyLoad L p r
  have hM : M ≤ 1 := by
    exact (ENNReal.toReal_le_toReal hfinite (by simp)).2 hgood
  have hsq := sq_diagonalWeakEnergy_le_maximum hq hE hEpd p r hfinite
  have hmajor : diagonalWeakEnergy hq t a p r ^ 2 ≤ 2 * Lambda ^ 2 := by
    rw [sq_profileEnergyLoad]
    calc
      diagonalWeakEnergy hq t a p r ^ 2 ≤
          (1 + M) * L ^ 2 + 2 * |vecDot p r| := hsq
      _ ≤ 2 * (L ^ 2 + |vecDot p r|) := by
        have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
        have hML : (1 + M) * L ^ 2 ≤ 2 * L ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hM]) hL2
        linarith only [hML]
  have hLambda0 : 0 ≤ Lambda := profileEnergyLoad_nonneg L p r
  have hrhs0 : 0 ≤ Real.sqrt 2 * Lambda := by positivity
  rw [show diagonalWeakEnergy hq t a p r =
      Real.sqrt (diagonalWeakEnergy hq t a p r ^ 2) by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (diagonalWeakEnergy_nonneg hq t a p r)]]
  refine (Real.sqrt_le_sqrt hmajor).trans_eq ?_
  rw [show 2 * Lambda ^ 2 = (Real.sqrt 2 * Lambda) ^ 2 by
        rw [mul_pow, Real.sq_sqrt (by norm_num)],
    Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs0]

/-- On the bad event the adjoint energy costs one square root of the same
maximum, with its independent plus load. -/
theorem diagonalWeakAdjointEnergy_le_sqrt_two_mul_bad
    {rho : ℝ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hbad : (1 : ℝ≥0∞) < diagonalWeakMaximum rho q t E a) :
    diagonalWeakAdjointEnergy hq t a p r ≤
      Real.sqrt 2 * Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
        profileEnergyLoad (diagonalWeakLoadPlus E p r) p r := by
  let M : ℝ := (diagonalWeakMaximum rho q t E a).toReal
  let L : ℝ := diagonalWeakLoadPlus E p r
  let Lambda : ℝ := profileEnergyLoad L p r
  have hM : 1 < M :=
    (ENNReal.toReal_lt_toReal (by simp) hfinite).2 hbad
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  have hdot : 0 ≤ |vecDot p r| := abs_nonneg _
  have hsq := sq_diagonalWeakAdjointEnergy_le_maximum hq hE hEpd p r hfinite
  have hmajor : diagonalWeakAdjointEnergy hq t a p r ^ 2 ≤
      2 * M * Lambda ^ 2 := by
    rw [sq_profileEnergyLoad]
    calc
      diagonalWeakAdjointEnergy hq t a p r ^ 2 ≤
          (1 + M) * L ^ 2 + 2 * |vecDot p r| := hsq
      _ ≤ 2 * M * (L ^ 2 + |vecDot p r|) := by
        have hML : (1 + M) * L ^ 2 ≤ 2 * M * L ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hM]) hL2
        have hMd : 2 * |vecDot p r| ≤ 2 * M * |vecDot p r| :=
          mul_le_mul_of_nonneg_right (by linarith only [hM]) hdot
        linarith only [hML, hMd]
  have hrootM0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hLambda0 : 0 ≤ Lambda := profileEnergyLoad_nonneg L p r
  have hrhs0 : 0 ≤ Real.sqrt 2 * Real.sqrt M * Lambda :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hrootM0) hLambda0
  have hadj0 : 0 ≤ diagonalWeakAdjointEnergy hq t a p r := by
    rw [diagonalWeakAdjointEnergy_eq]
    exact diagonalWeakEnergy_nonneg hq t a.transpose p r
  rw [show diagonalWeakAdjointEnergy hq t a p r =
      Real.sqrt (diagonalWeakAdjointEnergy hq t a p r ^ 2) by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg hadj0]]
  refine (Real.sqrt_le_sqrt hmajor).trans_eq ?_
  rw [show 2 * M * Lambda ^ 2 =
      (Real.sqrt 2 * Real.sqrt M * Lambda) ^ 2 by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
          Real.sq_sqrt (by linarith only [hM])],
    Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs0]

/-- On the good event the adjoint energy is bounded by its deterministic plus
load. -/
theorem diagonalWeakAdjointEnergy_le_sqrt_two_mul_good
    {rho : ℝ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (p r : Vec d)
    (hgood : diagonalWeakMaximum rho q t E a ≤ (1 : ℝ≥0∞)) :
    diagonalWeakAdjointEnergy hq t a p r ≤
      Real.sqrt 2 * profileEnergyLoad (diagonalWeakLoadPlus E p r) p r := by
  have hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hgood
  let M : ℝ := (diagonalWeakMaximum rho q t E a).toReal
  let L : ℝ := diagonalWeakLoadPlus E p r
  let Lambda : ℝ := profileEnergyLoad L p r
  have hM : M ≤ 1 :=
    (ENNReal.toReal_le_toReal hfinite (by simp)).2 hgood
  have hsq := sq_diagonalWeakAdjointEnergy_le_maximum hq hE hEpd p r hfinite
  have hmajor : diagonalWeakAdjointEnergy hq t a p r ^ 2 ≤
      2 * Lambda ^ 2 := by
    rw [sq_profileEnergyLoad]
    calc
      diagonalWeakAdjointEnergy hq t a p r ^ 2 ≤
          (1 + M) * L ^ 2 + 2 * |vecDot p r| := hsq
      _ ≤ 2 * (L ^ 2 + |vecDot p r|) := by
        have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
        have hML : (1 + M) * L ^ 2 ≤ 2 * L ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hM]) hL2
        linarith only [hML]
  have hLambda0 : 0 ≤ Lambda := profileEnergyLoad_nonneg L p r
  have hrhs0 : 0 ≤ Real.sqrt 2 * Lambda :=
    mul_nonneg (Real.sqrt_nonneg _) hLambda0
  have hadj0 : 0 ≤ diagonalWeakAdjointEnergy hq t a p r := by
    rw [diagonalWeakAdjointEnergy_eq]
    exact diagonalWeakEnergy_nonneg hq t a.transpose p r
  rw [show diagonalWeakAdjointEnergy hq t a p r =
      Real.sqrt (diagonalWeakAdjointEnergy hq t a p r ^ 2) by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg hadj0]]
  refine (Real.sqrt_le_sqrt hmajor).trans_eq ?_
  rw [show 2 * Lambda ^ 2 = (Real.sqrt 2 * Lambda) ^ 2 by
        rw [mul_pow, Real.sq_sqrt (by norm_num)],
    Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs0]

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The good-event energy coefficient at a released split level. -/
@[expose]
def energyGoodConstantAtLevel (lev : ℝ) : ℝ := Real.sqrt (1 + lev)

/-- On the released bad event the primal energy costs one square root of the
maximum, with the fixed-level constant. -/
theorem diagonalWeakEnergy_le_sqrt_two_mul_bad_at_level
    {rho lev : ℝ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (p r : Vec d) (hlev : 1 ≤ lev)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hbad : ENNReal.ofReal lev < diagonalWeakMaximum rho q t E a) :
    diagonalWeakEnergy hq t a p r ≤
      Real.sqrt 2 * Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
        profileEnergyLoad (diagonalWeakLoadMinus E p r) p r := by
  set M : ℝ := (diagonalWeakMaximum rho q t E a).toReal with hMdef
  set L : ℝ := diagonalWeakLoadMinus E p r with hLdef
  set Lambda : ℝ := profileEnergyLoad L p r with hLambdadef
  have hlev0 : (0 : ℝ) ≤ lev := by linarith only [hlev]
  have hlevM : lev < M := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfinite).2 hbad
    rwa [ENNReal.toReal_ofReal hlev0] at h
  have hM : 1 < M := by linarith only [hlev, hlevM]
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  have hdot : 0 ≤ |vecDot p r| := abs_nonneg _
  have hsq := sq_diagonalWeakEnergy_le_maximum hq hE hEpd p r hfinite
  have hmajor : diagonalWeakEnergy hq t a p r ^ 2 ≤ 2 * M * Lambda ^ 2 := by
    rw [hLambdadef, sq_profileEnergyLoad]
    calc
      diagonalWeakEnergy hq t a p r ^ 2 ≤
          (1 + M) * L ^ 2 + 2 * |vecDot p r| := hsq
      _ ≤ 2 * M * (L ^ 2 + |vecDot p r|) := by
        have hML : (1 + M) * L ^ 2 ≤ 2 * M * L ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hM]) hL2
        have hMd : 2 * |vecDot p r| ≤ 2 * M * |vecDot p r| :=
          mul_le_mul_of_nonneg_right (by linarith only [hM]) hdot
        linarith only [hML, hMd]
  have hrootM0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hLambda0 : 0 ≤ Lambda := profileEnergyLoad_nonneg L p r
  have hrhs0 : 0 ≤ Real.sqrt 2 * Real.sqrt M * Lambda :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hrootM0) hLambda0
  rw [show diagonalWeakEnergy hq t a p r =
      Real.sqrt (diagonalWeakEnergy hq t a p r ^ 2) by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (diagonalWeakEnergy_nonneg hq t a p r)]]
  refine (Real.sqrt_le_sqrt hmajor).trans_eq ?_
  rw [show 2 * M * Lambda ^ 2 =
      (Real.sqrt 2 * Real.sqrt M * Lambda) ^ 2 by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
          Real.sq_sqrt (by linarith only [hM])],
    Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs0]

/-- On the released good event the primal energy is bounded by its
deterministic load, at the coefficient `√(1+lev)`. -/
theorem diagonalWeakEnergy_le_sqrt_two_mul_good_at_level
    {rho lev : ℝ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (p r : Vec d) (hlev : 1 ≤ lev)
    (hgood : diagonalWeakMaximum rho q t E a ≤ ENNReal.ofReal lev) :
    diagonalWeakEnergy hq t a p r ≤
      energyGoodConstantAtLevel lev *
        profileEnergyLoad (diagonalWeakLoadMinus E p r) p r := by
  have hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgood
  set M : ℝ := (diagonalWeakMaximum rho q t E a).toReal with hMdef
  set L : ℝ := diagonalWeakLoadMinus E p r with hLdef
  set Lambda : ℝ := profileEnergyLoad L p r with hLambdadef
  have hlev0 : (0 : ℝ) ≤ lev := by linarith only [hlev]
  have hM : M ≤ lev := by
    have h := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).2 hgood
    rwa [ENNReal.toReal_ofReal hlev0] at h
  have hsq := sq_diagonalWeakEnergy_le_maximum hq hE hEpd p r hfinite
  have hmajor : diagonalWeakEnergy hq t a p r ^ 2 ≤ (1 + lev) * Lambda ^ 2 := by
    rw [hLambdadef, sq_profileEnergyLoad]
    calc
      diagonalWeakEnergy hq t a p r ^ 2 ≤
          (1 + M) * L ^ 2 + 2 * |vecDot p r| := hsq
      _ ≤ (1 + lev) * (L ^ 2 + |vecDot p r|) := by
        have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
        have hdot : 0 ≤ |vecDot p r| := abs_nonneg _
        have hML : (1 + M) * L ^ 2 ≤ (1 + lev) * L ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hM]) hL2
        have hMd : 2 * |vecDot p r| ≤ (1 + lev) * |vecDot p r| :=
          mul_le_mul_of_nonneg_right (by linarith only [hlev]) hdot
        linarith only [hML, hMd]
  have hLambda0 : 0 ≤ Lambda := profileEnergyLoad_nonneg L p r
  have hrhs0 : 0 ≤ Real.sqrt (1 + lev) * Lambda := by positivity
  rw [energyGoodConstantAtLevel,
    show diagonalWeakEnergy hq t a p r =
      Real.sqrt (diagonalWeakEnergy hq t a p r ^ 2) by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (diagonalWeakEnergy_nonneg hq t a p r)]]
  refine (Real.sqrt_le_sqrt hmajor).trans_eq ?_
  rw [show (1 + lev) * Lambda ^ 2 = (Real.sqrt (1 + lev) * Lambda) ^ 2 by
        rw [mul_pow, Real.sq_sqrt (by linarith only [hlev0])],
    Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs0]

/-- The adjoint mirror on the released bad event. -/
theorem diagonalWeakAdjointEnergy_le_sqrt_two_mul_bad_at_level
    {rho lev : ℝ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (p r : Vec d) (hlev : 1 ≤ lev)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hbad : ENNReal.ofReal lev < diagonalWeakMaximum rho q t E a) :
    diagonalWeakAdjointEnergy hq t a p r ≤
      Real.sqrt 2 * Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
        profileEnergyLoad (diagonalWeakLoadPlus E p r) p r := by
  set M : ℝ := (diagonalWeakMaximum rho q t E a).toReal with hMdef
  set L : ℝ := diagonalWeakLoadPlus E p r with hLdef
  set Lambda : ℝ := profileEnergyLoad L p r with hLambdadef
  have hlev0 : (0 : ℝ) ≤ lev := by linarith only [hlev]
  have hlevM : lev < M := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfinite).2 hbad
    rwa [ENNReal.toReal_ofReal hlev0] at h
  have hM : 1 < M := by linarith only [hlev, hlevM]
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  have hdot : 0 ≤ |vecDot p r| := abs_nonneg _
  have hsq := sq_diagonalWeakAdjointEnergy_le_maximum hq hE hEpd p r hfinite
  have hmajor : diagonalWeakAdjointEnergy hq t a p r ^ 2 ≤
      2 * M * Lambda ^ 2 := by
    rw [hLambdadef, sq_profileEnergyLoad]
    calc
      diagonalWeakAdjointEnergy hq t a p r ^ 2 ≤
          (1 + M) * L ^ 2 + 2 * |vecDot p r| := hsq
      _ ≤ 2 * M * (L ^ 2 + |vecDot p r|) := by
        have hML : (1 + M) * L ^ 2 ≤ 2 * M * L ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hM]) hL2
        have hMd : 2 * |vecDot p r| ≤ 2 * M * |vecDot p r| :=
          mul_le_mul_of_nonneg_right (by linarith only [hM]) hdot
        linarith only [hML, hMd]
  have hrootM0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hLambda0 : 0 ≤ Lambda := profileEnergyLoad_nonneg L p r
  have hrhs0 : 0 ≤ Real.sqrt 2 * Real.sqrt M * Lambda :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hrootM0) hLambda0
  rw [show diagonalWeakAdjointEnergy hq t a p r =
      Real.sqrt (diagonalWeakAdjointEnergy hq t a p r ^ 2) by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (by
            simpa only [diagonalWeakAdjointEnergy_eq] using
              diagonalWeakEnergy_nonneg hq t a.transpose p r)]]
  refine (Real.sqrt_le_sqrt hmajor).trans_eq ?_
  rw [show 2 * M * Lambda ^ 2 =
      (Real.sqrt 2 * Real.sqrt M * Lambda) ^ 2 by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
          Real.sq_sqrt (by linarith only [hM])],
    Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs0]

/-- The adjoint mirror on the released good event. -/
theorem diagonalWeakAdjointEnergy_le_sqrt_two_mul_good_at_level
    {rho lev : ℝ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (p r : Vec d) (hlev : 1 ≤ lev)
    (hgood : diagonalWeakMaximum rho q t E a ≤ ENNReal.ofReal lev) :
    diagonalWeakAdjointEnergy hq t a p r ≤
      energyGoodConstantAtLevel lev *
        profileEnergyLoad (diagonalWeakLoadPlus E p r) p r := by
  have hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgood
  set M : ℝ := (diagonalWeakMaximum rho q t E a).toReal with hMdef
  set L : ℝ := diagonalWeakLoadPlus E p r with hLdef
  set Lambda : ℝ := profileEnergyLoad L p r with hLambdadef
  have hlev0 : (0 : ℝ) ≤ lev := by linarith only [hlev]
  have hM : M ≤ lev := by
    have h := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).2 hgood
    rwa [ENNReal.toReal_ofReal hlev0] at h
  have hsq := sq_diagonalWeakAdjointEnergy_le_maximum hq hE hEpd p r hfinite
  have hmajor : diagonalWeakAdjointEnergy hq t a p r ^ 2 ≤
      (1 + lev) * Lambda ^ 2 := by
    rw [hLambdadef, sq_profileEnergyLoad]
    calc
      diagonalWeakAdjointEnergy hq t a p r ^ 2 ≤
          (1 + M) * L ^ 2 + 2 * |vecDot p r| := hsq
      _ ≤ (1 + lev) * (L ^ 2 + |vecDot p r|) := by
        have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
        have hdot : 0 ≤ |vecDot p r| := abs_nonneg _
        have hML : (1 + M) * L ^ 2 ≤ (1 + lev) * L ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hM]) hL2
        have hMd : 2 * |vecDot p r| ≤ (1 + lev) * |vecDot p r| :=
          mul_le_mul_of_nonneg_right (by linarith only [hlev]) hdot
        linarith only [hML, hMd]
  have hLambda0 : 0 ≤ Lambda := profileEnergyLoad_nonneg L p r
  have hrhs0 : 0 ≤ Real.sqrt (1 + lev) * Lambda := by positivity
  rw [energyGoodConstantAtLevel,
    show diagonalWeakAdjointEnergy hq t a p r =
      Real.sqrt (diagonalWeakAdjointEnergy hq t a p r ^ 2) by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (by
            simpa only [diagonalWeakAdjointEnergy_eq] using
              diagonalWeakEnergy_nonneg hq t a.transpose p r)]]
  refine (Real.sqrt_le_sqrt hmajor).trans_eq ?_
  rw [show (1 + lev) * Lambda ^ 2 = (Real.sqrt (1 + lev) * Lambda) ^ 2 by
        rw [mul_pow, Real.sq_sqrt (by linarith only [hlev0])],
    Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs0]

end

end HCPolySupport.HighContrast.Response
