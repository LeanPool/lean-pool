/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineFiniteTrace
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineFiniteTwoChannel

/-!
# CombineFiniteVariance

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Quantitative finite-corridor two-plus-eight estimate

This module combines the descendant and trace estimates at the same-cutoff
relative-normalized law.  The observation cube at physical scale `n` is
represented by the relative cube at scale `n - L - c`.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.Book.Ch02
open _root_.HCPolySupport.Book.Ch05.Section54.VarianceBoundGoodScale
open _root_.HCPolySupport.IndependentSums

noncomputable section

noncomputable def finiteCorridorSecondConst : ℝ :=
  2 *
    ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * 16) ^ (2 : ℕ) +
      (gammaMomentConst (1 / 2) *
        (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * 256) ^ (2 : ℕ))

noncomputable def finiteCorridorFourthConst : ℝ :=
  8 *
    ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * 16) ^ (4 : ℕ) +
      (gammaMomentConst (1 / 2) *
        (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * 256) ^ (4 : ℕ))

noncomputable def finiteCorridorBudgetConst : ℝ :=
  finiteCorridorSecondConst + 2 * finiteCorridorFourthConst

/-! The three constant-nonnegativity facts are proved once here.  Each `positivity`
call below sees only the smallest defining expression; the consumers reuse the
resulting lemma instead of re-running `positivity` on an unfolded copy. -/

private theorem finiteCorridorSecondConst_nonneg : 0 ≤ finiteCorridorSecondConst := by
  unfold finiteCorridorSecondConst
  positivity

private theorem finiteCorridorFourthConst_nonneg : 0 ≤ finiteCorridorFourthConst := by
  unfold finiteCorridorFourthConst
  positivity

private theorem finiteCorridorBudgetConst_nonneg : 0 ≤ finiteCorridorBudgetConst := by
  unfold finiteCorridorBudgetConst
  linarith only [finiteCorridorSecondConst_nonneg, finiteCorridorFourthConst_nonneg]

private theorem finiteCorridor_momentBudgets_le
    (E gamma : ℝ) (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hEgamma : E ^ 2 * gamma ≤ 1 / 2) :
    let x : ℝ := E⁻¹ ^ 3 * gamma⁻¹
    let rare : ℝ := Real.exp (-x)
    let rareSq : ℝ := Real.exp (-(2 * x))
    let delta : ℝ := E ^ 2 * gamma + rareSq
    let A : ℝ := 16 * E * Real.sqrt gamma
    let D : ℝ := 256 * rare
    let secondBudget : ℝ :=
      2 *
        ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ))
    let fourthBudget : ℝ :=
      8 *
        ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))
    let budget : ℝ := secondBudget + fourthBudget
    0 ≤ delta ∧ delta ≤ 2 ∧
      secondBudget ≤ finiteCorridorSecondConst * delta ∧
      fourthBudget ≤ finiteCorridorFourthConst * delta ^ (2 : ℕ) ∧
      budget ≤ finiteCorridorBudgetConst * delta := by
  let x : ℝ := E⁻¹ ^ 3 * gamma⁻¹
  let rare : ℝ := Real.exp (-x)
  let rareSq : ℝ := Real.exp (-(2 * x))
  let delta : ℝ := E ^ 2 * gamma + rareSq
  let A : ℝ := 16 * E * Real.sqrt gamma
  let D : ℝ := 256 * rare
  let secondBudget : ℝ :=
    2 *
      ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
        (gammaMomentConst (1 / 2) *
          (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ))
  let fourthBudget : ℝ :=
    8 *
      ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
        (gammaMomentConst (1 / 2) *
          (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))
  let budget : ℝ := secondBudget + fourthBudget
  have hsqrtSq : Real.sqrt gamma ^ (2 : ℕ) = gamma :=
    Real.sq_sqrt hgamma.le
  have hrareSq : rare ^ (2 : ℕ) = rareSq := by
    dsimp only [rare, rareSq]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hA2 : A ^ (2 : ℕ) = 16 ^ (2 : ℕ) * (E ^ 2 * gamma) := by
    dsimp only [A]
    rw [mul_pow, mul_pow, hsqrtSq]
    ring
  have hD2 : D ^ (2 : ℕ) = 256 ^ (2 : ℕ) * rareSq := by
    dsimp only [D]
    rw [mul_pow, hrareSq]
  have hA4 : A ^ (4 : ℕ) = 16 ^ (4 : ℕ) * (E ^ 2 * gamma) ^ (2 : ℕ) := by
    rw [show A ^ (4 : ℕ) = (A ^ (2 : ℕ)) ^ (2 : ℕ) by ring, hA2]
    ring
  have hD4 : D ^ (4 : ℕ) = 256 ^ (4 : ℕ) * rareSq ^ (2 : ℕ) := by
    rw [show D ^ (4 : ℕ) = (D ^ (2 : ℕ)) ^ (2 : ℕ) by ring, hD2]
    ring
  have hrareSqNonneg : 0 ≤ rareSq := (Real.exp_pos _).le
  have hdeltaNonneg : 0 ≤ delta := by
    exact add_nonneg (mul_nonneg (sq_nonneg E) hgamma.le) hrareSqNonneg
  have hxNonneg : 0 ≤ x := by
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans hE)) 3)
      (inv_nonneg.mpr hgamma.le)
  have hrareSqLe : rareSq ≤ 1 := by
    calc
      rareSq = Real.exp (-(2 * x)) := rfl
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg (by norm_num) hxNonneg))
      _ = 1 := Real.exp_zero
  have hdeltaLe : delta ≤ 2 := by
    dsimp only [delta]
    linarith only [hEgamma, hrareSqLe]
  have hsecondEq : secondBudget =
      2 *
        ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * 16) ^ (2 : ℕ) *
            (E ^ 2 * gamma) +
          (gammaMomentConst (1 / 2) *
            (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * 256) ^ (2 : ℕ) * rareSq) := by
    dsimp only [secondBudget]
    rw [show (gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) =
        (gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) * A ^ (2 : ℕ) by ring,
      show (gammaMomentConst (1 / 2) * (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ) =
        (gammaMomentConst (1 / 2) * (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹)) ^ (2 : ℕ) * D ^ (2 : ℕ) by ring,
      hA2, hD2]
    ring
  have hfourthEq : fourthBudget =
      8 *
        ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * 16) ^ (4 : ℕ) *
            (E ^ 2 * gamma) ^ (2 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * 256) ^ (4 : ℕ) *
              rareSq ^ (2 : ℕ)) := by
    dsimp only [fourthBudget]
    rw [show (gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) =
        (gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹)) ^ (4 : ℕ) * A ^ (4 : ℕ) by ring,
      show (gammaMomentConst (1 / 2) * (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ) =
        (gammaMomentConst (1 / 2) * (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹)) ^ (4 : ℕ) * D ^ (4 : ℕ) by ring,
      hA4, hD4]
    ring
  have hsecond : secondBudget ≤ finiteCorridorSecondConst * delta := by
    rw [hsecondEq]
    dsimp only [finiteCorridorSecondConst, delta]
    have hu : (0 : ℝ) ≤ E ^ 2 * gamma := mul_nonneg (sq_nonneg E) hgamma.le
    have hcross1 : (0 : ℝ) ≤
        (gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * 16) ^ (2 : ℕ) * rareSq :=
      mul_nonneg (sq_nonneg _) hrareSqNonneg
    have hcross2 : (0 : ℝ) ≤
        (gammaMomentConst (1 / 2) * (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * 256) ^ (2 : ℕ) *
          (E ^ 2 * gamma) :=
      mul_nonneg (sq_nonneg _) hu
    linarith only [hcross1, hcross2]
  have hfourth : fourthBudget ≤ finiteCorridorFourthConst * delta ^ (2 : ℕ) := by
    rw [hfourthEq]
    let cY : ℝ :=
      (gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * 16) ^ (4 : ℕ)
    let cD : ℝ :=
      (gammaMomentConst (1 / 2) *
        (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * 256) ^ (4 : ℕ)
    have hcY : 0 ≤ cY := by dsimp only [cY]; positivity
    have hcD : 0 ≤ cD := by dsimp only [cD]; positivity
    have hu : 0 ≤ E ^ 2 * gamma := mul_nonneg (sq_nonneg E) hgamma.le
    have huLe : E ^ 2 * gamma ≤ delta := by
      exact le_add_of_nonneg_right hrareSqNonneg
    have hrLe : rareSq ≤ delta := by
      exact le_add_of_nonneg_left hu
    have huSq : (E ^ 2 * gamma) ^ (2 : ℕ) ≤ delta ^ (2 : ℕ) :=
      (sq_le_sq₀ hu hdeltaNonneg).2 huLe
    have hrSq : rareSq ^ (2 : ℕ) ≤ delta ^ (2 : ℕ) :=
      (sq_le_sq₀ hrareSqNonneg hdeltaNonneg).2 hrLe
    change 8 * (cY * (E ^ 2 * gamma) ^ (2 : ℕ) +
        cD * rareSq ^ (2 : ℕ)) ≤
      8 * (cY + cD) * delta ^ (2 : ℕ)
    have hadd : cY * (E ^ 2 * gamma) ^ (2 : ℕ) +
        cD * rareSq ^ (2 : ℕ) ≤ (cY + cD) * delta ^ (2 : ℕ) := by
      calc
        cY * (E ^ 2 * gamma) ^ (2 : ℕ) + cD * rareSq ^ (2 : ℕ) ≤
            cY * delta ^ (2 : ℕ) + cD * delta ^ (2 : ℕ) :=
          add_le_add (mul_le_mul_of_nonneg_left huSq hcY)
            (mul_le_mul_of_nonneg_left hrSq hcD)
        _ = (cY + cD) * delta ^ (2 : ℕ) := by ring
    calc
      8 * (cY * (E ^ 2 * gamma) ^ (2 : ℕ) + cD * rareSq ^ (2 : ℕ)) ≤
          8 * ((cY + cD) * delta ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hadd (by norm_num)
      _ = 8 * (cY + cD) * delta ^ (2 : ℕ) := by ring
  have hbudget : budget ≤ finiteCorridorBudgetConst * delta := by
    change secondBudget + fourthBudget ≤
      (finiteCorridorSecondConst + 2 * finiteCorridorFourthConst) * delta
    have hFourthConstNonneg : 0 ≤ finiteCorridorFourthConst :=
      finiteCorridorFourthConst_nonneg
    have hdeltaSq : delta ^ (2 : ℕ) ≤ 2 * delta :=
      calc delta ^ (2 : ℕ) = delta * delta := pow_two delta
        _ ≤ 2 * delta := mul_le_mul_of_nonneg_right hdeltaLe hdeltaNonneg
    calc
      secondBudget + fourthBudget ≤
          finiteCorridorSecondConst * delta +
            finiteCorridorFourthConst * delta ^ (2 : ℕ) := add_le_add hsecond hfourth
      _ ≤ finiteCorridorSecondConst * delta +
            finiteCorridorFourthConst * (2 * delta) := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hdeltaSq hFourthConstNonneg)
      _ = (finiteCorridorSecondConst + 2 * finiteCorridorFourthConst) * delta := by ring
  exact ⟨hdeltaNonneg, hdeltaLe, hsecond, hfourth, hbudget⟩

noncomputable def finiteCorridorRosenthalConst (d : ℕ) : ℝ :=
  (Book.Ch04.rosenthalDescendantsAtScaleLpConst d
      (-(Cutoff.cutoffRelativeNormalizationShift d : ℤ)) 2 +
    Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d
      (-(Cutoff.cutoffRelativeNormalizationShift d : ℤ)) 2) ^ (2 : ℕ)

noncomputable def finiteCorridorProbeConst (d : ℕ) : ℝ :=
  192 * finiteCorridorRosenthalConst d * finiteCorridorBudgetConst +
    128 * finiteCorridorSecondConst ^ (2 : ℕ)

private theorem finiteCorridorRosenthalConst_nonneg (d : ℕ) :
    0 ≤ finiteCorridorRosenthalConst d := by
  unfold finiteCorridorRosenthalConst
  positivity

private theorem finiteCorridorProbeConst_nonneg (d : ℕ) :
    0 ≤ finiteCorridorProbeConst d := by
  unfold finiteCorridorProbeConst
  have h1 : (0 : ℝ) ≤ 192 * finiteCorridorRosenthalConst d * finiteCorridorBudgetConst :=
    mul_nonneg (mul_nonneg (by norm_num) (finiteCorridorRosenthalConst_nonneg d))
      finiteCorridorBudgetConst_nonneg
  have h2 : (0 : ℝ) ≤ 128 * finiteCorridorSecondConst ^ (2 : ℕ) :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  linarith only [h1, h2]

private theorem finiteCorridor_probeRhs_le
    {d : ℕ} [NeZero d]
    (N delta geom budget secondBudget : ℝ)
    (hNpos : 0 < N) (hNinv : N⁻¹ = geom)
    (hdelta : 0 ≤ delta) (hbudget : 0 ≤ budget)
    (hsecond : 0 ≤ secondBudget)
    (hbudgetLe : budget ≤ finiteCorridorBudgetConst * delta)
    (hsecondLe : secondBudget ≤ finiteCorridorSecondConst * delta)
    (q : FullBlockVec d) (hq : dotProduct q q ≤ 4) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let probeBudget : ℝ := 6 * (dotProduct q q) ^ (2 : ℕ) * budget
    let meanBudget : ℝ :=
      4 * (dotProduct q q) ^ (2 : ℕ) * secondBudget ^ (2 : ℕ)
    let K : ℝ := Real.sqrt probeBudget
    let rootBound : ℝ :=
      N⁻¹ *
        (Book.Ch04.rosenthalDescendantsAtScaleLpConst d (-c) 2 *
              N ^ (1 / (2 : ℝ)) * K +
          Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d (-c) 2 *
              Real.sqrt N * K)
    2 * rootBound ^ (2 : ℕ) + 2 * meanBudget ≤
      finiteCorridorProbeConst d * delta * (delta + geom) := by
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let probeBudget : ℝ := 6 * (dotProduct q q) ^ (2 : ℕ) * budget
  let meanBudget : ℝ :=
    4 * (dotProduct q q) ^ (2 : ℕ) * secondBudget ^ (2 : ℕ)
  let K : ℝ := Real.sqrt probeBudget
  let rootBound : ℝ :=
    N⁻¹ *
      (Book.Ch04.rosenthalDescendantsAtScaleLpConst d (-c) 2 *
            N ^ (1 / (2 : ℝ)) * K +
        Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d (-c) 2 *
            Real.sqrt N * K)
  let CR : ℝ := finiteCorridorRosenthalConst d
  let CB : ℝ := finiteCorridorBudgetConst
  let CS : ℝ := finiteCorridorSecondConst
  have hqNonneg : 0 ≤ dotProduct q q := dotProduct_self_nonneg q
  have hqSq : (dotProduct q q) ^ (2 : ℕ) ≤ 16 := by
    have h := pow_le_pow_left₀ hqNonneg hq 2
    norm_num at h ⊢
    exact h
  have hprobeNonneg : 0 ≤ probeBudget := by
    dsimp only [probeBudget]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hbudget
  have hmeanNonneg : 0 ≤ meanBudget := by
    dsimp only [meanBudget]
    positivity
  have hKsq : K ^ (2 : ℕ) = probeBudget := by
    dsimp only [K]
    exact Real.sq_sqrt hprobeNonneg
  have hNsqrtSq : Real.sqrt N ^ (2 : ℕ) = N := Real.sq_sqrt hNpos.le
  have hrootEq : rootBound ^ (2 : ℕ) = CR * N⁻¹ * probeBudget := by
    dsimp only [rootBound, CR, finiteCorridorRosenthalConst, c]
    rw [← Real.sqrt_eq_rpow]
    calc
      (N⁻¹ *
          (Book.Ch04.rosenthalDescendantsAtScaleLpConst d
                (-(Cutoff.cutoffRelativeNormalizationShift d : ℤ)) 2 *
              Real.sqrt N * K +
            Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d
                (-(Cutoff.cutoffRelativeNormalizationShift d : ℤ)) 2 *
              Real.sqrt N * K)) ^ (2 : ℕ) =
          N⁻¹ ^ (2 : ℕ) *
            (Book.Ch04.rosenthalDescendantsAtScaleLpConst d
                (-(Cutoff.cutoffRelativeNormalizationShift d : ℤ)) 2 +
              Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d
                (-(Cutoff.cutoffRelativeNormalizationShift d : ℤ)) 2) ^ (2 : ℕ) *
            (Real.sqrt N) ^ (2 : ℕ) * K ^ (2 : ℕ) := by ring
      _ = N⁻¹ ^ (2 : ℕ) *
            (Book.Ch04.rosenthalDescendantsAtScaleLpConst d
                (-(Cutoff.cutoffRelativeNormalizationShift d : ℤ)) 2 +
              Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d
                (-(Cutoff.cutoffRelativeNormalizationShift d : ℤ)) 2) ^ (2 : ℕ) *
            N * probeBudget := by rw [hNsqrtSq, hKsq]
      _ = (Book.Ch04.rosenthalDescendantsAtScaleLpConst d
                (-(Cutoff.cutoffRelativeNormalizationShift d : ℤ)) 2 +
              Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d
                (-(Cutoff.cutoffRelativeNormalizationShift d : ℤ)) 2) ^ (2 : ℕ) *
            N⁻¹ * probeBudget := by
        field_simp [hNpos.ne']
  have hCBNonneg : 0 ≤ CB := by
    dsimp only [CB]
    exact finiteCorridorBudgetConst_nonneg
  have hCSNonneg : 0 ≤ CS := by
    dsimp only [CS]
    exact finiteCorridorSecondConst_nonneg
  have hCRNonneg : 0 ≤ CR := by
    dsimp only [CR]
    exact finiteCorridorRosenthalConst_nonneg d
  have hgeomNonneg : 0 ≤ geom := by
    rw [← hNinv]
    exact inv_nonneg.mpr hNpos.le
  have hprobeLe : probeBudget ≤ 96 * CB * delta := by
    dsimp only [probeBudget, CB]
    calc
      6 * (dotProduct q q) ^ (2 : ℕ) * budget ≤ 6 * 16 * budget := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqSq (by norm_num)) hbudget
      _ = 96 * budget := by ring
      _ ≤ 96 * (finiteCorridorBudgetConst * delta) :=
        mul_le_mul_of_nonneg_left hbudgetLe (by norm_num : (0 : ℝ) ≤ 96)
      _ = 96 * finiteCorridorBudgetConst * delta := by ring
  have hrootLe : rootBound ^ (2 : ℕ) ≤
      96 * CR * CB * delta * geom := by
    rw [hrootEq, hNinv]
    calc
      CR * geom * probeBudget ≤ CR * geom * (96 * CB * delta) :=
        mul_le_mul_of_nonneg_left hprobeLe (mul_nonneg hCRNonneg hgeomNonneg)
      _ = 96 * CR * CB * delta * geom := by ring
  have hsecondSq : secondBudget ^ (2 : ℕ) ≤
      (CS * delta) ^ (2 : ℕ) := by
    exact (sq_le_sq₀ hsecond (mul_nonneg hCSNonneg hdelta)).2 hsecondLe
  have hmeanLe : meanBudget ≤ 64 * CS ^ (2 : ℕ) * delta ^ (2 : ℕ) := by
    dsimp only [meanBudget]
    calc
      4 * (dotProduct q q) ^ (2 : ℕ) * secondBudget ^ (2 : ℕ) ≤
          4 * 16 * secondBudget ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqSq (by norm_num)) (sq_nonneg _)
      _ = 64 * secondBudget ^ (2 : ℕ) := by ring
      _ ≤ 64 * (CS * delta) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hsecondSq (by norm_num : (0 : ℝ) ≤ 64)
      _ = 64 * CS ^ (2 : ℕ) * delta ^ (2 : ℕ) := by ring
  change 2 * rootBound ^ (2 : ℕ) + 2 * meanBudget ≤
    finiteCorridorProbeConst d * delta * (delta + geom)
  calc
    2 * rootBound ^ (2 : ℕ) + 2 * meanBudget ≤
        2 * (96 * CR * CB * delta * geom) +
          2 * (64 * CS ^ (2 : ℕ) * delta ^ (2 : ℕ)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hrootLe (by norm_num))
        (mul_le_mul_of_nonneg_left hmeanLe (by norm_num))
    _ = (192 * CR * CB + 128 * CS ^ (2 : ℕ)) * delta * (delta + geom) -
          (192 * CR * CB * delta ^ (2 : ℕ) +
            128 * CS ^ (2 : ℕ) * delta * geom) := by ring
    _ ≤ (192 * CR * CB + 128 * CS ^ (2 : ℕ)) * delta * (delta + geom) := by
      have hsub1 : (0 : ℝ) ≤ 192 * CR * CB * delta ^ (2 : ℕ) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCRNonneg) hCBNonneg)
          (sq_nonneg delta)
      have hsub2 : (0 : ℝ) ≤ 128 * CS ^ (2 : ℕ) * delta * geom :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg CS)) hdelta)
          hgeomNonneg
      have hsubNonneg : 0 ≤ 192 * CR * CB * delta ^ (2 : ℕ) +
          128 * CS ^ (2 : ℕ) * delta * geom := by linarith only [hsub1, hsub2]
      linarith only [hsubNonneg]
    _ = finiteCorridorProbeConst d * delta * (delta + geom) := by
      simp only [finiteCorridorProbeConst, CR, CB, CS]

noncomputable def finiteCorridorVarianceConst (d : ℕ) : ℝ :=
  max 1
    (18 * (Fintype.card (BlockCoord d) : ℝ) ^ (6 : ℕ) *
        finiteCorridorProbeConst d +
      8 * (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
        finiteCorridorFourthConst)

private theorem combineFiniteVariance_comparisonBounds1 :
    ∀ (d : ℕ) (M : ABKModel d) (E : { E : ℝ // (1 : ℝ) ≤ E }) (L n : ℤ),
      let this : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩;
      let x : ℝ := (↑E : ℝ)⁻¹ ^ (3 : ℕ) * M.gamma⁻¹;
      let rare : ℝ := Real.exp (-x);
      let delta : ℝ := (↑E : ℝ) ^ (2 : ℕ) * M.gamma + Real.exp (-((2 : ℝ) * x));
      let A : ℝ := (16 : ℝ) * (↑E : ℝ) * √M.gamma;
      let D : ℝ := (256 : ℝ) * rare;
      let c : ℤ := (↑(Cutoff.cutoffRelativeNormalizationShift d) : ℤ);
      let Q : TriadicCube d := originCube d (n - (L + c));
      let j : ℕ := (n - L).toNat;
      let N : ℝ := (↑(descendantsAtScale Q (-c)).card : ℝ);
      let card : ℝ := (↑(Fintype.card (BlockCoord d)) : ℝ);
      let geom : ℝ := Real.rpow (3 : ℝ) (-(↑d : ℝ) * (↑j : ℝ));
      let budget : ℝ :=
        (2 : ℝ) *
            ((gammaMomentConst (2 : ℝ) * (2 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (2 : ℕ) +
              (gammaMomentConst (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (2 : ℕ)) +
          (8 : ℝ) *
            ((gammaMomentConst (2 : ℝ) * (4 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (4 : ℕ) +
              (gammaMomentConst (1 / 2 : ℝ) * (4 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (4 : ℕ));
      let secondBudget : ℝ :=
        (2 : ℝ) *
          ((gammaMomentConst (2 : ℝ) * (2 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (2 : ℕ) +
            (gammaMomentConst (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (2 : ℕ));
      let fourthBudget : ℝ :=
        (8 : ℝ) *
          ((gammaMomentConst (2 : ℝ) * (4 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (4 : ℕ) +
            (gammaMomentConst (1 / 2 : ℝ) * (4 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (4 : ℕ));
      let probeRhs : FullBlockVec d → ℝ := fun (q : FullBlockVec d) =>
        let probeBudget : ℝ := (6 : ℝ) * (q ⬝ᵥ q) ^ (2 : ℕ) * budget;
        let meanBudget : ℝ := (4 : ℝ) * (q ⬝ᵥ q) ^ (2 : ℕ) * secondBudget ^ (2 : ℕ);
        let K : ℝ := √probeBudget;
        let rootBound : ℝ :=
          N⁻¹ *
            (Ch04.rosenthalDescendantsAtScaleLpConst d (-c) (2 : ℕ) * N ^ (1 / 2 : ℝ) * K +
              Ch04.rosenthalDescendantsAtScaleSqrtConst d (-c) (2 : ℕ) * √N * K);
        (2 : ℝ) * rootBound ^ (2 : ℕ) + (2 : ℝ) * meanBudget;
      let descendantRhs : ℝ :=
        (2 : ℝ) * card ^ (2 : ℕ) *
          (card *
            ∑ alpha : BlockCoord d,
              card *
                ∑ beta : BlockCoord d,
                  (3 : ℝ) *
                    (probeRhs (fullBlockCoordinateProbe alpha) + probeRhs (fullBlockPlusProbe alpha beta) +
                      probeRhs (fullBlockMinusProbe alpha beta)));
      let traceRhs : ℝ := (8 : ℝ) * (card ^ (2 : ℕ) * fourthBudget);
      ∀ (_ : (0 : ℝ) < N) (_ : N⁻¹ = geom) (_ : (0 : ℝ) ≤ delta)
        (_ : secondBudget ≤ finiteCorridorSecondConst * delta)
        (_ : fourthBudget ≤ finiteCorridorFourthConst * delta ^ (2 : ℕ))
        (_ : budget ≤ finiteCorridorBudgetConst * delta) (_ : ∀ (y : ℝ), (0 : ℝ) ≤ y ^ (4 : ℕ))
        (_ : (0 : ℝ) ≤ (gammaMomentConst (2 : ℝ) * (2 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (2 : ℕ))
        (_ : (0 : ℝ) ≤ (gammaMomentConst (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (2 : ℕ)),
        descendantRhs ≤ (18 : ℝ) * card ^ (6 : ℕ) * finiteCorridorProbeConst d * delta * (delta + geom) ∧
          traceRhs ≤ (8 : ℝ) * card ^ (2 : ℕ) * finiteCorridorFourthConst * delta * (delta + geom) := by
  intro d _ _ _ _ _ _ _ delta A D c _ _ N card geom budget secondBudget fourthBudget probeRhs descendantRhs traceRhs hNpos hNinv hdeltaNonneg hsecondLe hfourthLe hbudgetLe hpow4 hbudgetSecond1 hbudgetSecond2
  have hbudgetNonneg : 0 ≤ budget := by
    dsimp only [budget]
    have h3 := hpow4 (gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A)
    have h4 := hpow4 (gammaMomentConst (1 / 2) * (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D)
    linarith only [hbudgetSecond1, hbudgetSecond2, h3, h4]
  have hsecondNonneg : 0 ≤ secondBudget := by
    dsimp only [secondBudget]
    linarith only [hbudgetSecond1, hbudgetSecond2]
  have hprobe : ∀ q : FullBlockVec d, dotProduct q q ≤ 4 →
      probeRhs q ≤ finiteCorridorProbeConst d * delta * (delta + geom) := by
    intro q hq
    simpa only [c, probeRhs] using
      finiteCorridor_probeRhs_le N delta geom budget secondBudget hNpos hNinv
        hdeltaNonneg hbudgetNonneg hsecondNonneg hbudgetLe hsecondLe q hq
  have hdescRhs : descendantRhs ≤
      18 * card ^ (6 : ℕ) * finiteCorridorProbeConst d * delta *
        (delta + geom) := by
    dsimp only [descendantRhs]
    have hcardNonneg : 0 ≤ card := by dsimp only [card]; positivity
    have hprobeFactorNonneg : 0 ≤
        finiteCorridorProbeConst d * delta * (delta + geom) := by
      have hCp : 0 ≤ finiteCorridorProbeConst d := finiteCorridorProbeConst_nonneg d
      exact mul_nonneg (mul_nonneg hCp hdeltaNonneg)
        (add_nonneg hdeltaNonneg (Real.rpow_nonneg (by norm_num) _))
    have hsum :
        (card * ∑ alpha : BlockCoord d, card * ∑ beta : BlockCoord d, 3 *
          (probeRhs (fullBlockCoordinateProbe alpha) +
            probeRhs (fullBlockPlusProbe alpha beta) +
            probeRhs (fullBlockMinusProbe alpha beta))) ≤
          (card * ∑ _alpha : BlockCoord d, card * ∑ _beta : BlockCoord d,
            9 * (finiteCorridorProbeConst d * delta * (delta + geom))) := by
      refine mul_le_mul_of_nonneg_left ?_ hcardNonneg
      refine Finset.sum_le_sum fun alpha _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ hcardNonneg
      refine Finset.sum_le_sum fun beta _ => ?_
      calc
        3 * (probeRhs (fullBlockCoordinateProbe alpha) +
            probeRhs (fullBlockPlusProbe alpha beta) +
            probeRhs (fullBlockMinusProbe alpha beta)) ≤
            3 * (finiteCorridorProbeConst d * delta * (delta + geom) +
              finiteCorridorProbeConst d * delta * (delta + geom) +
              finiteCorridorProbeConst d * delta * (delta + geom)) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add
              (add_le_add
                (hprobe _ (by simp [dotProduct_coordinateProbe_self]))
                (hprobe _ (dotProduct_plusProbe_self_le_four alpha beta)))
              (hprobe _ (dotProduct_minusProbe_self_le_four alpha beta)))
            (by norm_num)
        _ = 9 * (finiteCorridorProbeConst d * delta * (delta + geom)) := by ring
    calc
      2 * card ^ (2 : ℕ) *
          (card * ∑ alpha : BlockCoord d, card * ∑ beta : BlockCoord d, 3 *
            (probeRhs (fullBlockCoordinateProbe alpha) +
              probeRhs (fullBlockPlusProbe alpha beta) +
              probeRhs (fullBlockMinusProbe alpha beta))) ≤
        2 * card ^ (2 : ℕ) *
          (card * ∑ _alpha : BlockCoord d, card * ∑ _beta : BlockCoord d,
            9 * (finiteCorridorProbeConst d * delta * (delta + geom))) := by
        exact mul_le_mul_of_nonneg_left hsum
          (mul_nonneg (by norm_num) (sq_nonneg card))
      _ = 18 * card ^ (6 : ℕ) * finiteCorridorProbeConst d * delta *
            (delta + geom) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have htraceRhs : traceRhs ≤
      8 * card ^ (2 : ℕ) * finiteCorridorFourthConst * delta *
        (delta + geom) := by
    dsimp only [traceRhs]
    have hgeomNonneg : 0 ≤ geom := by
      dsimp only [geom]
      exact Real.rpow_nonneg (by norm_num) _
    have hCFNonneg : 0 ≤ finiteCorridorFourthConst :=
      finiteCorridorFourthConst_nonneg
    have hcardSqNonneg : 0 ≤ card ^ (2 : ℕ) := sq_nonneg card
    have hdeltaLe : delta ≤ delta + geom := le_add_of_nonneg_right hgeomNonneg
    have hdeltaSqLe : delta ^ (2 : ℕ) ≤ delta * (delta + geom) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hdeltaLe hdeltaNonneg
    calc
      8 * (card ^ (2 : ℕ) * fourthBudget) ≤
          8 * (card ^ (2 : ℕ) *
            (finiteCorridorFourthConst * delta ^ (2 : ℕ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfourthLe hcardSqNonneg) (by norm_num)
      _ = (8 * card ^ (2 : ℕ) * finiteCorridorFourthConst) *
            delta ^ (2 : ℕ) := by ring
      _ ≤ (8 * card ^ (2 : ℕ) * finiteCorridorFourthConst) *
            (delta * (delta + geom)) :=
        mul_le_mul_of_nonneg_left hdeltaSqLe
          (mul_nonneg (mul_nonneg (by norm_num) hcardSqNonneg) hCFNonneg)
      _ = 8 * card ^ (2 : ℕ) * finiteCorridorFourthConst * delta *
            (delta + geom) := by ring
  exact ⟨hdescRhs, htraceRhs⟩

private theorem combineFiniteVariance_comparisonBounds2 :
    ∀ (d : ℕ),
      let shift : ℝ := (↑(Cutoff.cutoffRelativeNormalizationShift d) : ℝ);
      let Chom : ℝ := max (64 : ℝ) ((2 : ℝ) * (shift + (1 : ℝ)));
      ∀ (_ : (64 : ℝ) ≤ Chom) (_ : (1 : ℝ) ≤ Chom) (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E })
        (epsilon : ℝ) (_ : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ))
        (_ : M.gamma ≤ Chom⁻¹ * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * epsilon) (L : ℤ)
        (_ : (↑L : ℝ) ≤ (↑m : ℝ) - Chom * |Real.log epsilon|),
        L ≤ m - (1 : ℤ) ∧ (1 / 16 : ℝ) ∈ Set.Icc ((8 : ℝ) * M.gamma) (1 : ℝ) ∧ (↑E : ℝ) ^ (2 : ℕ) * M.gamma ≤ (1 / 2 : ℝ) := by
  intro _ _ Chom hChom64 hChomOne M m E epsilon hepsilon hgamma L hseparation
  have hepsilonPos : 0 < epsilon := hepsilon.1
  have hepsilonHalf : epsilon ≤ 1 / 2 := hepsilon.2
  have hlogNonpos : Real.log epsilon ≤ 0 :=
    Real.log_nonpos hepsilonPos.le
      (hepsilonHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have habsLog : |Real.log epsilon| = -Real.log epsilon :=
    abs_of_nonpos hlogNonpos
  have hlogHalf : Real.log epsilon ≤ Real.log (1 / 2 : ℝ) :=
    Real.log_le_log hepsilonPos hepsilonHalf
  have hlogTwo : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have habsLogHalf : (1 / 2 : ℝ) ≤ |Real.log epsilon| := by
    rw [habsLog]
    rw [hlogTwo] at hlogHalf
    linarith only [hlogHalf, Real.log_two_gt_d9]
  have hLplusOneReal : (L : ℝ) + 1 ≤ (m : ℝ) := by
    have hChomLog : 1 ≤ Chom * |Real.log epsilon| := by
      have hmul := mul_le_mul hChom64 habsLogHalf (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by positivity : 0 ≤ Chom)
      linarith only [hmul]
    linarith only [hChomLog, hseparation]
  have hLmOne : L ≤ m - 1 := by
    have hLplusOne : L + 1 ≤ m := by exact_mod_cast hLplusOneReal
    omega
  have hEpos : (0 : ℝ) < (E : ℝ) := zero_lt_one.trans_le E.property
  have hChomPos : 0 < Chom := zero_lt_one.trans_le hChomOne
  have hChomInv : Chom⁻¹ ≤ (64 : ℝ)⁻¹ :=
    (inv_le_inv₀ hChomPos (by norm_num : (0 : ℝ) < 64)).2 hChom64
  have hEinvSq : ((E : ℝ)⁻¹) ^ 2 ≤ 1 := by
    have hEinv : (E : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hEpos).2 E.property
    have hEinvNonneg : 0 ≤ (E : ℝ)⁻¹ := inv_nonneg.mpr hEpos.le
    calc ((E : ℝ)⁻¹) ^ 2 = (E : ℝ)⁻¹ * (E : ℝ)⁻¹ := pow_two _
      _ ≤ 1 * 1 := mul_le_mul hEinv hEinv hEinvNonneg zero_le_one
      _ = 1 := one_mul 1
  have hgamma128 : M.gamma ≤ 1 / 128 := by
    calc
      M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon := hgamma
      _ ≤ (64 : ℝ)⁻¹ * 1 * (1 / 2) := by gcongr
      _ = 1 / 128 := by norm_num
  have hwindow : (1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 := by
    constructor
    · linarith only [hgamma128]
    · norm_num
  have hEgamma : (E : ℝ) ^ 2 * M.gamma ≤ 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hgamma (sq_nonneg (E : ℝ))
    calc
      (E : ℝ) ^ 2 * M.gamma ≤
          (E : ℝ) ^ 2 * (Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon) := hmul
      _ = Chom⁻¹ * epsilon := by field_simp [hEpos.ne']
      _ ≤ 1 * (1 / 2) := by
        gcongr
        exact (inv_le_one₀ hChomPos).2 hChomOne
      _ = 1 / 2 := one_mul _
  exact ⟨hLmOne, hwindow, hEgamma⟩

private theorem combineFiniteVariance_comparisonBounds3 :
    ∀ (d : ℕ) (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E }) (L n : ℤ) (_ : n ∈ Set.Icc L m)
      (_ : (↑E : ℝ) ^ (2 : ℕ) * M.gamma ≤ (1 / 2 : ℝ)),
      let x : ℝ := (↑E : ℝ)⁻¹ ^ (3 : ℕ) * M.gamma⁻¹;
      let rare : ℝ := Real.exp (-x);
      let delta : ℝ := (↑E : ℝ) ^ (2 : ℕ) * M.gamma + Real.exp (-((2 : ℝ) * x));
      let A : ℝ := (16 : ℝ) * (↑E : ℝ) * √M.gamma;
      let D : ℝ := (256 : ℝ) * rare;
      let c : ℤ := (↑(Cutoff.cutoffRelativeNormalizationShift d) : ℤ);
      let Q : TriadicCube d := originCube d (n - (L + c));
      let j : ℕ := (n - L).toNat;
      let N : ℝ := (↑(descendantsAtScale Q (-c)).card : ℝ);
      let card : ℝ := (↑(Fintype.card (BlockCoord d)) : ℝ);
      let geom : ℝ := Real.rpow (3 : ℝ) (-(↑d : ℝ) * (↑j : ℝ));
      let budget : ℝ :=
        (2 : ℝ) *
            ((gammaMomentConst (2 : ℝ) * (2 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (2 : ℕ) +
              (gammaMomentConst (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (2 : ℕ)) +
          (8 : ℝ) *
            ((gammaMomentConst (2 : ℝ) * (4 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (4 : ℕ) +
              (gammaMomentConst (1 / 2 : ℝ) * (4 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (4 : ℕ));
      let secondBudget : ℝ :=
        (2 : ℝ) *
          ((gammaMomentConst (2 : ℝ) * (2 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (2 : ℕ) +
            (gammaMomentConst (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (2 : ℕ));
      let fourthBudget : ℝ :=
        (8 : ℝ) *
          ((gammaMomentConst (2 : ℝ) * (4 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (4 : ℕ) +
            (gammaMomentConst (1 / 2 : ℝ) * (4 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (4 : ℕ));
      L ≤ n ∧
        (0 : ℝ) < N ∧
          N⁻¹ = geom ∧
            (0 : ℝ) ≤ delta ∧
              secondBudget ≤ finiteCorridorSecondConst * delta ∧
                fourthBudget ≤ finiteCorridorFourthConst * delta ^ (2 : ℕ) ∧
                  budget ≤ finiteCorridorBudgetConst * delta ∧
                    (∀ (y : ℝ), (0 : ℝ) ≤ y ^ (4 : ℕ)) ∧
                      (0 : ℝ) ≤ (gammaMomentConst (2 : ℝ) * (2 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (2 : ℕ) ∧
                        (0 : ℝ) ≤ (gammaMomentConst (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ)⁻¹ * D) ^ (2 : ℕ) := by
  intro d M _ E L n hn hEgamma x rare delta A D c Q j N card geom budget secondBudget fourthBudget
  have hLn : L ≤ n := hn.1
  have hscale : -c ≤ Q.scale := by
    simp only [Q, originCube]
    omega
  have hNcard : (descendantsAtScale Q (-c)).card = (3 ^ d) ^ j := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hscale, descendantsAtDepth_card]
    congr 2
    simp only [Q, originCube]
    rw [show n - (L + c) - -c = n - L by ring]
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast (descendantsAtScale_nonempty Q hscale).card_pos
  have hNinv : N⁻¹ = geom := by
    have hNpow : N = ((3 : ℝ) ^ (d * j)) := by
      calc
        N = (((3 ^ d) ^ j : ℕ) : ℝ) := by
          dsimp only [N]
          exact_mod_cast hNcard
        _ = ((3 : ℝ) ^ (d * j)) := by
          norm_cast
          rw [pow_mul]
    have hrpow : Real.rpow (3 : ℝ) ((d * j : ℕ) : ℝ) =
        (3 : ℝ) ^ (d * j) := Real.rpow_natCast _ _
    calc
      N⁻¹ = ((3 : ℝ) ^ (d * j))⁻¹ := by rw [hNpow]
      _ = (Real.rpow (3 : ℝ) ((d * j : ℕ) : ℝ))⁻¹ := by rw [hrpow]
      _ = Real.rpow (3 : ℝ) (-((d * j : ℕ) : ℝ)) :=
        (Real.rpow_neg (by norm_num : 0 ≤ (3 : ℝ)) ((d * j : ℕ) : ℝ)).symm
      _ = geom := by
        simp only [geom]
        rw [Nat.cast_mul, neg_mul]
  have hMom := finiteCorridor_momentBudgets_le
    (E : ℝ) M.gamma E.property M.shellPrefix.gamma_pos hEgamma
  have hdeltaNonneg : 0 ≤ delta := by
    simpa only [x, rare, delta, A, D, secondBudget, fourthBudget, budget] using hMom.1
  have hsecondLe : secondBudget ≤ finiteCorridorSecondConst * delta := by
    simpa only [x, rare, delta, A, D, secondBudget, fourthBudget, budget] using hMom.2.2.1
  have hfourthLe : fourthBudget ≤ finiteCorridorFourthConst * delta ^ (2 : ℕ) := by
    simpa only [x, rare, delta, A, D, secondBudget, fourthBudget, budget] using hMom.2.2.2.1
  have hbudgetLe : budget ≤ finiteCorridorBudgetConst * delta := by
    simpa only [x, rare, delta, A, D, secondBudget, fourthBudget, budget] using hMom.2.2.2.2
  have hpow4 : ∀ y : ℝ, (0 : ℝ) ≤ y ^ (4 : ℕ) := fun y =>
    calc (0 : ℝ) ≤ (y ^ (2 : ℕ)) ^ (2 : ℕ) := sq_nonneg _
      _ = y ^ (4 : ℕ) := by ring
  have hbudgetSecond1 : (0 : ℝ) ≤
      (gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) := sq_nonneg _
  have hbudgetSecond2 : (0 : ℝ) ≤
      (gammaMomentConst (1 / 2) * (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ) :=
    sq_nonneg _
  exact ⟨hLn, hNpos, hNinv, hdeltaNonneg, hsecondLe, hfourthLe, hbudgetLe, hpow4, hbudgetSecond1,
    hbudgetSecond2⟩

/-- Uniform quantitative literal two-plus-eight control along the physical
integer corridor above the cutoff.  The fixed relative buffer, the
lower-clause specialization, and both channel bounds are discharged internally.
-/
theorem exists_relativeCutoff_finiteCorridor_fluctuationVariance_bound
    (d : ℕ) :
    ∃ Chom Cvar : ℝ, 64 ≤ Chom ∧
      2 * ((Cutoff.cutoffRelativeNormalizationShift d : ℝ) + 1) ≤ Chom ∧
      1 ≤ Cvar ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (gammaSigma 2) (gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon →
          ∀ L : ℤ,
            (L : ℝ) ≤ (m : ℝ) - Chom * |Real.log epsilon| →
            ∀ n : ℤ, n ∈ Set.Icc L m →
              let hd : NeZero d :=
                ⟨Nat.ne_of_gt
                  (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
              let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
              let P := Cutoff.relativeNormalizedCutoffLaw M L
              let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
              let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
              let center : ℤ := n - L - c
              let Q : TriadicCube d := originCube d (n - (L + c))
              let B : FullBlockMat d := @Book.Ch02.constantFullBlockMatrix d
                (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L))
              let Cn : BlockMat d :=
                @Book.Ch04.scalarAnnealedBlockMatrixAtScale d hd _ hP hStruct center
              let delta : ℝ :=
                (E : ℝ) ^ 2 * M.gamma +
                  Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))
              let decay : ℝ := Real.rpow 3
                (-(d : ℝ) * (((n - L).toNat : ℕ) : ℝ))
              2 * ∫ a, starredDescendantsAverageFluctuationOperatorNormSq B Cn Q
                    ((n - L).toNat) a ∂P +
                  8 * ∫ a, starredBlockJTraceAverageSq B Q ((n - L).toNat) a ∂P ≤
                Cvar * delta * (delta + decay) := by
  let shift : ℝ := Cutoff.cutoffRelativeNormalizationShift d
  let Chom : ℝ := max 64 (2 * (shift + 1))
  let Cvar : ℝ := finiteCorridorVarianceConst d
  have hChom64 : (64 : ℝ) ≤ Chom := le_max_left _ _
  have hChomShift : 2 * (shift + 1) ≤ Chom := le_max_right _ _
  have hChomOne : (1 : ℝ) ≤ Chom := by linarith only [hChom64]
  have hCvarOne : (1 : ℝ) ≤ Cvar := by
    exact le_max_left _ _
  refine ⟨Chom, Cvar, hChom64, hChomShift, hCvarOne, ?_⟩
  intro M m E hLower epsilon hepsilon hgamma L hseparation n hn
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  obtain ⟨hLmOne, hwindow, hEgamma⟩ :=
    (show (L ≤ m - 1) ∧ ((1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1) ∧ ((E : ℝ) ^ 2 * M.gamma ≤ 1 / 2)
      from
      @combineFiniteVariance_comparisonBounds2 (d) (hChom64) (hChomOne) (M) (m) (E) (epsilon)
        (hepsilon) (hgamma) (L) (hseparation))
  let x : ℝ := ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹
  let rare : ℝ := Real.exp (-x)
  let delta : ℝ := (E : ℝ) ^ 2 * M.gamma + Real.exp (-(2 * x))
  let A : ℝ := 16 * (E : ℝ) * Real.sqrt M.gamma
  let D : ℝ := 256 * rare
  have hLowerL0 := hLower L hLmOne (1 / 16) hwindow
  have hLowerL : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L ⟨1 / 16, by norm_num⟩) A D := by
    have hAeq : (E : ℝ) * 16 * Real.sqrt M.gamma = A := by
      dsimp only [A]
      ring
    have hDeq : (16 : ℝ) ^ (2 : ℕ) *
        Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) = D := by
      dsimp only [D, rare, x]
      norm_num
    simpa only [show (1 / 16 : ℝ)⁻¹ = 16 by norm_num, hAeq, hDeq] using hLowerL0
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
  let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
  let center : ℤ := n - L - c
  let Q : TriadicCube d := originCube d (n - (L + c))
  let j : ℕ := (n - L).toNat
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let Cn : BlockMat d :=
    Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  let N : ℝ := ((descendantsAtScale Q (-c)).card : ℝ)
  let card : ℝ := Fintype.card (BlockCoord d)
  let geom : ℝ := Real.rpow 3 (-(d : ℝ) * (j : ℝ))
  let budget : ℝ :=
    2 *
        ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ)) +
      8 *
        ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))
  let secondBudget : ℝ :=
    2 *
      ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
        (gammaMomentConst (1 / 2) *
          (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ))
  let fourthBudget : ℝ :=
    8 *
      ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
        (gammaMomentConst (1 / 2) *
          (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))
  let probeRhs : FullBlockVec d → ℝ := fun q =>
    let probeBudget : ℝ := 6 * (dotProduct q q) ^ (2 : ℕ) * budget
    let meanBudget : ℝ :=
      4 * (dotProduct q q) ^ (2 : ℕ) * secondBudget ^ (2 : ℕ)
    let K : ℝ := Real.sqrt probeBudget
    let rootBound : ℝ :=
      N⁻¹ *
        (Book.Ch04.rosenthalDescendantsAtScaleLpConst d (-c) 2 *
              N ^ (1 / (2 : ℝ)) * K +
          Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d (-c) 2 *
              Real.sqrt N * K)
    2 * rootBound ^ (2 : ℕ) + 2 * meanBudget
  let descendantRhs : ℝ :=
    2 * card ^ (2 : ℕ) *
      (card *
        ∑ alpha : BlockCoord d, card *
          ∑ beta : BlockCoord d, 3 *
            (probeRhs (fullBlockCoordinateProbe alpha) +
              probeRhs (fullBlockPlusProbe alpha beta) +
              probeRhs (fullBlockMinusProbe alpha beta)))
  let traceRhs : ℝ := 8 * (card ^ (2 : ℕ) * fourthBudget)
  obtain ⟨hLn, hNpos, hNinv, hdeltaNonneg, hsecondLe, hfourthLe, hbudgetLe, hpow4, hbudgetSecond1,
    hbudgetSecond2⟩ :=
    (show (L ≤ n) ∧ (0 < N) ∧ (N⁻¹ = geom) ∧ (0 ≤ delta) ∧ (secondBudget ≤
      finiteCorridorSecondConst * delta) ∧ (fourthBudget ≤ finiteCorridorFourthConst * delta ^ (2
        : ℕ)) ∧ (budget ≤ finiteCorridorBudgetConst * delta) ∧ (∀ y : ℝ, (0 : ℝ) ≤ y ^ (4 : ℕ)) ∧
          ((0 : ℝ) ≤
      (gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ)) ∧ ((0 : ℝ) ≤
      (gammaMomentConst (1 / 2) * (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ)) from
      @combineFiniteVariance_comparisonBounds3 (d) (M) (m) (E) (L) (n) (hn) (hEgamma))
  obtain ⟨hdescRhs, htraceRhs⟩ :=
    (show (descendantRhs ≤
      18 * card ^ (6 : ℕ) * finiteCorridorProbeConst d * delta *
        (delta + geom)) ∧ (traceRhs ≤
      8 * card ^ (2 : ℕ) * finiteCorridorFourthConst * delta *
        (delta + geom)) from
      @combineFiniteVariance_comparisonBounds1 (d) (M) (E) (L) (n) (hNpos) (hNinv) (hdeltaNonneg)
        (hsecondLe) (hfourthLe) (hbudgetLe) (hpow4) (hbudgetSecond1) (hbudgetSecond2))
  have hdesc :=
    two_mul_integral_relativeStarredDescendantOperatorNormSq_le
      M L n hLn (s := (1 / 16 : ℝ)) (by norm_num) hLowerL
  have htrace :=
    eight_mul_integral_relativeStarredBlockJTraceAverageSq_le
      M L n hLn hLowerL
  have hCsumNonneg : 0 ≤
      18 * card ^ (6 : ℕ) * finiteCorridorProbeConst d +
        8 * card ^ (2 : ℕ) * finiteCorridorFourthConst := by
    have hcardNonneg : (0 : ℝ) ≤ card := by dsimp only [card]; positivity
    have hs1 : (0 : ℝ) ≤ 18 * card ^ (6 : ℕ) * finiteCorridorProbeConst d :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hcardNonneg 6))
        (finiteCorridorProbeConst_nonneg d)
    have hs2 : (0 : ℝ) ≤ 8 * card ^ (2 : ℕ) * finiteCorridorFourthConst :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hcardNonneg 2))
        finiteCorridorFourthConst_nonneg
    linarith only [hs1, hs2]
  calc
    2 * ∫ a, starredDescendantsAverageFluctuationOperatorNormSq B Cn Q j a ∂P +
          8 * ∫ a, starredBlockJTraceAverageSq B Q j a ∂P ≤
        descendantRhs + traceRhs := by
      exact add_le_add
        (by
          simpa only [c, P, hP, hStruct, center, Q, sigma, a0, B, Cn, N, card,
            A, D, budget, secondBudget, probeRhs, descendantRhs, sub_sub] using hdesc.2)
        (by
          simpa only [c, P, center, Q, j, sigma, a0, B, card,
            A, D, fourthBudget, traceRhs] using htrace.2)
    _ ≤ (18 * card ^ (6 : ℕ) * finiteCorridorProbeConst d +
          8 * card ^ (2 : ℕ) * finiteCorridorFourthConst) * delta *
            (delta + geom) := by
      calc
        descendantRhs + traceRhs ≤
            18 * card ^ (6 : ℕ) * finiteCorridorProbeConst d * delta *
                (delta + geom) +
              8 * card ^ (2 : ℕ) * finiteCorridorFourthConst * delta *
                (delta + geom) := add_le_add hdescRhs htraceRhs
        _ = _ := by ring
    _ ≤ Cvar * delta * (delta + geom) := by
      have hsumLe :
          18 * card ^ (6 : ℕ) * finiteCorridorProbeConst d +
              8 * card ^ (2 : ℕ) * finiteCorridorFourthConst ≤ Cvar := by
        simpa only [Cvar, finiteCorridorVarianceConst] using
          (le_max_right (1 : ℝ)
            (18 * card ^ (6 : ℕ) * finiteCorridorProbeConst d +
              8 * card ^ (2 : ℕ) * finiteCorridorFourthConst))
      have hfactor : 0 ≤ delta * (delta + geom) :=
        mul_nonneg hdeltaNonneg
          (add_nonneg hdeltaNonneg (Real.rpow_nonneg (by norm_num) _))
      have hmul := mul_le_mul_of_nonneg_right hsumLe hfactor
      ring_nf at hmul ⊢
      exact hmul
    _ = Cvar *
        ((E : ℝ) ^ 2 * M.gamma +
          Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) *
        (((E : ℝ) ^ 2 * M.gamma +
            Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) +
          Real.rpow 3 (-(d : ℝ) * (((n - L).toNat : ℕ) : ℝ))) := by
      simp only [delta, x, geom, j]
      congr 4 <;> ring

end

end Algsuperdiff.Section3.Provider.Homogenization
