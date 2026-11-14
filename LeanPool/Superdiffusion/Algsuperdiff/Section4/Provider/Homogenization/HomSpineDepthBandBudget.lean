/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineDepthBandInput
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineSupFormClauseAt
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamBudgetArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineResidueLevel
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineEnergySlot

/-!
# HomSpineDepthBandBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The produced clause constant, inside the frozen budget

## What this file settles

`HomSpineDepthBandInput` produces the sup-form multiscale clause unconditionally
at `CA = (1 + C(d)·(near + 2·x₀⁻¹))^{1/p'}`; `HomSpineSupFormClauseAt` displays
the resulting clause constant as `(√d · CA · C(p,d)).toReal`.  The frozen budget
(`HomSeamCompositionCcg`) asks for exactly one inequality:

```text
  Ccg(M) · GEOM(M) ≤ C_bud · |log γ|.
```

This file proves it, at the realization's own pin `x₀ = s·p'` with
`s = homS M = |log γ|⁻¹`:

* `gridDepthConverseConst_toReal_le` — `CA ≤ K(d,p) · (1 + x₀⁻¹)^{1/p'}`, with
  `K(d,p) = 1 + C(d)·near + 2·C(d)` a MODEL-FREE numeral: the whole model
  dependence of `CA` is the far-band factor, and nothing else;
* `recutDepthBandPin` — the two-sided pin holds at `s = homS M`, `x₀ = s·p'`
  (the lower half by equality, the upper half by `s ≤ 1/4` and `p' ≤ 4/3`);
* `seamProducedCcg_le_budget` — the product with the energy factor, closed by
  the two-factor inequality
  `HomSeamBudgetArith.recut_geomBudget_le_absLog` (`GEOM · far ≤ 2|log γ|`).

So the frozen display's one extra `|log γ|` pays for BOTH machine-pinned costs of
realizing Step 3 at `p = 4d`, with the budget constant `√d·K·C(p,d)·2`.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. The dimensional Gagliardo constant, as a real -/

/-- The real behind `HomSpineDepthBandInput.gridDepthGagliardoConst`. -/
def gridDepthGagliardoConstReal (d : ℕ) (p : FiniteLpExponent) : ℝ :=
  (2 : ℝ) ^ p.conjugate.exponent.toReal * (2 ^ (d + 3) * ((d : ℝ) + 1) * 3 ^ d)

theorem gridDepthGagliardoConstReal_nonneg (d : ℕ) (p : FiniteLpExponent) :
    0 ≤ gridDepthGagliardoConstReal d p := by
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ p.conjugate.exponent.toReal :=
    Real.rpow_nonneg (by norm_num) _
  have hd : (0 : ℝ) ≤ 2 ^ (d + 3) * ((d : ℝ) + 1) * 3 ^ d := by positivity
  exact mul_nonneg h2 hd

theorem gridDepthGagliardoConst_eq_ofReal (d : ℕ) (p : FiniteLpExponent) :
    gridDepthGagliardoConst d p = ENNReal.ofReal (gridDepthGagliardoConstReal d p) := rfl

/-! ## 2. `CA` is the far-band factor times a MODEL-FREE numeral -/

/-- The model-free part of the dual-converse constant:
`K(d,p) = 1 + C(d)·near + 2·C(d)`. -/
def gridDepthPinConst (d : ℕ) (p : FiniteLpExponent) : ℝ :=
  1 + gridDepthGagliardoConstReal d p * nearBandGeometricConstant +
    2 * gridDepthGagliardoConstReal d p

theorem one_le_gridDepthPinConst (d : ℕ) (p : FiniteLpExponent) :
    1 ≤ gridDepthPinConst d p := by
  have hC0 : (0 : ℝ) ≤ gridDepthGagliardoConstReal d p :=
    gridDepthGagliardoConstReal_nonneg d p
  have hnear : (0 : ℝ) ≤ nearBandGeometricConstant := nearBandGeometricConstant_pos.le
  have h1 : (0 : ℝ) ≤ gridDepthGagliardoConstReal d p * nearBandGeometricConstant :=
    mul_nonneg hC0 hnear
  rw [gridDepthPinConst]
  linarith only [h1, hC0]

/-- **`CA` IS THE FAR-BAND FACTOR, UP TO A MODEL-FREE NUMERAL.**

`(1 + C(d)(near + 2x₀⁻¹))^{1/p'} ≤ K(d,p) · (1 + x₀⁻¹)^{1/p'}`.  All of the
model dependence of the dual-converse constant sits in `(1 + x₀⁻¹)^{1/p'}`,
which is EXACTLY the factor the two-factor budget controls. -/
theorem gridDepthConverseConst_toReal_le (d : ℕ) (p : FiniteLpExponent) {x₀ : ℝ}
    (hx₀ : 0 < x₀) :
    (gridDepthConverseConst p (gridDepthGagliardoConst d p) x₀).toReal ≤
      gridDepthPinConst d p * (1 + x₀⁻¹) ^ (p.conjugate.exponent.toReal)⁻¹ := by
  have hcd0 : (0 : ℝ) ≤ gridDepthGagliardoConstReal d p :=
    gridDepthGagliardoConstReal_nonneg d p
  have hnear : (0 : ℝ) ≤ nearBandGeometricConstant := nearBandGeometricConstant_pos.le
  have hr1 : (1 : ℝ) < p.conjugate.exponent.toReal :=
    one_lt_finiteLpExponent_toReal p.conjugate
  have hr0 : (0 : ℝ) < p.conjugate.exponent.toReal := by linarith only [hr1]
  have hinv0 : (0 : ℝ) < x₀⁻¹ := inv_pos.mpr hx₀
  have hK1 : (1 : ℝ) ≤ gridDepthPinConst d p := one_le_gridDepthPinConst d p
  have hmix : (0 : ℝ) ≤ gridDepthGagliardoConstReal d p *
      (nearBandGeometricConstant + 2 * x₀⁻¹) :=
    mul_nonneg hcd0 (by linarith only [hnear, hinv0])
  have hb0 : (0 : ℝ) ≤ 1 + gridDepthGagliardoConstReal d p *
      (nearBandGeometricConstant + 2 * x₀⁻¹) := by linarith only [hmix]
  have h1 : (0 : ℝ) ≤ gridDepthGagliardoConstReal d p * nearBandGeometricConstant :=
    mul_nonneg hcd0 hnear
  have h2 : (0 : ℝ) ≤
      gridDepthGagliardoConstReal d p * nearBandGeometricConstant * x₀⁻¹ :=
    mul_nonneg h1 hinv0.le
  have hbase : 1 + gridDepthGagliardoConstReal d p *
        (nearBandGeometricConstant + 2 * x₀⁻¹) ≤
      gridDepthPinConst d p * (1 + x₀⁻¹) := by
    rw [gridDepthPinConst]
    linarith only [hcd0, hinv0.le, h1, h2]
  have hval : (gridDepthConverseConst p (gridDepthGagliardoConst d p) x₀).toReal =
      (1 + gridDepthGagliardoConstReal d p *
        (nearBandGeometricConstant + 2 * x₀⁻¹)) ^ (p.conjugate.exponent.toReal)⁻¹ := by
    rw [gridDepthConverseConst, gridDepthGagliardoConst_eq_ofReal,
      ← ENNReal.ofReal_mul hcd0, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one hmix,
      ENNReal.ofReal_rpow_of_nonneg hb0 (inv_nonneg.mpr hr0.le),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hb0 _)]
  have hexp : (p.conjugate.exponent.toReal)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1.le
  have hpow : gridDepthPinConst d p ^ (p.conjugate.exponent.toReal)⁻¹ ≤
      gridDepthPinConst d p := by
    calc gridDepthPinConst d p ^ (p.conjugate.exponent.toReal)⁻¹
        ≤ gridDepthPinConst d p ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hK1 hexp
      _ = gridDepthPinConst d p := Real.rpow_one _
  rw [hval]
  calc (1 + gridDepthGagliardoConstReal d p *
        (nearBandGeometricConstant + 2 * x₀⁻¹)) ^ (p.conjugate.exponent.toReal)⁻¹
      ≤ (gridDepthPinConst d p * (1 + x₀⁻¹)) ^ (p.conjugate.exponent.toReal)⁻¹ :=
        Real.rpow_le_rpow hb0 hbase (inv_nonneg.mpr hr0.le)
    _ = gridDepthPinConst d p ^ (p.conjugate.exponent.toReal)⁻¹ *
          (1 + x₀⁻¹) ^ (p.conjugate.exponent.toReal)⁻¹ :=
        Real.mul_rpow (by linarith only [hK1]) (by linarith only [hinv0])
    _ ≤ gridDepthPinConst d p * (1 + x₀⁻¹) ^ (p.conjugate.exponent.toReal)⁻¹ :=
        mul_le_mul_of_nonneg_right hpow
          (Real.rpow_nonneg (by linarith only [hinv0]) _)

/-! ## 3. The conjugate exponent at the §4.5 pin, and the two-sided pin -/

/-- At `p = 4d` the conjugate exponent is at most `4/3`. -/
theorem recutConjugate_le (d : ℕ) (hd1 : 1 ≤ d) :
    (recutExponent d hd1).conjugate.exponent.toReal ≤ 4 / 3 := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hconj := holderConjugate_toReal (recutExponent d hd1)
  have hsum := Real.HolderConjugate.inv_add_inv_eq_one hconj
  have hp : (recutExponent d hd1).exponent.toReal = 4 * (d : ℝ) :=
    recutExponent_toReal d hd1
  have hr0 : (0 : ℝ) < (recutExponent d hd1).conjugate.exponent.toReal :=
    finiteLpExponent_toReal_pos (recutExponent d hd1).conjugate
  have hp4 : (4 : ℝ) ≤ 4 * (d : ℝ) := by linarith only [hdR]
  have hpinv : ((recutExponent d hd1).exponent.toReal)⁻¹ ≤ (4 : ℝ)⁻¹ := by
    rw [hp]
    exact inv_anti₀ (by norm_num) hp4
  have h34 : (3 : ℝ) / 4 ≤ ((recutExponent d hd1).conjugate.exponent.toReal)⁻¹ := by
    have h4 : (4 : ℝ)⁻¹ = 1 / 4 := by norm_num
    rw [h4] at hpinv
    linarith only [hsum, hpinv]
  have hmul := mul_le_mul_of_nonneg_right h34 hr0.le
  rw [inv_mul_cancel₀ hr0.ne'] at hmul
  linarith only [hmul]

/-- The two-sided pin holds at the realization's own order `s = homS M`, with
`x₀ = s·p'`: the lower half is an equality and the upper half is
`s·p' ≤ (1/4)·(4/3) ≤ 1/2`. -/
theorem recutDepthBandPin {d : ℕ} (hd1 : 1 ≤ d) (M : ABKModel d)
    (hlog : 4 ≤ |Real.log M.gamma|) :
    DepthBandPin (recutExponent d hd1)
      (homS M * (recutExponent d hd1).conjugate.exponent.toReal)
      (recutOrderBase M hlog) := by
  have hs : 0 < homS M := homS_pos (by linarith only [hlog])
  have hq : homS M ≤ 1 / 4 := homS_le_quarter hlog
  have hr : (recutExponent d hd1).conjugate.exponent.toReal ≤ 4 / 3 :=
    recutConjugate_le d hd1
  have hr0 : (0 : ℝ) < (recutExponent d hd1).conjugate.exponent.toReal :=
    finiteLpExponent_toReal_pos (recutExponent d hd1).conjugate
  refine ⟨le_of_eq ?_, ?_⟩
  · rw [recutOrderBase_val]
  · rw [recutOrderBase_val]
    have h := mul_le_mul hq hr hr0.le (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith only [h]

/-! ## 4. THE BUDGET -/

/-- The scalar shape of the budget: a bounded constant times a factor whose
product with the energy factor is controlled. -/
private theorem budget_combine {sq CA Cpd K far GEOM L : ℝ} (hsq : 0 ≤ sq)
    (hCpd : 0 ≤ Cpd) (hGEOM : 0 ≤ GEOM) (hK : 0 ≤ K) (hCA : CA ≤ K * far)
    (hprod : GEOM * far ≤ 2 * L) :
    sq * CA * Cpd * GEOM ≤ (sq * K * Cpd * 2) * L := by
  have h1 : sq * CA ≤ sq * (K * far) := mul_le_mul_of_nonneg_left hCA hsq
  have h2 : sq * CA * Cpd ≤ sq * (K * far) * Cpd := mul_le_mul_of_nonneg_right h1 hCpd
  have h3 : sq * CA * Cpd * GEOM ≤ sq * (K * far) * Cpd * GEOM :=
    mul_le_mul_of_nonneg_right h2 hGEOM
  have h4 : sq * (K * far) * Cpd * GEOM = (sq * K * Cpd) * (GEOM * far) := by ring
  have hcoef : (0 : ℝ) ≤ sq * K * Cpd := mul_nonneg (mul_nonneg hsq hK) hCpd
  have h5 : (sq * K * Cpd) * (GEOM * far) ≤ (sq * K * Cpd) * (2 * L) :=
    mul_le_mul_of_nonneg_left hprod hcoef
  have h6 : (sq * K * Cpd) * (2 * L) = (sq * K * Cpd * 2) * L := by ring
  linarith only [h3, h4.le, h4.ge, h5, h6.le, h6.ge]

/-- **The produced clause constant is inside the frozen budget.**

At the realization's pin `x₀ = s·p'`, `s = homS M`, the constant produced by
`HomSpineSupFormClauseAt` times the `ℓ^p` energy factor is at most
`(√d·K(d,p)·C(p,d)·2)·|log γ|`.  This is precisely the hypothesis `hbud` of
`HomSeamCompositionCcg.generator_renormalization_provider_final_of_supClauseAt`. -/
theorem seamProducedCcg_le_budget (d : ℕ) (hd1 : 1 ≤ d) (C : ℝ≥0∞) (M : ABKModel d)
    (hlog : 4 ≤ |Real.log M.gamma|) :
    (ENNReal.ofReal (Real.sqrt d) *
          gridDepthConverseConst (recutExponent d hd1)
            (gridDepthGagliardoConst d (recutExponent d hd1))
            (homS M * (recutExponent d hd1).conjugate.exponent.toReal) * C).toReal *
        coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4) ≤
      (Real.sqrt d * gridDepthPinConst d (recutExponent d hd1) * C.toReal * 2) *
        |Real.log M.gamma| := by
  have hs : 0 < homS M := homS_pos (by linarith only [hlog])
  have hr0 : (0 : ℝ) < (recutExponent d hd1).conjugate.exponent.toReal :=
    finiteLpExponent_toReal_pos (recutExponent d hd1).conjugate
  have hx0 : 0 < homS M * (recutExponent d hd1).conjugate.exponent.toReal :=
    mul_pos hs hr0
  have hppos : (0 : ℝ) < (recutExponent d hd1).exponent.toReal := by
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    rw [recutExponent_toReal]; linarith only [hdR]
  have hGEOM0 : (0 : ℝ) ≤
      coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4) :=
    coarseGrainingGeomFactor_nonneg hppos (by linarith only [hs])
  have hsqrt : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hK0 : (0 : ℝ) ≤ gridDepthPinConst d (recutExponent d hd1) := by
    have h := one_le_gridDepthPinConst d (recutExponent d hd1)
    linarith only [h]
  have hCAle := gridDepthConverseConst_toReal_le d (recutExponent d hd1) hx0
  have hbudget := recut_geomBudget_le_absLog hd1 M hlog
  rw [one_div] at hbudget
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hsqrt]
  exact budget_combine hsqrt ENNReal.toReal_nonneg hGEOM0 hK0 hCAle hbudget

end

end Algsuperdiff.Section4.Provider.Homogenization
