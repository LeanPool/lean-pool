/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.InputA
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.InputBC
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly.Skeleton
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Adjoint.H10Witness

/-!
# BoundProvider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The provider result for the frozen `D_h` bound

Source: ABK26 (`l.Dh.bound`).

This module assembles the completed proof of the frozen target
`Algsuperdiff.Frozen.Section24.coarseMatrixDerivative_bound`:

* the splitting identity with the `H¹₀` premise discharged, consumed here
  through the zero-trace witness itself
  (`Adjoint.exists_h10Function_grad_ae_eq_halfSum_add_const_unitCube`);
* the two-budget assembly
  `Assembly.abs_quadForm_coarseMatrixDerivative_le_of_positiveBesov_budgets`;
* the Term A budget `Discharge.InputA`;
* the Term BC budget `Discharge.InputBC`;
* the arithmetic fold `Assembly.abs_le_frozen_shape_of_budget_bounds`.

The constant is explicit:

```
C(d) = 2 (1 + d 3^{d+1}) (2 c_{3/8,2}^{-1/2}) ( termABesovConst d + termBCBesovConst d ).
```
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory Set
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
open Algsuperdiff.Section24.UnitCubeMultiscale
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section

/-! ## The explicit constant -/

/-- The Besov pairing constant of the `D_h` assembly. -/
def dhPairingConst (d : ℕ) : ℝ :=
  (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
    (2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2))

theorem dhPairingConst_pos (d : ℕ) : 0 < dhPairingConst d := by
  have h1 : (0 : ℝ) < 1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
    have : (0 : ℝ) < Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  have h2 : (0 : ℝ) < 2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2) := by
    have := poincareDiscountFactor_sensitivity_pos
    linarith
  exact mul_pos h1 h2

theorem termABesovConst_pos {d : ℕ} (hd : 2 ≤ d) : 0 < termABesovConst d := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have h1 : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have h2 : 0 < Besov.besovPerturbConst (3 / 8 : ℝ) :=
    Besov.besovPerturbConst_pos (by norm_num)
  unfold termABesovConst
  positivity

/-- The explicit constant of the frozen `D_h` bound. -/
def dhBoundConst (d : ℕ) : ℝ  :=
  2 * dhPairingConst d * (termABesovConst d + termBCBesovConst d)

theorem dhBoundConst_pos {d : ℕ} (hd : 2 ≤ d) : 0 < dhBoundConst d  := by
  have h1 := dhPairingConst_pos d
  have h2 := termABesovConst_pos hd
  have h3 := termBCBesovConst_nonneg d
  unfold dhBoundConst
  nlinarith

/-! ## The provider result -/

/-- **The unit-cube sensitivity estimate for the coarse-matrix derivative.**

This is the provider form of the frozen target
`Algsuperdiff.Frozen.Section24.coarseMatrixDerivative_bound`, with exactly the
frozen binders. -/
theorem coarseMatrixDerivative_bound {d : ℕ}
    (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d) (p q : Vec d),
      |blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative (cubeDomain (originCube d 0)) a
          h.toLInfSkewMatrixFieldOn.1) (p, -q))|
        ≤ C * (vecNorm p * h.w1Infinity *
              Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) +
            Real.sqrt |vecDot p q| * h.gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) +
          C * h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ *
            responseJ (cubeDomain (originCube d 0)) a p q := by
  classical
  have : NeZero d := ⟨by omega⟩
  refine ⟨dhBoundConst d, dhBoundConst_pos dimension, ?_⟩
  intro a h p q
  -- canonical maximizers for the primal and adjoint problems
  obtain ⟨vAdj, hvAdj⟩ :
      ∃ w : Solution (cubeDomain (originCube d 0)) a.transpose,
        IsResponseMaximizer (cubeDomain (originCube d 0)) a.transpose p (-q) w :=
    ⟨_, canonicalMaximizer_isMaximizer
      (responseExistenceTheory (cubeDomain (originCube d 0)) a.transpose) p (-q)⟩
  obtain ⟨v, hv⟩ :
      ∃ w : Solution (cubeDomain (originCube d 0)) a,
        IsResponseMaximizer (cubeDomain (originCube d 0)) a p q w :=
    ⟨_, canonicalMaximizer_isMaximizer
      (responseExistenceTheory (cubeDomain (originCube d 0)) a) p q⟩
  -- the zero-trace witness
  obtain ⟨u, hu⟩ :=
    Adjoint.exists_h10Function_grad_ae_eq_halfSum_add_const_unitCube a p q vAdj v
      hvAdj hv
  -- a compatible CoarseGraining coefficient family
  obtain ⟨F, hF⟩ := exists_compatibleTriadicCoeffFamily a
  -- abbreviations matching the arithmetic fold
  set np : ℝ := vecNorm p with hnp
  set w : ℝ := h.w1Infinity with hw
  set g : ℝ := h.gradientW1Infinity with hg
  set L : ℝ := (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ with hLdef
  set J : ℝ := responseJ (cubeDomain (originCube d 0)) a p q with hJdef
  have hLnn : 0 ≤ L := by
    rw [hLdef]
    exact le_of_lt (inv_pos.mpr (unitCubeLambda_sensitivity_pos a))
  have hJnn : 0 ≤ J := by
    rw [hJdef]; exact Ch02.responseJ_nonneg _ a p q
  -- the two Besov budgets
  have hHBC : Ch03.ForceBesovRegularity (originCube d 0) (3 / 8)
      (fun x => u.toH1Function.toFun x • matWeakDiv (unitCubeDerivData h) x) :=
    forceBesovRegularity_termBCField h u
  have hHBCle : Ch03.scaleNormalizedPositiveBesovVectorNormTwo (originCube d 0)
      (3 / 8)
      (fun x => u.toH1Function.toFun x • matWeakDiv (unitCubeDerivData h) x) ≤
      termBCBesovConst d * g * (Real.sqrt L * (Real.sqrt J + Real.sqrt |vecDot p q|)) :=
    scaleNormalizedPositiveBesovVectorNormTwo_termBCField_le a h p q hvAdj hv u hu
  have hbudget :=
    abs_quadForm_coarseMatrixDerivative_le_of_positiveBesov_budgets a h p q F hF
      vAdj v hvAdj hv u hu
      (BA := termABesovConst d * np * w)
      (BBC := termBCBesovConst d * g *
        (Real.sqrt L * (Real.sqrt J + Real.sqrt |vecDot p q|)))
      (forceBesovRegularity_termAField h p)
      (scaleNormalizedPositiveBesovVectorNormTwo_termAField_le h p)
      hHBC hHBCle
  -- the arithmetic fold
  have hfold := abs_le_frozen_shape_of_budget_bounds
    (K := dhPairingConst d) (CA := termABesovConst d) (CBC := termBCBesovConst d)
    (np := np) (w := w) (g := g) (sl := Real.sqrt L) (spq := Real.sqrt |vecDot p q|)
    (sJ := Real.sqrt J)
    (dhPairingConst_pos d).le (termABesovConst_pos dimension).le
    (termBCBesovConst_nonneg d)
    (by rw [hnp]; exact vecNorm_nonneg p)
    (by rw [hw]; exact Lipschitz.w1Infinity_nonneg h)
    (by rw [hg]; exact Lipschitz.gradientW1Infinity_nonneg h)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hbudget le_rfl (le_of_eq (by ring))
  refine hfold.trans (le_of_eq ?_)
  rw [Real.mul_self_sqrt hLnn, Real.mul_self_sqrt hJnn]
  unfold dhBoundConst
  ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound
