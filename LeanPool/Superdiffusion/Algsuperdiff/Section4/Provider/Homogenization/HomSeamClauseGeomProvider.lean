/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamGradProvider
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamEnergyFinitenessCuts

/-!
# HomSeamClauseGeomProvider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The §4.5 conditional provider at the multiscale clause and the factor D3

## What this file supplies

The §4.5 conditional provider reproduces the frozen root's conclusion verbatim
from EXACTLY

```text
  {0 < cstar, 0 < gamma0, 0 < Cgap, 0 ≤ GEOM}        -- numeral binders
  hclause: the multiscale coarse-graining clause, a.e., at the shape
  hgeom: one model-uniform bound for coarseGrainingGeomFactor (4d) (s/4)
```

and nothing else.  `C_en⁰`, `K_abs` and `C_top` are no longer slots: they are the
closed terms `Creg · 729 · GEOM`, `recutKabsHalf d hd1 Cgap (Creg · 729 · GEOM)`
and `seamTopScaleConst d C_step`, pinned INSIDE the proof after
`exists_regularity_minimalScale` has produced the model-free `Creg`.

`hgeom` is item **D3** and nothing else: it is exhibited as a hypothesis, not
assumed away.  Nothing here asserts that it holds.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 2. The `Creg` hoist: `C_en⁰` split into `Creg`, a numeral, and D3 -/

/-- **THE `3^{(1-α)k}` FACTOR OF `recutEnergySlotConst` IS MODEL-FREE.**

`1 - α = s/2 = 1/(2|log γ|)` and `k = ⌈10|log γ|⌉ ≤ 10|log γ| + 1`, so the
exponent is at most `5 + 1/(2|log γ|) ≤ 41/8 ≤ 6` on the printed gate
`|log γ| ≥ 4`.  This is the half of `C_en⁰` that carries no `γ`. -/
theorem three_rpow_homAlpha_homK_le (M : ABKModel d)
    (hlog : 4 ≤ |Real.log M.gamma|) :
    (3 : ℝ) ^ ((1 - homAlpha M) * (homK M : ℝ)) ≤ 729 := by
  have htpos : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hlog]
  have hsplit : (1 : ℝ) - homAlpha M = homS M / 2 := by rw [homAlpha]; ring
  have hsval : homS M = |Real.log M.gamma|⁻¹ := rfl
  have hKnn : (0 : ℝ) ≤ (homK M : ℝ) := Nat.cast_nonneg _
  have hK := homK_le M
  have htinv : |Real.log M.gamma|⁻¹ ≤ 1 / 4 := by
    have hmul : |Real.log M.gamma|⁻¹ * (4 : ℝ) ≤
        |Real.log M.gamma|⁻¹ * |Real.log M.gamma| :=
      mul_le_mul_of_nonneg_left hlog (inv_pos.mpr htpos).le
    rw [inv_mul_cancel₀ (ne_of_gt htpos)] at hmul
    linarith only [hmul]
  have hfac : (0 : ℝ) ≤ |Real.log M.gamma|⁻¹ / 2 := by positivity
  have hprod : |Real.log M.gamma|⁻¹ / 2 * (homK M : ℝ) ≤
      |Real.log M.gamma|⁻¹ / 2 * (10 * |Real.log M.gamma| + 1) :=
    mul_le_mul_of_nonneg_left hK hfac
  have hexpand : |Real.log M.gamma|⁻¹ / 2 * (10 * |Real.log M.gamma| + 1) =
      5 + |Real.log M.gamma|⁻¹ / 2 := by
    field_simp
    ring
  have hexp : (1 - homAlpha M) * (homK M : ℝ) ≤ 6 := by
    rw [hsplit, hsval]
    rw [hexpand] at hprod
    linarith only [hprod, htinv]
  have hmono : (3 : ℝ) ^ ((1 - homAlpha M) * (homK M : ℝ)) ≤ (3 : ℝ) ^ (6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hval : (3 : ℝ) ^ (6 : ℝ) = 729 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [hval] at hmono
  exact hmono

/-- **`C_en⁰`, SPLIT.**

The energy-slot constant of the per-`ω` display is `Creg · 3^{(1-α)k} ·
coarseGrainingGeomFactor (4d) (s/4)`.  The middle factor is model-free
(`three_rpow_homAlpha_homK_le`); the last factor is item **D3**, and it is the
ONLY place a model-uniform input is needed. -/
theorem recutEnergySlotConst_le_of_geom {M : ABKModel d} (hd1 : 1 ≤ d)
    {Creg GEOM : ℝ} (hCreg : 0 ≤ Creg) (hlog : 4 ≤ |Real.log M.gamma|)
    (hgeom : coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal)
      (homS M / 4) ≤ GEOM) :
    recutEnergySlotConst Creg (homAlpha M) ((recutExponent d hd1).exponent.toReal)
        (homS M) (homK M) ≤ Creg * 729 * GEOM := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hp : (0 : ℝ) < (recutExponent d hd1).exponent.toReal := by
    rw [recutExponent_toReal]; linarith only [hdR]
  have hs : 0 < homS M := homS_pos (by linarith only [hlog])
  have hgeom0 : (0 : ℝ) ≤
      coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4) :=
    coarseGrainingGeomFactor_nonneg hp (by linarith only [hs])
  have h3 := three_rpow_homAlpha_homK_le M hlog
  have hCreg729 : (0 : ℝ) ≤ Creg * 729 := by linarith only [hCreg]
  rw [recutEnergySlotConst]
  calc Creg * (3 : ℝ) ^ ((1 - homAlpha M) * (homK M : ℝ)) *
        coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4)
      ≤ Creg * 729 *
        coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hCreg) hgeom0
    _ ≤ Creg * 729 * GEOM := mul_le_mul_of_nonneg_left hgeom hCreg729

end

end Algsuperdiff.Section4.Provider.Homogenization
