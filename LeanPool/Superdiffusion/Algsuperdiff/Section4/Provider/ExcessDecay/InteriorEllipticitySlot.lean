/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorRebase

/-!
# InteriorEllipticitySlot

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The coarse-graining slot re-cut at `r = s/3`

At `t = s/8` no admissible `u` exists.

The obstruction is an artefact of the slot, not of the analysis:
CoarseGraining's package constrains only `0 < r < t_prop < 1/2` and `r ≤ r₂`,
so **any** `r ∈ (s/4, 3s/8)` is admissible, and every such `r` has `r/2 > s/8`.
This module re-cuts the slot at

```text
  (s_prop, r, r₂, j) = (3s/4, s/3, s, 0) ,        r/2 = s/6 ,
```

which is exactly the index the proved off-grid cap
(`InteriorGlueCap.ae_offGridChildError_le_representative_harmonicSlot`, printed
slot `(s/6, s/8)`) delivers.

## Deviations from the printed statement

* the slot index `r` moves from `s/4` to `s/3`.  No `γ`-move and no `s`-power
  move is made.
* the constants `216`, `1944` replace `1024/3`, `16384/3`; both are smaller.

## References

* ABK26, `p.general.coarse.graining`; `e.homogenization.L2.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Two elementary `s`-power facts -/

/-- `(s/3)^{-3} = 27 (s⁻¹)³`. -/
private theorem rpow_third_neg_three (s : ℝ) (hs : 0 < s) :
    Real.rpow (s / 3) (-3 : ℝ) = 27 * (s⁻¹) ^ (3 : ℕ) := by
  have hr : (0 : ℝ) < s / 3 := by linarith only [hs]
  have hbase : Real.rpow (s / 3) (-3 : ℝ) = ((s / 3)⁻¹) ^ (3 : ℕ) := by
    rw [Real.rpow_eq_pow, show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hr.le, Real.rpow_natCast, ← inv_pow]
  have hinv : (s / 3)⁻¹ = 3 * s⁻¹ := by
    field_simp
  rw [hbase, hinv, mul_pow]
  norm_num

/-- `(s/3)^{-5/2} ≤ 27 (s⁻¹)³` on `(0,1]`. -/
private theorem rpow_third_neg_five_halves_le (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow (s / 3) (-(5 / 2 : ℝ)) ≤ 27 * (s⁻¹) ^ (3 : ℕ) := by
  have hr : (0 : ℝ) < s / 3 := by linarith only [hs]
  have hr1 : s / 3 ≤ 1 := by linarith only [hs1]
  have hmono : Real.rpow (s / 3) (-(5 / 2 : ℝ)) ≤ Real.rpow (s / 3) (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  rw [rpow_third_neg_three s hs] at hmono
  exact hmono

/-! ## 2. The envelope at the re-cut slot -/

/-- **The `s`-envelope at the slot `(3s/4, s/3, s, 0)`.**

```text
  RHS₁ ≤ 216 s^{-4} · |a₀|^{1/2} 𝓔_{s/3,∞,1}(Q) ‖∇u‖_a
       + 1944 s^{-6} · (CoarseGraining forcing bracket at `r = s/3`) · [g]_{H^s(Q)} .
``` -/
theorem generalCoarseGrainingL2TwoExponentRHS_thirdSlot_le [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) {g : Vec d → Vec d} (hg : Ch03.ForceBesovRegularity Q s g)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    Ch03.generalCoarseGrainingL2TwoExponentRHS 1 Q a a0 (3 * s / 4) (s / 3) s 0 g u ≤
      216 * (s⁻¹) ^ (4 : ℕ) * coarseGrainingEnergyTerm Q a a0 (s / 3) u +
        1944 * (s⁻¹) ^ (6 : ℕ) * coarseGrainingForceTerm Q a a0 (s / 3) s g := by
  have hr : (0 : ℝ) < s / 3 := by linarith only [hs]
  have hr2 : (0 : ℝ) < s / 3 / 2 := by linarith only [hr]
  have hsinv : (0 : ℝ) < s⁻¹ := inv_pos.mpr hs
  have hG : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hg
  have hET : 0 ≤ coarseGrainingEnergyTerm Q a a0 (s / 3) u :=
    coarseGrainingEnergyTerm_nonneg Q a a0 hr u
  have hB1 : 0 ≤ Ch03.constantCoeffMatrixNormHalf a0 *
      Ch03.poincareLowerEllipticityFactor Q a (s / 3 / 2) (.finite 2) *
      Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 (s / 3) 0 :=
    mul_nonneg (mul_nonneg (constantCoeffMatrixNormHalf_nonneg a0)
      (poincareLowerEllipticityFactor_nonneg Q a hr2))
      (coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 hr 0)
  have hB2 : 0 ≤ Ch03.poincareUpperEllipticityFactor Q a (s / 3 / 2) (.finite 2) *
      Ch03.poincareLowerEllipticityFactor Q a (s / 3 / 2) (.finite 2) :=
    mul_nonneg (poincareUpperEllipticityFactor_nonneg Q a hr2)
      (poincareLowerEllipticityFactor_nonneg Q a hr2)
  have hB3 : 0 ≤ Ch03.constantCoeffMatrixNorm a0 *
      Real.rpow (Ch02.lambdaSq Q (s / 3 / 2) (.finite 2) a) (-1 : ℝ) :=
    mul_nonneg (constantCoeffMatrixNorm_nonneg a0)
      (Real.rpow_nonneg (Ch02.lambdaSq_finite_pos Q a hr2 (by norm_num)).le _)
  rw [generalCoarseGrainingL2TwoExponentRHS_depth_zero_eq Q a a0 (3 * s / 4) (s / 3) s g u,
    coarseGrainingForceTerm, coarseGrainingForceBracket]
  set B1 : ℝ := Ch03.constantCoeffMatrixNormHalf a0 *
    Ch03.poincareLowerEllipticityFactor Q a (s / 3 / 2) (.finite 2) *
    Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 (s / 3) 0 with hB1def
  set B2 : ℝ := Ch03.poincareUpperEllipticityFactor Q a (s / 3 / 2) (.finite 2) *
    Ch03.poincareLowerEllipticityFactor Q a (s / 3 / 2) (.finite 2) with hB2def
  set B3 : ℝ := Ch03.constantCoeffMatrixNorm a0 *
    Real.rpow (Ch02.lambdaSq Q (s / 3 / 2) (.finite 2) a) (-1 : ℝ) with hB3def
  set ET : ℝ := coarseGrainingEnergyTerm Q a a0 (s / 3) u with hETdef
  set G : ℝ := Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g with hGdef
  set P : ℝ := (3 * s / 4)⁻¹ * ((s / 3)⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - s / 3)⁻¹ with hPdef
  -- the prefactor
  have hIpos : (0 : ℝ) < (1 / 2 : ℝ) - s / 3 := by linarith only [hs1]
  have hI : ((1 / 2 : ℝ) - s / 3)⁻¹ ≤ 6 := by
    have hlow : (1 / 6 : ℝ) ≤ (1 / 2 : ℝ) - s / 3 := by linarith only [hs1]
    have h := inv_anti₀ (show (0 : ℝ) < 1 / 6 by norm_num) hlow
    rw [show ((1 : ℝ) / 6)⁻¹ = 6 by norm_num] at h
    exact h
  have hPeq : P = 12 * (s⁻¹) ^ (3 : ℕ) * ((1 / 2 : ℝ) - s / 3)⁻¹ := by
    rw [hPdef]
    have hs0 : s ≠ 0 := hs.ne'
    field_simp
    ring
  have hPnonneg : 0 ≤ P := by
    rw [hPeq]
    have h1 : (0 : ℝ) ≤ 12 * (s⁻¹) ^ (3 : ℕ) := by positivity
    exact mul_nonneg h1 (inv_pos.mpr hIpos).le
  have hPle : P ≤ 72 * (s⁻¹) ^ (3 : ℕ) := by
    rw [hPeq]
    have h1 : (0 : ℝ) ≤ 12 * (s⁻¹) ^ (3 : ℕ) := by positivity
    have h := mul_le_mul_of_nonneg_left hI h1
    linarith only [h]
  -- the inner bracket
  have hforce : Real.rpow (s / 3) (-(5 / 2 : ℝ)) * B1 +
      Real.rpow (s / 3) (-(5 / 2 : ℝ)) * B2 + Real.rpow (s / 3) (-3 : ℝ) * B3 ≤
      27 * (s⁻¹) ^ (3 : ℕ) * (B1 + B2 + B3) := by
    have h52 := rpow_third_neg_five_halves_le s hs hs1
    have h3 := rpow_third_neg_three s hs
    have e1 : Real.rpow (s / 3) (-(5 / 2 : ℝ)) * B1 ≤ 27 * (s⁻¹) ^ (3 : ℕ) * B1 :=
      mul_le_mul_of_nonneg_right h52 hB1
    have e2 : Real.rpow (s / 3) (-(5 / 2 : ℝ)) * B2 ≤ 27 * (s⁻¹) ^ (3 : ℕ) * B2 :=
      mul_le_mul_of_nonneg_right h52 hB2
    have e3 : Real.rpow (s / 3) (-3 : ℝ) * B3 = 27 * (s⁻¹) ^ (3 : ℕ) * B3 := by
      rw [h3]
    linarith only [e1, e2, e3]
  have hinner : (s / 3)⁻¹ * ET +
      (Real.rpow (s / 3) (-(5 / 2 : ℝ)) * B1 + Real.rpow (s / 3) (-(5 / 2 : ℝ)) * B2 +
        Real.rpow (s / 3) (-3 : ℝ) * B3) * G ≤
      3 * s⁻¹ * ET + 27 * (s⁻¹) ^ (3 : ℕ) * ((B1 + B2 + B3) * G) := by
    have hinv : (s / 3)⁻¹ = 3 * s⁻¹ := by field_simp
    have hmul := mul_le_mul_of_nonneg_right hforce hG
    rw [hinv]
    linarith only [hmul]
  have hinnernn : (0 : ℝ) ≤ 3 * s⁻¹ * ET + 27 * (s⁻¹) ^ (3 : ℕ) * ((B1 + B2 + B3) * G) := by
    have h1 : (0 : ℝ) ≤ 3 * s⁻¹ * ET := by positivity
    have h2 : (0 : ℝ) ≤ 27 * (s⁻¹) ^ (3 : ℕ) * ((B1 + B2 + B3) * G) := by
      have hb : (0 : ℝ) ≤ B1 + B2 + B3 := by linarith only [hB1, hB2, hB3]
      have h3 : (0 : ℝ) ≤ (B1 + B2 + B3) * G := mul_nonneg hb hG
      have h4 : (0 : ℝ) ≤ 27 * (s⁻¹) ^ (3 : ℕ) := by positivity
      exact mul_nonneg h4 h3
    linarith only [h1, h2]
  calc P * ((s / 3)⁻¹ * ET +
        (Real.rpow (s / 3) (-(5 / 2 : ℝ)) * B1 + Real.rpow (s / 3) (-(5 / 2 : ℝ)) * B2 +
          Real.rpow (s / 3) (-3 : ℝ) * B3) * G)
      ≤ P * (3 * s⁻¹ * ET + 27 * (s⁻¹) ^ (3 : ℕ) * ((B1 + B2 + B3) * G)) :=
        mul_le_mul_of_nonneg_left hinner hPnonneg
    _ ≤ 72 * (s⁻¹) ^ (3 : ℕ) *
          (3 * s⁻¹ * ET + 27 * (s⁻¹) ^ (3 : ℕ) * ((B1 + B2 + B3) * G)) :=
        mul_le_mul_of_nonneg_right hPle hinnernn
    _ = 216 * (s⁻¹) ^ (4 : ℕ) * ET + 1944 * (s⁻¹) ^ (6 : ℕ) * ((B1 + B2 + B3) * G) := by
        ring

/-! ## 3. `e.homogenization.L2.interior` at the re-cut slot -/

/-- **The interior `L²` estimate at the slot `(3s/4, s/3, s, 0)`.** -/
theorem coarseGraining_l2_thirdSlot_le [NeZero d] {Q : TriadicCube d}
    {a : Ch03.CoeffFamily d} {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    {g : Vec d → Vec d}
    (w : Ch03.CoarseGrainingComparisonDatum Q a (scalarComparator hsigma0) g)
    (z : H10Function (cubeSet Q))
    (hz : ∀ x, z.toH1Function.grad x = w.u.grad x - w.v.grad x)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hg : Ch03.ForceBesovRegularity Q s g) :
    sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => z.toH1Function.toFun x)) ≤
      3 * negNormBaseConst d * coarseGrainingP2Const d *
        (216 * (s⁻¹) ^ (4 : ℕ) *
            coarseGrainingEnergyTerm Q a (scalarComparator hsigma0) (s / 3) w.u +
          1944 * (s⁻¹) ^ (6 : ℕ) *
            coarseGrainingForceTerm Q a (scalarComparator hsigma0) (s / 3) s g) := by
  have ht : (0 : ℝ) < 3 * s / 8 := by linarith only [hs]
  have ht1 : 3 * s / 8 < 1 / 2 := by linarith only [hs1]
  have hr : (0 : ℝ) < s / 3 := by linarith only [hs]
  have hrt : s / 3 < 3 * s / 8 := by linarith only [hs]
  have hbase := coarseGraining_scaled_l2_le hsigma0 w z hz ht ht1 hr hrt
    (show s / 3 ≤ s by linarith only [hs]) hg (j := 0)
  rw [show (2 : ℝ) * (3 * s / 8) = 3 * s / 4 by ring] at hbase
  have henv := generalCoarseGrainingL2TwoExponentRHS_thirdSlot_le Q a
    (scalarComparator hsigma0) hs hs1 hg w.u
  have hCg : (0 : ℝ) ≤ coarseGrainingP2Const d := (coarseGrainingP2Const_pos d).le
  have hsplit : Ch03.generalCoarseGrainingL2TwoExponentRHS (coarseGrainingP2Const d) Q a
        (scalarComparator hsigma0) (3 * s / 4) (s / 3) s 0 g w.u =
      coarseGrainingP2Const d *
        Ch03.generalCoarseGrainingL2TwoExponentRHS 1 Q a (scalarComparator hsigma0)
          (3 * s / 4) (s / 3) s 0 g w.u :=
    generalCoarseGrainingL2TwoExponentRHS_eq_const_mul _ _ _ _ _ _ _ _ _ _
  set E : ℝ := 216 * (s⁻¹) ^ (4 : ℕ) *
      coarseGrainingEnergyTerm Q a (scalarComparator hsigma0) (s / 3) w.u +
    1944 * (s⁻¹) ^ (6 : ℕ) *
      coarseGrainingForceTerm Q a (scalarComparator hsigma0) (s / 3) s g with hEdef
  have hEnonneg : 0 ≤ E := by
    have h1 : 0 ≤ coarseGrainingEnergyTerm Q a (scalarComparator hsigma0) (s / 3) w.u :=
      coarseGrainingEnergyTerm_nonneg Q a (scalarComparator hsigma0) hr w.u
    have h2 : 0 ≤ coarseGrainingForceTerm Q a (scalarComparator hsigma0) (s / 3) s g := by
      rw [coarseGrainingForceTerm]
      exact mul_nonneg
        (coarseGrainingForceBracket_nonneg Q a (scalarComparator hsigma0) hr)
        (Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hg)
    have e1 : (0 : ℝ) ≤ 216 * (s⁻¹) ^ (4 : ℕ) *
        coarseGrainingEnergyTerm Q a (scalarComparator hsigma0) (s / 3) w.u := by
      have hc : (0 : ℝ) ≤ 216 * (s⁻¹) ^ (4 : ℕ) := by positivity
      exact mul_nonneg hc h1
    have e2 : (0 : ℝ) ≤ 1944 * (s⁻¹) ^ (6 : ℕ) *
        coarseGrainingForceTerm Q a (scalarComparator hsigma0) (s / 3) s g := by
      have hc : (0 : ℝ) ≤ 1944 * (s⁻¹) ^ (6 : ℕ) := by positivity
      exact mul_nonneg hc h2
    rw [hEdef]
    linarith only [e1, e2]
  have hRHSle : Ch03.generalCoarseGrainingL2TwoExponentRHS (coarseGrainingP2Const d) Q a
      (scalarComparator hsigma0) (3 * s / 4) (s / 3) s 0 g w.u ≤
      coarseGrainingP2Const d * E := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left henv hCg
  have hfac : negNormBaseConst d *
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 * s / 8)))⁻¹) ≤
      3 * negNormBaseConst d := by
    have h := mul_le_mul_of_nonneg_left (negNormSqrtFactor_slot_le_three hs1)
      (negNormBaseConst_pos d).le
    linarith only [h]
  have hfacpos : (0 : ℝ) ≤ negNormBaseConst d *
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 * s / 8)))⁻¹) :=
    mul_nonneg (negNormBaseConst_pos d).le (Real.sqrt_nonneg _)
  have hprod : (0 : ℝ) ≤ coarseGrainingP2Const d * E := mul_nonneg hCg hEnonneg
  calc sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => z.toH1Function.toFun x))
      ≤ negNormBaseConst d *
          Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 * s / 8)))⁻¹) *
        Ch03.generalCoarseGrainingL2TwoExponentRHS (coarseGrainingP2Const d) Q a
          (scalarComparator hsigma0) (3 * s / 4) (s / 3) s 0 g w.u := hbase
    _ ≤ negNormBaseConst d *
          Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - 3 * s / 8)))⁻¹) *
        (coarseGrainingP2Const d * E) :=
        mul_le_mul_of_nonneg_left hRHSle hfacpos
    _ ≤ 3 * negNormBaseConst d * (coarseGrainingP2Const d * E) :=
        mul_le_mul_of_nonneg_right hfac hprod
    _ = 3 * negNormBaseConst d * coarseGrainingP2Const d * E := by ring

/-- The re-cut slot estimate, entered at the equation alone. -/
theorem coarseGraining_l2_thirdSlot_le_of_isForcedEquation [NeZero d] {Q : TriadicCube d}
    {a : Ch03.CoeffFamily d} {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : Ch03.IsForcedEquation Q a u g) (hgL2 : MemVectorL2 (openCubeSet Q) g)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hg : Ch03.ForceBesovRegularity Q s g) :
    sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) fun x =>
          (replacementDefect (scalarComparator hsigma0) u hgL2).toH1Function.toFun x) ≤
      3 * negNormBaseConst d * coarseGrainingP2Const d *
        (216 * (s⁻¹) ^ (4 : ℕ) *
            coarseGrainingEnergyTerm Q a (scalarComparator hsigma0) (s / 3) u +
          1944 * (s⁻¹) ^ (6 : ℕ) *
            coarseGrainingForceTerm Q a (scalarComparator hsigma0) (s / 3) s g) :=
  coarseGraining_l2_thirdSlot_le hsigma0
    (coarseGrainingDatum a (scalarComparator hsigma0) hu hgL2)
    (replacementDefect (scalarComparator hsigma0) u hgL2)
    (replacementDefect_grad a (scalarComparator hsigma0) hu hgL2) hs hs1 hg

/-! ## 4. The harmonic display at the re-cut slot -/

theorem coarseGraining_l2_thirdSlot_harmonic_le [NeZero d] {Q : TriadicCube d}
    {a : Ch03.CoeffFamily d} {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : Ch03.IsForcedEquation Q a u g)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hg : Ch03.ForceBesovRegularity Q s g) :
    sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) fun x =>
          (harmonicCorrector (scalarComparator hsigma0) u).toH1Function.toFun x) ≤
      3 * negNormBaseConst d * coarseGrainingP2Const d *
          (216 * (s⁻¹) ^ (4 : ℕ) *
              coarseGrainingEnergyTerm Q a (scalarComparator hsigma0) (s / 3) u +
            1944 * (s⁻¹) ^ (6 : ℕ) *
              coarseGrainingForceTerm Q a (scalarComparator hsigma0) (s / 3) s g) +
        2 * negNormBaseConst d * negativeToL2Factor s *
          (Real.sqrt (Fintype.card (Fin d) : ℝ) *
            Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) := by
  have hgL2 : MemVectorL2 (openCubeSet Q) g :=
    memVectorL2_openCubeSet_of_forceBesovRegularity hg
  set a0 : Ch03.ConstantCoeffMatrix d := scalarComparator hsigma0 with ha0
  have hmemG : MeasureTheory.MemLp
      (fun x => (dirichletCorrector a0 u hgL2).toH1Function.toFun x) 2
      (normalizedCubeMeasure Q) :=
    memLp_scalar_normalizedCubeMeasure (dirichletCorrector a0 u hgL2).toH1Function.memL2
  have hmemW : MeasureTheory.MemLp
      (fun x => (replacementCorrection a0 u hgL2).toH1Function.toFun x) 2
      (normalizedCubeMeasure Q) :=
    memLp_scalar_normalizedCubeMeasure
      (replacementCorrection a0 u hgL2).toH1Function.memL2
  have htri := cubeLpNorm_two_sub_le Q
    (f := fun x => (harmonicCorrector a0 u).toH1Function.toFun x)
    (g := fun x => (dirichletCorrector a0 u hgL2).toH1Function.toFun x)
    (h := fun x => (replacementCorrection a0 u hgL2).toH1Function.toFun x)
    (fun x => by
      simp only [replacementCorrection_toFun]
      ring) hmemG hmemW
  have hweight : (0 : ℝ) ≤ cubeBesovScaleWeight (1 : ℝ) Q :=
    cubeBesovScaleWeight_nonneg (1 : ℝ) Q
  have hsplit : sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
      cubeLpNorm Q (2 : ℝ≥0∞) fun x =>
        (harmonicCorrector a0 u).toH1Function.toFun x) ≤
      sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞) fun x =>
            (dirichletCorrector a0 u hgL2).toH1Function.toFun x) +
        sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞) fun x =>
            (replacementCorrection a0 u hgL2).toH1Function.toFun x) := by
    have hinner := mul_le_mul_of_nonneg_left htri hweight
    have houter := mul_le_mul_of_nonneg_left hinner hsigma0.le
    have hring : sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
        (cubeLpNorm Q (2 : ℝ≥0∞) (fun x =>
            (dirichletCorrector a0 u hgL2).toH1Function.toFun x) +
          cubeLpNorm Q (2 : ℝ≥0∞) fun x =>
            (replacementCorrection a0 u hgL2).toH1Function.toFun x)) =
        sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
            cubeLpNorm Q (2 : ℝ≥0∞) fun x =>
              (dirichletCorrector a0 u hgL2).toH1Function.toFun x) +
          sigma0 * (cubeBesovScaleWeight (1 : ℝ) Q *
            cubeLpNorm Q (2 : ℝ≥0∞) fun x =>
              (replacementCorrection a0 u hgL2).toH1Function.toFun x) := by ring
    rw [hring] at houter
    exact houter
  have hmain := coarseGraining_l2_thirdSlot_le_of_isForcedEquation hsigma0 hu hgL2 hs hs1 hg
  rw [replacementDefect] at hmain
  rw [H10Function.toCubeSet_toH1Function_toFun] at hmain
  have hcorr := replacementCorrection_l2_le hsigma0 u hgL2 hs hs1 hg
  exact hsplit.trans (add_le_add hmain hcorr)

/-! ## 5. The interior clause's left-hand side, at the re-based family -/

/-- **The `x`-frame composition at the re-based family and the re-cut slot.**

* the slot index `r = s/3` (§2--§4),

so that both right-hand coarse-graining objects are read at the index `s/6`,
which is exactly the index the proved off-grid cap delivers. -/
theorem eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased [NeZero d] (M : ABKModel d)
    (L : ℤ) (omega : Cutoff.CutoffSample d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {n m : ℤ} {x z : Vec d}
    (hsub : translateSet x (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m))
    (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hsol : Support.IsDirichletSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u hdat g)
    (hgL2 : MemLp g 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
    (v : H1Function ((fun y => x + y) '' openCubeSet (originCube d n)))
    (w : H10Function ((fun y => x + y) '' openCubeSet (originCube d n)))
    (hharm : Support.IsWeaklyHarmonicOn
      ((fun y => x + y) '' openCubeSet (originCube d n)) v)
    (hval : ∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y)
    (hgrad : ∀ y, v.grad y = u.grad y - w.toH1Function.grad y)
    {sigma0 : ℝ} (hsigma0 : 0 < sigma0) :
    sigma0 * (cubeBesovScaleWeight (1 : ℝ) (originCube d n) *
        (eLpNorm (fun y => u.toFun y - v.toFun y) 2
          (Support.normalizedVolumeMeasureOn
            ((fun y => x + y) '' openCubeSet (originCube d n)))).toReal) ≤
      3 * negNormBaseConst d * coarseGrainingP2Const d *
          (216 * (s⁻¹) ^ (4 : ℕ) *
              coarseGrainingEnergyTerm (originCube d n)
                (parentRebasedFamily M L (n + 2) x z omega) (scalarComparator hsigma0)
                (s / 3)
                (H1Function.untranslate x
                  (u.restrict (isOpen_translateSet_openCubeSet x n) hsub)) +
            1944 * (s⁻¹) ^ (6 : ℕ) *
              coarseGrainingForceTerm (originCube d n)
                (parentRebasedFamily M L (n + 2) x z omega) (scalarComparator hsigma0)
                (s / 3) s (fun y => -g (y + x))) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
          Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          (Support.normalizedGagliardoESeminormOn
            ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal := by
  have hsubimg : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m) := by
    rw [image_add_eq_translateSet x (openCubeSet (originCube d n))]
    exact hsub
  have hgL2child := memLp_two_child_of_clause_iv hsubimg hgL2
  have hgWchild := memLp_two_gagliardo_child_of_clause_iv hsubimg hgW
  have hforce : Ch03.ForceBesovRegularity (originCube d n) s (fun y => -g (y + x)) :=
    forceBesovRegularity_translated_neg (originCube d n) hs hs1 hgL2child hgWchild
  have heq := isForcedEquation_parentRebasedFamily (k := n + 2) M L x z omega hsub hsol.2
  have hmain := coarseGraining_l2_thirdSlot_harmonic_le hsigma0 heq hs hs1 hforce
  have hlhs : cubeLpNorm (originCube d n) (2 : ℝ≥0∞)
      (fun y =>
        (harmonicCorrector (scalarComparator hsigma0)
          (H1Function.untranslate x
            (u.restrict (isOpen_translateSet_openCubeSet x n) hsub))).toH1Function.toFun
          y) =
      (eLpNorm (fun y => u.toFun y - v.toFun y) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => x + y) '' openCubeSet (originCube d n)))).toReal := by
    show (eLpNorm _ (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d n))).toReal = _
    exact congrArg ENNReal.toReal
      (eLpNorm_sub_weaklyHarmonic_eq_harmonicCorrector hsigma0
        (image_add_eq_translateSet x (openCubeSet (originCube d n))) hsub u v w hharm
        hval hgrad).symm
  exact hlhs ▸ (hmain.trans (add_le_add le_rfl
    (correctionLeg_le_anchorGagliardo n hs hs1 hgL2child hgWchild)))

end

end Algsuperdiff.Section4.Provider.ExcessDecay
