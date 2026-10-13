/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.TwoTermOrlicz

/-!
# InductionState

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Section3.inductionState
    {d : ℕ} (M : ABKModel d) (m0 : ℤ)
    (E : {E : ℝ // 1 ≤ E}) : Prop :=
  (∀ m : ℤ, m ≤ m0 →
      (1 / 4 : ℝ) *
          max
            (Disorder.cstar M * M.gamma⁻¹ *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
            (M.nu ^ 2)
        ≤ (Annealed.sigmaBar M m : ℝ) ^ 2 ∧
      (Annealed.sigmaBar M m : ℝ) ^ 2
        ≤ 4 *
          max
            (Disorder.cstar M * M.gamma⁻¹ *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
            (M.nu ^ 2)) ∧
    ∀ m : ℤ, m ≤ m0 →
      ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
        Probability.IsTwoTermBigOWith
          (Cutoff.cutoffSampleLaw M).toMeasure
          (HCPolySupport.IndependentSums.gammaSigma 2)
          (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M m
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
          ((s⁻¹) ^ 2 *
            Real.exp
              (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))
-- FROZEN-STATEMENT-END
