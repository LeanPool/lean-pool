/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Vocabulary

/-!
# ResponseJSensitivityUnconditional

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

open Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional
  renaming responseJ_sensitivity_unconditional → provider_responseJ_sensitivity


/-- Unconditional four-term sensitivity estimate for the response functional. -/
-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.responseJ_sensitivity_unconditional {d : ℕ}
    (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d) (s t μ σ0 : ℝ) (e : Vec d),
      0 < s → s ≤ 1 / 4 → 0 < t → t ≤ 1 / 4 → 0 < μ → 0 < σ0 → vecNorm e = 1 →
      responseJ (cubeDomain (originCube d 0))
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1)
          ((Real.sqrt (μ * σ0))⁻¹ • e) (Real.sqrt (μ * σ0) • e)
        ≤ C * μ⁻¹ * Real.rpow
            (1 + h.gradientW1Infinity *
              (unitCubeLambda s (.finite 2) a)⁻¹)
            (2 * t / (1 - 2 * s)) *
            (unitCubeHomogenizationError t (.finite 2) (.finite 2)
              a (scalarMatrix σ0)) ^ 2 +
          C * μ⁻¹ * σ0 *
            (unitCubeLambda s (.finite 2) a)⁻¹ *
            Real.rpow
              (1 + h.gradientW1Infinity *
                (unitCubeLambda s (.finite 2) a)⁻¹)
              (2 * s / (1 - 2 * s)) *
            (σ0⁻¹ ^ 2 * h.valueL2 ^ 2 + (μ - 1) ^ 2) +
          C * μ⁻¹ ^ 2 * σ0⁻¹ ^ 2 * h.gradientW1Infinity ^ 2 +
          C * min 1 (h.gradientW1Infinity *
            (unitCubeLambda s (.finite 2) a)⁻¹) ^ 2
-- FROZEN-STATEMENT-END
    := by
  exact
    provider_responseJ_sensitivity
    dimension
