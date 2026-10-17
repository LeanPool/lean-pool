/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Vocabulary

/-!
# LambdaSensitivityUnconditional

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

/-- Unconditional sensitivity of `lambda_{t,q}`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.lambda_sensitivity_unconditional {d : ℕ}
    (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d) (s t : ℝ) (q : Book.Ch02.MultiscaleExponent),
      0 < s → s ≤ 1 / 4 → 0 < t → t ≤ 1 / 4 → q.IsAdmissible →
      (unitCubeLambda t q
        (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1))⁻¹
        ≤ 6 * Real.rpow
          (1 + C * h.gradientW1Infinity *
            (unitCubeLambda s (.finite 2) a)⁻¹)
          (2 * t / (1 - 2 * s)) *
          (unitCubeLambda t q a)⁻¹
-- FROZEN-STATEMENT-END
    := by
  exact
    Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.lambda_sensitivity_unconditional
    dimension
