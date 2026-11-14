/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Vocabulary

/-!
# BigLambdaSensitivityAtDelta

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

/-- Free-`δ` sensitivity of `Lambda_{s,2}`, stated on the one-sided `δ`
range. -/
-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.bigLambda_sensitivity_at_delta {d : ℕ}
    (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d),
      h.gradientW1Infinity ≤ C⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a →
      ∀ (s δ : ℝ), 0 < s → s < 3 / 8 → 0 < δ → δ ≤ 1 →
      unitCubeBigLambda s (.finite 2)
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1)
        ≤ (1 + δ + C * h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            unitCubeBigLambda s (.finite 2) a +
          C * δ⁻¹ * (3 / 8 - s)⁻¹ * h.w1Infinity ^ 2 *
            (unitCubeLambda s (.finite 2) a)⁻¹
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.bigLambda_sensitivity_at_delta
    dimension
