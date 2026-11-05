/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Vocabulary

/-!
# ResponseJSensitivity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

/-- Conditional sensitivity of the response functional. -/
-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.responseJ_sensitivity {d : ℕ}
    (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d),
      h.gradientW1Infinity ≤ C⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a →
      ∀ (p q : Vec d) (δ : ℝ), 0 < δ → δ ≤ 1 →
      responseJ (cubeDomain (originCube d 0))
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1) p q
        ≤ (1 + δ + C * h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            responseJ (cubeDomain (originCube d 0)) a p q +
          C * δ⁻¹ * (vecNormSq p * h.w1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ +
            |vecDot p q| * h.gradientW1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ^ 2)
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.Sensitivity.Provider.Response.responseJ_sensitivity dimension
