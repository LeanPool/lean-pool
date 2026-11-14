/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Induction.InductionStepAssembly

/-!
# InductionStep

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.induction_step
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        Algsuperdiff.Frozen.Section3.inductionState M m E
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.Induction.induction_step_provided d
