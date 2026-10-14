/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.J2Observable
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# ShellLawJ2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- ABK26 (J2): the exact strict Gaussian tail for the three
weighted essential-`L∞` cube norms.  The qualitative `C^2`
regularity is already enforced by the shell carrier and is not repeated as a
hypothesis. -/
structure Algsuperdiff.Frozen.Assumptions.ShellLawJ2
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d)) : Prop where
  gaussian_tail : ∀ t : ℝ, 1 ≤ t →
    P.toMeasure
        {F | t < Algsuperdiff.Frozen.Assumptions.ShellField.j2Observable d (F 0)} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2)))
-- FROZEN-STATEMENT-END
