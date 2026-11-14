/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.LIHLocalSigma
public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.SequenceLaw
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm
public import Mathlib.Probability.Independence.Basic

/-!
# ShellLawJ1

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Elementwise

-- FROZEN-STATEMENT-BEGIN
/-- ABK26 (J1): the zero shell is integrable and mean-zero at
every point, invariant in law under every real translation, and has range of
dependence `sqrt d` for the integral-generated local sigma-fields `F(U)` of
the governing homogenization-manuscript convention. -/
structure Algsuperdiff.Frozen.Assumptions.ShellLawJ1
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d)) : Prop where
  integrable : ∀ x : Vec d,
    Integrable
      (fun F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d ↦ F 0 x)
      P.toMeasure
  mean_zero : ∀ x : Vec d,
    ∫ F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d, F 0 x ∂P.toMeasure = 0
  stationary : ∀ z : Vec d,
    Measure.map
        (Algsuperdiff.Frozen.Assumptions.ShellField.translate z)
        (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw P).toMeasure =
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw P).toMeasure
  range_dependence : ∀ (U V : Set (Vec d)),
    MeasurableSet U → MeasurableSet V →
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
        Real.sqrt (d : ℝ) ≤ HCPolySupport.Book.Ch02.vecNorm (x - y)) →
      Indep
        (Algsuperdiff.Frozen.Assumptions.ShellField.lihLocalSigma U)
        (Algsuperdiff.Frozen.Assumptions.ShellField.lihLocalSigma V)
        (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw P).toMeasure
-- FROZEN-STATEMENT-END
