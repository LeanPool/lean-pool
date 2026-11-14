/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.SequenceLaw
public import Mathlib.Probability.Independence.Basic

/-!
# ShellLawPrefix

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
/-- The `nu`-free shell-law prefix from ABK26:
the paper-wide dimension and scaling parameters, mutual independence of all
shells, and the exact marginal scaling law under the canonical sequence law.
Molecular diffusivity `nu > 0` is deferred to the
cutoff/coefficient parameter surface.  Antisymmetry and
qualitative `C^2` regularity hold by the `ShellField` carrier itself. -/
structure Algsuperdiff.Frozen.Assumptions.ShellLawPrefix
    (d : ℕ) (gamma : ℝ)
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d)) : Prop where
  dimension : 2 ≤ d
  gamma_pos : 0 < gamma
  gamma_le_quarter : gamma ≤ (1 : ℝ) / 4
  independent :
    iIndepFun
      (fun k : ℤ ↦ fun F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d ↦ F k)
      P.toMeasure
  marginal_scaling : ∀ k : ℤ,
    Algsuperdiff.Frozen.Assumptions.ShellField.shellMarginalLaw P k =
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw P).map
        (Algsuperdiff.Frozen.Assumptions.ShellField.triadicScale
          gamma k)
-- FROZEN-STATEMENT-END
