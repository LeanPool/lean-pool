/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Assumptions.ShellFieldCompactOpenTopology
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# ShellFieldBorelMeasurableSpace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

-- FROZEN-STATEMENT-BEGIN
/-- The Borel measurable structure induced by the shell's compact-open topology. -/
@[instance_reducible] noncomputable def
    Algsuperdiff.Frozen.Assumptions.shellFieldBorelMeasurableSpace
    (d : ℕ) :
    MeasurableSpace
      (Algsuperdiff.Frozen.Assumptions.ShellField d) :=
  @borel
    (Algsuperdiff.Frozen.Assumptions.ShellField d)
    (Algsuperdiff.Frozen.Assumptions.shellFieldCompactOpenTopology d)
-- FROZEN-STATEMENT-END
