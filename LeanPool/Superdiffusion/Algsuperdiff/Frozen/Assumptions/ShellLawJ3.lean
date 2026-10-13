/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.SequenceLaw

/-!
# ShellLawJ3

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- ABK26 (J3): the joint law of the entire shell sequence is
invariant under every hyperoctahedral conjugation and, separately, under
whole-sequence negation. -/
structure Algsuperdiff.Frozen.Assumptions.ShellLawJ3
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d)) : Prop where
  hyperoctahedral : ∀ (R : Mat d)
      (hR : HCPolySupport.IsSignedPermutationMatrix R),
    P.map
        (Algsuperdiff.Frozen.Assumptions.ShellField.rotateSequence
          R hR) = P
  negation :
    P.map
        (Algsuperdiff.Frozen.Assumptions.ShellField.negateSequence
          (d := d)) = P
-- FROZEN-STATEMENT-END
