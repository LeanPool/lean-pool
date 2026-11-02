/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Assumptions.ShellLawJ1
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Assumptions.ShellLawJ2
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.StationaryValueProjection

/-!
# ShellLawJ4

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Frozen.Assumptions.ShellField
  (zeroShellRegLaw_stationary_of_zeroShellLaw_stationary)

open HCPolySupport MeasureTheory



-- FROZEN-STATEMENT-BEGIN
/-- ABK26 (J4): one positive non-degeneracy constant, shared
by every unit vector, gives the exact stationary potential-corrector energy.
The stationarity and `L²` proofs consumed by the canonical corrector are derived
from (J1) and (J2), not added as J4 hypotheses. -/
structure Algsuperdiff.Frozen.Assumptions.ShellLawJ4
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d))
    (_dimension : 2 ≤ d)
    (hJ1 : Algsuperdiff.Frozen.Assumptions.ShellLawJ1 d P)
    (hJ2 : Algsuperdiff.Frozen.Assumptions.ShellLawJ2 d P) : Prop where
  nondegenerate : ∃ cstar : ℝ, 0 < cstar ∧
    ∀ e : {e : Vec d // HCPolySupport.Book.Ch02.vecNorm e = 1},
      ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector
          P
          (zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
              P hJ1.stationary)
          e.1
          (Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
            P hJ2.gaussian_tail e.1 e.2)‖ ^ 2 =
        cstar * Real.log 3
-- FROZEN-STATEMENT-END
