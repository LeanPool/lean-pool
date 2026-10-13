/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Assumptions.ShellLawJ3
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Assumptions.ShellLawJ4
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Assumptions.ShellLawPrefix

/-!
# Model

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The standing ABK model

This file packages precisely the paper data used throughout Section 3.

## Main definitions

* `Algsuperdiff.Section3.ABKModel`: molecular diffusivity, the canonical shell
  sequence law, and the exact prefix and (J1)--(J4) assumptions of ABK26.

## References

* ABK26.
-/

namespace Algsuperdiff.Section3

open MeasureTheory

/-- The complete standing probabilistic model of ABK26.

The dimension is an external parameter.  Its lower bound and the complete
admissible range for `gamma` belong exactly to `prefix`; this aggregate adds
only molecular diffusivity positivity and the four separately frozen shell-law
assumptions. The shell carrier enforces qualitative C² regularity, which
strengthens the paper's local C^{1,1} assumption. -/
structure ABKModel (d : ℕ) where
  /-- The molecular diffusivity from ABK26. -/
  nu : ℝ
  /-- Molecular diffusivity is strictly positive. -/
  nu_pos : 0 < nu
  /-- The scale parameter from ABK26. -/
  gamma : ℝ
  /-- The canonical probability law of the bi-infinite shell sequence. -/
  P : ProbabilityMeasure (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d)
  /-- The exact dimension, scale, independence, and marginal-scaling prefix. -/
  shellPrefix : Algsuperdiff.Frozen.Assumptions.ShellLawPrefix d gamma P
  /-- The exact mean-zero, stationarity, and finite-range assumption (J1). -/
  J1 : Algsuperdiff.Frozen.Assumptions.ShellLawJ1 d P
  /-- The Gaussian-tail assumption (J2), with C² regularity in the shell carrier. -/
  J2 : Algsuperdiff.Frozen.Assumptions.ShellLawJ2 d P
  /-- The exact joint hyperoctahedral and negation invariance assumption (J3). -/
  J3 : Algsuperdiff.Frozen.Assumptions.ShellLawJ3 d P
  /-- The exact stationary potential-projection nondegeneracy assumption (J4). -/
  J4 : Algsuperdiff.Frozen.Assumptions.ShellLawJ4 d P shellPrefix.dimension J1 J2

end Algsuperdiff.Section3
