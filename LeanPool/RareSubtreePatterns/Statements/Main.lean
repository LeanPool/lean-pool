/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Setup.Marks
public import LeanPool.RareSubtreePatterns.PlaneTree.Patterns

/-!
# Statements of the four Introduction theorems (statement level)

The propositions `PoissonApproximationStatement` (Theorem 1.1), `PoissonApproximation2Statement`
(Theorem 1.2), `MaxStringStatement` (Theorem 1.3) and `MaxLeafHeightStatement` (Theorem 1.4),
with their auxiliary definitions `cB`, `tStar`, `tStarStar`, `twoPointSet`,
`TwoPointLocalization` and `LatticeGumbel`, are defined in `PoissonDeclumping.Statements.Defs`,
which originate in the upstream statement contract. The phase refinement is strengthened here
to nontrivial filters of admissible sizes. They are propositions, not theorems;
`PoissonDeclumping.MainTheorems` proves them. This module re-exports them under its historical name.

All limits run along admissible sizes through `admissibleSizes μ`. Periodic offspring laws are
included (no aperiodicity hypothesis).
-/
