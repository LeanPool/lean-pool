/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.PlaneTree.Countable

/-!
# Bienaymé trees: definitions

Section 2.1 of the paper (source lines 679–713). An offspring law is a probability mass
function `μ` on `ℕ`. The Bienaymé tree law gives a finite plane tree `T` the weight
`∏_{u ∈ T} μ_{k_u(T)}`. That the weights sum to one for a critical `μ` with `μ 1 ≠ 1`
(normalization, i.e. almost sure finiteness of the tree) is a theorem proved in
`PoissonDeclumping.Bienayme.Normalization`, not part of the definition.

The definitions `IsCritical`, `PlaneTree.weight`, `PlaneTree.bienayme`, `PlaneTree.Admissible`
and `PlaneTree.conditioned` are in `PoissonDeclumping.Statements.Defs`, whose text is shared
verbatim with `Challenge.lean`; this module only re-exports them under its historical name.
-/
