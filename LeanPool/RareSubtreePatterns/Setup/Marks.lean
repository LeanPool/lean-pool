/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Setup.Walk
public import LeanPool.RareSubtreePatterns.Declumping.Probability

/-!
# Marks, cutoffs and Assumptions (M), (S), (C)

Source lines 189–300. A "`{0,1}`-valued function on plane trees" is a predicate
`G : PlaneTree → Prop` (its indicator is `1` exactly on the marked trees). A sequence
`(G_k)` of marks is `G : ℕ → PlaneTree → Prop`; `k : ℕ → ℕ` is the sequence `(k_n)` and
`M : ℕ → ℕ` the cutoff sequence. All limits run along the *admissible* sizes `n`
(those with `P(|𝒯| = n) > 0`), through the filter `admissibleSizes μ`; the actual size `n`,
not an index of a subsequence, appears in `n π_n` and in `M_n / n`.

Conditional probabilities use mathlib's `ProbabilityTheory.cond`, which is `0` when the
conditioning event is null; this is only relevant on subsequences with `π_n = 0`, which the
paper excludes ("we work along subsequences on which the marking probability is positive").

The definitions (the discrete σ-algebra on `List PlaneTree`, `admissibleSizes`, `IsCutoff`,
`markProb`, `uniformFringeLaw`, `Microscopic`, `Skeleton`, `StructuralMicroscopic`, `pairProb`,
`NonClustering`, `markedCountLaw`) are in `PoissonDeclumping.Statements.Defs`, whose text is
shared verbatim with `Challenge.lean`; this module only re-exports them under its historical name.
-/
