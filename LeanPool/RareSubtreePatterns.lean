/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.MainTheorems
public import LeanPool.RareSubtreePatterns.MainConsequences
public import LeanPool.RareSubtreePatterns.Stable.DensityLaw
public import LeanPool.RareSubtreePatterns.Stable.MaximalTightness
public import LeanPool.RareSubtreePatterns.Examples.BinomialWalk
public import LeanPool.RareSubtreePatterns.Examples.SimpleWalk

/-!
# Rare subtree patterns in conditioned Bienaymé trees

Source: arxiv:2607.22291v1, url:https://github.com/igor-kortchemski/rare-subtree-patterns
Authors: Igor Kortchemski
Status: verified
Main declarations: `PoissonDeclumping.poissonApproximation`,
  `PoissonDeclumping.poissonApproximation2`, `PoissonDeclumping.maxString`,
  `PoissonDeclumping.maxLeafHeight`
Tags: probability, branching-processes, random-trees, poisson-approximation
MSC: 60J80, 60G50, 05C05, 05C80
-/

/-!
# Rare subtree patterns in conditioned Bienaymé trees

The four introduction theorems of Kortchemski and Vetter, with the
critical stable-domain, marking, cutoff and non-clustering hypotheses.
The library also provides stable-law and lattice local-limit estimates,
Chen–Stein approximation, tree coding and extreme-height consequences.
-/
