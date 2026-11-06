/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.MainTheorems
public import LeanPool.RareSubtreePatterns.Bridge.EndpointSmoothing
public import LeanPool.RareSubtreePatterns.Extremes.MaxString
public import LeanPool.RareSubtreePatterns.Extremes.MaxLeafHeightFirstOrder

/-!
# The four Introduction theorems

Final composition. Each theorem has exactly the type of the independently reviewed
statement-level proposition of `Statements/Main.lean`, and its proof retains the paper's stated
marking and cutoff hypotheses together with its standing assumption `(H_α)` (`InStableDomain μ` /
  `StableDomain μ α a`), which is
part of the statement.

* `Bridge.tendsto_errorB3` (Proposition 4.8, with Lemma 4.9) closes the last Chen–Stein error term
  for the bridge, for periodic laws as well as aperiodic ones (see
    `MANUSCRIPT_RECOMMENDATIONS.md`, R4);
* `Bridge.poissonApproximationStatement_of_b3` and `Bridge.poissonApproximation2Statement_of_b3`
  assemble Theorems 1.1 and 1.2;
* `Extremes.maxString_of` and `MaxLeafHeight.maxLeafHeight_of` assemble Theorems 1.3 and 1.4;
* the stable random-walk toolbox needed throughout is *derived* from `StableDomain`
  (`Stable.stableToolkit`) inside the bridge lemmas for each `μ`, not assumed.
-/

@[expose] public section

namespace PoissonDeclumping

/-- The Chen–Stein error term `b_3` of the bridge vanishes (Proposition 4.8): the hypothesis form
`ErrorB3Statement` used by the assembly lemmas. -/
theorem errorB3Statement : Bridge.ErrorB3Statement :=
  fun _μ _α _a hT _G _k _M hM _hmic hbd f hf => Bridge.tendsto_errorB3 hT hM hbd f hf

/-- **Theorem 1.1** (`thm:PoissonApproximation`): Poisson approximation and law of large
numbers for marked fringe subtrees, under (M) and (C). -/
theorem poissonApproximation : PoissonApproximationStatement :=
  Bridge.poissonApproximationStatement_of_b3 errorB3Statement

/-- **Theorem 1.2** (`thm:PoissonApproximation2`): root declumping. -/
theorem poissonApproximation2 : PoissonApproximation2Statement :=
  Bridge.poissonApproximation2Statement_of_b3 errorB3Statement

/-- **Theorem 1.3** (`thm:max_string`): the maximal complete non-fringe `r`-ary height. -/
theorem maxString : MaxStringStatement :=
  Extremes.maxString_of poissonApproximation poissonApproximation2

/-- **Theorem 1.4** (`thm:max_lh`): the maximum leaf-height. -/
theorem maxLeafHeight : MaxLeafHeightStatement :=
  MaxLeafHeight.maxLeafHeight_of poissonApproximation poissonApproximation2 maxString

end PoissonDeclumping
