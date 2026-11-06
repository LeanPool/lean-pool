/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.PlaneTree.Countable

/-!
# Complete `r`-ary patterns, non-fringe embeddings and leaf-height

Definitions of Sections 1.3–1.4 and 2.1 of the paper (source lines 464–473, 525–531, 682):

* `completeTree r k` is the complete `r`-ary tree `H_{r,k}` of height `k`;
* `Embeds T' T` is the relation `T' ≺ T`: `T` is obtained from `T'` by grafting arbitrary
  plane trees onto the leaves of `T'`. Internal vertices of `T'` keep their exact number of
  children (this is *not* "choose some children");
* `maxCompleteHeight r T` is `H_r(T) = max {k ≥ 0 : ∃ u ∈ T, H_{r,k} ≺ T_u}`;
* `rootLeafHeight T` is `λ_∅(T)`, the distance from the root to the closest leaf descendant
  (zero for a leaf), and `leafHeight T = max_v λ_v(T)`.

All five are defined in `PoissonDeclumping.Statements.Defs` (namespace
`PoissonDeclumping.PlaneTree`), whose text is shared verbatim with `Challenge.lean`; this module
only re-exports them under its historical name.
-/
