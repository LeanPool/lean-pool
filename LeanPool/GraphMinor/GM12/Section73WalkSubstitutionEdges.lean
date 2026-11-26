/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73WalkSubstitution

/-!
# Edge containment in a substituted walk

The circuit comparison in XII (7.3), Claim (1), page 262,
uses the old edges of each replaced spoke inside the lifted walk.
`exists_closed_walk_substitution_with_edge_sets` records these edges
alongside the length and point-set identities.
-/
