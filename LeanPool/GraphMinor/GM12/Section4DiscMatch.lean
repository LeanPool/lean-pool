/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscMatch
public import LeanPool.GraphMinor.GM12.Section4DiscTwist
public import LeanPool.GraphMinor.GM12.Section4JoinedCollars

/-!
# Matching nested discs and adjusting boundary points

Homeomorphisms that carry nested discs and adjust their boundaries, used in XII (4.3), claim (7).
-/

public section

namespace GraphMinor.GM12

export Surface (exists_disc_onto_nested exists_boundary_twist)

end GraphMinor.GM12
