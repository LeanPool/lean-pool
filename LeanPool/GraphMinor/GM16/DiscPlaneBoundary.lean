/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Boundaries of plane discs

The closed domain of a Jordan curve is the complement of its outer
side. Its frontier is therefore that curve. This identifies the
intrinsic disc boundary with the frontier in the plane presentations
used in XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface

export Surface (complex_disc_frontier plane_disc_frontier)

end GraphMinor.GM16
