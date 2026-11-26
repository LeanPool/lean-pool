/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.DiscBoundaryHomeomorphism
public import LeanPool.GraphMinor.GM15.Section7
public import LeanPool.GraphMinor.GM16.ProperArrangement

/-!
# Disc coordinates for proper arrangements

Planar disc boundaries and increasing angle interpolation for XVI (7.2).
-/

public section

namespace GraphMinor.GM16

export GM14 (isInteriorPoint_euclideanPlane
  isClosedDisc_frontier_eq_discBd_euclideanPlane
  isClosedDisc_subBd_eq_discBd_euclideanPlane
  exists_strictMonoOn_interp
  exists_circle_homeo_matching_angles)

end GraphMinor.GM16
