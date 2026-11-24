/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.BridgeFacts
public import LeanPool.GraphMinor.GM15.Section7
public import LeanPool.GraphMinor.GM16.ProperArrangement

/-!
# Bridge intersections in the local arrangement assembly

These graph facts supply Claim (1) and Claim (2) of XV (7.7), pages 139–140.
-/

public section

namespace GraphMinor.GM16

export GM14 (isBridge_of_component exists_bridge_of_mem_vertexSet exists_bridge_of_mem_edgeSet
  isBridge_disjoint_edgeSet isBridge_vertexSet_eq_of_inter)

end GraphMinor.GM16
