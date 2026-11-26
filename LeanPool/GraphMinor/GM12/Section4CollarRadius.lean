/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.JoinedCollar

/-!
# Radius coordinates for joining two collars

The outer-annulus radius change used in the collar construction for XII (4.3), claim (7).
-/

public section

namespace GraphMinor.GM12

export Surface (collarOuterStep continuous_collarOuterStep collarOuterStep_norm
  collarOuterStep_injOn collarOuterStep_two exists_collarOuterStep_preimage)

end GraphMinor.GM12
