/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.JoinedCollar
public import LeanPool.GraphMinor.GM12.Section4CollarRadius

/-!
# Joining compatible inner and outer collars

The joined collar gives the three nested discs in XII (4.3), claim (7), a common radius coordinate.
-/

public section

namespace GraphMinor.GM12

export Surface (exists_joined_collar_coordinates)

end GraphMinor.GM12
