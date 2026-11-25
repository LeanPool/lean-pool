/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.DiscBoundaryHomeomorphism
public import LeanPool.GraphMinor.GM16.ProperDiscCoordinates

/-!
# Extending homeomorphisms of disc boundaries

Extending ordered boundary maps to discs in the proper arrangement of XVI (7.2).
-/

public section

namespace GraphMinor.GM16

export GM14 (exists_disc_extension_of_bd_homeo
  exists_angles_of_isClockwiseSeq)

end GraphMinor.GM16
