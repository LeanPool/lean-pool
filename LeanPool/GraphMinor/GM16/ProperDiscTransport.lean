/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.DiscArrangement
public import LeanPool.GraphMinor.GM16.ProperDiscExtension

/-!
# Transporting a disc arrangement to a surface

Matching boundary points and transporting the disc arrangement in XVI (7.2).
-/

public section

namespace GraphMinor.GM16

export GM14 (exists_bd_homeo_of_agreesWithOArcHomeo
  exists_surface_disc_arrangement_of_isDiscArrangement)

end GraphMinor.GM16
