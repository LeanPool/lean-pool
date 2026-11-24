/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Thinning
import LeanPool.GraphMinor.GM19.Section2Proved
public import LeanPool.GraphMinor.GM19.FrameMove

import LeanPool.GraphMinor.GM19.Section15b

/-!
# Graph Minors XIX: proved deductions from Thinning

The deductions use existing proofs after the preliminary geometry has been defined.
-/

public section
namespace GraphMinor.GM19
open Set Topology GraphMinor.Surface
universe w

/-- Graph Minors XIX, (2.1), using the proved colouring and topology results. -/
theorem gm19Theorem21' :
    GM20.GM19Theorem21Statement.{w} :=
  gm19Theorem21

end GraphMinor.GM19
