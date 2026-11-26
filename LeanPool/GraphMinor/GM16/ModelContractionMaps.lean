/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.Basic

/-!
# The contraction realizing a minor model

The vertex and edge equivalences of the contraction in XVI (4.2), page 53, retain the maps of
the given minor model.
-/

public section

namespace GraphMinor.GM16

export GraphMinor (exists_contraction_realizing_model)

end GraphMinor.GM16
