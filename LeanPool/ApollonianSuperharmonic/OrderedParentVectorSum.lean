/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.IncomingSuperbasisRelation
public import Mathlib.Init


/-!
# OrderedParentVectorSum

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace OrderedParentVectorSum

/-- Shared incoming identity for OrderedParentVectorSum. -/
theorem incoming :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (BandVectors.1
            (q 1) (q 0) + BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0) = 0) ) := by
  classical
  intro q cfg
  simpa [Fin.sum_univ_succ, add_assoc] using (IncomingSuperbasisRelation q cfg.proper).1

end OrderedParentVectorSum
end ApollonianSuperharmonic

end
