/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial

/-!
# Spatial Gradient

Supporting estimates for the Navier–Stokes development.
-/

public section

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The classical coordinate gradient expression associated with `rem:gradient-datum`. -/
@[expose]
def spatialGradient (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (i : Fin 3) : Vec3 :=
  fun j => spatialPartial (fun w => u w i) j z

end CKN
