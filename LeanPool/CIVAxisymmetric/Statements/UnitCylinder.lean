/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Unit Cylinder

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The unit parabolic cylinder `Q = B(1) × (-1, 0)` on which the solutions of
arXiv:2609.20803 live; its upper time endpoint `t = 0` is the blow-up time. -/
@[expose] def unitCylinder : Set ParabolicPoint := spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0)

end CIV
