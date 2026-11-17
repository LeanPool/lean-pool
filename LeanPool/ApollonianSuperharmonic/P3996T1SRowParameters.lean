/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex
public import LeanPool.ApollonianSuperharmonic.CircleCoordinates

-- [TABLET NODE: P3996T1SRowParameters]

/-!
# P3996T1SRowParameters

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A numerical $S$-row entry consists of a child slot $l\in\operatorname{Fin}3$,
a child sign and a source sign, two periodic subtile indices $X,Y$,
a Boolean recording whether $X$ is exterior, a quadruple $p$ of circle
coordinates, a parent slot $m\in\operatorname{Fin}3$, a rotation
$s\in\operatorname{Fin}4$, and three Gaussian integers $b,d,a$.
The last three numbers are respectively the child occurrence shift, the
right displacement, and the old-companion shift.
An entry has no assertions or geometric certificates.
-/
structure P3996T1SRowParameters where
-- BODY
  /-- The selected child slot in the signed decomposition. -/
  childSlot : Fin 3
  /-- The sign of the selected child occurrence. -/
  childSign : Bool
  /-- The sign of the source occurrence in the row. -/
  sourceSign : Bool
  /-- The literal periodic index of the child occurrence. -/
  childIndex : PeriodicSubtileIndex
  /-- The literal periodic index of its parent occurrence. -/
  parentIndex : PeriodicSubtileIndex
  /-- Whether the child occurrence occupies the exterior role in this row. -/
  childIsExterior : Bool
  /-- The fixed predecessor presentation prescribed by the row. -/
  predecessor : Fin 4 → CircleCoordinates
  /-- The parent slot within that predecessor presentation. -/
  parentSlot : Fin 3
  /-- The prescribed quarter-turn index of the child-parent presentation. -/
  rotation : Fin 4
  /-- The translation of the selected child occurrence. -/
  childShift : GaussianInt
  /-- The right-neighbor displacement prescribed by the row. -/
  rightShift : GaussianInt
  /-- The translation of the old companion occurrence. -/
  oldShift : GaussianInt

end ApollonianSuperharmonic

end
