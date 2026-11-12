/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandGeneralCircle

-- [TABLET NODE: BandTangency]

/-!
# BandTangency

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For raw integral curvature-coordinate pairs $C,D$, the relation
$\operatorname{BandTangency}(C,D)$ holds exactly when there are a
semi-proper Descartes quadruple $q$ and distinct indices
$i,j\in\{0,1,2,3\}$ such that $q_i=C$ and $q_j=D$.  If no such quadruple and
indices exist, then $\operatorname{BandTangency}(C,D)$ does not hold.  In
particular, the arguments of this ambient relation are not assumed in its
definition to be geometric circles or oriented lines.
-/
def BandTangency (C D : CircleCoordinates) : Prop :=
-- BODY
  ∃ q : Fin 4 → CircleCoordinates, SemiProperQuadruple q ∧
    ∃ i j : Fin 4, i ≠ j ∧ q i = C ∧ q j = D

end ApollonianSuperharmonic

end
