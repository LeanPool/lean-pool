/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple

-- [TABLET NODE: BandGeneralCircle]

/-!
# BandGeneralCircle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The band packing of general circles, denoted $\mathcal B^{\rm gen}$, consists
of the raw integral curvature-coordinate pairs
$C=(c,w)\in\mathbb Z\times\mathbb Z[i]$ which occur as an entry of a
semi-proper Descartes quadruple and satisfy
$$
             c>0\qquad\text{or}\qquad
             c=0\ \text{ and }\ w\in\{1,-1\}.
$$
Pairs in the first alternative are called positive-curvature coordinates.
The two pairs in the second alternative are retained solely as the two
admissible oriented-line coordinate symbols for Descartes recursion; their
second coordinates are the corresponding unit Gaussian normals.  Equality
in $\mathcal B^{\rm gen}$ is coordinate equality.  In particular, no other
curvature-zero raw pair belongs to $\mathcal B^{\rm gen}$.
-/
def BandGeneralCircle : Type :=
-- BODY
  {C : CircleCoordinates //
    (0 < C.1 ∨ (C.1 = 0 ∧ (C.2 = 1 ∨ C.2 = -1))) ∧
      ∃ q : Fin 4 → CircleCoordinates,
        SemiProperQuadruple q ∧ ∃ j : Fin 4, q j = C}

end ApollonianSuperharmonic

end
