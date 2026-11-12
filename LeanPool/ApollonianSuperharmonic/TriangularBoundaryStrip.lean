/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TriangularMaxIncrement
public import LeanPool.ApollonianSuperharmonic.TriangularSignedHeight

-- [TABLET NODE: TriangularBoundaryStrip]

/-!
# TriangularBoundaryStrip

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For distinct endpoints $x,y\in\mathbb Z^2$, their left boundary strip is
the height window
$$
 \mathcal B(x,y)=\{z\in\mathbb Z^2:0\leq
 \Phi_{x,y}(z)<M_{x,y}\},
$$
where $\Phi$ and $M$ are respectively
`TriangularSignedHeight` and
`TriangularMaxIncrement`.
The same formula is used when $x=y$; in that case $M_{x,x}=0$ and the
window is empty.  The equal-endpoint string is handled separately by the
segment definition.
-/
def TriangularBoundaryStrip (x y z : Int × Int) : Prop :=
-- BODY
  0 ≤ TriangularSignedHeight x y z ∧
    TriangularSignedHeight x y z < TriangularMaxIncrement x y

end ApollonianSuperharmonic

end
