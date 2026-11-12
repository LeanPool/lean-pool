/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TileString
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientation

-- [TABLET NODE: BoundaryString]

/-!
# BoundaryString

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $(C_0,C_1,C_2,C_3)$ be proper, let $c_i>0$, and let $T_0$ be a
band prototile for $C_0$.  Choose a unit orientation $\epsilon$.  A
$C_i$ boundary string for $T_0$ is the $\epsilon$-oriented
`TileString` in a translate of the $C_i$ regular tiling whose
end tiles $R_i^-,R_i^+$ satisfy
$$
 \operatorname{cent}(R_i^\pm)-\operatorname{cent}(T_0)
   =\tfrac12(v_{i0}\pm v_{0i}).
$$
If $c_i=1$, this orientation is bound to the selected occurrence
$(C_0,C_1,C_2,C_3;i)$ by
`UnitOccurrenceOrientation`.  Thus the orientation is transported
from the selected unit parent's genealogical role in one of the two first
proper successor families; it is not inferred from $C_i$ alone.  In
particular, the whole endpoint-to-midpoint displacements $v_{ji}$ and
$i v_{ik}$ are not required to be unit steps.  They record the lengths and
directions of the two full substrings and may have squared norm greater than
$2$.  No ancestor-odometer condition is part of this definition.
The positive-curvature type of $C_i$ makes the string's tiling lattice and
adjacency meaningful; a curvature-zero parent has no boundary string.
-/
def BoundaryString (C₀ Cᵢ : BandCircle) (i : Fin 3) (orientation : Bool)
    (T₀ base Rminus Rplus : ProtoTile) (tiles : List ProtoTile) : Prop :=
-- BODY
  ∃ q : Fin 4 → CircleCoordinates,
    ProperBandQuadruple q ∧ q 0 = C₀.1.1 ∧ q i.succ = Cᵢ.1.1 ∧
    BandPrototile C₀.1.1 T₀ ∧
    (Cᵢ.1.1.1 = 1 →
      UnitOccurrenceOrientation q i orientation) ∧
    TileString Cᵢ orientation base Rminus Rplus tiles ∧
    TileCentroid Rminus - TileCentroid T₀ =
      (1 / 2 : ℝ) • GaussianRealPoint
        (BandVectors.1 (q i.succ) (q 0) - BandVectors.1 (q 0) (q i.succ)) ∧
    TileCentroid Rplus - TileCentroid T₀ =
      (1 / 2 : ℝ) • GaussianRealPoint
        (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ))

end ApollonianSuperharmonic

end
