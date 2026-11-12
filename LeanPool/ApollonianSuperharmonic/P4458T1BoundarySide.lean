/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.P4458T1BoundaryFrame
public import LeanPool.ApollonianSuperharmonic.TileString

-- [TABLET NODE: P4458T1BoundarySide]

/-!
# P4458T1BoundarySide

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Fix an outer boundary frame $F$ with selected circle $C$, chart $\epsilon$
and base $B$. A side from literal $(U,g)$ to literal $(V,h)$ is one of two
pieces of construction data. A direct side records the two-term
$\epsilon$-oriented tile string $[U,V]$ in the same regular family and
$\operatorname{LeftLatticeAdjacent}(C,U,V,g,h)$.
A recursive side records a boundary frame $G$ with the same selected
circle, chart, base and literal endpoint functions $(U,g),(V,h)$,
a parent slot $j$ of $F.q$ with $G.C_0=F.q_{j+1}$, and
$\operatorname{AncestorOdometer}(G.C_0,F.C_0,G.T_0,F.T_0,G.h_0,F.h_0)$.
It does not record a recursive string or a respected odometer list.
-/
inductive P4458T1BoundarySide
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (U V : ProtoTile) (g h : PartialOdometer) : Type where
-- BODY
  | direct
      (string : TileString C orientation base U V [U, V])
      (link : LeftLatticeAdjacent C U V g h)
  | recursive
      (frame : P4458T1BoundaryFrame C orientation base U V g h)
      (outerSlot : Fin 3)
      (parent : frame.outer.1.1 = F.q outerSlot.succ)
      (ancestor : AncestorOdometer frame.outer.1.1 F.outer.1.1
        frame.tile F.tile frame.odometer F.odometer)

end ApollonianSuperharmonic

end
