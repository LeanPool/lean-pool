/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: ModifiedSubtileOccurrenceInterpretation]

/-!
# ModifiedSubtileOccurrenceInterpretation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For six signed occurrences $S_i^\pm$, a common precursor $O$, and periods
$u,v$, the modified interpretation of a periodic subtile index agrees with
`SubtileOccurrenceInterpretation` except at label $A$: it assigns
$$
 (A\setminus O)_{m,n}
$$
to $(A,m,n)$.  The labels $B,C,D,E,F$ retain their unmodified occurrences.
Cell difference is the operation of `TileCellComplement`, and the
whole result is translated by $mu+nv$.
-/
def ModifiedSubtileOccurrenceInterpretation
    (S : Fin 3 -> Bool -> ProtoTile) (O : ProtoTile)
    (u v : GaussianInt) (o : PeriodicSubtileIndex) : ProtoTile :=
-- BODY
  let T := match o.label with
    | .A => TileCellComplement (S 0 true) O
    | .B => S 0 false
    | .C => S 1 true
    | .D => S 1 false
    | .E => S 2 true
    | .F => S 2 false
  TileTranslation T
    ((o.first : GaussianInt) * u + (o.second : GaussianInt) * v)

end ApollonianSuperharmonic

end
