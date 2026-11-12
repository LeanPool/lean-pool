/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: SubtileOccurrenceInterpretation]

/-!
# SubtileOccurrenceInterpretation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Given six signed occurrences $S_i^\pm$ and two period vectors $u,v$, the
geometric interpretation of $(X,m,n)$ is the translate by $mu+nv$ of the
occurrence selected by
$$
 A=S_1^+,\quad B=S_1^-,\quad C=S_2^+,\quad D=S_2^-,\quad
 E=S_3^+,\quad F=S_3^-.
$$
This interpretation applies without change to the Ford configuration,
where $E,F$ are anchored empty line occurrences, and to the diamond
configuration, where the six occurrences include the two unit-parent pairs
and the predecessor pair.
-/
def SubtileOccurrenceInterpretation (S : Fin 3 → Bool → ProtoTile)
    (u v : GaussianInt) (o : PeriodicSubtileIndex) : ProtoTile :=
-- BODY
  let T := match o.label with
    | .A => S 0 true
    | .B => S 0 false
    | .C => S 1 true
    | .D => S 1 false
    | .E => S 2 true
    | .F => S 2 false
  TileTranslation T ((o.first : GaussianInt) * u + (o.second : GaussianInt) * v)

end ApollonianSuperharmonic

end
