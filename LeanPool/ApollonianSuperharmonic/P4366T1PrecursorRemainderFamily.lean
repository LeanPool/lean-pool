/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileCellComplement

-- [TABLET NODE: P4366T1PrecursorRemainderFamily]

/-!
# P4366T1PrecursorRemainderFamily

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a signed family $P_i^s$, indexed by $i\in\{0,1,2\}$ and a
Boolean sign $s$, and a prototile $O$, define the signed family $F$ by
$$
 F_i^s=\begin{cases}
 \operatorname{TileCellComplement}(P_i^s,O),&i=0,\\
 P_i^s,&i\ne0.
 \end{cases}
$$
Thus only the two largest-parent occurrences have their $O$-cells
deleted. The complements retain the auxiliary anchors of their parents.
-/
def P4366T1PrecursorRemainderFamily
    (P : Fin 3 → Bool → ProtoTile) (O : ProtoTile) :
    Fin 3 → Bool → ProtoTile :=
-- BODY
  fun i s => if i = 0 then TileCellComplement (P i s) O else P i s

end ApollonianSuperharmonic

end
