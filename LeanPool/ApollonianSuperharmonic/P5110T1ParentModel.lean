/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: P5110T1ParentModel]

/-!
# P5110T1ParentModel

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For natural numbers $r,s$, put $q=r+s$ and write
$Q_n(a,b)=\operatorname{FordTile}(n)+(a,b)$, with its literal translated
anchor.  The models $M_i^\epsilon$ for $i=0,1,2$ and a Boolean
$\epsilon$ are the following prototile records:
$$
\begin{array}{c|cc}
i&M_i^{\mathrm{true}}&M_i^{\mathrm{false}}\\\hline
0&Q_r(s,q)&Q_r(q,0)\\
1&Q_s(-s,0)&Q_s(0,q)\\
2&\varnothing@(q,0)&\varnothing@(0,0).
\end{array}
$$
Here $\varnothing@a$ is the record with empty cell set and anchor $a$.
These are the plus- and minus-centroid parent placements used in the Ford
T4 and T5 calculations, not the signed subtiles inside the child.
-/
def P5110T1ParentModel (r s : Nat) (i : Fin 3) (plus : Bool) : ProtoTile :=
-- BODY
  if plus then
    ![TileTranslation (FordTile r) ⟨(s : Int), ((r + s : Nat) : Int)⟩,
      TileTranslation (FordTile s) ⟨-(s : Int), 0⟩,
      (⟨∅, ⟨((r + s : Nat) : Int), 0⟩⟩ : ProtoTile)] i
  else
    ![TileTranslation (FordTile r) ⟨((r + s : Nat) : Int), 0⟩,
      TileTranslation (FordTile s) ⟨0, ((r + s : Nat) : Int)⟩,
      (⟨∅, 0⟩ : ProtoTile)] i

end ApollonianSuperharmonic

end
