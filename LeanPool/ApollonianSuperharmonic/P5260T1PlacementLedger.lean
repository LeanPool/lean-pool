/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5124T1ParentModel

-- [TABLET NODE: P5260T1PlacementLedger]

/-!
# P5260T1PlacementLedger

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $k\geq0$, $i\in\{0,1,2\}$ and a Boolean $b$, define
$M(k,i,b)=((W,Z),(r,l),(x,y))$ by the following table.
Here $D'=\operatorname{DiamondTile}(k-1)$ (natural truncated subtraction),
$[a]$ is the prototile with singleton cell base and anchor $a$, and
every translate is `TileTranslation`. The first three $W$
entries are exactly the positive models of
`P5124T1ParentModel`, not new versions of those models.
$$
\begin{array}{c|c|c|c|c|c|c|c}
b&i&W&Z&r&l&x&y\\ \hline
0& 0& [2k\mathrm{i}]& D'+k+(k+1)\mathrm{i}& -k+(k+1)\mathrm{i}& (k+1)+k\mathrm{i}& 2k\mathrm{i}&
1+2k\mathrm{i}\\
0& 1& [-k-1+(k-1)\mathrm{i}]& [-k-1+k\mathrm{i}]& -k-(k+1)\mathrm{i}& -k-1+k\mathrm{i}&
-k+(k-1)\mathrm{i}& -k+k\mathrm{i}\\
0&2&D'+k+(1-k)\mathrm{i}&[-\mathrm{i}]&2k&-2k\mathrm{i}&k+(k-1)\mathrm{i}&1\\
1& 0& [-k-1+k\mathrm{i}]& [-k-1+(k-1)\mathrm{i}]& -k+(k+1)\mathrm{i}& -k-1-k\mathrm{i}&
-k+(k+1)\mathrm{i}& -k+k\mathrm{i}\\
1&1&[-\mathrm{i}]&D'+k+(1-k)\mathrm{i}&-k-(k+1)\mathrm{i}&(k+1)-k\mathrm{i}&0&1\\
1&2&D'+k+(k+1)\mathrm{i}&[2k\mathrm{i}]&2k&2k\mathrm{i}&k+(k+1)\mathrm{i}&1+2k\mathrm{i}.
\end{array}
$$
This is coordinate data only: $x,y$ specify the proposed right and
incoming junctions; their interface properties are not part of the definition.
-/
def P5260T1PlacementLedger (k : Nat) (i : Fin 3) (odd : Bool) :
    (ProtoTile × ProtoTile) × (GaussianInt × GaussianInt) ×
      (GaussianInt × GaussianInt) :=
-- BODY
  let unit := fun z : GaussianInt => (⟨{z}, z⟩ : ProtoTile)
  let pred := DiamondTile (k - 1)
  if odd then
    ![((unit ⟨-(k : Int) - 1, (k : Int)⟩,
          unit ⟨-(k : Int) - 1, (k : Int) - 1⟩),
        (⟨-(k : Int), (k : Int) + 1⟩, ⟨-(k : Int) - 1, -(k : Int)⟩),
        (⟨-(k : Int), (k : Int) + 1⟩, ⟨-(k : Int), (k : Int)⟩)),
      ((unit ⟨0, -1⟩, TileTranslation pred ⟨(k : Int), 1 - (k : Int)⟩),
        (⟨-(k : Int), -(k : Int) - 1⟩, ⟨(k : Int) + 1, -(k : Int)⟩),
        (0, 1)),
      ((TileTranslation pred ⟨(k : Int), (k : Int) + 1⟩,
          unit ⟨0, 2 * (k : Int)⟩),
        (⟨2 * (k : Int), 0⟩, ⟨0, 2 * (k : Int)⟩),
        (⟨(k : Int), (k : Int) + 1⟩, ⟨1, 2 * (k : Int)⟩))] i
  else
    ![((P5124T1ParentModel k 0 true,
          TileTranslation pred ⟨(k : Int), (k : Int) + 1⟩),
        (⟨-(k : Int), (k : Int) + 1⟩, ⟨(k : Int) + 1, (k : Int)⟩),
        (⟨0, 2 * (k : Int)⟩, ⟨1, 2 * (k : Int)⟩)),
      ((P5124T1ParentModel k 1 true,
          unit ⟨-(k : Int) - 1, (k : Int)⟩),
        (⟨-(k : Int), -(k : Int) - 1⟩, ⟨-(k : Int) - 1, (k : Int)⟩),
        (⟨-(k : Int), (k : Int) - 1⟩, ⟨-(k : Int), (k : Int)⟩)),
      ((P5124T1ParentModel k 2 true, unit ⟨0, -1⟩),
        (⟨2 * (k : Int), 0⟩, ⟨0, -2 * (k : Int)⟩),
        (⟨(k : Int), (k : Int) - 1⟩, 1))] i

end ApollonianSuperharmonic

end
