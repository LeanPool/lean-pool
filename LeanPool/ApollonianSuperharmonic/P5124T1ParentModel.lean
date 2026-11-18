/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: P5124T1ParentModel]

/-!
# P5124T1ParentModel

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an integer $k\geq0$, let $D_n$ be the explicit diamond prototile and
let $s_z=\langle\{z\},z\rangle$ be the canonical singleton prototile.
With zero-based parent slots, define
$$
\begin{array}{c|cc}
i&P_i^+(k)&P_i^-(k)\\ \hline
0&s_{2ki}&s_{k+(k-1)i}\\
1&s_{-(k+1)+(k-1)i}&s_{-1+2ki}\\
2&D_{k-1}+k+(1-k)i&D_{k-1}-k+(1-k)i.
\end{array}
$$
Here the predecessor index is natural truncated subtraction; translation
acts on both cells and anchors. The Boolean argument is true for $+$ and
false for $-$. In particular, at $k=1$ the two models in slot $2$ are
empty with anchors $1$ and $-1$, respectively.
-/
def P5124T1ParentModel (k : Nat) (i : Fin 3) (s : Bool) : ProtoTile :=
-- BODY
  if s then
    ![⟨{⟨0, 2 * (k : Int)⟩}, ⟨0, 2 * (k : Int)⟩⟩,
      ⟨{⟨-(k : Int) - 1, (k : Int) - 1⟩},
        ⟨-(k : Int) - 1, (k : Int) - 1⟩⟩,
      TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩] i
  else
    ![⟨{⟨(k : Int), (k : Int) - 1⟩}, ⟨(k : Int), (k : Int) - 1⟩⟩,
      ⟨{⟨-1, 2 * (k : Int)⟩}, ⟨-1, 2 * (k : Int)⟩⟩,
      TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩] i

end ApollonianSuperharmonic

end
