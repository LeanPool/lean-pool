/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: P5064T3Rectangles]

/-!
# P5064T3Rectangles

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For nonnegative integers $r,s$, define the six-record family
$M(r,s)$, indexed by a parent slot $0,1,2$ and a Boolean sign, by
$$
\begin{array}{lll}
 M_0^+=T_r,&M_0^-=T_r+(s,s),\\
 M_1^+=T_s+(r,0),&M_1^-=T_s+(0,r),\\
 M_2^+=\langle\varnothing,(s,r+s)\rangle,
 &M_2^-=\langle\varnothing,(r,0)\rangle.
\end{array}
$$
Here $T_n$ is the explicit Ford square, addition denotes tile translation,
and the last two records have no cells and the displayed auxiliary anchors.
The signs $+$ and $-$ mean Boolean true and false, respectively.  These are
the canonical coordinate representatives for the signed Ford occurrences;
they do not fix the auxiliary anchors of other nonempty representatives.
-/
def P5064T3Rectangles (r s : Nat) : Fin 3 → Bool → ProtoTile :=
-- BODY
  ![fun b => if b then FordTile r else
      TileTranslation (FordTile r) ⟨(s : Int), (s : Int)⟩,
    fun b => if b then TileTranslation (FordTile s) ⟨(r : Int), 0⟩ else
      TileTranslation (FordTile s) ⟨0, (r : Int)⟩,
    fun b => if b then ⟨∅, ⟨(s : Int), ((r + s : Nat) : Int)⟩⟩ else
      ⟨∅, ⟨(r : Int), 0⟩⟩]

end ApollonianSuperharmonic

end
