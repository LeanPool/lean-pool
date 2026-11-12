/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Complex.Module

-- [TABLET NODE: P4909T1ParentEdges]

/-!
# P4909T1ParentEdges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $p_i=w_i/c_i$ for positive parents of $q$.
The set $E_L(q)$ consists of all center-to-center segments $[p_i,p_j]$
for distinct positive parent indices, all center-to-foot segments
$[p_i,(h_k,\operatorname{Im}p_i)]$ for a positive parent $i$ and a
zero-curvature parent $k$, and the entire lines $X=h_k$ for these zero
parents. Here $h_k=L$ if $w_k=-1$, and $h_k=L+2$ otherwise.
It is a boundary carrier, not a claim that every listed segment is an edge.
-/
def P4909T1ParentEdges (L : ℝ) (q : Fin 4 → CircleCoordinates) : Set ℂ :=
-- BODY
  let p (i : Fin 3) : ℂ := (q i.succ).2 / ((q i.succ).1 : ℝ)
  {z | (∃ i j : Fin 3, i ≠ j ∧ 0 < (q i.succ).1 ∧
      0 < (q j.succ).1 ∧ z ∈ segment ℝ (p i) (p j)) ∨
    (∃ i k : Fin 3, 0 < (q i.succ).1 ∧ (q k.succ).1 = 0 ∧
      z ∈ segment ℝ (p i)
        ⟨if (q k.succ).2 = -1 then L else L + 2, (p i).im⟩) ∨
    (∃ k : Fin 3, (q k.succ).1 = 0 ∧
      z.re = if (q k.succ).2 = -1 then L else L + 2)}

end ApollonianSuperharmonic

end
