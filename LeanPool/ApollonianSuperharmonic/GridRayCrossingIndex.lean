/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LatticeCell

-- [TABLET NODE: GridRayCrossingIndex]

/-!
# GridRayCrossingIndex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $q$ be a lattice cell and let $p=[z_0,\ldots,z_{n-1}]$ be a list of
lattice vertices.  For an ordered pair $(a,b)$ of lattice vertices, set
$$
 c_q(a,b)=
 \begin{cases}
  1,&b=a+i,\quad \operatorname{Im}(a)=\operatorname{Im}(q),
       \quad \operatorname{Re}(a)\leq \operatorname{Re}(q),\\
  -1,&b=a-i,\quad \operatorname{Im}(b)=\operatorname{Im}(q),
       \quad \operatorname{Re}(a)\leq \operatorname{Re}(q),\\
  0,&\text{otherwise.}
 \end{cases}
$$
If $p$ is nonempty, close it cyclically by the ordered pair
$(z_{n-1},z_0)$ and define the *signed grid-ray crossing index* by
$$
 \operatorname{gind}_q(p)
   =\sum_{0\leq j<n-1}c_q(z_j,z_{j+1})+c_q(z_{n-1},z_0).
$$
For the empty list, define $\operatorname{gind}_q(p)=0$.  Thus upward
unit vertical pairs contribute $1$, downward unit vertical pairs
contribute $-1$, and every other consecutive or closing pair contributes
$0$.  For a nonempty $p$, if every consecutive pair and the closing pair
are four-neighbor adjacent (that is, each displacement is one of
$\pm1,\pm i$), then this sum is equivalently the signed number of
crossings of the leftward horizontal ray starting at the center of $q$.
-/
def GridRayCrossingIndex (q : LatticeCell) (p : List GaussianInt) : Int :=
-- BODY
  let step : GaussianInt → GaussianInt → Int := fun a b ↦
    if b = a + ⟨0, 1⟩ ∧ a.im = q.im ∧ a.re ≤ q.re then 1
    else if b = a - ⟨0, 1⟩ ∧ b.im = q.im ∧ a.re ≤ q.re then -1
    else 0
  (List.zipWith step p p.tail).sum +
    match p.getLast?, p.head? with
    | some a, some b => step a b
    | _, _ => 0

end ApollonianSuperharmonic

end
