/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint

/-!
# P3776T1WalkMap

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

noncomputable section

-- [TABLET NODE: P3776T1WalkMap]
/--
For a list $p=(z_0,\ldots,z_n)$ with at least two terms, its map on
$[0,1]$ linearly traverses each consecutive segment in time $1/n$.
Precisely, set $s=nt$, $k=\min(\lfloor s\rfloor,n-1)$ and $r=s-k$,
and take $(1-r)[z_k]+r[z_{k+1}]$. For a singleton the map is constant
at its real point; for the empty list it is constant at the origin.
Thus the endpoint $t=1$ is on the final segment with $r=1$.
-/
def P3776T1WalkMap (p : List GaussianInt) (t : Set.Icc (0 : Real) 1) :
    Real × Real :=
-- BODY
  let n := p.length - 1
  if n = 0 then GaussianRealPoint (p.getD 0 0)
  else
    let s := (n : Real) * (t : Real)
    let k := min (Nat.floor s) (n - 1)
    let r := s - (k : Real)
    (1 - r) • GaussianRealPoint (p.getD k 0) +
      r • GaussianRealPoint (p.getD (k + 1) 0)

end

end ApollonianSuperharmonic

end
