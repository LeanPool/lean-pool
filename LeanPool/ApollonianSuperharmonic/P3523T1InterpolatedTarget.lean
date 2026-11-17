/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3475T1BoundarySubdivision
public import LeanPool.ApollonianSuperharmonic.P3475T1TriangleTree

-- [TABLET NODE: P3523T1InterpolatedTarget]

/-!
# P3523T1InterpolatedTarget

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an ordered subdivision $s$ of $q$ by $p$ as in
`P3475T1BoundarySubdivision` and a triangle tree $t$ for
$(q,X,K)$ as in `P3475T1TriangleTree`, define, at every
original fine index $j$,
$$
 Q_j=(1-s.\mathrm{parameter}(j))t.\mathrm{target}(s.\mathrm{edge}(j))
       +s.\mathrm{parameter}(j)t.\mathrm{target}(s.\mathrm{edge}(j)+1).
$$
The fine labels are unchanged; this definition only gives their target
positions using the same coarse-edge parameters as the source.
-/
def P3523T1InterpolatedTarget {r n : Nat}
    {q : P3381T1PolygonBoundary r} {p : P3381T1PolygonBoundary n}
    (s : P3475T1BoundarySubdivision q p)
    {X K : Set (Real × Real)} (t : P3475T1TriangleTree q X K)
    (j : Fin (n + 3)) : Real × Real :=
-- BODY
  (1 - s.parameter j) • t.target (s.edge j) +
    s.parameter j • t.target (s.edge j + 1)

end ApollonianSuperharmonic

end
