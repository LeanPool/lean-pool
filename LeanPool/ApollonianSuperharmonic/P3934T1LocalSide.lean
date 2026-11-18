/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order

-- [TABLET NODE: P3934T1LocalSide]

/-!
# P3934T1LocalSide

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a plane set $U$, a point $z$, a vector $w$, and a Boolean $e$,
write $\operatorname{Side}(U,z,w,e)$ if some $r>0$ satisfies
$$
 U\cap B(z,r)=\{q\in B(z,r):[w,q-z]>0\}\quad(e=\mathrm{true}),
$$
and the same equation with $[w,q-z]<0$ if $e=\mathrm{false}$.
Here $[w,h]=w_1h_2-w_2h_1$ and balls use the product norm.
-/
def P3934T1LocalSide (U : Set (Real × Real)) (z w : Real × Real)
    (positive : Bool) : Prop :=
-- BODY
  ∃ r : Real, 0 < r ∧ U ∩ Metric.ball z r =
    {q | q ∈ Metric.ball z r ∧
      if positive then 0 < w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1)
      else w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1) < 0}

end ApollonianSuperharmonic

end
