/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4715T1Position
public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceVertices

-- [TABLET NODE: P4715T1Region]

/-!
# P4715T1Region

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a face $f$ of `PeriodicSubtileFaceIndex`, put
$p_j=p(\operatorname{SixSubtileFaceVertices}(f,j))$ using
`SixSubtileFaceVertices` and `P4715T1Position`.
Define $R_f=\{(1-s-t)p_0+sp_1+tp_2:s>0,\ t>0,\ s+t<1\}$.
This definition prescribes the region rather than choosing an unspecified
component of a complement.
-/
def P4715T1Region (f : PeriodicSubtileFaceIndex) : Set (Real × Real) :=
-- BODY
  {z | ∃ s t : Real, 0 < s ∧ 0 < t ∧ s + t < 1 ∧
    z = (1 - s - t) • P4715T1Position (SixSubtileFaceVertices f 0) +
      s • P4715T1Position (SixSubtileFaceVertices f 1) +
      t • P4715T1Position (SixSubtileFaceVertices f 2)}

end ApollonianSuperharmonic

end
