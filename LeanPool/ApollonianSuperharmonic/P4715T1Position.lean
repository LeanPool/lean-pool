/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4715T1Offsets
public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex

-- [TABLET NODE: P4715T1Position]

/-!
# P4715T1Position

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an index $a=(X,m,n)$ of `PeriodicSubtileIndex`, define
$p(a)=(m,n)+o_X$, using `P4715T1Offsets`.
-/
noncomputable def P4715T1Position (a : PeriodicSubtileIndex) : Real × Real :=
-- BODY
  ((a.first : Real), (a.second : Real)) + P4715T1Offsets a.label

end ApollonianSuperharmonic

end
