/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4715T1Position
public import Mathlib.Analysis.Convex.Segment

-- [TABLET NODE: P4715T1Arc]

/-!
# P4715T1Arc

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For every ordered pair of indices, including a nonedge or a repeated
index, let $S(a,b)=[p(a),p(b)]$ be the closed real segment between
the positions of `P4715T1Position`.
-/
def P4715T1Arc (a b : PeriodicSubtileIndex) : Set (Real × Real) :=
-- BODY
  segment Real (P4715T1Position a) (P4715T1Position b)

end ApollonianSuperharmonic

end
