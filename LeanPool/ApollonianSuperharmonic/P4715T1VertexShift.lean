/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex

-- [TABLET NODE: P4715T1VertexShift]

/-!
# P4715T1VertexShift

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $k=(r,s)\in\mathbb Z^2$, define
$\tau_k(X,m,n)=(X,m+r,n+s)$ on `PeriodicSubtileIndex`.
-/
def P4715T1VertexShift (k : Int × Int) (a : PeriodicSubtileIndex) :
    PeriodicSubtileIndex :=
-- BODY
  ⟨a.label, a.first + k.1, a.second + k.2⟩

end ApollonianSuperharmonic

end
