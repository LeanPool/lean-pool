/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Prod

public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileFaceIndex

-- [TABLET NODE: P4715T1FaceShift]

/-!
# P4715T1FaceShift

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $k=(r,s)\in\mathbb Z^2$, define
$\sigma_k(X,m,n)=(X,m+r,n+s)$ on `PeriodicSubtileFaceIndex`.
-/
def P4715T1FaceShift (k : Int × Int) (f : PeriodicSubtileFaceIndex) :
    PeriodicSubtileFaceIndex :=
-- BODY
  ⟨f.label, f.first + k.1, f.second + k.2⟩

end ApollonianSuperharmonic

end
