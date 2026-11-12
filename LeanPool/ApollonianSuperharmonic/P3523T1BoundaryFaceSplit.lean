/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3523T1InsertionData

-- [TABLET NODE: P3523T1BoundaryFaceSplit]

/-!
# P3523T1BoundaryFaceSplit

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a finite family $\mathcal F$ of finite label sets and labels
$a,d,b$, replace every $F\in\mathcal F$ containing $a,b$ by
$$
 (F\setminus\{b\})\cup\{d\},\qquad
 (F\setminus\{a\})\cup\{d\},
$$
and retain every other $F$. Take the finite union of these outputs.
In the intended application exactly one face contains the boundary
pair $a,b$. The formula is defined even without that hypothesis and
makes no claim of correctness for such inputs.
-/
def P3523T1BoundaryFaceSplit {I : Type} [DecidableEq I]
    (faces : Finset (Finset I)) (a d b : I) : Finset (Finset I) :=
-- BODY
  faces.biUnion fun F =>
    if a ∈ F ∧ b ∈ F then {insert d (F.erase b), insert d (F.erase a)}
    else {F}

end ApollonianSuperharmonic

end
