/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex

-- [TABLET NODE: P3723T1EdgeContact]

/-!
# P3723T1EdgeContact

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a `PeriodicTileComplex` $P$, two indices have genuine
edge contact if they are distinct and the intersection of their
`FootprintEdges` is nonempty. This relation does not require
prescribed adjacency and does not include corner-only contacts.
-/
def P3723T1EdgeContact {ι : Type} (P : PeriodicTileComplex ι)
    (a b : ι) : Prop :=
-- BODY
  a ≠ b ∧ (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty

end ApollonianSuperharmonic

end
