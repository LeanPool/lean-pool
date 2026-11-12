/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4733T1EdgeRow

-- [TABLET NODE: P4733T1RowLabelRigidity]

/-!
# P4733T1RowLabelRigidity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4733T1RowLabelRigidity : Function.Injective
    (fun t : Fin 18 × Bool =>
      let faces := (P4733T1EdgeRow t.1).2
      if t.2 then (faces.1.label, faces.2.label)
      else (faces.2.label, faces.1.label)) := by
-- BODY
  decide +kernel

end ApollonianSuperharmonic

end
