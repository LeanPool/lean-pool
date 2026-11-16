/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.NormNum

public import LeanPool.ApollonianSuperharmonic.P4715T1Position
public import LeanPool.ApollonianSuperharmonic.P4715T1PatchFaces
public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceVertices
public import Mathlib.LinearAlgebra.Matrix.Notation

-- [TABLET NODE: P4783T1PatchCoordinates]

/-!
# P4783T1PatchCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4783T1PatchCoordinates (j : Fin 12) :
    P4715T1Position ∘ SixSubtileFaceVertices (P4715T1PatchFaces j) =
      (![![(0,0),(-1/3,-2/3),(-1/2,-1/2)],
         ![(-1,-1),(-1/3,-2/3),(-1/2,-1/2)],
         ![(-1,0),(-4/3,-2/3),(-5/6,-1/6)],
         ![(-1,0),(-1/3,1/3),(-5/6,-1/6)],
         ![(-1,-1),(-1/2,-1/2),(-11/12,-7/12)],
         ![(-1/2,-1/2),(-5/6,-1/6),(-11/12,-7/12)],
         ![(-4/3,-2/3),(-5/6,-1/6),(-11/12,-7/12)],
         ![(-1,-1),(-4/3,-2/3),(-11/12,-7/12)],
         ![(0,0),(-1/2,-1/2),(-5/12,-1/12)],
         ![(-1/2,-1/2),(-5/6,-1/6),(-5/12,-1/12)],
         ![(-1/3,1/3),(-5/6,-1/6),(-5/12,-1/12)],
         ![(0,0),(-1/3,1/3),(-5/12,-1/12)]] :
           Fin 12 → Fin 3 → Real × Real) j := by
-- BODY
  fin_cases j <;> funext k <;> fin_cases k <;>
    norm_num [P4715T1Position, P4715T1Offsets,
      P4715T1PatchFaces, SixSubtileFaceVertices, Function.comp_def]

end ApollonianSuperharmonic

end
