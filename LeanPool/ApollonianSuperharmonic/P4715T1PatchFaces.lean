/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fin.VecNotation

public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileFaceIndex

-- [TABLET NODE: P4715T1PatchFaces]

/-!
# P4715T1PatchFaces

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The ordered list of face indices in the base patch is
$$
I_1,\ (J_3)_{-1,-1},\ (I_2)_{-1,0},\ (J_4)_{-1,0},\
(J_5)_{-1,-1},\ J_7,\ (I_4)_{-1,0},\ (J_1)_{-1,-1},\
I_3,\ J_8,\ (J_6)_{0,1},\ J_2,
$$
where omitted subscripts are $(0,0)$ and face indices are those of
`PeriodicSubtileFaceIndex`.
-/
def P4715T1PatchFaces : Fin 12 → PeriodicSubtileFaceIndex :=
-- BODY
  ![⟨.I1, 0, 0⟩, ⟨.J3, -1, -1⟩, ⟨.I2, -1, 0⟩, ⟨.J4, -1, 0⟩,
    ⟨.J5, -1, -1⟩, ⟨.J7, 0, 0⟩, ⟨.I4, -1, 0⟩, ⟨.J1, -1, -1⟩,
    ⟨.I3, 0, 0⟩, ⟨.J8, 0, 0⟩, ⟨.J6, 0, 1⟩, ⟨.J2, 0, 0⟩]

end ApollonianSuperharmonic

end
