/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex

-- [TABLET NODE: P4261T1ExteriorIndices]

/-!
# P4261T1ExteriorIndices

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The exterior index set consists of the twelve positions
$$
 A_{-1,-1},A_{0,-1},C_{1,0},C_{1,1},E_{0,1},E_{-1,0},
 B_{1,1},B_{0,1},D_{-1,0},D_{-1,-1},F_{0,-1},F_{1,0}.
$$
These are the four exterior positions for each parent in the ordered-general
contact calculation, with period coordinates relative to $v_{01},v_{02}$.
-/
def P4261T1ExteriorIndices : Finset PeriodicSubtileIndex :=
-- BODY
  {⟨.A, -1, -1⟩, ⟨.A, 0, -1⟩, ⟨.C, 1, 0⟩, ⟨.C, 1, 1⟩,
   ⟨.E, 0, 1⟩, ⟨.E, -1, 0⟩, ⟨.B, 1, 1⟩, ⟨.B, 0, 1⟩,
   ⟨.D, -1, 0⟩, ⟨.D, -1, -1⟩, ⟨.F, 0, -1⟩, ⟨.F, 1, 0⟩}

end ApollonianSuperharmonic

end
