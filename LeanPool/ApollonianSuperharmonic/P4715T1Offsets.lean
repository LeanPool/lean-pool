/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.SixSubtileLabel

-- [TABLET NODE: P4715T1Offsets]

/-!
# P4715T1Offsets

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The coefficient offsets of the six labels of `SixSubtileLabel`
are the following vectors in $\mathbb R^2$:
$$
o_A=(0,0),\quad o_B=(-4,-8)/12,\quad o_C=(-6,-6)/12,\quad
o_D=(2,-2)/12,\quad o_E=(1,-7)/12,\quad o_F=(-5,-1)/12.
$$
-/
noncomputable def P4715T1Offsets : SixSubtileLabel → Real × Real :=
-- BODY
  fun l => match l with
  | .A => (0, 0)
  | .B => (-4 / 12, -8 / 12)
  | .C => (-6 / 12, -6 / 12)
  | .D => (2 / 12, -2 / 12)
  | .E => (1 / 12, -7 / 12)
  | .F => (-5 / 12, -1 / 12)

end ApollonianSuperharmonic

end
