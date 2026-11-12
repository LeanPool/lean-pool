/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init


-- [TABLET NODE: SixSubtileLabel]

/-!
# SixSubtileLabel

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The six labels for a tile decomposition are
$$
 A=T_1^+,\quad B=T_1^-,\quad C=T_2^+,\quad D=T_2^-,\quad
 E=T_3^+,\quad F=T_3^-.
$$
They are combinatorial labels and do not themselves assert any geometric
intersection.
-/
inductive SixSubtileLabel : Type where
-- BODY
  | A | B | C | D | E | F
  deriving DecidableEq

end ApollonianSuperharmonic

end
