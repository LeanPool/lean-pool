/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.ZMod

/-!
# A tight bound for Green's arithmetic triangle removal lemma in vector spaces

Source: arxiv:1606.01230, url:https://github.com/gdahia/ArithmeticTriangleRemovalInVectorSpaces/tree/3bddc92e8027badc994ba8993f7c625e60c7b13a
Authors: Gabriel Dahia
Status: verified
Main declarations:
  `ArithmeticTriangleRemovalInVectorSpaces.exists_subset_card_sdiff_add_le_forall_add_ne_zero`,
  `ArithmeticTriangleRemovalInVectorSpaces.card_le_rpow_one_sub_c_mul`,
  `ArithmeticTriangleRemovalInVectorSpaces.div_pow_rpow_C_mul_sq_le_card_triangles`,
  `ArithmeticTriangleRemovalInVectorSpaces.le_rpow_C_sub_of_forall_exists_subset`
Tags: additive-combinatorics, removal-lemma, slice-rank, finite-fields, sum-free-sets
MSC: 11B30, 05D40, 11T99
-/

/-!
## Upstream attribution

Adapted for Lean Pool from upstream commit `3bddc92e8027badc994ba8993f7c625e60c7b13a` by
moving the library under `LeanPool.ArithmeticTriangleRemovalInVectorSpaces`. The upstream
Palomar `Challenge` and `Solution` modules are omitted: `Solution` only restates the theorems of
`LeanPool.ArithmeticTriangleRemovalInVectorSpaces.ZMod` under primed names.
-/
