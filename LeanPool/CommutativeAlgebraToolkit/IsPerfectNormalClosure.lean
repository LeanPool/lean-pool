/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.GroupTheory.IsPerfect

/-!
# The normal closure of a perfect subgroup is perfect

## Main statements

* `Subgroup.isPerfect_normalClosure`: if `H` is a perfect subgroup of `G`, its normal closure is
  perfect.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- The normal closure of a perfect subgroup is perfect: each conjugate of `H` is perfect, hence
lies in the commutator subgroup of the normal closure, which is normal. -/
theorem isPerfect_normalClosure (H : Subgroup G) [Group.IsPerfect H] :
    Group.IsPerfect (normalClosure (H : Set G)) := by
  rw [isPerfect_iff]
  refine le_antisymm (commutator_le_left _ _) (normalClosure_le_normal fun h hh ↦ ?_)
  rw [← (commutator_eq_self : ⁅H, H⁆ = H)] at hh
  exact commutator_mono le_normalClosure le_normalClosure hh

end Subgroup
