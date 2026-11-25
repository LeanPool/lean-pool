/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Order.Group.End

/-!
# Linear actions on submodule lattices
-/

@[expose] public section

namespace AlmostInvariant

/-- A linear automorphism acts on the lattice of submodules. -/
def linearAct {R M G : Type*} [Ring R] [AddCommGroup M] [Module R M] [Group G] (ρ : G →* (M ≃ₗ[R]
    M)) :
    G →* (Submodule R M ≃o Submodule R M) where
  toFun g := Submodule.orderIsoMapComap (ρ g)
  map_one' := by
    ext S x
    simp
  map_mul' g h := by
    ext S x
    simp only [map_mul, Submodule.orderIsoMapComap_apply, RelIso.mul_apply, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ρ h y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩

theorem linearAct_mul_apply {R M G : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Group G] (ρ : G →* (M ≃ₗ[R] M)) (g h : G) (S : Submodule R M) :
    linearAct ρ (g * h) S = linearAct ρ g (linearAct ρ h S) := by
  rw [map_mul, RelIso.mul_apply]

end AlmostInvariant
