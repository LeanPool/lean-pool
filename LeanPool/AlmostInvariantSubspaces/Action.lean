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
def linearAct {R M G : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Monoid G]
    (ρ : G →* (M ≃ₗ[R] M)) :
    G →* (Submodule R M ≃o Submodule R M) where
  toFun g := Submodule.orderIsoMapComap (ρ g)
  map_one' := by
    ext S x
    simp
  map_mul' g h := by
    apply RelIso.ext
    intro S
    change S.map (ρ (g * h) : M →ₗ[R] M) = (S.map (ρ h : M →ₗ[R] M)).map (ρ g : M →ₗ[R] M)
    rw [map_mul]
    exact Submodule.map_comp (ρ h : M →ₗ[R] M) (ρ g : M →ₗ[R] M) S

theorem linearAct_mul_apply {R M G : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Monoid G] (ρ : G →* (M ≃ₗ[R] M)) (g h : G) (S : Submodule R M) :
    linearAct ρ (g * h) S = linearAct ρ g (linearAct ρ h S) := by
  rw [map_mul, RelIso.mul_apply]

end AlmostInvariant
