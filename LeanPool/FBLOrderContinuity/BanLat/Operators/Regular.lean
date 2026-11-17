/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

/-
Authors: David Muñoz-Lahoz
-/

public import LeanPool.FBLOrderContinuity.BanLat.Sublattice
public import LeanPool.FBLOrderContinuity.BanLat.Operators.OrderBounded
public import LeanPool.OrderClosures.BanLat.OrderComplete



/-!
# Regular operators

An operator between vector lattices is **regular** (`IsRegularOp`) if it can
be written as the difference of two positive operators. Every regular operator
is order bounded; when the codomain is order complete, the converse holds.
-/

@[expose] public section

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X]
  [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]

/-- A linear map is **regular** if it is the difference of two positive
operators. -/
def IsRegularOp (f : X →ₗ[ℝ] Y) : Prop :=
  ∃ g h : X →ₗ[ℝ] Y, Positive g ∧ Positive h ∧ f = g - h

namespace IsRegularOp

/-- Every regular operator is order bounded. -/
theorem isOrderBounded {f : X →ₗ[ℝ] Y}
    (hf : IsRegularOp f) : IsOrderBounded f := by
  obtain ⟨g, h, hg, hh, rfl⟩ := hf
  exact IsOrderBounded.sub
    (Positive.isOrderBounded hg) (Positive.isOrderBounded hh)

end IsRegularOp
