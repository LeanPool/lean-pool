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
public import LeanPool.OrderClosures.BanLat.Substructures.Sublattice



/-!
# Order dense subsets of a vector lattice

A subset `s` of a vector lattice `X` is **order dense** when every strictly
positive element of `X` dominates a strictly positive element of `s`. -/

@[expose] public section

/-- A subset `s` of a preordered type with a `0` is **order dense** if every
strictly positive element dominates some strictly positive element of `s`. -/
def IsOrderDense {X : Type*} [Zero X] [Preorder X] (s : Set X) : Prop :=
  ∀ ⦃x : X⦄, 0 < x → ∃ y ∈ s, 0 < y ∧ y ≤ x

namespace IsOrderDense

variable {X : Type*} [Zero X] [Preorder X]

/-- The whole space is order dense. -/
theorem univ : IsOrderDense (Set.univ : Set X) :=
  fun _ hx => ⟨_, Set.mem_univ _, hx, le_rfl⟩

/-- Order density is monotone in the underlying set. -/
theorem mono {s t : Set X} (hst : s ⊆ t) (hs : IsOrderDense s) :
    IsOrderDense t := fun _ hx =>
  let ⟨y, hy, hy_pos, hy_le⟩ := hs hx
  ⟨y, hst hy, hy_pos, hy_le⟩

end IsOrderDense

/-- A vector sublattice is **order dense** when its underlying set is. -/
abbrev VectorSublattice.IsOrderDense {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (Y : VectorSublattice X) : Prop :=
  _root_.IsOrderDense (Y : Set X)
