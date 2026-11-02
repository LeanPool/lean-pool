/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.MacMahon.Data

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Inventories and physical constructions
-/

@[expose] public section

namespace MacMahon
open scoped BigOperators

/-- A variety offers a specified oriented corner. -/
def HasCorner (p : Pair) (c : Corner) : Prop := c ∈ cornerList p.1 p.2
instance (p : Pair) (c : Corner) : Decidable (HasCorner p c) :=
  inferInstanceAs (Decidable (c ∈ cornerList p.1 p.2))
/-- A physical cube shares at least one oriented corner with the target variety. -/
def Usable (t p : Pair) : Prop := ∃ c : Corner, HasCorner t c ∧ HasCorner p c
instance (t p : Pair) : Decidable (Usable t p) :=
  inferInstanceAs (Decidable (∃ c : Corner, HasCorner t c ∧ HasCorner p c))

/-- After a specified proper rotation, a cube matches the target on all three outward faces. -/
def FaceFits (t p : Pair) (k : Slot) (r : Fin 24) : Prop :=
  ∀ f : Fin 3, faceColours p.1 p.2 (rotations r (exposedFaces k f)) =
    faceColours t.1 t.2 (exposedFaces k f)
instance (t p : Pair) (k : Slot) (r : Fin 24) : Decidable (FaceFits t p k r) :=
  inferInstanceAs (Decidable (∀ f : Fin 3,
    faceColours p.1 p.2 (rotations r (exposedFaces k f)) =
      faceColours t.1 t.2 (exposedFaces k f)))

/-- Distinct physical copies of the varieties with the prescribed multiplicities. -/
abbrev Stock (a : Inventory) := (p : Pair) × Fin (a p)
/-- An injective allocation of eight physical copies matching the target corners. -/
def Builds (a : Inventory) (t : Pair) : Prop :=
  ∃ f : Slot ↪ Stock a, ∀ k, HasCorner (f k).1 (cornerAt t.1 t.2 k)
/-- Eight distinct cubes with proper rotations matching all outward target faces. -/
def PhysicalBuilds (a : Inventory) (t : Pair) : Prop :=
  ∃ f : Slot ↪ Stock a, ∀ k, ∃ r : Fin 24, FaceFits t (f k).1 k r
/-- Every valid target variety admits a physical assembly from the inventory. -/
def PhysicalUniversal (a : Inventory) : Prop :=
  ∀ i j : Label, i ≠ j → PhysicalBuilds a (i, j)
/-- Every valid target variety admits a corner-matching assembly from the inventory. -/
def Universal (a : Inventory) : Prop := ∀ i j : Label, i ≠ j → Builds a (i, j)
/-- The invalid diagonal tableau entries have zero multiplicity. -/
def DiagonalZero (a : Inventory) : Prop := ∀ i : Label, a (i, i) = 0
/-- The number of physical cubes in an inventory. -/
def total (a : Inventory) : ℕ := ∑ p, a p
/-- The total multiplicity in a fixed Conway tableau row. -/
def row (a : Inventory) (i : Label) : ℕ := ∑ j, a (i, j)
/-- The total multiplicity in a fixed Conway tableau column. -/
def col (a : Inventory) (j : Label) : ℕ := ∑ i, a (i, j)
/-- The number of physical copies sharing a corner with a given target. -/
def usableCount (a : Inventory) (t : Pair) : ℕ :=
  ∑ p : Pair, if Usable t p then a p else 0

end MacMahon
