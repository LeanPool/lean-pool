/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.SetTheory.Cardinal.Finite

public import LeanPool.MacMahon.Arithmetic
public import LeanPool.MacMahon.Classification
public import LeanPool.MacMahon.Colourings
public import LeanPool.MacMahon.Geometry
public import LeanPool.MacMahon.Witness

/-!
# Minimum universal collections of coloured cubes
-/

@[expose] public section
namespace MacMahon

/-- Complete classification, including inventories with repeated physical cubes. -/
theorem classification (a : Inventory) (hz : DiagonalZero a) (ht : total a = 12) :
    Universal a ↔ ∃ b : Fin 10, a = winner b := by
  constructor
  · intro h
    have hr := rows_two a hz h ht
    have hc := cols_two a hz h ht
    have hs := symmetric_of_degree_two a hr hc (reverse_bound a hz h ht)
    exact classify_degree_two a hz hr hs (universal_partition_cover a h)
  · rintro ⟨b, rfl⟩
    exact winner_universal b

theorem minimum_has_no_repeats (a : Inventory) (hz : DiagonalZero a)
    (ht : total a = 12) (h : Universal a) : ∀ p, a p ≤ 1 := by
  obtain ⟨b, rfl⟩ := (classification a hz ht).mp h
  exact (winner_properties b).2.2

/-- Universal corner-matching inventories attaining size twelve. -/
abbrev MinimumInventory := {a : Inventory // DiagonalZero a ∧ total a = 12 ∧ Universal a}

/-- The minimum inventory supplied by one of the ten triple partitions. -/
def minimumMap (b : Fin 10) : MinimumInventory :=
  ⟨winner b, (winner_properties b).1, (winner_properties b).2.1, winner_universal b⟩

/-- Classify the labelled minimum inventories by the ten triple partitions. -/
noncomputable def minimumEquiv : Fin 10 ≃ MinimumInventory :=
  Equiv.ofBijective minimumMap ⟨by
    intro b c h
    exact winners_distinct (congrArg Subtype.val h), by
    rintro ⟨a, hz, ht, hu⟩
    obtain ⟨b, hb⟩ := (classification a hz ht).mp hu
    exact ⟨b, Subtype.ext hb.symm⟩⟩

/-- Exactly ten labelled minimum universal inventories exist. -/
theorem exactly_ten : Nat.card MinimumInventory = 10 := by
  rw [← Nat.card_congr minimumEquiv]
  simp

theorem physical_minimum (a : Inventory) (hz : DiagonalZero a)
    (h : PhysicalUniversal a) : 12 ≤ total a :=
  universal_minimum a hz ((universal_iff_physical a).mpr h)

theorem physical_classification (a : Inventory) (hz : DiagonalZero a) (ht : total a = 12) :
    PhysicalUniversal a ↔ ∃ b : Fin 10, a = winner b := by
  rw [← universal_iff_physical, classification a hz ht]

/-- The structural form of the classification: two disjoint triangles. -/
theorem physical_iff_two_triangles (a : Inventory) (hz : DiagonalZero a)
    (ht : total a = 12) : PhysicalUniversal a ↔
    ∃ s : Finset Label, s.card = 3 ∧ a = twoTriangles s := by
  rw [physical_classification a hz ht, winners_iff_two_triangles]

/-- Physically universal inventories attaining size twelve. -/
abbrev MinimumPhysicalInventory :=
  {a : Inventory // DiagonalZero a ∧ total a = 12 ∧ PhysicalUniversal a}

theorem physical_exactly_ten : Nat.card MinimumPhysicalInventory = 10 := by
  have e : MinimumInventory ≃ MinimumPhysicalInventory :=
    Equiv.subtypeEquivRight (fun a => by rw [universal_iff_physical])
  rw [← Nat.card_congr e]
  exact exactly_ten

theorem minimum_size : IsLeast
    {n : ℕ | ∃ a : Inventory, DiagonalZero a ∧ PhysicalUniversal a ∧ total a = n} 12 := by
  constructor
  · exact ⟨winner 0, (winner_properties 0).1,
      (universal_iff_physical _).mp (winner_universal 0), (winner_properties 0).2.1⟩
  · rintro n ⟨a, hz, hu, rfl⟩
    exact physical_minimum a hz hu

end MacMahon
