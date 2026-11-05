/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
-- Modified for Lean Pool integration.
module

public import LeanPool.MacMahon.Definitions

public import Mathlib.Data.Fintype.Powerset

/-!
# The ten two-triangle inventories
-/

@[expose] public section
namespace MacMahon

/-- The ten unordered partitions, choosing the triple containing label 0. -/
def triple : Fin 10 → Finset Label :=
  ![{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 2, 3},
    {0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5}, {0, 4, 5}]

/-- One copy of each directed edge within either triple. -/
def twoTriangles (s : Finset Label) : Inventory := fun p =>
  if p.1 ≠ p.2 ∧ ((p.1 ∈ s ∧ p.2 ∈ s) ∨ (p.1 ∉ s ∧ p.2 ∉ s)) then 1 else 0

/-- The ten candidates, defined structurally rather than by a matrix table. -/
def winner (b : Fin 10) : Inventory := twoTriangles (triple b)

lemma triple_card : ∀ b : Fin 10, (triple b).card = 3 := by decide +kernel

lemma winner_two_triangles : ∀ b : Fin 10,
    (triple b).card = 3 ∧ winner b = twoTriangles (triple b) :=
  fun b => ⟨triple_card b, rfl⟩

lemma partition_complete : ∀ s : Finset Label, s.card = 3 →
    ∃ b : Fin 10, twoTriangles s = winner b := by decide +kernel

lemma winners_iff_two_triangles (a : Inventory) :
    (∃ b : Fin 10, a = winner b) ↔
    ∃ s : Finset Label, s.card = 3 ∧ a = twoTriangles s := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨triple b, winner_two_triangles b⟩
  · rintro ⟨s, hs, rfl⟩
    exact partition_complete s hs
lemma winner_properties : ∀ b : Fin 10,
    DiagonalZero (winner b) ∧ total (winner b) = 12 ∧ ∀ p, winner b p ≤ 1 := by
  unfold DiagonalZero total
  decide +kernel

theorem winners_distinct : Function.Injective winner := by decide +kernel

end MacMahon
