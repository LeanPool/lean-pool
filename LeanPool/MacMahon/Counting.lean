/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
-- Modified for Lean Pool integration.
module

public import LeanPool.MacMahon.Incidence

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card

public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Necessary corner and inventory bounds
-/

@[expose] public section
namespace MacMahon
open scoped BigOperators

/-- A genuine solution supplies at least eight usable physical cubes. -/
theorem builds_usable_bound (a : Inventory) (i j : Label) (hij : i ≠ j)
    (hb : Builds a (i, j)) : 8 ≤ usableCount a (i, j) := by
  obtain ⟨f, hf⟩ := hb
  let U := {p : Pair // Usable (i, j) p}
  let g : Slot → ((p : U) × Fin (a p.1)) := fun k =>
    ⟨⟨(f k).1, ⟨cornerAt i j k, cornerAt_mem i j hij k, hf k⟩⟩, (f k).2⟩
  have hg : Function.Injective g := by
    intro k l h
    apply f.injective
    exact congrArg (fun z : ((p : U) × Fin (a p.1)) => (⟨z.1.1, z.2⟩ : Stock a)) h
  have hc := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin, Fintype.card_sigma] at hc
  change 8 ≤ ∑ p : U, a p.1 at hc
  have hs : (∑ p : U, a p.1) = usableCount a (i, j) := by
    rw [← Finset.sum_subtype (Finset.univ.filter (Usable (i, j))) (by simp)]
    simp [usableCount, Finset.sum_filter]
  exact hs ▸ hc

/-- Universality must supply every one of the forty corner types. -/
theorem universal_corner (a : Inventory) (h : Universal a) (c : Corner) :
    ∃ p : Pair, HasCorner p c ∧ 0 < a p := by
  obtain ⟨i, j, hij, k, hk⟩ := every_corner c
  obtain ⟨f, hf⟩ := h i j hij
  refine ⟨(f k).1, ?_, Nat.zero_lt_of_lt (f k).2.isLt⟩
  simpa [hk] using hf k

theorem universal_partition_cover (a : Inventory) (h : Universal a) (b : Fin 10) :
    0 < ∑ p : Pair, winner b p * a p := by
  obtain ⟨p, hp, ha⟩ := universal_corner a h (partitionCorner b)
  have hw := partition_corner_support b p hp
  have hs : winner b p * a p ≤ ∑ q : Pair, winner b q * a q :=
    Finset.single_le_sum (f := fun q => winner b q * a q) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ p)
  have hpos : 0 < winner b p * a p := by simpa only [hw, one_mul] using ha
  exact lt_of_lt_of_le hpos hs

end MacMahon
