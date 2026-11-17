/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
-- Modified for Lean Pool integration.
module

public import LeanPool.MacMahon.Partitions

/-!
# Corner incidence and usable varieties
-/

@[expose] public section
namespace MacMahon
theorem cornerAt_mem : ∀ i j : Label, i ≠ j → ∀ k : Slot,
    HasCorner (i, j) (cornerAt i j k) := by decide +kernel

theorem every_corner : ∀ c : Corner, ∃ i j : Label, i ≠ j ∧
    ∃ k : Slot, cornerAt i j k = c := by decide +kernel

theorem usable_rule : ∀ i j : Label, i ≠ j → ∀ p : Pair,
    Usable (i, j) p ↔ p.1 ≠ p.2 ∧
      (p = (i, j) ∨ (p.1 ≠ i ∧ p.2 ≠ j ∧ p ≠ (j, i))) := by decide +kernel

theorem partition_corner_support : ∀ b : Fin 10, ∀ p : Pair,
    HasCorner p (partitionCorner b) → winner b p = 1 := by decide +kernel

end MacMahon
