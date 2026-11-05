/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidentCoreDegree
public import LeanPool.GoldbergSeymour.MaximumDegree

/-!
# Incident Core Maximum Degree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreMaximumDegree {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) :
    MaximumDegree (IncidentCore G) = MaximumDegree G := by
  classical
  unfold MaximumDegree
  apply Nat.le_antisymm
  · apply Finset.max'_le
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
      true_and] at hy
    rcases hy with rfl | ⟨x, rfl⟩
    · exact Nat.zero_le _
    · rw [IncidentCoreDegree G x]
      apply Finset.le_max'
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x.1, by simp⟩)
  · apply Finset.max'_le
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
      true_and] at hy
    rcases hy with rfl | ⟨v, rfl⟩
    · exact Nat.zero_le _
    · by_cases hz : Degree G v = 0
      · rw [hz]
        exact Nat.zero_le _
      · have hpos : 0 < Degree G v := Nat.pos_of_ne_zero hz
        unfold Degree at hpos
        obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
        have hie : Incident G v e := (Finset.mem_filter.mp he).2
        let x : IncidentVertex G := ⟨v, e, hie⟩
        rw [← IncidentCoreDegree G x]
        apply Finset.le_max'
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, by simp⟩)

end GoldbergSeymour

end
