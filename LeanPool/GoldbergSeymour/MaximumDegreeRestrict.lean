/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.Sets

public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.RestrictEdges

/-!
# Maximum Degree Restrict

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem MaximumDegreeRestrict {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E) :
    MaximumDegree (RestrictEdges G F) ≤ MaximumDegree G := by
  classical
  unfold MaximumDegree
  have degree_le (v : V) : Degree (RestrictEdges G F) v ≤ Degree G v := by
    unfold Degree
    apply Finset.card_le_card_of_injOn (fun e : {e // e ∈ F} => e.1)
    · intro e he
      have filtered := Finset.mem_filter.mp he
      have incident : v ∈ G.ends e.1 := by
        simpa [Incident, RestrictEdges] using filtered.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, incident⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
  apply Finset.max'_le
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_image] at hn
  rcases hn with rfl | ⟨v, hv, hdeg⟩
  · exact Nat.zero_le _
  · rw [← hdeg]
    have member : Degree G v ∈ insert 0 (Finset.image (fun v => Degree G v) Finset.univ) :=
      Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨v, Finset.mem_univ _, rfl⟩)
    exact (degree_le v).trans (Finset.le_max'
      (insert 0 (Finset.image (fun v => Degree G v) Finset.univ)) (Degree G v) member)

end GoldbergSeymour

end
