/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.Sets

public import LeanPool.GoldbergSeymour.DensityCeil
public import LeanPool.GoldbergSeymour.RestrictEdges

/-!
# Density Monotone

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem DensityMonotone {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E) :
    DensityCeil (RestrictEdges G F) ≤ DensityCeil G := by
  classical
  unfold DensityCeil Density
  dsimp
  apply Nat.ceil_mono
  apply Finset.max'_le
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · rcases Finset.mem_image.mp hq with ⟨U, hU, rfl⟩
    have hcard : (InternalEdges (RestrictEdges G F) U).card ≤
        (InternalEdges G U).card := by
      rw [← Finset.card_image_iff.mpr (fun a ha b hb hab => Subtype.ext hab)]
      apply Finset.card_le_card
      intro e he
      rcases Finset.mem_image.mp he with ⟨e', he', heq⟩
      subst e
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have heprop := (Finset.mem_filter.mp he').2
      intro v hv
      apply heprop v
      simpa [Incident, RestrictEdges] using hv
    have hden : 0 < U.card - 1 := by
      have hsize : 3 ≤ U.card := (Finset.mem_filter.mp hU).2.1
      omega
    have hvalue : DensityValue (RestrictEdges G F) U ≤ DensityValue G U := by
      unfold DensityValue
      apply div_le_div_of_nonneg_right
      · exact_mod_cast Nat.mul_le_mul_left 2 hcard
      · have hone : (1 : ℚ) ≤ U.card := by
          exact_mod_cast (show 1 ≤ U.card by omega)
        linarith
    exact le_trans hvalue
      (Finset.le_max' _ _ (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨U, hU, rfl⟩)))

end GoldbergSeymour

end
