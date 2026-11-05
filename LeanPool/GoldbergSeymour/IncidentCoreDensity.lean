/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DensityCeil

public import LeanPool.GoldbergSeymour.IncidentCoreInternalEdges

/-!
# Incident Core Density

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreDensity {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) :
    DensityCeil (IncidentCore G) ≤ DensityCeil G := by
  classical
  unfold DensityCeil Density
  dsimp
  apply Nat.ceil_mono
  apply Finset.max'_le
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · rcases Finset.mem_image.mp hq with ⟨U, hU, rfl⟩
    let image : Finset V := U.map
      ⟨(fun x : IncidentVertex G => x.1), Subtype.coe_injective⟩
    have hdata := IncidentCoreInternalEdges G U
    have hcard : image.card = U.card := hdata.1
    have hodd : Odd image.card := by
      rw [hcard]
      exact (Finset.mem_filter.mp hU).2.2
    have hlarge : 3 ≤ image.card := by
      rw [hcard]
      exact (Finset.mem_filter.mp hU).2.1
    have himage : EligibleOddSet image := ⟨hlarge, hodd⟩
    have hvalue : DensityValue (IncidentCore G) U = DensityValue G image := by
      unfold DensityValue
      rw [hdata.2, hcard]
    rw [hvalue]
    exact Finset.le_max' _ _
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨image, by
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by
          intro v hv
          exact Finset.mem_univ v), himage⟩, rfl⟩))

end GoldbergSeymour

end
