/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidentCoreIncidence
public import LeanPool.GoldbergSeymour.IncidentVertexFintype
public import LeanPool.GoldbergSeymour.InternalEdges

/-!
# Incident Core Internal Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreInternalEdges {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (U : Finset (IncidentVertex G)) :
    (U.map ⟨(fun x : IncidentVertex G => x.1), Subtype.coe_injective⟩).card =
        U.card ∧
      InternalEdges (IncidentCore G) U =
        InternalEdges G
          (U.map ⟨(fun x : IncidentVertex G => x.1), Subtype.coe_injective⟩) := by
  classical
  constructor
  · exact Finset.card_map _
  · unfold InternalEdges
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v hv
      let x : IncidentVertex G := ⟨v, e, hv⟩
      have hx : x ∈ U := h x ((IncidentCoreIncidence G x e).2 hv)
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · intro h x hx
      have hv := h x.1 ((IncidentCoreIncidence G x e).1 hx)
      obtain ⟨y, hy, heq⟩ := Finset.mem_map.mp hv
      have hyx : y = x := Subtype.ext heq
      simpa [hyx] using hy

end GoldbergSeymour

end
