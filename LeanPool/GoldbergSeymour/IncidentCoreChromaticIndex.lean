/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ChromaticIndexSpec
public import LeanPool.GoldbergSeymour.IncidentCoreColoringTransport
public import LeanPool.GoldbergSeymour.IncidentVertexFintype

/-!
# Incident Core Chromatic Index

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreChromaticIndex {V E : Type*} [Finite V] [Fintype E]
    (G : LooplessMultigraph V E) :
    ChromaticIndex (IncidentCore G) = ChromaticIndex G ∧
      ∀ F : Finset E,
        ChromaticIndex (RestrictEdges (IncidentCore G) F) =
          ChromaticIndex (RestrictEdges G F) := by
  classical
  let _ := Fintype.ofFinite V
  have full : ChromaticIndex (IncidentCore G) = ChromaticIndex G := by
    apply Nat.le_antisymm
    · obtain ⟨phi, hp, hf⟩ := (ChromaticIndexSpec G).1
      apply (ChromaticIndexSpec (IncidentCore G)).2 (ChromaticIndex G)
      exact ⟨phi, (IncidentCoreColoringTransport G).2.1
        (ChromaticIndex G) phi |>.2 hp, hf⟩
    · obtain ⟨phi, hp, hf⟩ := (ChromaticIndexSpec (IncidentCore G)).1
      apply (ChromaticIndexSpec G).2 (ChromaticIndex (IncidentCore G))
      exact ⟨phi, (IncidentCoreColoringTransport G).2.1
        (ChromaticIndex (IncidentCore G)) phi |>.1 hp, hf⟩
  refine ⟨full, ?_⟩
  intro F
  apply Nat.le_antisymm
  · obtain ⟨phi, hp, hf⟩ := (ChromaticIndexSpec (RestrictEdges G F)).1
    apply (ChromaticIndexSpec (RestrictEdges (IncidentCore G) F)).2
      (ChromaticIndex (RestrictEdges G F))
    exact ⟨phi, (IncidentCoreColoringTransport G).2.2.2 F
      (ChromaticIndex (RestrictEdges G F)) phi |>.2 hp, hf⟩
  · obtain ⟨phi, hp, hf⟩ :=
      (ChromaticIndexSpec (RestrictEdges (IncidentCore G) F)).1
    apply (ChromaticIndexSpec (RestrictEdges G F)).2
      (ChromaticIndex (RestrictEdges (IncidentCore G) F))
    exact ⟨phi, (IncidentCoreColoringTransport G).2.2.2 F
      (ChromaticIndex (RestrictEdges (IncidentCore G) F)) phi |>.1 hp, hf⟩

end GoldbergSeymour

end
