/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.GoldbergSeymour.ChromaticIndexSpec
public import LeanPool.GoldbergSeymour.ProperColoringRestricts

/-!
# Chromatic Index Restrict

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ChromaticIndexRestrict {V E : Type*} [Finite V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E) :
    ChromaticIndex (RestrictEdges G F) ≤ ChromaticIndex G := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨φ, hproper, hfull⟩ := (ChromaticIndexSpec G).1
  apply (ChromaticIndexSpec (RestrictEdges G F)).2 (ChromaticIndex G)
  refine ⟨(fun e => φ e.1), ProperColoringRestricts G F φ hproper, ?_⟩
  intro e
  exact hfull e.1

end GoldbergSeymour

end
