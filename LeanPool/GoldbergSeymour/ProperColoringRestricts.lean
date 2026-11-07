/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.GoldbergSeymour.RestrictEdges
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring

/-!
# Proper Coloring Restricts

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ProperColoringRestricts {V E : Type*} [Finite V] [Finite E]
    (G : LooplessMultigraph V E) (F : Finset E) {k : ℕ}
    (φ : PartialEdgeColoring E k) (hφ : IsProperEdgeColoring G φ) :
    IsProperEdgeColoring (RestrictEdges G F) (fun e => φ e.1) := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  intro e f c hne hadj he hf
  apply hφ (e := e.1) (f := f.1) ?_
      (by simpa [AdjacentEdges, Incident, RestrictEdges] using hadj) he hf
  intro hef
  apply hne
  exact Subtype.ext hef

end GoldbergSeymour

end
