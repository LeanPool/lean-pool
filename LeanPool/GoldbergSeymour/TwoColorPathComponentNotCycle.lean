/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorComponentCycle
public import LeanPool.GoldbergSeymour.TwoColorPathComponent

/-!
# Two Color Path Component Not Cycle

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TwoColorPathComponentNotCycle {V E : Type*}
      (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (z : Sum V E)
    (hpath : TwoColorPathComponent G phi alpha beta z) :
    ¬TwoColorComponentCycle G phi alpha beta z := by
  classical
  rintro ⟨cycle, hcycle⟩
  obtain ⟨_, x, hxComponent, hxLeaf⟩ := hpath
  have hxSupport : x ∈ cycle.walk.support := (hcycle x).2 hxComponent
  let rotated := cycle.walk.rotate x hxSupport
  have hrotated : rotated.IsCycle := cycle.isCycle.rotate hxSupport
  have hfirst : (TwoColorIncidenceGraph G phi alpha beta).Adj x rotated.snd :=
    rotated.adj_snd hrotated.not_nil
  have hlast : (TwoColorIncidenceGraph G phi alpha beta).Adj x rotated.penultimate :=
    (rotated.adj_penultimate hrotated.not_nil).symm
  exact hrotated.snd_ne_penultimate (hxLeaf hfirst hlast)

end GoldbergSeymour

end
