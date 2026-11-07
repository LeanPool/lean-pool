/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.PartialEdgeColoring
public import LeanPool.GoldbergSeymour.TashkinovExtensionKind
public import LeanPool.GoldbergSeymour.TreeSequence

/-!
# Tashkinov Series Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/--
Trees, colorings, stored colors and optional extension witnesses indexed by their series stages. -/
structure TashkinovSeriesData {V E : Type*} (G : LooplessMultigraph V E) (k rounds : ℕ)
    (e0 : E) where
  /-- The ordered tree or tree sequence recorded by this certificate. -/
  tree : Fin (rounds + 2) → TreeSequence G e0
  /-- The partial coloring or sequence of partial colorings recorded by this certificate. -/
  coloring : Fin (rounds + 1) → PartialEdgeColoring E k
  /-- The color set stored at each extension stage. -/
  stored : Fin (rounds + 1) → Finset (Fin k)
  /-- The finite set of connecting edges at each extension stage. -/
  connectingEdges : Fin (rounds + 1) → Finset E
  /-- The optional extension kind at each stage, absent at the initial stage. -/
  kind : Fin (rounds + 1) → Option TashkinovExtensionKind
  /-- The optional support vertex chosen at each extension stage. -/
  chosenVertex : Fin (rounds + 1) → Option V
  /-- The optional outside endpoint chosen at each extension stage. -/
  outsideVertex : Fin (rounds + 1) → Option V
  /-- The companion color used for the component swap at each stage. -/
  delta : Fin (rounds + 1) → Option (Fin k)
  /-- The auxiliary color or color family used by this configuration. -/
  gamma : Fin (rounds + 1) → Option (Fin k)

end GoldbergSeymour

end
