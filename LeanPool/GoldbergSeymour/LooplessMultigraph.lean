/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Sym.Sym2

/-!
# Loopless Multigraph

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- A multigraph with independently identified edges, unordered endpoint pairs and no loops. -/
structure LooplessMultigraph (V E : Type*) where
  /-- The unordered pair of endpoints of each independently identified edge. -/
  ends : E → Sym2 V
  loopless : ∀ e v, ends e ≠ s(v, v)

end GoldbergSeymour

end
