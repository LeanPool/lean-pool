/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/

module

public import LeanPool.GoldbergSeymour.ThmGS

/-!
# The Goldberg–Seymour edge-coloring theorem

Source: arxiv:1901.10316v2, url:https://github.com/wpegden/goldberg_seymour/tree/88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12
Authors: Wesley Pegden
Status: verified
Main declarations: `GoldbergSeymour.goldbergSeymour`, `GoldbergSeymour.GeneralHighIndexElementary`
Tags: graph-theory, edge-coloring, multigraphs, tashkinov-trees
MSC: 05C15
-/

/-!
Formalized by Trellis, operated by Wesley Pegden, following the mathematical
theorem of Guantao Chen, Guangming Jing and Wenan Zang, arXiv:1901.10316v2.
Adapted from wpegden/goldberg_seymour at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The Goldberg–Seymour bound for the chromatic index of a finite loopless multigraph. -/
theorem goldbergSeymour {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) :
    ChromaticIndex G ≤ max (MaximumDegree G + 1) (DensityCeil G) := by
  classical
  exact ThmGS G

end GoldbergSeymour

end
