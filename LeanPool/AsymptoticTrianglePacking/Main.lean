/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.NibbleRounding
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.Closed
import LeanPool.AsymptoticTrianglePacking.Internal.WeightedBoundedEdges

/-!
# Finite near-regular hypergraph rounding

Public entry point for the finite, ceiling-carrying near-regular hypergraph nibble theorem.
-/

@[expose] public section

namespace LeanPool.AsymptoticTrianglePacking

/-- The fractional and integral triangle-packing optima differ by `o(n²)`, uniformly over finite
graphs. -/
theorem trianglePackingGap (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
        Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ) ≤
          ε * (Fintype.card V : ℝ) ^ 2 :=
  Nibble.AX1.nibbleGapHyp_holds ε hε

/-- The fractional triangle-cover optimum exceeds the integral triangle-packing optimum by at
most `o(n²)`, uniformly over finite graphs. -/
theorem triangleCoverPackingGap (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
        Nibble.AX1.tau3Star G - (Nibble.YusterE.nu3 G : ℝ) ≤
          ε * (Fintype.card V : ℝ) ^ 2 :=
  Nibble.AX1.ax1Statement_holds ε hε

end LeanPool.AsymptoticTrianglePacking
