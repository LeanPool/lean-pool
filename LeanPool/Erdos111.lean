/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.FinalAssembly

/-!
# Linear finite bipartization costs force countable graph colourings

Source: url:https://github.com/plasma-ai/erdos-111/tree/de72caf0e388c729697b6813f4ea90bfe1617c7b
Authors: Jacob Parish
Status: verified
Main declarations: `Erdos111.countably_colorable_of_linear`
Tags: graph-theory, infinite-combinatorics, graph-colouring, probability
MSC: 05C15, 05C63, 03E05
-/

/-!
# Proof of Erdős Problem 111: bipartizing finite subgraphs of uncountably chromatic graphs

Imported from `plasma-ai/erdos-111`, commit
`de72caf0e388c729697b6813f4ea90bfe1617c7b`, under Apache-2.0.
The upstream project checks these three statements with Comparator against its
Mathlib-only `Challenge.lean`. This module exports the ported proofs.
-/

@[expose] public section

open Filter
open scoped Cardinal

universe u

namespace Erdos111

/-- A graph in which every finite subgraph on `m` vertices can be made bipartite by
deleting at most `C m` edges has countable chromatic number. -/
theorem countably_colorable_of_linear {V : Type u} (G : SimpleGraph V) (C : ℝ)
    (hC : ∀ H : G.Subgraph, H.verts.Finite →
      (bipartizationNumber H : ℝ) ≤ C * H.verts.ncard) :
    Nonempty (G.Coloring ℕ) :=
  countably_colorable_of_linear_proved G C hC

/-- `h G n / n → ∞` for every graph `G` that is not countably colorable. -/
theorem tendsto_of_not_countably_colorable {V : Type u} (G : SimpleGraph V)
    (hG : IsEmpty (G.Coloring ℕ)) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop :=
  tendsto_of_not_countably_colorable_proved G hG

/-- Erdős Problem 111: `h G n / n → ∞` for every graph `G` of chromatic number `ℵ₁`. -/
theorem erdos_111 {V : Type u} (G : SimpleGraph V) (hG : chromaticCardinal G = ℵ₁) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop :=
  erdos_111_proved G hG

end Erdos111
