/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.Coloring
public import LeanPool.Erdos111.Reduction

/-!
# Assembly of Erdős Problem 111: bipartizing finite subgraphs of uncountably chromatic graphs

The hypothesis of `countably_colorable_of_linear_proved` is `C`-linearity
(`linear_of_bipartizationNumber_le`), so the theorem is `nonempty_coloring_of_linear`.
The reduction (`tendsto_of_isEmpty_coloring`) turns it into the limit for every graph
that is not countably colorable, and a graph of chromatic number `ℵ₁` is one of them.
-/

@[expose] public section

open Filter
open scoped Cardinal

universe u

namespace Erdos111

/-- A graph in which every finite subgraph on `m` vertices can be made bipartite by
deleting at most `C m` edges has countable chromatic number. -/
theorem countably_colorable_of_linear_proved {V : Type u} (G : SimpleGraph V) (C : ℝ)
    (hC : ∀ H : G.Subgraph, H.verts.Finite →
      (bipartizationNumber H : ℝ) ≤ C * H.verts.ncard) :
    Nonempty (G.Coloring ℕ) :=
  nonempty_coloring_of_linear G (linear_of_bipartizationNumber_le hC)

/-- `h G n / n → ∞` for every graph `G` that is not countably colorable. -/
theorem tendsto_of_not_countably_colorable_proved {V : Type u} (G : SimpleGraph V)
    (hG : IsEmpty (G.Coloring ℕ)) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop :=
  tendsto_of_isEmpty_coloring (fun _ H _ hH => nonempty_coloring_of_linear H hH) G hG

/-- Erdős Problem 111: `h G n / n → ∞` for every graph `G` of chromatic number `ℵ₁`. -/
theorem erdos_111_proved {V : Type u} (G : SimpleGraph V) (hG : chromaticCardinal G = ℵ₁) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop :=
  tendsto_of_not_countably_colorable_proved G (isEmpty_coloring_of_chromaticCardinal hG)

end Erdos111
