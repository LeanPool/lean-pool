/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Greedy colorings along a well-founded order

If every edge joins comparable vertices of a well-founded relation and every vertex has
finitely many neighbours below it, coloring each vertex by the least natural number not
used by its neighbours below is a proper coloring by `ℕ`.
-/

@[expose] public section

namespace Erdos111

/-- Greedy coloring along a well-founded relation with finitely many earlier
neighbours. -/
theorem nonempty_coloring_of_wellFounded {V : Type*} (H : SimpleGraph V) {r : V → V → Prop}
    (hr : WellFounded r) (hcomp : ∀ u v, H.Adj u v → r u v ∨ r v u)
    (hfin : ∀ v, {u | r u v ∧ H.Adj u v}.Finite) : Nonempty (H.Coloring ℕ) := by
  -- color `v` by the least number not used by its neighbours below
  let c : V → ℕ := hr.fix fun v g => sInf {n | ∀ u (h : r u v), H.Adj u v → g u h ≠ n}
  have hc : ∀ v, c v = sInf {n | ∀ u, r u v → H.Adj u v → c u ≠ n} := fun v =>
    hr.fix_eq _ v
  -- the least unused number avoids every neighbour below
  have hne : ∀ u v, r u v → H.Adj u v → c u ≠ c v := by
    intro u v huv hadj
    have hmem : c v ∈ {n | ∀ u, r u v → H.Adj u v → c u ≠ n} := by
      rw [hc v]
      refine Nat.sInf_mem ?_
      obtain ⟨n, hn⟩ := ((hfin v).image c).infinite_compl.nonempty
      exact ⟨n, fun u hu hadj hcu => hn ⟨u, ⟨hu, hadj⟩, hcu⟩⟩
    exact hmem u huv hadj
  refine ⟨SimpleGraph.Coloring.mk c fun {u v} hadj => ?_⟩
  rcases hcomp u v hadj with huv | hvu
  · exact hne u v huv hadj
  · exact (hne v u hvu hadj.symm).symm

end Erdos111
