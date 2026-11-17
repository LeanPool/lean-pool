/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.SimpleGraphAddVertex
import LeanPool.FiniteRamsey.SimpleGraphLemmas

/-!
# Clique-saturated graphs

A graph `G` is `n`-clique-*edge*-saturated if it is `n`-clique-free but adding any missing edge
creates an `n`-clique, the classical `K_n`-saturated graph of extremal graph theory. This file
also names the vertex-addition analogue, `SimpleGraph.CliqueVertexSaturated`: `n`-clique-free, but
extending by any new vertex (with any neighbourhood among the old vertices) always creates an
`n`-clique.

## Naming

`CliqueVertexSaturated` is not called `CliqueVertexCritical`: "vertex-critical" is standard
graph-theory terminology for *chromatic* criticality (`G` is `k`-vertex-critical if `χ(G) = k` but
`χ(G - v) < k` for every vertex `v`), a different notion from the one defined here. Naming this
predicate after `CliqueEdgeSaturated` instead avoids that collision and makes the
vertex-addition/edge-addition parallel explicit.

This file imports `LeanPool.FiniteRamsey.SimpleGraphLemmas` (for
`SimpleGraph.cliqueFree_iso_iff` and `SimpleGraph.Iso.supEdge`) and
`LeanPool.FiniteRamsey.SimpleGraphAddVertex` (for `SimpleGraph.addVertex` and its
isomorphism transport); in a real PR series these would instead be ordinary
`Mathlib.Combinatorics.SimpleGraph` imports once those earlier files have landed upstream.

## Main declarations

* `SimpleGraph.CliqueVertexSaturated`: `n`-clique-free, and every one-vertex extension creates an
  `n`-clique.
* `SimpleGraph.CliqueEdgeSaturated`: `n`-clique-free, and every one-edge extension between
  *distinct, non-adjacent* vertices creates an `n`-clique, the classical `K_n`-saturated graph.
* Both notions only depend on `G` up to isomorphism
  (`SimpleGraph.cliqueVertexSaturated_iso_iff`, `SimpleGraph.cliqueEdgeSaturated_iso_iff`).
* `SimpleGraph.not_cliqueFree_sup_edge_iff_not_cliqueFreeOn_commonNeighbors`: the common-
  neighbourhood characterisation of when adding an edge between non-adjacent `v`, `w` creates an
  `(n + 2)`-clique: exactly when `v` and `w`'s common neighbourhood already has an `n`-clique.

## References

* P. Erdős, A. Hajnal, J. W. Moon, *A problem in graph theory*, Amer. Math. Monthly 71 (1964),
  1107-1110.
* B. Bollobás, *Extremal Graph Theory*, Academic Press, 1978, Chapter 6.
* B. Currie, J. Faudree, R. Faudree, J. Schmitt, *A survey of minimum saturated graphs*, Electron.
  J. Combin., Dynamic Survey DS19 (2011).

## Tags

graph theory, extremal graph theory, saturation
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}

section Saturation

/-- `G` is `n`-clique-vertex-saturated: it is `n`-clique-free, but extending it by any new
vertex — whatever neighbourhood among the old vertices that vertex is given — always creates an
`n`-clique. The vertex-addition analogue of `n`-clique-saturation
(`SimpleGraph.CliqueEdgeSaturated`, the edge-addition analogue). -/
def CliqueVertexSaturated (G : SimpleGraph V) (n : ℕ) : Prop :=
  G.CliqueFree n ∧ ∀ N : Set V, ¬(G.addVertex N).CliqueFree n

theorem CliqueVertexSaturated.cliqueFree (h : CliqueVertexSaturated G n) : G.CliqueFree n :=
  h.1

theorem CliqueVertexSaturated.not_cliqueFree_addVertex (h : CliqueVertexSaturated G n)
    (N : Set V) : ¬(G.addVertex N).CliqueFree n :=
  h.2 N

/-- Vertex-saturation transfers back along an isomorphism. -/
theorem CliqueVertexSaturated.of_iso (e : G ≃g H) (h : CliqueVertexSaturated H n) :
    CliqueVertexSaturated G n :=
  ⟨(cliqueFree_iso_iff e).mpr h.1, fun N hN =>
    h.2 (e '' N) ((cliqueFree_iso_iff (e.addVertex N)).mp hN)⟩

/-- Vertex-saturation only depends on `G` up to isomorphism. -/
theorem cliqueVertexSaturated_iso_iff (e : G ≃g H) (n : ℕ) :
    CliqueVertexSaturated G n ↔ CliqueVertexSaturated H n :=
  ⟨.of_iso e.symm, .of_iso e⟩

/-- `G` is `n`-clique-edge-saturated — a `K_n`-saturated graph in the classical extremal graph
theory sense: it is `n`-clique-free, but adding any missing edge between *distinct* vertices
creates an `n`-clique. The edge-addition counterpart of `SimpleGraph.CliqueVertexSaturated`.

The `v ≠ w` hypothesis is essential, not merely a convenience: without it the universal
quantifier's `v = w` instance is always available (a graph is always non-adjacent to itself,
`edge v v = ⊥`, so that instance demands `¬G.CliqueFree n`), directly contradicting the first
conjunct for every nonempty `V` — the predicate would be satisfiable only by the empty graph. -/
def CliqueEdgeSaturated (G : SimpleGraph V) (n : ℕ) : Prop :=
  G.CliqueFree n ∧ ∀ v w : V, v ≠ w → ¬G.Adj v w → ¬(G ⊔ edge v w).CliqueFree n

theorem CliqueEdgeSaturated.cliqueFree (h : CliqueEdgeSaturated G n) : G.CliqueFree n :=
  h.1

theorem CliqueEdgeSaturated.not_cliqueFree_sup_edge (h : CliqueEdgeSaturated G n) {v w : V}
    (hne : v ≠ w) (hvw : ¬G.Adj v w) : ¬(G ⊔ edge v w).CliqueFree n :=
  h.2 v w hne hvw

/-- Edge-saturation transfers back along an isomorphism. -/
theorem CliqueEdgeSaturated.of_iso (e : G ≃g H) (h : CliqueEdgeSaturated H n) :
    CliqueEdgeSaturated G n :=
  ⟨(cliqueFree_iso_iff e).mpr h.1, fun v w hne hvw hcf => h.2 (e v) (e w) (e.injective.ne hne)
    (mt e.map_adj_iff.mp hvw) ((cliqueFree_iso_iff (e.supEdge v w)).mp hcf)⟩

/-- Edge-saturation only depends on `G` up to isomorphism. -/
theorem cliqueEdgeSaturated_iso_iff (e : G ≃g H) (n : ℕ) :
    CliqueEdgeSaturated G n ↔ CliqueEdgeSaturated H n :=
  ⟨.of_iso e.symm, .of_iso e⟩

end Saturation

section CommonNeighborsCharacterisation

/-- **The common-neighbourhood characterisation of edge-saturation.** Given `G` is
`(n + 2)`-clique-free and `v ≠ w` are non-adjacent, adding the edge `v w` creates an
`(n + 2)`-clique exactly when `v` and `w`'s common neighbourhood already has an `n`-clique: any
`(n + 2)`-clique of `G ⊔ edge v w` must use the new edge (else it would already be an
`(n + 2)`-clique of `G`), so it consists of `v`, `w`, and an `n`-clique of `G` inside their common
neighbourhood — and conversely, `v` and `w` together with any such `n`-clique give one directly. -/
theorem not_cliqueFree_sup_edge_iff_not_cliqueFreeOn_commonNeighbors
    (hG : G.CliqueFree (n + 2)) {v w : V} (hne : v ≠ w) :
    ¬(G ⊔ edge v w).CliqueFree (n + 2) ↔ ¬G.CliqueFreeOn (G.commonNeighbors v w) n := by
  classical
  constructor
  · intro h hcf
    obtain ⟨t, ht⟩ := not_forall_not.mp h
    have ht' : (G ⊔ edge w v).IsNClique (n + 2) t := edge_comm v w ▸ ht
    have hvt := hG.mem_of_sup_edge_isNClique ht
    have hwt := hG.mem_of_sup_edge_isNClique ht'
    have hv := ht.1.sdiff_of_sup_edge
    have hw := ht'.1.sdiff_of_sup_edge
    refine hcf (t := (t.erase v).erase w) (fun x hx => ?_) ⟨hv.subset fun x hx => ?_, ?_⟩
    · simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hx
      exact ⟨hw ⟨hvt, hne⟩ ⟨hx.1.1, hx.2⟩ (Ne.symm hx.1.2), hv ⟨hwt, hne.symm⟩ hx.1 (Ne.symm hx.2)⟩
    · simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hx
      exact hx.1
    · rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm, hwt⟩),
        Finset.card_erase_of_mem hvt, ht.card_eq]
      rfl
  · intro h hcf
    obtain ⟨t, hts, ht⟩ : ∃ t : Finset V, ↑t ⊆ G.commonNeighbors v w ∧ G.IsNClique n t := by
      simpa [CliqueFreeOn] using h
    refine hcf (insert v (insert w t))
      (((ht.mono le_sup_left).insert (a := w) fun b hb => .inl (hts hb).2).insert fun b hb => ?_)
    rcases Finset.mem_insert.mp hb with rfl | hbt
    · exact .inr ((edge_adj v b v b).mpr ⟨.inl ⟨rfl, rfl⟩, hne⟩)
    · exact .inl (hts hbt).1



/-- **The complete graph is edge-saturated once it is too small to hold the target clique.**
`⊤ : SimpleGraph (Fin (n + 1))` has only `n + 1` vertices, so it is `(n + 2)`-clique-free; and
since it is complete, it has no non-adjacent pair to check, so the saturation condition holds
vacuously. A minimal witness that `CliqueEdgeSaturated` is satisfiable by a nonempty graph. -/
theorem cliqueEdgeSaturated_top (n : ℕ) :
    CliqueEdgeSaturated (⊤ : SimpleGraph (Fin (n + 1))) (n + 2) :=
  ⟨cliqueFree_of_card_lt (by simp), fun v w hne hvw => absurd ((top_adj v w).mpr hne) hvw⟩

/-- The triangle `K₃` is `4`-clique-edge-saturated: it has only `3` vertices, so is trivially
`4`-clique-free, and being complete, has no non-adjacent pair to extend. The `n = 2` case of
`cliqueEdgeSaturated_top`. -/
theorem cliqueEdgeSaturated_top_three : CliqueEdgeSaturated (⊤ : SimpleGraph (Fin 3)) 4 :=
  cliqueEdgeSaturated_top 2

end CommonNeighborsCharacterisation

end SimpleGraph
