/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Main
public import LeanPool.Vizing.Endpoints

/-!
# Critical graphs, colourings of `G − e`, missing colours

Built on the partial edge colourings `PEC` of the registered Vizing entry.

* `IsClassTwo G`: `G` has no proper edge colouring with `Δ(G)` colours.
* `IsDeltaCritical G`: `G` is connected, of class two, and `G − e` is `Δ(G)`-edge-colourable
  for every edge `e`.
* `IsOverfull G`: `|E(G)| > Δ(G) ⌊|V(G)|/2⌋`.
* `IsColMinus c a b`: the partial colouring `c` colours every edge of `G` except `ab`.
* `missing c v`: the colours missing (free) at `v`; `Elementary c X`: missing sets pairwise
  disjoint on `X`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `G` is of class two: no proper edge colouring with `Δ(G)` colours. -/
def IsClassTwo (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ¬ G.lineGraph.Colorable G.maxDegree

/-- `G` is `Δ`-critical: connected, of class two, and every edge-deleted subgraph is
`Δ(G)`-edge-colourable. -/
def IsDeltaCritical (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ IsClassTwo G ∧
    ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).lineGraph.Colorable G.maxDegree

/-- `G` is overfull: `|E(G)| > Δ(G) ⌊|V(G)|/2⌋`. -/
def IsOverfull (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.maxDegree * (Fintype.card V / 2) < #G.edgeFinset

omit [DecidableEq V] in
theorem not_total_of_classTwo (h : IsClassTwo G) (c : PEC G (Fin G.maxDegree)) :
    ¬ ∀ u v, G.Adj u v → c.col u v ≠ none := by
  classical
  exact fun htot => h ⟨c.lineGraphColoring htot⟩

/-- `c` colours every edge of `G` except `ab`. -/
structure IsColMinus {k : ℕ} (c : PEC G (Fin k)) (a b : V) : Prop where
  adj : G.Adj a b
  uncol : c.col a b = none
  total : ∀ u v, G.Adj u v → s(u, v) ≠ s(a, b) → c.col u v ≠ none

/-- The colours missing at `v`. -/
noncomputable def missing {k : ℕ} (c : PEC G (Fin k)) (v : V) : Finset (Fin k) :=
  by classical exact univ.filter fun γ => c.IsFree v γ

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem mem_missing {k : ℕ} {c : PEC G (Fin k)} {v : V} {γ : Fin k} :
    γ ∈ missing c v ↔ c.IsFree v γ := by
  classical
  simp [missing]

/-- `X` is elementary for `c`: the missing sets of distinct vertices of `X` are disjoint. -/
def Elementary {k : ℕ} (c : PEC G (Fin k)) (X : Set V) : Prop :=
  ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ∀ γ, c.IsFree u γ → ¬ c.IsFree v γ

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- A colouring of `G − ab` from a colouring of the line graph of `G − ab`. -/
theorem exists_colMinus_of_colorable {a b : V} (hab : G.Adj a b) {k : ℕ}
    (hcol : (G.deleteEdges {s(a, b)}).lineGraph.Colorable k) :
    ∃ c : PEC G (Fin k), IsColMinus c a b := by
  classical
  obtain ⟨C⟩ := hcol
  have hmem : ∀ {u v}, G.Adj u v → s(u, v) ≠ s(a, b) →
      s(u, v) ∈ (G.deleteEdges {s(a, b)}).edgeSet := fun huv hne => by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨huv, hne⟩
  let col : V → V → Option (Fin k) := fun u v =>
    if h : G.Adj u v ∧ s(u, v) ≠ s(a, b) then some (C ⟨s(u, v), hmem h.1 h.2⟩) else none
  have hcol_symm : ∀ u v, col u v = col v u := by
    intro u v
    simp only [col]
    by_cases h : G.Adj u v ∧ s(u, v) ≠ s(a, b)
    · have h' : G.Adj v u ∧ s(v, u) ≠ s(a, b) := ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
      rw [dite_eq_left h, dite_eq_left h']
      congr 2
      exact Subtype.ext Sym2.eq_swap
    · have h' : ¬ (G.Adj v u ∧ s(v, u) ≠ s(a, b)) := fun h' =>
        h ⟨h'.1.symm, by rw [Sym2.eq_swap]; exact h'.2⟩
      rw [dite_eq_right h, dite_eq_right h']
  refine ⟨⟨col, hcol_symm, fun {u v γ} h => ?_, fun {u v w γ} h1 h2 => ?_⟩, ⟨hab, ?_, ?_⟩⟩
  · simp only [col] at h
    split_ifs at h with hh
    exact hh.1
  · simp only [col] at h1 h2
    split_ifs at h1 h2 with hv hw
    by_contra hne
    have hadj : (G.deleteEdges {s(a, b)}).lineGraph.Adj ⟨s(u, v), hmem hv.1 hv.2⟩
        ⟨s(u, w), hmem hw.1 hw.2⟩ := by
      rw [lineGraph_adj_iff_exists]
      refine ⟨fun h => hne ?_, u, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
      rcases Sym2.eq_iff.1 (congrArg Subtype.val h) with ⟨-, h⟩ | ⟨h1, h2⟩
      · exact h
      · exact h2.trans h1
    exact C.valid hadj (Option.some_injective _ (h1.trans h2.symm))
  · change col a b = none
    simp only [col]
    rw [dite_eq_right (fun h => h.2 rfl)]
  · intro u v huv hne
    change col u v ≠ none
    simp only [col]
    rw [dite_eq_left ⟨huv, hne⟩]
    exact Option.some_ne_none _
end Overfull

end LeanPool.BalancedEdgeColourings
