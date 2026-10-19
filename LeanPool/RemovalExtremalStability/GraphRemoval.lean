/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Tactic
public import LeanPool.RemovalExtremalStability.GeneralGraphRemoval

/-!

Adapted from [jtraverso/graph-removal-lemma](https://github.com/jtraverso/graph-removal-lemma/blob/589cf03ef1e4c80ea8cdd6be77778232c62dd37c/Solution.lean) (Palomar-registered source).
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `RemovalLib/GraphRemoval.lean` (namespace `GraphRemoval`), on top of
`StabilityLib/` (the clique counting, clique removal and embedding lemmas of the registered entry
PALOMAR-2026-10-16-000024, included unchanged). The counting lemma is the greedy embedding argument
of `StabilityLib/Embedding.lean`, turned into a count of partial embeddings. The far form applies
Mathlib's Szemerédi regularity lemma (`szemeredi_regularity`) and finds a copy of `H` in the
reduced graph; its parts satisfy the hypotheses of the counting lemma. The removal lemma is its
contrapositive.
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace RemovalLemma

/-- **Counting lemma for a fixed graph.** Let `L` be a graph on a finite type `β` with
`k = card β` vertices, and `s : β → Finset α` parts of a graph `G` such that for every edge `xy` of
`L`, all subsets `A ⊆ s x`, `B ⊆ s y` with `#A ≥ η #(s x)`, `#B ≥ η #(s y)` have edge density at
least `d`, where `0 < η ≤ 1`, `0 < d ≤ 1`, `2 k η ≤ d ^ k` and every part has at least `4 k / d ^ k`
elements. Then there are at least `(d ^ k / 4) ^ k ∏ₓ #(s x)` injective maps `f : β → α` with
`f x ∈ s x` for every `x` that send edges of `L` to edges of `G`. -/
theorem card_copies_ge {α β : Type*} [Fintype β] (L : SimpleGraph β)
    (G : SimpleGraph α) [DecidableRel G.Adj] (s : β → Finset α) {η d : ℝ} (hη : 0 < η)
    (hη₁ : η ≤ 1) (hd : 0 < d) (hd₁ : d ≤ 1) (hηd : 2 * card β * η ≤ d ^ card β)
    (hsize : ∀ x, 4 * card β ≤ d ^ card β * #(s x))
    (hs : ∀ x y, L.Adj x y → ∀ A ⊆ s x, ∀ B ⊆ s y, η * #(s x) ≤ #A → η * #(s y) ≤ #B →
      d ≤ G.edgeDensity A B) :
    (d ^ card β / 4) ^ card β * ∏ x, (#(s x) : ℝ) ≤
      Nat.card {f : β ↪ α // (∀ x, f x ∈ s x) ∧ ∀ x y, L.Adj x y → G.Adj (f x) (f y)} :=
  GraphRemoval.card_copies_ge L G s hη hη₁ hd hd₁ hηd hsize hs

/-- **Graph removal lemma, far form** (Erdős–Frankl–Rödl 1986). For every finite graph `H` and
every `ε > 0` there is `δ > 0` such that every finite graph on `n` vertices that is `ε n²`-far from
being `H`-free has at least `δ n ^ (card β)` labelled copies of `H`. -/
theorem le_labelledCopyCount_of_deleteFar {β : Type} [Fintype β] (H : SimpleGraph β) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj], G.DeleteFar (fun G' ↦ H.Free G') (ε * (card α ^ 2 : ℕ)) →
        δ * card α ^ card β ≤ G.labelledCopyCount H :=
  GraphRemoval.le_labelledCopyCount_of_deleteFar H hε

/-- **Graph removal lemma** (Erdős–Frankl–Rödl 1986). For every finite graph `H` and every
`ε > 0` there is `δ > 0` such that every finite graph on `n` vertices with fewer than
`δ n ^ (card β)` labelled copies of `H` has an `H`-free subgraph obtained by deleting fewer than
`ε n²` edges. -/
theorem graph_removal {β : Type} [Fintype β] (H : SimpleGraph β) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj], (G.labelledCopyCount H : ℝ) < δ * card α ^ card β →
        ∃ G' ≤ G, ∃ _ : DecidableRel G'.Adj,
          (#G.edgeFinset - #G'.edgeFinset : ℝ) < ε * (card α ^ 2 : ℕ) ∧ H.Free G' :=
  GraphRemoval.graph_removal H hε

end RemovalLemma
