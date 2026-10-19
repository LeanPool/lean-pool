/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Tactic
public import LeanPool.RemovalExtremalStability.StabilityGeneral

/-!

Adapted from [jtraverso/turan-stability](https://github.com/jtraverso/turan-stability/blob/3eb99033cc931add291781f77b7446dcba8f5f9d/Solution.lean) (Palomar-registered source).
# Proofs of the statements in `Challenge.lean`

The proofs are in `StabilityLib/`: `Furedi.lean` (Füredi's greedy maximum-degree partition and
Mathlib's Turán bound), `CliqueCounting.lean` (induction on the clique size with good
neighbourhoods, generalising Mathlib's triangle counting lemma), `CliqueRemoval.lean` (Szemerédi's
regularity lemma and Mathlib's reduced graph, generalising Mathlib's triangle removal lemma),
`Embedding.lean` (greedy embedding) and `StabilityGeneral.lean` (the reduced graph of an `L`-free
graph is `K_{p+1}`-free by the embedding lemma, and Füredi's theorem applied to it).
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace TuranStability

section Furedi

variable {V : Type*} [Fintype V]

/-- **Füredi's partition inequality.** Every `K_{p+1}`-free finite graph has a partition into
`p` parts (the fibres of `f`) such that the number of edges of `G` plus the number of edges of
`G` inside the parts is at most the number of edges of the complete `p`-partite graph on these
parts. -/
theorem card_edgeSet_add_le {W : Type*} [Finite W] (G : SimpleGraph W) {p : ℕ} (hp : 0 < p)
    (hG : G.CliqueFree (p + 1)) :
    ∃ f : W → Fin p, G.edgeSet.ncard + (G \ (⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard ≤
      ((⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard :=
  _root_.Furedi.card_edgeSet_add_le G hp hG

/-- **Füredi's theorem (2015).** If `G` is a `K_{p+1}`-free graph on `n` vertices with at least
`turanNumber n p - t` edges, then `G` has a `p`-colourable (i.e. `p`-partite) subgraph `H` with
at least `e(G) - t` edges. -/
theorem furedi (G : SimpleGraph V) {p t : ℕ} (hp : 0 < p) (hG : G.CliqueFree (p + 1))
    (ht : turanNumber (card V) p ≤ G.edgeSet.ncard + t) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.Colorable p ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard + t :=
  _root_.Furedi.furedi G hp hG ht

/-- **Füredi's theorem, edit-distance form.** Under the hypotheses of `furedi`, there is a
partition into `p` parts with at most `t` edges of `G` inside the parts, and `G` differs from the
complete `p`-partite graph on these parts in at most `3 t` edges. -/
theorem exists_partition_symmDiff_le (G : SimpleGraph V) {p t : ℕ} (hp : 0 < p)
    (hG : G.CliqueFree (p + 1)) (ht : turanNumber (card V) p ≤ G.edgeSet.ncard + t) :
    ∃ f : V → Fin p, (G \ (⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard ≤ t ∧
      (symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard ≤ 3 * t :=
  _root_.Furedi.exists_partition_symmDiff_le G hp hG ht

/-- **Erdős–Simonovits stability theorem for cliques** (Erdős 1967, Simonovits 1968), in the
form obtained from Füredi's theorem: for every `ε > 0` there is `δ > 0` such that every
`K_{p+1}`-free graph on `n` vertices with at least `(1 - 1/p) n² / 2 - δ n²` edges differs from
some complete `p`-partite graph on the same vertices in at most `ε n²` edges. -/
theorem erdos_simonovits_stability {p : ℕ} (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (W : Type) [Fintype W] (G : SimpleGraph W), G.CliqueFree (p + 1) →
      (1 - 1 / (p : ℝ)) * (card W : ℝ) ^ 2 / 2 - δ * (card W : ℝ) ^ 2 ≤ G.edgeSet.ncard →
      ∃ f : W → Fin p,
        ((symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard : ℝ) ≤
          ε * (card W : ℝ) ^ 2 :=
  _root_.Furedi.erdos_simonovits_stability hp hε

end Furedi

section CliqueCounting

variable {α : Type*} (G : SimpleGraph α) [DecidableRel G.Adj]

/-- **Clique counting lemma, robust-density form.** If any two of the parts `s i`, `s j`
(`i ≠ j`) have edge density at least `d` between all subsets of relative size at least `η`,
`η ≤ 1` and `2 r η ≤ d ^ (r - 1)`, then at least `d ^ (r choose 2) / 2 ^ r` of the tuples in
`∏ i, s i` are cliques. (Without `η ≤ 1` the hypothesis on subsets would be vacuous.) -/
theorem card_transversalCliques_ge {r : ℕ} (s : Fin r → Finset α) {η d : ℝ} (hη : 0 < η)
    (hη₁ : η ≤ 1) (hd : 0 < d) (hηd : 2 * r * η ≤ d ^ (r - 1))
    (hs : ∀ i j, i ≠ j → ∀ A ⊆ s i, ∀ B ⊆ s j, η * #(s i) ≤ #A → η * #(s j) ≤ #B →
      d ≤ G.edgeDensity A B) :
    d ^ r.choose 2 / 2 ^ r * ∏ i, (#(s i) : ℝ) ≤
      #{x ∈ Fintype.piFinset s | ∀ i j, i ≠ j → G.Adj (x i) (x j)} :=
  _root_.CliqueCounting.card_transversalCliques_ge G s hη hη₁ hd hηd hs

/-- **Clique counting lemma, uniform form.** If every pair of distinct parts is `ε`-uniform with
edge density at least `d + ε`, and `2 r ε ≤ d ^ (r - 1)`, then at least
`d ^ (r choose 2) / 2 ^ r` of the tuples in `∏ i, s i` are cliques. -/
theorem card_transversalCliques_ge_of_isUniform {r : ℕ} (s : Fin r → Finset α) {ε d : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (hεd : 2 * r * ε ≤ d ^ (r - 1))
    (hu : ∀ i j, i ≠ j → G.IsUniform ε (s i) (s j))
    (hdens : ∀ i j, i ≠ j → d + ε ≤ G.edgeDensity (s i) (s j)) :
    d ^ r.choose 2 / 2 ^ r * ∏ i, (#(s i) : ℝ) ≤
      #{x ∈ Fintype.piFinset s | ∀ i j, i ≠ j → G.Adj (x i) (x j)} :=
  _root_.CliqueCounting.card_transversalCliques_ge_of_isUniform G s hε hd hεd hu hdens

/-- **Clique counting lemma.** If `s : Fin r → Finset α` are pairwise disjoint sets of vertices,
every two of them `ε`-uniform with edge density at least `d + ε`, and `2 r ε ≤ d ^ (r - 1)`,
then `G` has at least `d ^ (r choose 2) / 2 ^ r · ∏ i, #(s i)` cliques of size `r`. -/
theorem card_cliqueFinset_ge [Fintype α] [DecidableEq α] {r : ℕ} (s : Fin r → Finset α)
    {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (hεd : 2 * r * ε ≤ d ^ (r - 1))
    (hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j))
    (hu : ∀ i j, i ≠ j → G.IsUniform ε (s i) (s j))
    (hdens : ∀ i j, i ≠ j → d + ε ≤ G.edgeDensity (s i) (s j)) :
    d ^ r.choose 2 / 2 ^ r * ∏ i, (#(s i) : ℝ) ≤ #(G.cliqueFinset r) :=
  _root_.CliqueCounting.card_cliqueFinset_ge G s hε hd hεd hdisj hu hdens

end CliqueCounting

section CliqueRemoval

/-- **Clique removal lemma, far form.** For every `r` and `ε > 0` there is `δ > 0` such that a
finite graph on `n` vertices that is `ε n²`-far from being `K_r`-free (in the sense of Mathlib's
`SimpleGraph.DeleteFar`) has at least `δ n^r` cliques of size `r`. -/
theorem le_card_cliqueFinset_of_deleteFar (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj], G.DeleteFar (fun H ↦ H.CliqueFree r) (ε * (card α ^ 2 : ℕ)) →
        δ * card α ^ r ≤ #(G.cliqueFinset r) :=
  _root_.CliqueRemoval.le_card_cliqueFinset_of_deleteFar r hε

/-- **Clique removal lemma.** For every `r` and `ε > 0` there is `δ > 0` such that every finite
graph on `n` vertices with fewer than `δ n^r` cliques of size `r` has a `K_r`-free subgraph
obtained by deleting fewer than `ε n²` edges. -/
theorem clique_removal (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj], (#(G.cliqueFinset r) : ℝ) < δ * card α ^ r →
        ∃ G' ≤ G, ∃ _ : DecidableRel G'.Adj,
          (#G.edgeFinset - #G'.edgeFinset : ℝ) < ε * (card α ^ 2 : ℕ) ∧ G'.CliqueFree r :=
  _root_.CliqueRemoval.clique_removal r hε

end CliqueRemoval

section Embedding

variable {α : Type*} (G : SimpleGraph α) [DecidableRel G.Adj]

/-- **Embedding lemma, robust-density form.** Let `L` be a graph on a finite type `β` with
`k = card β` vertices and a proper colouring `c : β → Fin r`. Suppose that for all colours
`i ≠ j`, all subsets `A ⊆ s i`, `B ⊆ s j` with `#A ≥ η #(s i)` and `#B ≥ η #(s j)` have edge
density at least `d`, where `0 < η ≤ 1`, `0 < d ≤ 1`, `2 k η ≤ d ^ k`, and every part has at least
`2 k / d ^ k` vertices. Then there is an injective map `f : β → α` sending each `x` into `s (c x)`
and edges of `L` to edges of `G`. -/
theorem exists_embedding {β : Type*} [Fintype β] (L : SimpleGraph β) {r : ℕ}
    (c : β → Fin r) (hc : ∀ x y, L.Adj x y → c x ≠ c y) (s : Fin r → Finset α) {η d : ℝ}
    (hη : 0 < η) (hη₁ : η ≤ 1) (hd : 0 < d) (hd₁ : d ≤ 1)
    (hηd : 2 * card β * η ≤ d ^ card β) (hsize : ∀ i, 2 * card β ≤ d ^ card β * #(s i))
    (hs : ∀ i j, i ≠ j → ∀ A ⊆ s i, ∀ B ⊆ s j, η * #(s i) ≤ #A → η * #(s j) ≤ #B →
      d ≤ G.edgeDensity A B) :
    ∃ f : β → α, Function.Injective f ∧ (∀ x, f x ∈ s (c x)) ∧
      ∀ x y, L.Adj x y → G.Adj (f x) (f y) :=
  _root_.Embedding.exists_embedding G L c hc s hη hη₁ hd hd₁ hηd hsize hs

/-- **Embedding lemma, uniform form.** Under the hypotheses of `exists_embedding`, with the
robust density condition replaced by: every pair of distinct parts is `ε`-uniform with edge
density at least `d + ε`, and `2 k ε ≤ d ^ k`. -/
theorem exists_embedding_of_isUniform {β : Type*} [Fintype β]
    (L : SimpleGraph β) {r : ℕ} (c : β → Fin r) (hc : ∀ x y, L.Adj x y → c x ≠ c y)
    (s : Fin r → Finset α) {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (hd₁ : d ≤ 1)
    (hεd : 2 * card β * ε ≤ d ^ card β) (hsize : ∀ i, 2 * card β ≤ d ^ card β * #(s i))
    (hu : ∀ i j, i ≠ j → G.IsUniform ε (s i) (s j))
    (hdens : ∀ i j, i ≠ j → d + ε ≤ G.edgeDensity (s i) (s j)) :
    ∃ f : β → α, Function.Injective f ∧ (∀ x, f x ∈ s (c x)) ∧
      ∀ x y, L.Adj x y → G.Adj (f x) (f y) :=
  _root_.Embedding.exists_embedding_of_isUniform G L c hc s hε hd hd₁ hεd hsize hu hdens

/-- **Embedding lemma, containment form.** Under the hypotheses of
`exists_embedding_of_isUniform`, `L` is contained in `G` (`L ⊑ G`, Mathlib's
`SimpleGraph.IsContained`). -/
theorem isContained_of_isUniform {β : Type*} [Fintype β]
    (L : SimpleGraph β) {r : ℕ} (c : β → Fin r) (hc : ∀ x y, L.Adj x y → c x ≠ c y)
    (s : Fin r → Finset α) {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (hd₁ : d ≤ 1)
    (hεd : 2 * card β * ε ≤ d ^ card β) (hsize : ∀ i, 2 * card β ≤ d ^ card β * #(s i))
    (hu : ∀ i j, i ≠ j → G.IsUniform ε (s i) (s j))
    (hdens : ∀ i j, i ≠ j → d + ε ≤ G.edgeDensity (s i) (s j)) :
    L.IsContained G :=
  _root_.Embedding.isContained_of_isUniform G L c hc s hε hd hd₁ hεd hsize hu hdens

end Embedding

section ErdosSimonovits

/-- **Erdős–Simonovits stability theorem.** Let `L` be a finite graph that is
`(p + 1)`-colourable. For every `ε > 0` there are `δ > 0` and `n₀` such that every graph `G` on
`n ≥ n₀` vertices that does not contain `L` and has at least `(1 - 1/p) n² / 2 - δ n²` edges
differs from some complete `p`-partite graph on the same vertices in at most `ε n²` edges. -/
theorem stability {β : Type} [Finite β] (L : SimpleGraph β) {p : ℕ} (hp : 0 < p)
    (hL : L.Colorable (p + 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ (W : Type) [Fintype W] (G : SimpleGraph W), n₀ ≤ card W →
      ¬ L.IsContained G →
      (1 - 1 / (p : ℝ)) * (card W : ℝ) ^ 2 / 2 - δ * (card W : ℝ) ^ 2 ≤ G.edgeSet.ncard →
      ∃ f : W → Fin p,
        ((symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard : ℝ) ≤
          ε * (card W : ℝ) ^ 2 :=
  _root_.ErdosSimonovits.stability L hp hL hε

end ErdosSimonovits

end TuranStability
