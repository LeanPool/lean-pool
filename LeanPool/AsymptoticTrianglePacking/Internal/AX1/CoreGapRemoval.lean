/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the triangle-removal branch of the AX1 core gap

`Nibble.AX1.CoreGapAt ε δ` (`Nibble.CoreGapAX1`) is the residual of AX1: the packing gap
`ν₃*(G) − ν₃(G) ≤ ε|V|²` for large graphs all of whose vertices are isolated or of degree `≥ δ|V|`.
Two branches were already proved unconditionally: `Nibble.AX1.coreGapAt_of_ninth` (`ε ≥ 1/9`) and
`Nibble.AX1.coreGapAt_dense` (`δ ≥ θ(ε)`).  This file adds a third, orthogonal one, and uses it to
shrink the residual.

* `Nibble.AX1.nu3star_le_of_few_triangles` — **the removal branch**: for every `ε > 0`, every graph
  with fewer than `triangleRemovalBound(ε)·|V|³` triangles already has `ν₃* ≤ ε|V|²`, hence
  (`Nibble.AX1.gap_le_of_few_triangles`) packing gap at most `ε|V|²`.

  The proof is Mathlib's triangle removal lemma (`SimpleGraph.triangle_removal`): a graph with
  `o(|V|³)` triangles becomes triangle-free after deleting `< ε|V|²` edges, and *every* triangle of
  `G` then contains a deleted edge, so the whole fractional packing is carried by the deleted edges
  — each of load at most `1` (`Nibble.AX1.nu3star_le_add_deleted` with a triangle-free residue).

  This strictly extends the previously proved triangle-poor branch
  `Nibble.AX1.nibbleGap_fewTriangles`, which needs `#triangles ≤ ε|V|²`: the threshold here is at
  the natural cubic scale `|V|³`.

* `Nibble.AX1.CoreGapAtRich`, `Nibble.AX1.CoreGapRichResidual` — the residual restricted to
  *triangle-rich* graphs (`κ|V|³ ≤ #triangles`), and `Nibble.AX1.coreGapResidual_of_rich`,
  `Nibble.AX1.rich_of_coreGapResidual` — the two reductions, so the restricted residual is
  *equivalent* to `Nibble.AX1.CoreGapResidual`: the removal branch removes the triangle-poor
  instances from the residual at no cost, and nothing is smuggled in.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapAX1
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-! # CoreGapRemoval -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Counting the deleted edges -/

/-- The `2`-cliques lost when passing to a subgraph are at most the edges lost: the endpoint map
`Sym2 V → Finset V` sends the deleted edges onto the deleted `2`-cliques. -/
theorem card_clique2_sdiff_le (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G' ≤ G) :
    ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ)
      ≤ (G.edgeFinset.card : ℝ) - (G'.edgeFinset.card : ℝ) := by
  classical
  have hsub : G'.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hle
  have hsurj : Set.SurjOn (fun e : Sym2 V => e.toFinset)
      ((G.edgeFinset \ G'.edgeFinset : Finset (Sym2 V)) : Set (Sym2 V))
      ((G.cliqueFinset 2 \ G'.cliqueFinset 2 : Finset (Finset V)) : Set (Finset V)) := by
    intro f hf
    simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff]
      at hf
    obtain ⟨hfG, hfG'⟩ := hf
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hfG.card_eq
    have hadj : G.Adj a b := hfG.1 (by simp) (by simp) hab
    have hnadj : ¬ G'.Adj a b := by
      intro h
      refine hfG' ⟨?_, Finset.card_pair hab⟩
      simpa using SimpleGraph.isClique_pair.mpr (fun _ => h)
    refine ⟨s(a, b), ?_, ?_⟩
    · simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe, SimpleGraph.mem_edgeFinset]
      exact ⟨hadj, hnadj⟩
    · ext x; simp [Sym2.mem_toFinset]
  have hcard := Finset.card_le_card_of_surjOn _ hsurj
  have hsd : (G.edgeFinset \ G'.edgeFinset).card = G.edgeFinset.card - G'.edgeFinset.card :=
    Finset.card_sdiff_of_subset hsub
  have hle' : G'.edgeFinset.card ≤ G.edgeFinset.card := Finset.card_le_card hsub
  rw [hsd] at hcard
  have h2 : ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ)
      ≤ ((G.edgeFinset.card - G'.edgeFinset.card : ℕ) : ℝ) := by exact_mod_cast hcard
  rw [Nat.cast_sub hle'] at h2
  exact h2

/-- A triangle-free graph has fractional triangle packing number `0`. -/
theorem nu3star_eq_zero_of_cliqueFree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.CliqueFree 3) : nu3star G ≤ 0 := by
  have hemp : G.cliqueFinset 3 = ∅ := SimpleGraph.cliqueFinset_eq_empty_iff.mpr h
  have := nu3star_le_card_triangles G
  rwa [hemp, Finset.card_empty, Nat.cast_zero] at this

/-! ### The removal branch -/

/-- **The removal branch.**  A graph with fewer than `triangleRemovalBound(ε)·|V|³` triangles has
`ν₃* ≤ ε|V|²`.

Mathlib's triangle removal lemma produces a triangle-free spanning subgraph `G'` obtained by
deleting fewer than `ε|V|²` edges.  Since `G'` has no triangle, *every* triangle of `G` contains a
deleted edge, so the entire fractional packing is carried by the deleted edges, each of load at
most `1`. -/
theorem nu3star_le_of_few_triangles (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ}
    (hfew : ((G.cliqueFinset 3).card : ℝ)
      < SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3) :
    nu3star G ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hfew' : ((G.cliqueFinset 3).card : ℝ)
      < SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℕ) ^ 3 := hfew
  obtain ⟨G', hle, hdec, hdel, hfree⟩ := SimpleGraph.triangle_removal (G := G) (ε := ε) hfew'
  have hzero : nu3star G' ≤ 0 := nu3star_eq_zero_of_cliqueFree G' hfree
  have hmain := nu3star_le_add_deleted G G' hle
  have hcnt := card_clique2_sdiff_le G G' hle
  have hdel' : (G.edgeFinset.card : ℝ) - (G'.edgeFinset.card : ℝ)
      < ε * (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast hdel
  linarith only [hzero, hmain, hcnt, hdel']

/-- **The removal branch, as a packing-gap bound.**  For every `ε > 0` there is `κ > 0` such that
every graph with fewer than `κ|V|³` triangles has packing gap at most `ε|V|²`. -/
theorem gap_le_of_few_triangles (ε : ℝ) (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        ((G.cliqueFinset 3).card : ℝ) < κ * (Fintype.card V : ℝ) ^ 3 →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  refine ⟨SimpleGraph.triangleRemovalBound ε, SimpleGraph.triangleRemovalBound_pos hε, ?_⟩
  intro V _ _ G _ hfew
  have h1 := nu3star_le_of_few_triangles G hfew
  have h2 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
  linarith only [h1]

/-! ### The residual, restricted to triangle-rich graphs -/

/-- **The core packing-gap statement at parameters `(ε, δ)`, for triangle-rich graphs.**  As
`Nibble.AX1.CoreGapAt ε δ`, but only for graphs with at least `κ|V|³` triangles. -/
def CoreGapAtRich (ε δ κ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    (∀ x : V, G.degree x = 0 ∨ δ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)) →
    κ * (Fintype.card V : ℝ) ^ 3 ≤ ((G.cliqueFinset 3).card : ℝ) →
    ε * (Fintype.card V : ℝ) ^ 2 < nu3star G →
    nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **The residual restricted to triangle-rich graphs**, at the removal-lemma threshold. -/
def CoreGapRichResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → CoreGapAtRich ε δ (SimpleGraph.triangleRemovalBound ε)

/-- Lowering the richness threshold strengthens the statement. -/
theorem CoreGapAtRich.mono_kappa {ε δ κ κ' : ℝ} (h : CoreGapAtRich ε δ κ) (hκ : κ ≤ κ') :
    CoreGapAtRich ε δ κ' := by
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, fun V _ _ G _ hV hdeg hrich hval => hmain V G hV hdeg ?_ hval⟩
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 3 := by positivity
  nlinarith only [hκ, hrich, hn]

/-- **The reduction.**  The full core residual follows from its triangle-rich restriction: the
triangle-poor instances are discharged outright by the removal branch. -/
theorem coreGapResidual_of_rich (h : CoreGapRichResidual) : CoreGapResidual := by
  intro ε hε δ hδ
  obtain ⟨n₀, hmain⟩ := h ε hε δ hδ
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdeg hval
  rcases lt_or_ge ((G.cliqueFinset 3).card : ℝ)
    (SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3) with hfew | hrich
  · have h1 := nu3star_le_of_few_triangles G hfew
    have h2 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
    linarith only [h1]
  · exact hmain V G hV hdeg hrich hval

/-- **The converse.**  The restricted residual is a weakening of the full one, so the two are
equivalent: no strength has been smuggled in. -/
theorem rich_of_coreGapResidual (h : CoreGapResidual) : CoreGapRichResidual := by
  intro ε hε δ hδ
  obtain ⟨n₀, hmain⟩ := h ε hε δ hδ
  exact ⟨n₀, fun V _ _ G _ hV hdeg _ hval => hmain V G hV hdeg hval⟩

/-- **AX1 from the triangle-rich residual.** -/
theorem ax1_of_coreGapRichResidual (h : CoreGapRichResidual) : AX1Statement :=
  ax1_of_coreGapResidual (coreGapResidual_of_rich h)

end Nibble.AX1
