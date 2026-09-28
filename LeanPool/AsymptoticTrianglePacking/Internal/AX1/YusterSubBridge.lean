/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Yuster — bridge `triangleHypergraphSub` ↔ `nu3`, and the nibble lower bound on `ν₃`

Standalone, Mathlib-only. Connects the two edge-based encodings: a matching of the edge-VERTEX-type
triangle hypergraph `triangleHypergraphSub G` (on `EdgeV G`, the encoding `NibbleTheorem` runs
on) maps
—via the subtype-forgetting embedding `EdgeV G ↪ Finset V`— to a matching of `triangleHypergraphE G`
(on `Finset V`, the encoding defining `nu3`) of the SAME cardinality. Hence a `Sub`-matching
lower-bounds `nu3 G`.

Combined with Y5 (`nibble_gives_triangleSub_matching`) this yields `ν₃ G ≥ (1-β)·|E(G)|/3` directly.

* `sub_matching_card_le_nu3` — `IsMatching (triangleHypergraphSub G) M → M.card ≤ nu3 G`.
* `nu3_ge_nibble` — assuming `NibbleTheorem` + the Y3 interface, `(1-β)·|E(G)|/3 ≤ ν₃ G`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdge
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdgeType
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterNibbleApply

/-! # YusterSubBridge -/

@[expose] public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Sub ↦ E bridge.** A matching of the edge-vertex-type triangle hypergraph lower-bounds `nu3`:
mapping each hyperedge `T` by the subtype embedding `EdgeV G ↪ Finset V` (`T ↦ T.map emb`) turns a
matching of `triangleHypergraphSub G` into a matching of `triangleHypergraphE G` of the same
cardinality (the embedding is injective — preserves card and disjointness — and recovers the
original
`2`-subsets of each triangle since they are all `2`-cliques). Then `nu3_ge`. -/
theorem sub_matching_card_le_nu3 {M : Finset (Finset (EdgeV G))}
    (hM : IsMatching (triangleHypergraphSub G) M) : M.card ≤ nu3 G := by
  set emb : EdgeV G ↪ Finset V := Function.Embedding.subtype (· ∈ G.cliqueFinset 2) with hemb
  -- each mapped hyperedge lands in triangleHypergraphE G
  have hmem : ∀ T ∈ M, T.map emb ∈ triangleHypergraphE G := by
    intro T hT
    have hTsub := hM.subset hT
    rw [triangleHypergraphSub, Finset.mem_image] at hTsub
    obtain ⟨t, ht, rfl⟩ := hTsub
    have hclique : G.IsNClique 3 t := (SimpleGraph.mem_cliqueFinset_iff).mp ht
    have hall : ∀ x ∈ t.powersetCard 2, x ∈ G.cliqueFinset 2 :=
      powersetCard_two_subset_cliqueFinset G hclique
    have hrec : ((t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)).map emb = t.powersetCard 2 := by
      rw [hemb]; exact Finset.subtype_map_of_mem hall
    rw [hrec, triangleHypergraphE, Finset.mem_image]
    exact ⟨t, ht, rfl⟩
  -- the image matching of triangleHypergraphE
  have hM' : IsMatching (triangleHypergraphE G) (M.image (fun T => T.map emb)) := by
    refine ⟨?_, ?_⟩
    · intro T' hT'
      rw [Finset.mem_image] at hT'
      obtain ⟨T, hT, rfl⟩ := hT'
      exact hmem T hT
    · intro a ha b hb hab
      rw [Finset.mem_image] at ha hb
      obtain ⟨T, hT, rfl⟩ := ha
      obtain ⟨T', hT', rfl⟩ := hb
      have hTT' : T ≠ T' := fun h => hab (by rw [h])
      rw [Finset.disjoint_map]
      exact hM.disjoint T hT T' hT' hTT'
  have hcard : (M.image (fun T => T.map emb)).card = M.card :=
    Finset.card_image_of_injective M (Finset.map_injective emb)
  calc M.card = (M.image (fun T => T.map emb)).card := hcard.symm
    _ ≤ nu3 G := nu3_ge G hM'

/-- **`ν₃` lower bound from the nibble.** Assuming `NibbleTheorem` and the Y3
near-regularity/codegree
interface on `triangleHypergraphSub G`, the integral triangle-packing number satisfies
`(1-β)·|E(G)|/3 ≤ ν₃ G`. Combines Y5 (`nibble_gives_triangleSub_matching`) with the Sub ↦
`nu3` bridge.
This is the quantitative half of Y6 (the other half is `ν₃* ≤` an upper bound). -/
theorem nu3_ge_nibble (hNibble : NibbleTheorem) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegular (triangleHypergraphSub G) d μ →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (nu3 G : ℝ) := by
  obtain ⟨μ, hμ, d₀, hd₀, hmain⟩ := nibble_gives_triangleSub_matching G hNibble hβ
  refine ⟨μ, hμ, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  obtain ⟨M, hM, hcard⟩ := hmain hd hd0 hReg hCod
  exact le_trans hcard (by exact_mod_cast sub_matching_card_le_nu3 G hM)

end Nibble.YusterE
