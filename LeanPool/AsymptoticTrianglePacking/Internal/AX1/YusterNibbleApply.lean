/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Yuster Y5 (scaffold) — applying `NibbleTheorem` to the triangle hypergraph

Standalone, Mathlib-only. The Y5 step of the Yuster route: feed the edge-vertex-type triangle
hypergraph `triangleHypergraphSub G` (on `EdgeV G`, whose `Fintype.card` is `|E(G)|`) to
`NibbleTheorem`. Since that hypergraph is `3`-uniform and — under the Y3 hypotheses
`NearlyRegular d μ`
and `CodegreeBounded (μ·d)` — meets the nibble's requirements, `NibbleTheorem` yields an
edge-disjoint
triangle packing (a matching) of size `≥ (1-β)·|E(G)|/3`.

`NibbleTheorem` and the near-regularity/codegree data are kept as HYPOTHESES: the former is the T3
interface (to be discharged by the nibble machinery), the latter is exactly what
`triangleHypergraph_nearlyRegular_codegreeBounded` (Y3) supplies from a Szemerédi partition. This
scaffold wires the three together, leaving only those two inputs open.

Note the vertex type `EdgeV G` has universe `0` (`{V : Type}`), matching `NibbleTheorem`'s `∀
{V : Type}`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.Interface
public import LeanPool.AsymptoticTrianglePacking.Internal.RegularMost
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdgeType
public import Mathlib.Algebra.Order.Ring.Star

/-! # YusterNibbleApply -/

@[expose] public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Y5 (scaffold) — nibble ⇒ large triangle packing.** Assuming `NibbleTheorem`, there is a
near-regularity tolerance `μ > 0` such that, whenever the edge-type triangle hypergraph is
`(1±μ)`-nearly `d`-regular with codegree `≤ μd`, it has a matching (edge-disjoint triangle
packing) of
size `≥ (1-β)·|E(G)|/3`. Direct application of `NibbleTheorem` to `triangleHypergraphSub G`, using
`card_EdgeV` to turn `Fintype.card (EdgeV G)` into `|E(G)| = |cliqueFinset 2|`. -/
theorem nibble_gives_triangleSub_matching (hNibble : NibbleTheorem) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegular (triangleHypergraphSub G) d μ →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (M.card : ℝ) := by
  obtain ⟨μ, hμ, d₀, hd₀, hmain⟩ := hNibble 3 (by norm_num) β hβ
  refine ⟨μ, hμ, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  obtain ⟨M, hM, hcard⟩ :=
    hmain (triangleHypergraphSub G) d hd hd0 (triangleHypergraphSub_uniform G) hReg hCod
  refine ⟨M, hM, ?_⟩
  rwa [card_EdgeV] at hcard

/-- **Y5 (majority) — nibble ⇒ large triangle packing, tolerating an exceptional edge set.** The
`NibbleTheoremMost` version of `nibble_gives_triangleSub_matching`: assuming the majority interface,
there are tolerances `μ, η > 0` such that whenever the edge-type triangle hypergraph is
`NearlyRegularMost d μ η` (near-`d`-regular outside an `η`-fraction of edges) with codegree `≤
μd`, it
has an edge-disjoint triangle packing of size `≥ (1-β)·|E(G)|/3`. This is the version the
Szemerédi+counting reconstruction (which yields `NearlyRegularMost`, not strict) feeds. -/
theorem nibble_gives_triangleSub_matching_most (hNibble : NibbleTheoremMost) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegularMost (triangleHypergraphSub G) d μ η →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (M.card : ℝ) := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := hNibble 3 (by norm_num) β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  obtain ⟨M, hM, hcard⟩ :=
    hmain (triangleHypergraphSub G) d hd hd0 (triangleHypergraphSub_uniform G) hReg hCod
  refine ⟨M, hM, ?_⟩
  rwa [card_EdgeV] at hcard

end Nibble.YusterE
