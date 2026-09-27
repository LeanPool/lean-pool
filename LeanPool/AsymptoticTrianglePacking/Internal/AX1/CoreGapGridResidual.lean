/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the AX1 structural residual, reduced to a finite combinatorial *design* problem

This file records the state of the deterministic (probability-free) route to
`Nibble.AX1.ReducedFamilyResidual`.

`Nibble.AX1.hasNearRegularFamily_of_isSubTripleDesign` (`Nibble.CoreGapDesign`) shows that all the
*analytic* content of the residual — the per-edge regularity counting
(`Nibble.AX1.uniform_triple_codegree`), its triangle-degree form
(`Nibble.AX1.tripleGraph_near_regular`) and the pruning of the exceptional edges
(`Nibble.AX1.prune_near_regular`) — is already discharged: a near-regular family exists as soon as
one can *construct* a `Nibble.AX1.IsSubTripleDesign`, i.e. a finite list of vertex sub-triples which
are pairwise uniform and dense, whose triangle-degree scales are equalised, whose tripartite graphs
are pairwise edge-disjoint, and which together carry `3ν₃* − 3ε|V|²` edges.

* `Nibble.AX1.SubTripleDesignAt`, `Nibble.AX1.SubTripleDesignResidual` — the residual in this form.
* `Nibble.AX1.reducedFamilyAt_of_subTripleDesignAt`,
  `Nibble.AX1.reducedFamilyResidual_of_subTripleDesign`, `Nibble.AX1.ax1_of_subTripleDesign` — the
  machine-checked reductions to `Nibble.AX1.ReducedFamilyAt`, `Nibble.AX1.ReducedFamilyResidual` and
  `AX1Statement`.
* `Nibble.AX1.subTripleDesignResidual_of_reducedFamilyResidual` is *not* claimed: the design form is
  (a priori strictly) stronger than the family form, since it fixes the shape of the family.

The two ingredients of the missing construction, and their status, are:

1. **the sub-block grid inside one cluster triple** — split the clusters `U`, `W`, `X` of a good
   triple into vertex blocks of sizes proportional to the *opposite* pair densities (this equalises
   the three triangle-degree scales, which is the hypothesis `hClo … hAhi` of the design) and take
   the diagonal family `(U_{(j+k) mod n_U}, W_j, X_k)`.  Uniformity passes to the blocks by
   `Nibble.AX1.isUniform_subblock`, and the diagonal family is edge-disjoint by
   `Nibble.AX1.gridDesign_pairwise_edgeDisjoint` (`Nibble.GridDesign`) — the combinatorial core,
   proved;

2. **the allocation of each cluster pair among the triples that use it** — a fractional triangle
   packing puts total weight at most `e(U, W)` on the triples through the pair
   (`Nibble.AX1.sum_pair_classes_le`) and its value is the sum of those weights
   (`Nibble.AX1.sum_split_partClass`), so the areas required in the `U × W` grid do fit; what is
   missing is a *packing* of the corresponding block rectangles.  Note that the blocks of a pair
   cannot be smaller than the regularity scale allows, so this step also needs the fractional
   optimum to be re-routed onto a solution using only boundedly many triples per pair — a
   sparsification of the cluster-level LP.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapDesign
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridDesign

/-! # CoreGapGridResidual -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-- **The design form of the reduced residual at parameters `(ε, μ, η, d₀)` and regularity scale
`ε₁`**: every triangle-rich regularity-reduced graph carries a sub-triple design in the sense of
`Nibble.AX1.IsSubTripleDesign`. -/
def SubTripleDesignAt (ε μ η d₀ ε₁ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)),
    n₀ ≤ Fintype.card V →
    P.IsEquipartition →
    4 / ε₁ ≤ (P.parts.card : ℝ) →
    (P.parts.card : ℝ) ≤ ((SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ : ℕ) : ℝ) →
    P.IsUniform G (ε₁ / 8) →
    SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3
      ≤ ((((G.regularityReduced P (ε₁ / 8) (ε₁ / 4))).cliqueFinset 3).card : ℝ) →
    ∃ (ε₂ μ₂ t : ℝ) (k : ℕ) (A B C : ℕ → Finset V) (d Elo : ℕ → ℝ),
      IsSubTripleDesign (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)) ε μ η d₀ ε₂ μ₂ t k A B C d Elo

/-- **The design residual**: a sub-triple design at every window of parameters, for some regularity
scale `ε₁` as small as one likes. -/
def SubTripleDesignResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ μ : ℝ, 0 < μ → ∀ η : ℝ, 0 < η → ∀ d₀ : ℝ, 0 < d₀ →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧ ε₁ ≤ 1 ∧ SubTripleDesignAt ε μ η d₀ ε₁

/-- **A design gives the reduced family.** -/
theorem reducedFamilyAt_of_subTripleDesignAt {ε μ η d₀ ε₁ : ℝ}
    (h : SubTripleDesignAt ε μ η d₀ ε₁) : ReducedFamilyAt ε μ η d₀ ε₁ := by
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ P hV hP hPl hPb hPu hrich
  obtain ⟨ε₂, μ₂, t, k, A, B, C, d, Elo, hdes⟩ := hmain V G P hV hP hPl hPb hPu hrich
  exact hasNearRegularFamily_of_isSubTripleDesign _ hdes

/-- **The design residual implies the structural residual `Nibble.AX1.ReducedFamilyResidual`.** -/
theorem reducedFamilyResidual_of_subTripleDesign (h : SubTripleDesignResidual) :
    ReducedFamilyResidual := by
  intro ε hε μ hμ η hη d₀ hd₀
  obtain ⟨ε₁, hε₁, hε₁ε, hε₁1, hdes⟩ := h ε hε μ hμ η hη d₀ hd₀
  exact ⟨ε₁, hε₁, hε₁ε, hε₁1, reducedFamilyAt_of_subTripleDesignAt hdes⟩

/-- **AX1 from the design residual.** -/
theorem ax1_of_subTripleDesign (h : SubTripleDesignResidual) : AX1Statement :=
  ax1_of_reducedFamily (reducedFamilyResidual_of_subTripleDesign h)

end Nibble.AX1
