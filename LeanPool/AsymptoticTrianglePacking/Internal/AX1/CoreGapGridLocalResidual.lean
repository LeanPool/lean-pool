/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the AX1 structural residual in its **local** design form

`Nibble.CoreGapGridResidual` records the AX1 residual as `Nibble.AX1.SubTripleDesignResidual`, the
existence of a `Nibble.AX1.IsSubTripleDesign`.  That package charges the exceptional edges of the
`i`-th sub-triple at the *global* rate `(2·Badᵢ/t)·|V|`.  As explained in
`Nibble.CoreGapDesignLocal`, that global rate cannot be met by any construction whose sub-triples
live inside the clusters of the regularity partition:

* the sub-triples are `ε₂`-uniform only because they are blocks of relative size `α` inside an
  `(ε₁/8)`-uniform cluster pair, so `ε₂ ≥ ε₁/(8α)`;
* their triangle-degree scale `d` is at most the size of a cluster, `≈ |V|/m`, so the slack `t`
  obeys `t ≤ μ·|V|/m` with `m = #P.parts`;
* the exceptional clause then forces `ε₂ ≲ ημδ/m`, i.e. `ε₁·m ≲ ημ·α`, while the hypotheses of
  `Nibble.AX1.SubTripleDesignAt` themselves force `m ≥ 4/ε₁`, hence `ε₁ · m ≥ 4`.

So for small `η` or `μ` the *global* design form is out of reach of the grid construction — and the
project already carries the repair: `Nibble.AX1.hasNearRegularFamily_of_subTripleDesignLocal`
(`Nibble.CoreGapDesignLocal`) provides exactly the same bridge with the exceptional edges charged
against the *support* `|A| + |B| + |C|` of the sub-triple, which is the honest rate coming out of
`Nibble.AX1.uniform_triple_member_local`.

This file mirrors `Nibble.CoreGapGridResidual` for that local bridge:

* `Nibble.AX1.SubTripleDesignLocalAt`, `Nibble.AX1.SubTripleDesignLocalResidual` — the residual in
  local design form;
* `Nibble.AX1.reducedFamilyAt_of_subTripleDesignLocalAt`,
  `Nibble.AX1.reducedFamilyResidual_of_subTripleDesignLocal`,
  `Nibble.AX1.ax1_of_subTripleDesignLocal` — the machine-checked reductions to
  `Nibble.AX1.ReducedFamilyAt`, `Nibble.AX1.ReducedFamilyResidual` and `AX1Statement`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapDesignLocal
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapGridResidual

/-! # CoreGapGridLocalResidual -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-- **The local design form of the reduced residual at parameters `(ε, μ, η, d₀)` and regularity
scale `ε₁`**: every triangle-rich regularity-reduced graph carries a sub-triple design in the sense
of `Nibble.AX1.IsSubTripleDesignLocal`. -/
def SubTripleDesignLocalAt (ε μ η d₀ ε₁ : ℝ) : Prop :=
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
      IsSubTripleDesignLocal (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)) ε μ η d₀ ε₂ μ₂ t k A B C
        d Elo

/-- **The local design residual**: a local sub-triple design at every window of parameters, for
some regularity scale `ε₁` as small as one likes. -/
def SubTripleDesignLocalResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ μ : ℝ, 0 < μ → ∀ η : ℝ, 0 < η → ∀ d₀ : ℝ, 0 < d₀ →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧ ε₁ ≤ 1 ∧ SubTripleDesignLocalAt ε μ η d₀ ε₁

/-- **A local design gives the reduced family.** -/
theorem reducedFamilyAt_of_subTripleDesignLocalAt {ε μ η d₀ ε₁ : ℝ}
    (h : SubTripleDesignLocalAt ε μ η d₀ ε₁) : ReducedFamilyAt ε μ η d₀ ε₁ := by
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ P hV hP hPl hPb hPu hrich
  obtain ⟨ε₂, μ₂, t, k, A, B, C, d, Elo, hdes⟩ := hmain V G P hV hP hPl hPb hPu hrich
  exact hasNearRegularFamily_of_subTripleDesignLocal _ hdes

/-- **The local design residual implies the structural residual
`Nibble.AX1.ReducedFamilyResidual`.** -/
theorem reducedFamilyResidual_of_subTripleDesignLocal (h : SubTripleDesignLocalResidual) :
    ReducedFamilyResidual := by
  intro ε hε μ hμ η hη d₀ hd₀
  obtain ⟨ε₁, hε₁, hε₁ε, hε₁1, hdes⟩ := h ε hε μ hμ η hη d₀ hd₀
  exact ⟨ε₁, hε₁, hε₁ε, hε₁1, reducedFamilyAt_of_subTripleDesignLocalAt hdes⟩

/-- **AX1 from the local design residual.** -/
theorem ax1_of_subTripleDesignLocal (h : SubTripleDesignLocalResidual) : AX1Statement :=
  ax1_of_reducedFamily (reducedFamilyResidual_of_subTripleDesignLocal h)

end Nibble.AX1
