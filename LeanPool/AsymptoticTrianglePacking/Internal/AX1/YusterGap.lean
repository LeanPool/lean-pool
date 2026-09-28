/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Yuster Y6 (capstone) — the integrality gap `ν₃* − ν₃ ≤ β·|E(G)|/3`

Standalone, Mathlib-only. Combines the two quantitative halves of the Yuster route:

* `nu3_ge_nibble`  — `(1-β)·|E(G)|/3 ≤ ν₃ G`   (nibble ⇒ large integral packing), and
* `nu3star_le`     — `ν₃* G ≤ |E(G)|/3`         (fractional relaxation bound),

to bound the integrality gap `ν₃*(G) − ν₃(G) ≤ β·|E(G)|/3`. Since `β > 0` is arbitrary and
`|E(G)| = O(n²)`, letting `β → 0` (with the nibble tolerance `μ(β)`) drives the gap to `o(n²)`
— this
is the content of AX1 (`ν₃* − ν₃ = o(n²)`), modulo the two open inputs (`NibbleTheorem` and the
Szemerédi regular-pair data feeding the Y3 interface).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterSubBridge
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterFracUpper

/-! # YusterGap -/

@[expose] public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Y6 capstone — integrality gap bound.** Assuming `NibbleTheorem` and the Y3 near-regularity /
codegree interface on `triangleHypergraphSub G`, the gap between the fractional and integral
triangle
packing numbers is at most `β·|E(G)|/3`. Combining `nu3_ge_nibble` and `nu3star_le`. As `β → 0` this
is `o(n²)` — AX1. -/
theorem nu3star_sub_nu3_le (hNibble : NibbleTheorem) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegular (triangleHypergraphSub G) d μ →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      nu3star G - (nu3 G : ℝ) ≤ β * ((G.cliqueFinset 2).card : ℝ) / 3 := by
  obtain ⟨μ, hμ, d₀, hd₀, hlb⟩ := nu3_ge_nibble G hNibble hβ
  refine ⟨μ, hμ, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  have h1 := hlb hd hd0 hReg hCod
  have h2 := nu3star_le G
  have hring : (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3)
      = ((G.cliqueFinset 2).card : ℝ) / 3 - β * (((G.cliqueFinset 2).card : ℝ) / 3) := by ring
  rw [hring] at h1
  have hgoal : β * ((G.cliqueFinset 2).card : ℝ) / 3 = β * (((G.cliqueFinset 2).card : ℝ) / 3) := by
    ring
  rw [hgoal]
  linarith only [h1, h2]

end Nibble.YusterE
