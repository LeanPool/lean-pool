/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Yuster — the majority (`NibbleTheoremMost`) chain to AX1 form

Standalone, Mathlib-only. Mirrors the strict Yuster chain (`nu3_ge_nibble`, `nu3star_sub_nu3_le`,
`nu3star_sub_nu3_le_eps`) using the MAJORITY interface `NibbleTheoremMost` +
`NearlyRegularMost` — the
version the Szemerédi+counting Y3 reconstruction actually yields (near-regularity outside a small
exceptional edge set). This is the chain the edge-based Y1c feeds.

* `nu3_ge_nibble_most` — `NibbleTheoremMost` + Y3-majority ⇒ `ν₃ ≥ (1-β)|E|/3`.
* `nu3star_sub_nu3_le_most` — ⇒ `ν₃* − ν₃ ≤ β|E|/3`.
* `nu3star_sub_nu3_le_eps_most` — ⇒ `ν₃* − ν₃ ≤ ε|V|²` (AX1 shape).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterSubBridge
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterNibbleApply
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterFracUpper
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterAX1

/-! # YusterMost -/

@[expose] public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Majority `ν₃` lower bound.** `NibbleTheoremMost` + the Y3-majority interface ⇒ `ν₃ ≥
(1-β)|E|/3`. -/
theorem nu3_ge_nibble_most (hNibble : NibbleTheoremMost) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegularMost (triangleHypergraphSub G) d μ η →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (nu3 G : ℝ) := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibble_gives_triangleSub_matching_most G hNibble hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  obtain ⟨M, hM, hcard⟩ := hmain hd hd0 hReg hCod
  exact le_trans hcard (by exact_mod_cast sub_matching_card_le_nu3 G hM)

/-- **Majority integrality-gap bound** `ν₃* − ν₃ ≤ β|E|/3`. -/
theorem nu3star_sub_nu3_le_most (hNibble : NibbleTheoremMost) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegularMost (triangleHypergraphSub G) d μ η →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      nu3star G - (nu3 G : ℝ) ≤ β * ((G.cliqueFinset 2).card : ℝ) / 3 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hlb⟩ := nu3_ge_nibble_most G hNibble hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  have h1 := hlb hd hd0 hReg hCod
  have h2 := nu3star_le G
  have hring : (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3)
      = ((G.cliqueFinset 2).card : ℝ) / 3 - β * (((G.cliqueFinset 2).card : ℝ) / 3) := by ring
  rw [hring] at h1
  have hgoal : β * ((G.cliqueFinset 2).card : ℝ) / 3 = β * (((G.cliqueFinset 2).card : ℝ) / 3) := by
    ring
  rw [hgoal]
  linarith only [h1, h2]

/-- **Majority AX1-form gap** `ν₃* − ν₃ ≤ ε|V|²`. -/
theorem nu3star_sub_nu3_le_eps_most (hNibble : NibbleTheoremMost) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegularMost (triangleHypergraphSub G) d μ η →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ :=
    nu3star_sub_nu3_le_most G hNibble (by linarith : (0:ℝ) < 3 * ε)
  refine ⟨μ, hμ, η, hη, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  have hgap := hmain hd hd0 hReg hCod
  have hEq : (3 * ε) * ((G.cliqueFinset 2).card : ℝ) / 3 = ε * ((G.cliqueFinset 2).card : ℝ) := by
    ring
  rw [hEq] at hgap
  calc nu3star G - (nu3 G : ℝ)
      ≤ ε * ((G.cliqueFinset 2).card : ℝ) := hgap
    _ ≤ ε * (Fintype.card V : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (edge_card_le_card_sq G) (le_of_lt hε)

end Nibble.YusterE
