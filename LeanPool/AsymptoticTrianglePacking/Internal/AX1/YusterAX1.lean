/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Yuster — the `o(n²)` arithmetic: integrality gap in AX1 form

Standalone, Mathlib-only. The Y6 gap bound `ν₃*(G) − ν₃(G) ≤ β·|E(G)|/3`
(`nu3star_sub_nu3_le`) is put
into the AX1 shape `≤ ε·|V(G)|²` using `|E(G)| ≤ |V(G)|²` and `β = 3ε`. This is the `o(n²)`
accounting
step of the Yuster route (AX1 as stated in Paper III: `∀ε>0, ν₃*−ν₃ ≤ ε·|V|²` for large `V`).

* `edge_card_le_card_sq` — `|E(G)| ≤ |V(G)|²`.
* `nu3star_sub_nu3_le_eps` — `ν₃* − ν₃ ≤ ε·|V|²` (modulo `NibbleTheoremMost` + the edge-based
Y3 interface).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterGap

/-! # YusterAX1 -/

@[expose] public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Edge count bound** `|E(G)| ≤ |V(G)|²`. Each edge is a `2`-subset of the vertex set, so
`|E| ≤ C(|V|,2) ≤ |V|²`. -/
theorem edge_card_le_card_sq :
    ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  have hle : (G.cliqueFinset 2).card ≤ (Fintype.card V).choose 2 := by
    have hsub : (G.cliqueFinset 2).card ≤
        (Finset.univ.powersetCard 2 : Finset (Finset V)).card := by
      apply Finset.card_le_card
      intro e he
      rw [SimpleGraph.mem_cliqueFinset_iff] at he
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ e, he.card_eq⟩
    rwa [Finset.card_powersetCard, Finset.card_univ] at hsub
  have hchoose : (Fintype.card V).choose 2 ≤ (Fintype.card V) ^ 2 := by
    rw [Nat.choose_two_right, pow_two]
    exact le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul (le_refl _) (Nat.sub_le _ _))
  calc ((G.cliqueFinset 2).card : ℝ) ≤ ((Fintype.card V).choose 2 : ℝ) := by exact_mod_cast hle
    _ ≤ ((Fintype.card V) ^ 2 : ℝ) := by exact_mod_cast hchoose
    _ = (Fintype.card V : ℝ) ^ 2 := by ring

/-- **AX1-form gap.** Assuming `NibbleTheorem` and the edge-based Y3 interface, the
integrality gap is
`≤ ε·|V(G)|²` — the shape AX1 states. Takes `β = 3ε` in `nu3star_sub_nu3_le` (so `β·|E|/3 =
ε·|E|`) and
bounds `|E| ≤ |V|²`. -/
theorem nu3star_sub_nu3_le_eps (hNibble : NibbleTheorem) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegular (triangleHypergraphSub G) d μ →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, d₀, hd₀, hmain⟩ := nu3star_sub_nu3_le G hNibble (by linarith : (0:ℝ) < 3 * ε)
  refine ⟨μ, hμ, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  have hgap := hmain hd hd0 hReg hCod
  have hEq : (3 * ε) * ((G.cliqueFinset 2).card : ℝ) / 3 = ε * ((G.cliqueFinset 2).card : ℝ) := by
    ring
  rw [hEq] at hgap
  calc nu3star G - (nu3 G : ℝ)
      ≤ ε * ((G.cliqueFinset 2).card : ℝ) := hgap
    _ ≤ ε * (Fintype.card V : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (edge_card_le_card_sq G) (le_of_lt hε)

end Nibble.YusterE
