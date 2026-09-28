/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — reducing NibbleGapHyp to NibbleTheoremMost + the ② regularization obligation

Bottoms the AX1 dependency chain out at its irreducible pieces. Combined with `AX1Reduction`, gives
  AX1  ⟸  StrongDualityHyp  +  NibbleTheoremMost  +  NearRegObligation
i.e. AX1 sorry-free reduces to EXACTLY: cover-side strong duality (Aristotle `b3ee717f`), the nibble
theorem `NibbleTheoremMost` (Aristotle residual crux `39a79122` + convergence), and the
`②` near-regularity
regularization (Szemerédi / Haxell–Rödl, pending the route decision).

* `UniformNibbleGap`, `NearRegObligation` — the two sub-obligations of `NibbleGapHyp`.
* `nibbleGap_of_uniform_and_regularity`, `nibbleGap_of_nibbleTheorem` — the reductions.
* `ax1_of_nibbleTheorem_strongDuality_regularity` — the full composite: the three obligations ⟹ AX1.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.Reduction
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterMost
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # NibbleGapReduction -/

@[expose] public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-- **Uniform nibble gap**: tolerances `μ, η` depending only on `ε` (NOT on `G`) such that
every graph that is near-`d`-regular (outside `η`-fraction) with bounded codegree has
`ν₃* − ν₃ ≤ ε n²`. This is the
`G`-uniform form of the proven per-graph `nu3star_sub_nu3_le_eps_most`. -/
def UniformNibbleGap : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] {d : ℝ}, 0 < d →
      NearlyRegularMost (triangleHypergraphSub G) d μ η →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **Near-regularity obligation** (the ② core): for tolerances `μ, η`, every large enough
graph admits a near-regularity witness `d` (with the free codegree bound). This is
exactly what a Szemerédi/Haxell–Rödl
regularization must supply. -/
def NearRegObligation (μ η d₀ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    ∃ d : ℝ, 0 < d ∧ d₀ ≤ d ∧ NearlyRegularMost (triangleHypergraphSub G) d μ η ∧
      CodegreeBounded (triangleHypergraphSub G) (μ * d) ∧
      -- ② global ceiling (corrected nibble): every edge lies in ≤ (1+μ)d triangles (no exceptional
      -- high-degree vertex). At δ≥(9/10+ε)|V| this is free; see
      -- `Nibble.YusterE.triangleSub_degree_window`.
      (∀ e : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) e : ℝ) ≤ (1 + μ) * d)

/-- **Sized near-regularity obligation.** The corrected Freedman route also needs the triangle
hypergraph vertex count (`|E(G)|`) to be polynomially bounded by the regular degree scale `d`. -/
def NearRegObligationSized (μ η d₀ K : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    ∃ d : ℝ, 0 < d ∧ d₀ ≤ d ∧ NearlyRegularMost (triangleHypergraphSub G) d μ η ∧
      CodegreeBounded (triangleHypergraphSub G) (μ * d) ∧
      (∀ e : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) e : ℝ) ≤ (1 + μ) * d) ∧
      (Fintype.card (EdgeV G) : ℝ) ≤ K * d ^ 2

/-- Dense-regime sized obligation in the natural graph-scale form: the base vertex count is linearly
controlled by the regular degree scale. -/
def NearRegObligationLinearSized (μ η d₀ L : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    ∃ d : ℝ, 0 < d ∧ d₀ ≤ d ∧ NearlyRegularMost (triangleHypergraphSub G) d μ η ∧
      CodegreeBounded (triangleHypergraphSub G) (μ * d) ∧
      (∀ e : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) e : ℝ) ≤ (1 + μ) * d) ∧
      (Fintype.card V : ℝ) ≤ L * d

/-- The triangle-hypergraph vertex count is quadratically controlled by any linear base-size bound
`|V(G)| ≤ L d`. -/
theorem edgeV_card_le_sq_of_base_card_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {L d : ℝ}
    (hL : 0 ≤ L) (hd : 0 ≤ d) (hbase : (Fintype.card V : ℝ) ≤ L * d) :
    (Fintype.card (EdgeV G) : ℝ) ≤ L ^ 2 * d ^ 2 := by
  have hE : (Fintype.card (EdgeV G) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    rw [card_EdgeV]
    exact edge_card_le_card_sq G
  have hbase_sq : (Fintype.card V : ℝ) ^ 2 ≤ (L * d) ^ 2 := by
    have hn : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    have hLd : 0 ≤ L * d := mul_nonneg hL hd
    nlinarith only [hbase]
  calc (Fintype.card (EdgeV G) : ℝ)
      ≤ (Fintype.card V : ℝ) ^ 2 := hE
    _ ≤ (L * d) ^ 2 := hbase_sq
    _ = L ^ 2 * d ^ 2 := by ring

/-- A linear base-size ② obligation implies the polynomial hypergraph-size obligation consumed by
the sized nibble interface. -/
theorem nearRegSized_of_linearSized {μ η d₀ L : ℝ} (hL : 0 ≤ L)
    (h : NearRegObligationLinearSized μ η d₀ L) :
    NearRegObligationSized μ η d₀ (L ^ 2) := by
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨d, hd, hd0, hreg, hcod, hceil, hbase⟩ := hn₀ V G hV
  refine ⟨d, hd, hd0, hreg, hcod, hceil, ?_⟩
  exact edgeV_card_le_sq_of_base_card_le G hL (le_of_lt hd) hbase

/-- Linear size control for every positive constant implies the exact sized obligation for every
positive `K`, by taking `L = sqrt K`. -/
theorem nearRegSized_of_forall_linearSized {μ η d₀ K : ℝ} (hK : 0 < K)
    (h : ∀ L : ℝ, 0 < L → NearRegObligationLinearSized μ η d₀ L) :
    NearRegObligationSized μ η d₀ K := by
  have hsized := nearRegSized_of_linearSized (μ := μ) (η := η) (d₀ := d₀)
    (L := Real.sqrt K) (Real.sqrt_nonneg K) (h (Real.sqrt K) (Real.sqrt_pos.2 hK))
  simpa [Real.sq_sqrt hK.le] using hsized

/-- **NibbleGapHyp reduction.** The unconditional packing gap follows from the
`G`-uniform nibble gap plus the near-regularity obligation for its tolerances.
Bottoms the AX1 chain out at `NibbleTheoremMost`
(via `UniformNibbleGap`) and the ② regularization (via `NearRegObligation`). -/
theorem nibbleGap_of_uniform_and_regularity
    (hU : UniformNibbleGap)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ → NearRegObligation μ η d₀) :
    NibbleGapHyp := by
  intro ε hε
  obtain ⟨μ, hμ, η, hη, hgap⟩ := hU ε hε
  obtain ⟨n₀, hn₀⟩ := hReg μ η 1 hμ hη one_pos
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨d, hd, _hd0, hreg, hcod, _hceil⟩ := hn₀ V G hV
  exact hgap G hd hreg hcod

/-- **NibbleGapHyp directly from `NibbleTheoremMost`.** Extracts the uniform tolerances
`μ, η` from the nibble interface once (at `r = 3`, `β = 3ε`), consumes the
near-regularity obligation, and inlines the
packing-gap arithmetic (`ν₃* ≤ |E|/3` and matching `≥ (1-3ε)|E|/3 ≤ ν₃`, so `ν₃*−ν₃ ≤ ε|E| ≤ ε n²`).
This bottoms the AX1 dependency chain out at exactly `NibbleTheoremMost` plus
the `②` regularization. -/
theorem nibbleGap_of_nibbleTheorem (hNib : NibbleTheoremMost)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ → NearRegObligation μ η d₀) : NibbleGapHyp := by
  intro ε hε
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := hNib 3 (by norm_num) (3 * ε) (by linarith)
  obtain ⟨n₀, hn₀⟩ := hReg μ η d₀ hμ hη hd₀
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨d, hd, hd0, hreg, hcod, _hceil⟩ := hn₀ V G hV
  obtain ⟨M, _hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) d hd hd0 (triangleHypergraphSub_uniform G) hreg hcod
  set E : ℝ := ((G.cliqueFinset 2).card : ℝ) with hE
  have hcardE : (Fintype.card (EdgeV G) : ℝ) = E := by rw [hE]; exact_mod_cast card_EdgeV G
  rw [hcardE] at hMcard
  have h1 : (M.card : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast sub_matching_card_le_nu3 G _hM
  have h2 : nu3star G ≤ E / 3 := nu3star_le G
  have h3 : E ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
  have hlb : (1 - 3 * ε) * (E / 3) ≤ (nu3 G : ℝ) := le_trans hMcard h1
  have hεE : ε * E ≤ ε * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 hε.le
  nlinarith only [h2, hlb, hεE]

/-- **NibbleGapHyp from the corrected ceiling-aware nibble theorem.** This is the same accounting as
`nibbleGap_of_nibbleTheorem`, but it keeps the ② global-degree ceiling supplied by
`NearRegObligation` and passes it into the nibble interface. -/
theorem nibbleGap_of_nibbleTheoremCeil (hNib : NibbleTheoremMostCeil)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ → NearRegObligation μ η d₀) :
    NibbleGapHyp := by
  dsimp [NibbleTheoremMostCeil] at hNib
  intro ε hε
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := hNib 3 (by norm_num) (3 * ε) (by linarith)
  obtain ⟨n₀, hn₀⟩ := hReg μ η d₀ hμ hη hd₀
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨d, hd, hd0, hreg, hcod, hceil⟩ := hn₀ V G hV
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) d hd hd0 (triangleHypergraphSub_uniform G) hreg hcod hceil
  set E : ℝ := ((G.cliqueFinset 2).card : ℝ) with hE
  have hcardE : (Fintype.card (EdgeV G) : ℝ) = E := by rw [hE]; exact_mod_cast card_EdgeV G
  rw [hcardE] at hMcard
  have h1 : (M.card : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast sub_matching_card_le_nu3 G hM
  have h2 : nu3star G ≤ E / 3 := nu3star_le G
  have h3 : E ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
  have hlb : (1 - 3 * ε) * (E / 3) ≤ (nu3 G : ℝ) := le_trans hMcard h1
  have hεE : ε * E ≤ ε * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 hε.le
  nlinarith only [h2, hlb, hεE]

/-- **NibbleGapHyp from the sized corrected nibble theorem.** This is the target shape for the
Freedman parameter route: all probabilistic plumbing is abstract, while the triangle-specific
regularization supplies both the global ceiling and the size-vs-degree bound. -/
theorem nibbleGap_of_nibbleTheoremCeilSized (hNib : NibbleTheoremMostCeilSized)
    (hReg : ∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K →
      NearRegObligationSized μ η d₀ K) :
    NibbleGapHyp := by
  dsimp [NibbleTheoremMostCeilSized] at hNib
  intro ε hε
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, K, hK, hmain⟩ := hNib 3 (by norm_num) (3 * ε) (by linarith)
  obtain ⟨n₀, hn₀⟩ := hReg μ η d₀ K hμ hη hd₀ hK
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨d, hd, hd0, hreg, hcod, hceil, hsize⟩ := hn₀ V G hV
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) d hd hd0 (triangleHypergraphSub_uniform G) hreg hcod hceil hsize
  set E : ℝ := ((G.cliqueFinset 2).card : ℝ) with hE
  have hcardE : (Fintype.card (EdgeV G) : ℝ) = E := by rw [hE]; exact_mod_cast card_EdgeV G
  rw [hcardE] at hMcard
  have h1 : (M.card : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast sub_matching_card_le_nu3 G hM
  have h2 : nu3star G ≤ E / 3 := nu3star_le G
  have h3 : E ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
  have hlb : (1 - 3 * ε) * (E / 3) ≤ (nu3 G : ℝ) := le_trans hMcard h1
  have hεE : ε * E ≤ ε * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 hε.le
  nlinarith only [h2, hlb, hεE]

/-- Version of `nibbleGap_of_nibbleTheoremCeilSized` consuming the dense-regime linear size
obligation. -/
theorem nibbleGap_of_nibbleTheoremCeilSized_linear (hNib : NibbleTheoremMostCeilSized)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      NearRegObligationLinearSized μ η d₀ L) :
    NibbleGapHyp :=
  nibbleGap_of_nibbleTheoremCeilSized hNib
    (fun μ η d₀ _K hμ hη hd₀ hK =>
      nearRegSized_of_forall_linearSized hK (fun L hL => hReg μ η d₀ L hμ hη hd₀ hL))

/-- **The full AX1 reduction.** AX1 sorry-free ⟸ the three irreducible obligations. -/
theorem ax1_of_nibbleTheorem_strongDuality_regularity
    (hNib : NibbleTheoremMost) (hdual : StrongDualityHyp)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ → NearRegObligation μ η d₀) :
    AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap hdual (nibbleGap_of_nibbleTheorem hNib hReg)

/-- **The full AX1 reduction, ceiling-aware form.** This is the corrected target for the Freedman
route: the ② regularization supplies the global degree ceiling consumed by
`NibbleTheoremMostCeil`. -/
theorem ax1_of_nibbleTheoremCeil_strongDuality_regularity
    (hNib : NibbleTheoremMostCeil) (hdual : StrongDualityHyp)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ → NearRegObligation μ η d₀) :
    AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap hdual (nibbleGap_of_nibbleTheoremCeil hNib hReg)

/-- **The full AX1 reduction, sized ceiling-aware form.** This is the version aligned with the
Freedman parameter atom after exposing the necessary size control. -/
theorem ax1_of_nibbleTheoremCeilSized_strongDuality_regularity
    (hNib : NibbleTheoremMostCeilSized) (hdual : StrongDualityHyp)
    (hReg : ∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K →
      NearRegObligationSized μ η d₀ K) :
    AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap hdual (nibbleGap_of_nibbleTheoremCeilSized hNib hReg)

/-- Sized Freedman AX1 reduction consuming the linear dense-regime form of ②. -/
theorem ax1_of_nibbleTheoremCeilSized_strongDuality_linearRegularity
    (hNib : NibbleTheoremMostCeilSized) (hdual : StrongDualityHyp)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      NearRegObligationLinearSized μ η d₀ L) :
    AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap hdual
    (nibbleGap_of_nibbleTheoremCeilSized_linear hNib hReg)

end Nibble.AX1
