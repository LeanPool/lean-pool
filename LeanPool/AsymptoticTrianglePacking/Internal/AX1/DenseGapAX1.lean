/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the packing gap `ν₃* − ν₃ ≤ ε n²` in the dense regime, and the residual for AX1

`Nibble.AX1.nibbleGap_holds` currently consumes
`hReg : ∀ μ η d₀ K, … → NearRegObligationSized μ η d₀ K`, i.e. near-`d`-regularity of the triangle
hypergraph for **every** graph.  That hypothesis is false as stated — a triangle-free `G` with at
least one edge already refutes it, see `Nibble.NearRegObligationRefutation` — so it is not an honest
input.  This file removes it in the regime where it is genuinely true, and isolates the remaining
mathematics as one precisely stated residual.

* `Nibble.AX1.gap_le_of_sub_matching` — the packing-gap accounting: a large matching of
  `triangleHypergraphSub G` gives `ν₃* − ν₃ ≤ ε|V|²`.
* `Nibble.AX1.nibbleGap_dense` — **unconditional**: for every `ε > 0` there is a density threshold
  `θ < 1` and an `n₀` such that every graph on `≥ n₀` vertices with minimum degree `≥ θ|V|`
  satisfies `ν₃* − ν₃ ≤ ε|V|²`.  Proof: at that minimum degree the triangle hypergraph is
  near-`|V|`-regular with an EMPTY exceptional set and the global degree ceiling
  (`Nibble.YusterE.triangleSub_linearSized_data_of_minDeg`), which is exactly the input of the
  unconditional nibble theorem `Nibble.nibbleTheoremMostCeil_holds`.
* `Nibble.AX1.nibbleGap_fewTriangles` — **unconditional**: graphs with few triangles have small gap
  (`ν₃* ≤ #triangles`).
* `Nibble.AX1.NibbleGapResidual` — the residual: the packing gap for graphs that both have a vertex
  of degree below the threshold `θ|V|` and have more than `ε|V|²` triangles.
* `Nibble.AX1.nibbleGapHyp_of_residual`, `Nibble.AX1.ax1_holds_of_residual` — the machine-checked
  reductions `residual → NibbleGapHyp → AX1Statement` (the latter also using the proved
  `Nibble.AX1.strongDualityHyp_holds`).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.TightNibble
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.Tight.DenseRegDischarge
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.StrongDuality

/-! # DenseGapAX1 -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-- **Packing-gap accounting.**  A matching of the triangle hypergraph of size at least
`(1 − 3ε)|E(G)|/3` forces `ν₃* − ν₃ ≤ ε|V|²`, using `ν₃* ≤ |E|/3` and `|E| ≤ |V|²`. -/
theorem gap_le_of_sub_matching {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ} (hε : 0 < ε)
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hMcard : (1 - 3 * ε) * ((Fintype.card (EdgeV G) : ℝ) / 3) ≤ (M.card : ℝ)) :
    nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  set E : ℝ := ((G.cliqueFinset 2).card : ℝ) with hE
  have hcardE : (Fintype.card (EdgeV G) : ℝ) = E := by rw [hE]; exact_mod_cast card_EdgeV G
  rw [hcardE] at hMcard
  have h1 : (M.card : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast sub_matching_card_le_nu3 G hM
  have h2 : nu3star G ≤ E / 3 := nu3star_le G
  have h3 : E ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
  have hεE : ε * E ≤ ε * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 hε.le
  nlinarith only [h2, hMcard, h1, hεE]

/-- **The dense branch, unconditionally.**  For every `ε > 0` there is a density threshold `θ < 1`
and a size threshold `n₀` such that every graph on at least `n₀` vertices with minimum degree at
least `θ|V|` satisfies `ν₃* − ν₃ ≤ ε|V|²`.

At minimum degree `θ|V| = (1 − μ/2)|V|` the common neighbourhood of every edge has size in
`[(1−μ)|V|, |V|]`, so the triangle hypergraph is near-`|V|`-regular with an *empty* exceptional set,
bounded codegree and the global degree ceiling — precisely the hypotheses of the unconditional
nibble theorem `Nibble.nibbleTheoremMostCeil_holds`. -/
theorem nibbleGap_dense (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (∀ x : V, θ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ :=
    nibbleTheoremMostCeil_holds 3 (by norm_num) (3 * ε) (by linarith)
  have hmpos : 0 < min μ 1 := lt_min hμ one_pos
  have hm1 : min μ 1 ≤ 1 := min_le_right _ _
  have hmμ : min μ 1 ≤ μ := min_le_left _ _
  refine ⟨1 - min μ 1 / 2, by linarith, by linarith,
    ⌈max d₀ (max (1 / μ) 1)⌉₊, ?_⟩
  intro V _ _ G _ hV hdeg
  have hnR : max d₀ (max (1 / μ) 1) ≤ (Fintype.card V : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hV)
  have hd0 : d₀ ≤ (Fintype.card V : ℝ) := le_trans (le_max_left _ _) hnR
  have hinv : 1 / μ ≤ (Fintype.card V : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnR
  have hn1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnR
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := lt_of_lt_of_le one_pos hn1
  -- the integer minimum-degree floor
  set D : ℕ := ⌈(1 - min μ 1 / 2) * (Fintype.card V : ℝ)⌉₊ with hDdef
  have hD : ∀ x, D ≤ G.degree x := fun x => Nat.ceil_le.mpr (hdeg x)
  have hDR : (1 - min μ 1 / 2) * (Fintype.card V : ℝ) ≤ (D : ℝ) := Nat.le_ceil _
  have h2DR : (Fintype.card V : ℝ) ≤ 2 * (D : ℝ) := by nlinarith
  have h2D : Fintype.card V ≤ 2 * D := by exact_mod_cast h2DR
  have hcodeg : (1 : ℝ) ≤ μ * (Fintype.card V : ℝ) := by
    rw [div_le_iff₀ hμ] at hinv
    linarith
  obtain ⟨hreg, hcod, hceil, -⟩ :=
    triangleSub_linearSized_data_of_minDeg (μ := μ) (η := η) (d := (Fintype.card V : ℝ)) (L := 1)
      G D hD h2D hη.le hcodeg (by rw [one_mul]) (by nlinarith) (by nlinarith)
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) (Fintype.card V : ℝ) hnpos hd0
      (triangleHypergraphSub_uniform G) hreg hcod hceil
  refine gap_le_of_sub_matching G hε hM ?_
  simpa using hMcard

/-- Every fractional triangle packing has total weight at most the number of triangles: each single
weight is at most `1` by its own edge constraint. -/
theorem fracPacking_sum_le_card_triangles {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {w : Finset (Finset V) → ℝ}
    (hw : IsFracPacking G w) :
    (∑ T ∈ triangleHypergraphE G, w T) ≤ ((G.cliqueFinset 3).card : ℝ) := by
  obtain ⟨hnn, -, hcon⟩ := hw
  have hone : ∀ T ∈ triangleHypergraphE G, w T ≤ 1 := by
    intro T hT
    have hcard : T.card = 3 := triangleHypergraphE_uniform G T hT
    obtain ⟨e, he⟩ : T.Nonempty := Finset.card_pos.mp (by rw [hcard]; norm_num)
    refine le_trans (Finset.single_le_sum (f := w) (fun T' _ => hnn T') ?_) (hcon e)
    exact Finset.mem_filter.mpr ⟨hT, he⟩
  calc (∑ T ∈ triangleHypergraphE G, w T)
      ≤ ∑ _T ∈ triangleHypergraphE G, (1 : ℝ) := Finset.sum_le_sum hone
    _ = ((triangleHypergraphE G).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((G.cliqueFinset 3).card : ℝ) := by
        exact_mod_cast Finset.card_image_le (s := G.cliqueFinset 3)
          (f := fun t : Finset V => t.powersetCard 2)

/-- **`ν₃*` is at most the number of triangles.** -/
theorem nu3star_le_card_triangles {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    nu3star G ≤ ((G.cliqueFinset 3).card : ℝ) := by
  refine csSup_le ⟨0, ⟨fun _ => 0, isFracPacking_zero G, by simp⟩⟩ ?_
  rintro x ⟨w, hw, rfl⟩
  exact fracPacking_sum_le_card_triangles G hw

/-- **The triangle-poor branch, unconditionally.**  If `G` has at most `ε|V|²` triangles then the
packing gap is at most `ε|V|²`, because `ν₃* ≤ #triangles` and `ν₃ ≥ 0`. -/
theorem nibbleGap_fewTriangles {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ}
    (h : ((G.cliqueFinset 3).card : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2) :
    nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  have h1 := nu3star_le_card_triangles G
  have h2 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
  linarith

/-- **The residual.**  The packing gap for the graphs that neither branch above covers: those that
fail the density threshold (some vertex has degree below `θ|V|`) *and* are triangle-rich (more than
`ε|V|²` triangles).  Stated for every threshold `θ ∈ (0,1)` because the dense branch's threshold
depends on `ε`.

This is a *true* statement (a special case of the Haxell–Rödl theorem), unlike the previous blocker
`NearRegObligationSized`, which asserts near-regularity of the triangle hypergraph of an arbitrary
graph and is false. -/
def NibbleGapResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, 0 < θ → θ < 1 → ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → (∃ x : V, (G.degree x : ℝ) < θ * (Fintype.card V : ℝ)) →
      ε * (Fintype.card V : ℝ) ^ 2 < ((G.cliqueFinset 3).card : ℝ) →
      nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **The reduction.**  `NibbleGapHyp` follows from the residual alone: the dense case is discharged
unconditionally by `nibbleGap_dense` and the triangle-poor case by `nibbleGap_fewTriangles`. -/
theorem nibbleGapHyp_of_residual (h : NibbleGapResidual) : NibbleGapHyp := by
  intro ε hε
  obtain ⟨θ, hθ0, hθ1, n₁, hdense⟩ := nibbleGap_dense ε hε
  obtain ⟨n₂, hres⟩ := h ε hε θ hθ0 hθ1
  refine ⟨max n₁ n₂, ?_⟩
  intro V _ _ G _ hV
  by_cases hmin : ∀ x : V, θ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)
  · exact hdense V G (le_trans (le_max_left _ _) hV) hmin
  push Not at hmin
  rcases le_or_gt ((G.cliqueFinset 3).card : ℝ) (ε * (Fintype.card V : ℝ) ^ 2) with hfew | hmany
  · exact nibbleGap_fewTriangles G hfew
  · exact hres V G (le_trans (le_max_right _ _) hV) hmin hmany

/-- **AX1 from the residual.**  Combines the reduction with the proved strong-duality input
`Nibble.AX1.strongDualityHyp_holds`. -/
theorem ax1_holds_of_residual (h : NibbleGapResidual) : AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap strongDualityHyp_holds (nibbleGapHyp_of_residual h)

end Nibble.AX1
