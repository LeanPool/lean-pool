/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.RemovalExtremalStability.TuranStability
public import LeanPool.RemovalExtremalStability.GraphRemoval

/-!
# Stability with few forbidden copies

This combines the graph removal lemma with Erdős–Simonovits stability. The graph is allowed to
contain a small positive density of labelled copies of the forbidden graph.
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace RemovalExtremalStability

/-- If `H` is `(p + 1)`-colourable, a graph with nearly the Turán number of edges and sufficiently
few labelled copies of `H` is close to a complete `p`-partite graph. -/
theorem stability_of_few_copies {β : Type} [Fintype β] (H : SimpleGraph β) {p : ℕ}
    (hp : 0 < p) (hH : H.Colorable (p + 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧ ∃ n₀ : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
        n₀ ≤ card W →
        (G.labelledCopyCount H : ℝ) < η * card W ^ card β →
        (1 - 1 / (p : ℝ)) * (card W : ℝ) ^ 2 / 2 - δ * (card W : ℝ) ^ 2 ≤
          G.edgeSet.ncard →
        ∃ f : W → Fin p,
          ((symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard : ℝ) ≤
            ε * (card W : ℝ) ^ 2 := by
  classical
  obtain ⟨δ₀, hδ₀, n₀, hstab⟩ := TuranStability.stability H hp hH (half_pos hε)
  let ξ : ℝ := min (δ₀ / 2) (ε / 2)
  have hξ : 0 < ξ := lt_min (half_pos hδ₀) (half_pos hε)
  obtain ⟨η, hη, hrem⟩ := RemovalLemma.graph_removal H hξ
  refine ⟨δ₀ / 2, η, half_pos hδ₀, hη, n₀, ?_⟩
  intro W _ _ G _ hn hcopies hedges
  obtain ⟨G', hsub, _, hdelete, hfree⟩ := hrem W G hcopies
  have he : G.edgeSet.ncard = #G.edgeFinset := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  have he' : G'.edgeSet.ncard = #G'.edgeFinset := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  rw [← he, ← he'] at hdelete
  have hcard : G'.edgeSet.ncard ≤ G.edgeSet.ncard :=
    Set.ncard_le_ncard (edgeSet_mono hsub) (Set.toFinite _)
  have hdiff : ((G.edgeSet.ncard - G'.edgeSet.ncard : ℕ) : ℝ) <
      ξ * (card W : ℝ) ^ 2 := by
    rw [Nat.cast_sub hcard]
    simpa only [Nat.cast_pow] using hdelete
  have hedges' :
      (1 - 1 / (p : ℝ)) * (card W : ℝ) ^ 2 / 2 - δ₀ * (card W : ℝ) ^ 2 ≤
        G'.edgeSet.ncard := by
    have hξδ : ξ ≤ δ₀ / 2 := min_le_left _ _
    have hn2 : (0 : ℝ) ≤ (card W : ℝ) ^ 2 := sq_nonneg _
    rw [Nat.cast_sub hcard] at hdiff
    nlinarith
  obtain ⟨f, hf⟩ := hstab W G' hn (by exact hfree) hedges'
  refine ⟨f, ?_⟩
  have hdist := ErdosSimonovits.ncard_symmDiff_le hsub
      ((⊤ : SimpleGraph (Fin p)).comap f)
  have hξε : ξ ≤ ε / 2 := min_le_right _ _
  have hn2 : (0 : ℝ) ≤ (card W : ℝ) ^ 2 := sq_nonneg _
  have hdist' :
      ((symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard : ℝ) ≤
        ((symmDiff G' ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard : ℝ) +
          ((G.edgeSet.ncard - G'.edgeSet.ncard : ℕ) : ℝ) := by
    exact_mod_cast hdist
  nlinarith

end RemovalExtremalStability
