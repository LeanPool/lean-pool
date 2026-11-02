/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic
public import LeanPool.RemovalExtremalStability.CliqueCounting

/-!

Adapted from [jtraverso/turan-stability](https://github.com/jtraverso/turan-stability/blob/3eb99033cc931add291781f77b7446dcba8f5f9d/StabilityLib/CliqueRemoval.lean) (Palomar-registered source).
# The clique removal lemma

This file generalises Mathlib's triangle removal lemma (`SimpleGraph.triangle_removal`,
`SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset`) from triangles to cliques of any size `r`,
using Szemerédi's regularity lemma (`SzemerediRegularity`, `szemeredi_regularity`), Mathlib's
reduced graph `SimpleGraph.regularityReduced` and the clique counting lemma
`CliqueCounting.card_cliqueFinset_ge`.

* `CliqueRemoval.le_card_cliqueFinset_of_deleteFar`: **clique removal lemma, far form.** For every
  `r` and `ε > 0` there is `δ > 0` such that every finite graph from which one must delete at least
  `ε n²` edges to destroy all `r`-cliques has at least `δ n^r` cliques of size `r`.
* `CliqueRemoval.clique_removal`: **clique removal lemma.** For every `r` and `ε > 0` there is
  `δ > 0` such that every finite graph on `n` vertices with fewer than `δ n^r` cliques of size `r`
  can be made `K_r`-free by deleting fewer than `ε n²` edges.
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace CliqueRemoval

variable {α : Type*} [DecidableEq α] [Fintype α] {G : SimpleGraph α} [DecidableRel G.Adj]
  {P : Finpartition (univ : Finset α)}

/-- Arithmetic helper: `n < 2 k (n / k)` when `0 < k ≤ n`. -/
theorem aux_lt_two_mul {n k : ℕ} (hk : 0 < k) (hn : k ≤ n) : n < 2 * k * (n / k) := by
  rw [mul_assoc, two_mul, ← add_lt_add_iff_right (n % k), add_right_comm, add_assoc,
    Nat.mod_add_div n k, add_comm, add_lt_add_iff_right]
  apply (Nat.mod_lt n hk).trans_le
  simpa using Nat.mul_le_mul_left k ((Nat.one_le_div_iff hk).2 hn)

/-- Parts of an equipartition with at most `B` parts have size at least `card α / (2 B)`. -/
theorem card_bound {B : ℕ} {s : Finset α} (hP₁ : P.IsEquipartition) (hP₃ : #P.parts ≤ B)
    (hX : s ∈ P.parts) : card α / (2 * B : ℝ) ≤ #s := by
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  have := Finset.Nonempty.card_pos ⟨_, hX⟩
  calc
    _ ≤ card α / (2 * #P.parts : ℝ) := by gcongr
    _ ≤ ↑(card α / #P.parts) :=
      (div_le_iff₀' (by positivity)).2 <| mod_cast (aux_lt_two_mul ‹_› P.card_parts_le_card).le
    _ ≤ (#s : ℝ) := mod_cast hP₁.average_le_card_part hX

/-- Generalisation of `SimpleGraph.unreduced_edges_subset` to arbitrary parameters. -/
theorem unreduced_edges_subset' {η δ : ℝ} :
    (univ ×ˢ univ).filter (fun (x, y) ↦ G.Adj x y ∧ ¬ (G.regularityReduced P η δ).Adj x y) ⊆
      (P.nonUniforms G η).biUnion (fun (U, V) ↦ U ×ˢ V) ∪ P.parts.biUnion offDiag ∪
        (P.sparsePairs G δ).biUnion fun (U, V) ↦ G.interedges U V := by
  rintro ⟨x, y⟩
  simp only [mem_filter, regularityReduced_adj, not_and, not_exists,
    not_le, mem_biUnion, mem_union, mem_product, Prod.exists, mem_offDiag, and_imp,
    or_assoc, and_assoc, P.mk_mem_nonUniforms, Finpartition.mk_mem_sparsePairs, mem_interedges_iff]
  intro hx hy h h'
  replace h' := h' h
  obtain ⟨U, hU, hx⟩ := P.exists_mem hx
  obtain ⟨V, hV, hy⟩ := P.exists_mem hy
  obtain rfl | hUV := eq_or_ne U V
  · exact Or.inr (Or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩)
  by_cases h₂ : G.IsUniform η U V
  · exact Or.inr <| Or.inr ⟨U, V, hU, hV, hUV, h' _ hU _ hV hx hy hUV h₂, hx, hy, h⟩
  · exact Or.inl ⟨U, V, hU, hV, hUV, h₂, hx, hy⟩

/-- Generalisation of `SimpleGraph.regularityReduced_edges_card_aux` to a uniformity parameter
`η ≤ ε / 8`. -/
theorem regularityReduced_edges_card_aux' [Nonempty α] {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hηε : η ≤ ε / 8) (hP : P.IsEquipartition)
    (hPε : P.IsUniform G η) (hP' : 4 / ε ≤ #P.parts) :
    (#G.edgeFinset - #(G.regularityReduced P η (ε / 4)).edgeFinset : ℝ)
      < ε * (card α ^ 2 : ℕ) := by
  let A := (P.nonUniforms G η).biUnion fun (U, V) ↦ U ×ˢ V
  let B := P.parts.biUnion offDiag
  let C := (P.sparsePairs G (ε / 4)).biUnion fun (U, V) ↦ G.interedges U V
  suffices h : 2 * (#G.edgeFinset - #(G.regularityReduced P η (ε / 4)).edgeFinset : ℝ)
      < 2 * ε * (card α ^ 2 : ℕ) by linarith
  calc
    _ = (#((univ ×ˢ univ).filter fun (x, y) ↦
          G.Adj x y ∧ ¬(G.regularityReduced P η (ε / 4)).Adj x y) : ℝ) := by
      rw [univ_product_univ, mul_sub, filter_and_not, cast_card_sdiff]
      · norm_cast
        rw [two_mul_card_edgeFinset, two_mul_card_edgeFinset]
      · gcongr with xy _
        exact fun hxy ↦ regularityReduced_le hxy
    _ ≤ (#(A ∪ B ∪ C) : ℝ) := by
      exact_mod_cast card_le_card (unreduced_edges_subset' (G := G) (P := P) (η := η) (δ := ε / 4))
    _ ≤ #(A ∪ B) + #C := mod_cast (card_union_le _ _)
    _ ≤ #A + #B + #C := by gcongr; exact mod_cast card_union_le _ _
    _ < 4 * η * card α ^ 2 + _ + _ := by
      gcongr; exact hP.sum_nonUniforms_lt univ_nonempty hη hPε
    _ ≤ 4 * (ε / 8) * card α ^ 2 + ε / 2 * card α ^ 2 + 4 * (ε / 4) * card α ^ 2 := by
      gcongr
      · exact hP.card_biUnion_offDiag_le hε hP'
      · exact hP.card_interedges_sparsePairs_le (G := G) (ε := ε / 4) (by positivity)
    _ = 2 * ε * (card α ^ 2 : ℕ) := by push_cast; ring

/-- An `r`-clique of the reduced graph yields many `r`-cliques of `G`. -/
theorem card_cliqueFinset_ge_of_mem_reduced {r B : ℕ} {ε η d : ℝ} (hη : 0 < η) (hd : 0 < d)
    (hηd : 2 * r * η ≤ d ^ (r - 1)) (hdη : d + η ≤ ε / 4) (hP₁ : P.IsEquipartition)
    (hP₃ : #P.parts ≤ B) {t : Finset α}
    (ht : (G.regularityReduced P η (ε / 4)).IsNClique r t) :
    d ^ r.choose 2 / 2 ^ r * (card α / (2 * B : ℝ)) ^ r ≤ #(G.cliqueFinset r) := by
  let e := t.equivFin
  let v : Fin r → α := fun i ↦ (e.symm (Fin.cast ht.card_eq.symm i) : α)
  have hv : ∀ i j, i ≠ j → (G.regularityReduced P η (ε / 4)).Adj (v i) (v j) := by
    intro i j hij
    refine ht.isClique (e.symm _).2 (e.symm _).2 ?_
    intro h
    apply hij
    have := e.symm.injective (Subtype.ext h)
    exact Fin.cast_injective _ this
  let U : Fin r → Finset α := fun i ↦ P.part (v i)
  have key : ∀ i j, i ≠ j → U i ∈ P.parts ∧ U j ∈ P.parts ∧ U i ≠ U j ∧
      G.IsUniform η (U i) (U j) ∧ ε / 4 ≤ G.edgeDensity (U i) (U j) := by
    intro i j hij
    obtain ⟨-, X, hX, Y, hY, hxX, hyY, hXY, hu, hdens⟩ := hv i j hij
    have h1 : U i = X := P.part_eq_of_mem hX hxX
    have h2 : U j = Y := P.part_eq_of_mem hY hyY
    rw [h1, h2]
    exact ⟨hX, hY, hXY, hu, hdens⟩
  have hcount := CliqueCounting.card_cliqueFinset_ge G U hη hd hηd
    (fun i j hij ↦ by
      obtain ⟨h1, h2, h3, -⟩ := key i j hij
      exact P.disjoint h1 h2 h3)
    (fun i j hij ↦ (key i j hij).2.2.2.1)
    (fun i j hij ↦ hdη.trans (key i j hij).2.2.2.2)
  refine le_trans ?_ hcount
  gcongr
  calc
    (card α / (2 * B : ℝ)) ^ r = ∏ _i : Fin r, (card α / (2 * B : ℝ)) := by
      rw [prod_const, card_univ, Fintype.card_fin]
    _ ≤ ∏ i, (#(U i) : ℝ) := by
      gcongr with i
      exact card_bound hP₁ hP₃ (P.part_mem.2 (mem_univ _))

/-- **Clique removal lemma, far form.** For every `r` and `ε > 0` there is `δ > 0` such that a
finite graph on `n` vertices that is `ε n²`-far from being `K_r`-free (in the sense of Mathlib's
`SimpleGraph.DeleteFar`) has at least `δ n^r` cliques of size `r`. -/
theorem le_card_cliqueFinset_of_deleteFar (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj], G.DeleteFar (fun H ↦ H.CliqueFree r) (ε * (card α ^ 2 : ℕ)) →
        δ * card α ^ r ≤ #(G.cliqueFinset r) := by
  classical
  obtain rfl | hr := Nat.eq_zero_or_pos r
  · refine ⟨1, one_pos, fun α _ _ G _ _ ↦ ?_⟩
    have : 0 < #(G.cliqueFinset 0) := card_pos.2 ⟨∅, by simp⟩
    simp only [pow_zero, mul_one, Nat.one_le_cast]
    exact this
  set d : ℝ := ε / 8 with hd_def
  have hd : 0 < d := by positivity
  set η : ℝ := min (ε / 8) (d ^ (r - 1) / (2 * r + 1)) with hη_def
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηε : η ≤ ε / 8 := min_le_left _ _
  have hηd : 2 * r * η ≤ d ^ (r - 1) := by
    have h1 : η ≤ d ^ (r - 1) / (2 * r + 1) := min_le_right _ _
    have hp : 0 < d ^ (r - 1) := by positivity
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hdη : d + η ≤ ε / 4 := by linarith
  set l : ℕ := ⌈4 / ε⌉₊ with hl_def
  have hl : 4 / ε ≤ l := Nat.le_ceil _
  set B : ℕ := SzemerediRegularity.bound η l with hB_def
  have hB : (0 : ℝ) < B := by positivity
  set δ : ℝ := min 1 (min (1 / (2 * (l + 1) ^ r)) (d ^ r.choose 2 / 2 ^ r * (1 / (2 * B)) ^ r))
    with hδ_def
  have hδ1 : δ ≤ 1 / (2 * (l + 1) ^ r) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ d ^ r.choose 2 / 2 ^ r * (1 / (2 * B)) ^ r :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, by positivity, fun α _ _ G _ hG ↦ ?_⟩
  have hδ0 : 0 ≤ δ := by positivity
  obtain hn | hn := Nat.eq_zero_or_pos (card α)
  · rw [hn, Nat.cast_zero, zero_pow hr.ne', mul_zero]
    positivity
  have hnc : ¬ G.CliqueFree r := by
    intro h
    have := hG (s := ∅) (empty_subset _) (by simpa only [coe_empty, deleteEdges_empty] using h)
    rw [Finset.card_empty, Nat.cast_zero] at this
    have : (0 : ℝ) < ε * (card α ^ 2 : ℕ) := by positivity
    linarith
  rcases le_total (card α) l with hl' | hl'
  · obtain ⟨t, ht⟩ : ∃ t, G.IsNClique r t := by
      simpa [CliqueFree] using hnc
    have h1 : (1 : ℝ) ≤ #(G.cliqueFinset r) := by
      exact_mod_cast card_pos.2 ⟨t, mem_cliqueFinset_iff.2 ht⟩
    calc δ * card α ^ r ≤ 1 / (2 * (l + 1) ^ r) * (l + 1) ^ r := by
          gcongr
          exact_mod_cast hl'.trans (Nat.le_succ l)
      _ = 1 / 2 := by field_simp
      _ ≤ _ := by linarith
  · have : Nonempty α := Fintype.card_pos_iff.1 hn
    obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G hη hl'
    have hP' : 4 / ε ≤ #P.parts := hl.trans (Nat.cast_le.2 hP₂)
    have k := regularityReduced_edges_card_aux' hε hη hηε hP₁ hP₄ hP'
    have hnc' : ¬ (G.regularityReduced P η (ε / 4)).CliqueFree r := by
      intro h
      have := (deleteFar_iff.1 hG) regularityReduced_le h
      linarith
    obtain ⟨t, ht⟩ : ∃ t, (G.regularityReduced P η (ε / 4)).IsNClique r t := by
      simpa [CliqueFree] using hnc'
    have := card_cliqueFinset_ge_of_mem_reduced hη hd hηd hdη hP₁ hP₃ ht
    calc δ * card α ^ r ≤ d ^ r.choose 2 / 2 ^ r * (1 / (2 * B)) ^ r * card α ^ r := by
          gcongr
      _ = d ^ r.choose 2 / 2 ^ r * (card α / (2 * B : ℝ)) ^ r := by
          rw [div_pow, div_pow, div_pow, one_pow]; ring
      _ ≤ _ := this

/-- **Clique removal lemma.** For every `r` and `ε > 0` there is `δ > 0` such that every finite
graph on `n` vertices with fewer than `δ n^r` cliques of size `r` has a `K_r`-free subgraph
obtained by deleting fewer than `ε n²` edges. -/
theorem clique_removal (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj], (#(G.cliqueFinset r) : ℝ) < δ * card α ^ r →
        ∃ G' ≤ G, ∃ _ : DecidableRel G'.Adj,
          (#G.edgeFinset - #G'.edgeFinset : ℝ) < ε * (card α ^ 2 : ℕ) ∧ G'.CliqueFree r := by
  obtain ⟨δ, hδ, h⟩ := le_card_cliqueFinset_of_deleteFar r hε
  refine ⟨δ, hδ, fun α _ _ G _ hG ↦ ?_⟩
  by_contra! h'
  refine hG.not_ge (h α G (deleteFar_iff.2 ?_))
  intro G' _ hG' hG''
  exact le_of_not_gt fun i ↦ h' G' hG' _ i hG''

end CliqueRemoval
