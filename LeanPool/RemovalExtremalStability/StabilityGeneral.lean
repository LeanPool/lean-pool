/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Tactic
public import LeanPool.RemovalExtremalStability.Furedi
public import LeanPool.RemovalExtremalStability.CliqueRemoval
public import LeanPool.RemovalExtremalStability.Embedding

/-!

Adapted from [jtraverso/turan-stability](https://github.com/jtraverso/turan-stability/blob/3eb99033cc931add291781f77b7446dcba8f5f9d/StabilityLib/StabilityGeneral.lean) (Palomar-registered source).
# The Erdős–Simonovits stability theorem

**Erdős–Simonovits stability theorem** (Erdős 1967, Simonovits 1968), in the form derived by
Füredi (2015) from the regularity method: let `L` be a finite graph with chromatic number at most
`p + 1` (i.e. `L.Colorable (p + 1)`). For every `ε > 0` there are `δ > 0` and `n₀` such that every
`L`-free graph on `n ≥ n₀` vertices with at least `(1 - 1/p) n² / 2 - δ n²` edges differs from
some complete `p`-partite graph on the same vertices in at most `ε n²` edges.

The proof combines Szemerédi's regularity lemma (through the reduced graph of
`StabilityLib/CliqueRemoval.lean`), the embedding lemma `Embedding.exists_embedding_of_isUniform`
(the reduced graph of an `L`-free graph is `K_{p+1}`-free) and Füredi's theorem
`Furedi.exists_partition_symmDiff_le` applied to the reduced graph.

`ErdosSimonovits.stability`: the theorem above. The complete `p`-partite graph with parts the
fibres of `f : W → Fin p` is `(⊤ : SimpleGraph (Fin p)).comap f`; `L ⊑ G` is Mathlib's
`SimpleGraph.IsContained`.
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace ErdosSimonovits

/-- The reduced graph of an `L`-free graph is `K_r`-free, provided `L` is properly
`r`-coloured and the parameters allow the embedding lemma. -/
theorem regularityReduced_cliqueFree {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {β : Type*} [Fintype β] (L : SimpleGraph β)
    {r : ℕ} (c : β → Fin r) (hc : ∀ x y, L.Adj x y → c x ≠ c y)
    {P : Finpartition (univ : Finset α)} {B : ℕ} {η d ε : ℝ} (hη : 0 < η) (hd : 0 < d)
    (hd₁ : d ≤ 1) (hηd : 2 * card β * η ≤ d ^ card β) (hdη : d + η ≤ ε / 4)
    (hP₁ : P.IsEquipartition) (hP₃ : #P.parts ≤ B)
    (hsize : 2 * card β ≤ d ^ card β * (card α / (2 * B : ℝ))) (hL : ¬ L.IsContained G) :
    (G.regularityReduced P η (ε / 4)).CliqueFree r := by
  intro t ht
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
  have key : ∀ i j, i ≠ j → G.IsUniform η (U i) (U j) ∧ ε / 4 ≤ G.edgeDensity (U i) (U j) := by
    intro i j hij
    obtain ⟨-, X, hX, Y, hY, hxX, hyY, -, hu, hdens⟩ := hv i j hij
    have h1 : U i = X := P.part_eq_of_mem hX hxX
    have h2 : U j = Y := P.part_eq_of_mem hY hyY
    rw [h1, h2]
    exact ⟨hu, hdens⟩
  refine hL (Embedding.isContained_of_isUniform G L c hc U hη hd hd₁ hηd (fun i ↦ ?_)
    (fun i j hij ↦ (key i j hij).1) (fun i j hij ↦ hdη.trans (key i j hij).2))
  refine hsize.trans ?_
  gcongr
  exact CliqueRemoval.card_bound hP₁ hP₃ (P.part_mem.2 (mem_univ _))

/-- Edit distance to `K` grows by at most the number of deleted edges when passing from a
subgraph `G'` to `G`. -/
theorem ncard_symmDiff_le {W : Type*} [Finite W] {G G' : SimpleGraph W} (h : G' ≤ G)
    (K : SimpleGraph W) :
    (symmDiff G K).edgeSet.ncard ≤
      (symmDiff G' K).edgeSet.ncard + (G.edgeSet.ncard - G'.edgeSet.ncard) := by
  have hle : symmDiff G K ≤ symmDiff G' K ⊔ (G \ G') := by
    intro x y hxy
    simp only [symmDiff_def, sup_adj, sdiff_adj] at hxy ⊢
    by_cases h1 : G'.Adj x y
    · have := h h1
      tauto
    · rcases hxy with hxy | hxy
      · tauto
      · exact Or.inl (Or.inr ⟨hxy.1, fun h2 ↦ hxy.2 (h h2)⟩)
  calc (symmDiff G K).edgeSet.ncard ≤ (symmDiff G' K ⊔ (G \ G')).edgeSet.ncard :=
        Set.ncard_le_ncard (edgeSet_mono hle) (Set.toFinite _)
    _ ≤ (symmDiff G' K).edgeSet.ncard + (G \ G').edgeSet.ncard := by
        rw [edgeSet_sup]; exact Set.ncard_union_le _ _
    _ = _ := by
        rw [edgeSet_sdiff, Set.ncard_sdiff (edgeSet_mono h) (Set.toFinite _)]

/-- **Erdős–Simonovits stability theorem.** Let `L` be a finite graph that is
`(p + 1)`-colourable. For every `ε > 0` there are `δ > 0` and `n₀` such that every graph `G` on
`n ≥ n₀` vertices that does not contain `L` and has at least `(1 - 1/p) n² / 2 - δ n²` edges
differs from some complete `p`-partite graph on the same vertices in at most `ε n²` edges. -/
theorem stability {β : Type} [Finite β] (L : SimpleGraph β) {p : ℕ} (hp : 0 < p)
    (hL : L.Colorable (p + 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ (W : Type) [Fintype W] (G : SimpleGraph W), n₀ ≤ card W →
      ¬ L.IsContained G →
      (1 - 1 / (p : ℝ)) * (card W : ℝ) ^ 2 / 2 - δ * (card W : ℝ) ^ 2 ≤ G.edgeSet.ncard →
      ∃ f : W → Fin p,
        ((symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard : ℝ) ≤
          ε * (card W : ℝ) ^ 2 := by
  classical
  have := Fintype.ofFinite β
  set k := card β with hk_def
  have C : L.Coloring (Fin (p + 1)) := hL.some
  set ε' : ℝ := min ε 1 with hε'_def
  have hε' : 0 < ε' := lt_min hε one_pos
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  set ε₁ : ℝ := ε' / 8 with hε₁_def
  have hε₁ : 0 < ε₁ := by positivity
  set d : ℝ := ε₁ / 8 with hd_def
  have hd : 0 < d := by positivity
  have hd₁ : d ≤ 1 := by linarith
  set η : ℝ := min (ε₁ / 8) (d ^ k / (2 * k + 1)) with hη_def
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηε : η ≤ ε₁ / 8 := min_le_left _ _
  have hηd : 2 * k * η ≤ d ^ k := by
    have h1 : η ≤ d ^ k / (2 * k + 1) := min_le_right _ _
    have hp : 0 < d ^ k := by positivity
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hdη : d + η ≤ ε₁ / 4 := by linarith
  set l : ℕ := ⌈4 / ε₁⌉₊ with hl_def
  have hl : 4 / ε₁ ≤ l := Nat.le_ceil _
  set B : ℕ := SzemerediRegularity.bound η l with hB_def
  have hB : (0 : ℝ) < B := by positivity
  refine ⟨ε / 12, by positivity, max (l + 1) (⌈2 * B * (2 * k / d ^ k)⌉₊ + 1), ?_⟩
  intro W _ G hn hLG hedge
  set n := card W with hn_def
  have hn1 : l + 1 ≤ n := (le_max_left _ _).trans hn
  have hn2 : ⌈2 * B * (2 * k / d ^ k)⌉₊ + 1 ≤ n := (le_max_right _ _).trans hn
  have : Nonempty W := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G hη (show l ≤ card W by omega)
  have hP' : 4 / ε₁ ≤ #P.parts := hl.trans (Nat.cast_le.2 hP₂)
  have hrem := CliqueRemoval.regularityReduced_edges_card_aux' hε₁ hη hηε hP₁ hP₄ hP'
  set G' := G.regularityReduced P η (ε₁ / 4) with hG'_def
  have hG'G : G' ≤ G := regularityReduced_le
  have hsize : 2 * (k : ℝ) ≤ d ^ k * (n / (2 * B : ℝ)) := by
    have h1 : 2 * B * (2 * k / d ^ k) < (n : ℝ) := by
      have := Nat.lt_of_ceil_lt (show ⌈2 * B * (2 * k / d ^ k)⌉₊ < n by omega)
      exact this
    have hdk : 0 < d ^ k := by positivity
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    rw [mul_div_assoc', div_lt_iff₀ hdk] at h1
    nlinarith
  have hfree : G'.CliqueFree (p + 1) :=
    regularityReduced_cliqueFree G L C (fun x y h ↦ C.valid h) hη hd hd₁ hηd hdη hP₁ hP₃
      hsize hLG
  set T := turanNumber n p
  set e' := G'.edgeSet.ncard
  set e := G.edgeSet.ncard
  obtain ⟨f, -, h2⟩ := Furedi.exists_partition_symmDiff_le G' hp hfree (t := T - e') le_add_tsub
  refine ⟨f, ?_⟩
  have h3 := ncard_symmDiff_le hG'G ((⊤ : SimpleGraph (Fin p)).comap f)
  have hee : e' ≤ e := Set.ncard_le_ncard (edgeSet_mono hG'G) (Set.toFinite _)
  have hrem' : (e : ℝ) - e' < ε₁ * (n : ℝ) ^ 2 := by
    have he : e = #G.edgeFinset := by rw [← Set.ncard_coe_finset, coe_edgeFinset]
    have he' : e' = #G'.edgeFinset := by rw [← Set.ncard_coe_finset, coe_edgeFinset]
    rw [he, he']
    push_cast at hrem
    exact hrem
  have hT : (T : ℝ) ≤ (1 - 1 / (p : ℝ)) * (n : ℝ) ^ 2 / 2 := by
    have h := mul_turanNumber_le (r := p) (n := n)
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hc : (2 * p * T : ℝ) ≤ ((p : ℝ) - 1) * (n : ℝ) ^ 2 := by
      have := (Nat.cast_le (α := ℝ)).mpr h
      push_cast [Nat.cast_sub (show 1 ≤ p from hp)] at this
      exact this
    rw [show (1 - 1 / (p : ℝ)) * (n : ℝ) ^ 2 / 2 = ((p - 1) * (n : ℝ) ^ 2) / (2 * p) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have ht : ((T - e' : ℕ) : ℝ) ≤ ε / 12 * (n : ℝ) ^ 2 + ε₁ * (n : ℝ) ^ 2 := by
    rcases le_total T e' with h | h
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]; positivity
    · rw [Nat.cast_sub h]; linarith
  have h4 : ((symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard : ℝ) ≤
      3 * ((T - e' : ℕ) : ℝ) + ((e - e' : ℕ) : ℝ) := by
    exact_mod_cast h3.trans (Nat.add_le_add_right h2 _)
  rw [Nat.cast_sub hee] at h4
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have : ε₁ * (n : ℝ) ^ 2 ≤ ε / 8 * (n : ℝ) ^ 2 := by gcongr; linarith
  nlinarith

end ErdosSimonovits
