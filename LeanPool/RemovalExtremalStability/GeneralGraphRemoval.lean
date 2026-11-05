/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Tactic
public import LeanPool.RemovalExtremalStability.CliqueRemoval
public import LeanPool.RemovalExtremalStability.PartialEmbedding

/-!

Adapted from [jtraverso/graph-removal-lemma](https://github.com/jtraverso/graph-removal-lemma/blob/589cf03ef1e4c80ea8cdd6be77778232c62dd37c/RemovalLib/GraphRemoval.lean) (Palomar-registered source).
# The graph removal lemma for every fixed graph

Let `H` be a fixed finite graph on `k` vertices.

* `GraphRemoval.card_copies_ge`: **counting lemma for `H`.** If parts `s x` (one per vertex `x` of
  `H`, possibly repeated) are pairwise dense in a robust sense *along the edges of `H`*, and large
  enough, then the number of injective maps `f` with `f x ∈ s x` sending edges of `H` to edges of
  `G` is at least `(d^k / 4)^k ∏ₓ #(s x)`.
* `GraphRemoval.le_labelledCopyCount_of_deleteFar`: **graph removal lemma, far form**.
  For every `ε > 0` there is `δ > 0` such that a graph on `n` vertices
  from which one must delete at least `ε n²` edges to destroy all copies of `H` (Mathlib's
  `SimpleGraph.DeleteFar` and `SimpleGraph.Free`) has at least `δ n^k` labelled copies of `H`
  (Mathlib's `SimpleGraph.labelledCopyCount`).
* `GraphRemoval.graph_removal`: **graph removal lemma.** A graph on `n` vertices with fewer than
  `δ n^k` labelled copies of `H` can be made `H`-free by deleting fewer than `ε n²` edges.

The quantitative copy-count formulation is stated in Conlon–Fox, *Graph removal lemmas*,
[Theorem 1.1](https://arxiv.org/pdf/1211.3487v1). For fixed `H`, changing from unlabelled copies to
injective labelled copies changes only a factor depending on `H`, which is absorbed into `δ`.
The far form is the contrapositive. Erdős–Frankl–Rödl (1986),
[Theorems 1.5 and 1.5′](https://www.renyi.hu/~p_erdos/1986-17.pdf), give related precursors:
starting from an `H`-free graph, they remove few edges to exclude a clique or a homomorphic image.
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace GraphRemoval

private theorem finite_constrained_copies {α β : Type*} [Finite β] (L : SimpleGraph β)
    (G : SimpleGraph α) (s : β → Finset α) :
    Finite {f : β ↪ α // (∀ x, f x ∈ s x) ∧ ∀ x y, L.Adj x y → G.Adj (f x) (f y)} := by
  classical
  have : Fintype β := Fintype.ofFinite β
  refine Finite.of_injective (β := ↥(Fintype.piFinset s))
    (fun p => ⟨⇑p.1, Fintype.mem_piFinset.2 p.2.1⟩) ?_
  intro p q h
  exact Subtype.ext (DFunLike.coe_injective (congrArg Subtype.val h))

/-- **Counting lemma for a fixed graph.** Let `L` be a graph on a finite type `β` with
`k = card β` vertices, and `s : β → Finset α` parts of a graph `G` such that for every edge `xy` of
`L`, all subsets `A ⊆ s x`, `B ⊆ s y` with `#A ≥ η #(s x)`, `#B ≥ η #(s y)` have edge density at
least `d`, where `0 < η ≤ 1`, `0 < d ≤ 1`, `2 k η ≤ d ^ k` and every part has at least `4 k / d ^ k`
elements. Then there are at least `(d ^ k / 4) ^ k ∏ₓ #(s x)` injective maps `f : β → α` with
`f x ∈ s x` for every `x` that send edges of `L` to edges of `G`. -/
theorem card_copies_ge {α β : Type*} [Fintype β] (L : SimpleGraph β)
    (G : SimpleGraph α) [DecidableRel G.Adj] (s : β → Finset α) {η d : ℝ} (hη : 0 < η)
    (hη₁ : η ≤ 1) (hd : 0 < d) (hd₁ : d ≤ 1) (hηd : 2 * card β * η ≤ d ^ card β)
    (hsize : ∀ x, 4 * card β ≤ d ^ card β * #(s x))
    (hs : ∀ x y, L.Adj x y → ∀ A ⊆ s x, ∀ B ⊆ s y, η * #(s x) ≤ #A → η * #(s y) ≤ #B →
      d ≤ G.edgeDensity A B) :
    (d ^ card β / 4) ^ card β * ∏ x, (#(s x) : ℝ) ≤
      Nat.card {f : β ↪ α // (∀ x, f x ∈ s x) ∧ ∀ x y, L.Adj x y → G.Adj (f x) (f y)} := by
  classical
  set k := card β with hk
  set D : ℝ := d ^ k with hD_def
  have hfin : Finite {f : β ↪ α // (∀ x, f x ∈ s x) ∧ ∀ x y, L.Adj x y → G.Adj (f x) (f y)} :=
    finite_constrained_copies L G s
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have hk0 : k = 0 := Fintype.card_eq_zero
    have hne : Nonempty {f : β ↪ α // (∀ x, f x ∈ s x) ∧ ∀ x y, L.Adj x y → G.Adj (f x) (f y)} :=
      ⟨⟨Function.Embedding.ofIsEmpty, fun a => isEmptyElim a, fun a => isEmptyElim a⟩⟩
    simp only [hk0, pow_zero, univ_eq_empty, Finset.prod_empty]
    exact_mod_cast Nat.card_pos
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Fintype.card_pos
  have hDpos : 0 < D := pow_pos hd _
  obtain ⟨a₀, -⟩ : (s hβ.some).Nonempty := by
    rw [← Finset.card_pos]
    by_contra h
    have := hsize hβ.some
    rw [Nat.eq_zero_of_not_pos h] at this
    simp at this
    linarith
  let Cand : (β → α) → Finset β → β → Finset α := fun f S y =>
    {w ∈ s y | ∀ z ∈ S, L.Adj z y → G.Adj (f z) w}
  have hCandEq : ∀ f S y, Cand f S y = PartialEmbedding.candidates G L s f S y := by
    intros f S y
    ext w
    simp [Cand, PartialEmbedding.candidates]
  let Good : Finset β → Finset (β → α) := fun S =>
    {f ∈ Fintype.piFinset (fun y => if y ∈ S then s y else {a₀}) | Set.InjOn f S ∧
      (∀ x ∈ S, ∀ y ∈ S, L.Adj x y → G.Adj (f x) (f y)) ∧
      ∀ y ∉ S, d ^ #S * #(s y) ≤ #(Cand f S y)}
  have key : ∀ S, ∏ x ∈ S, (D / 4 * #(s x)) ≤ (#(Good S) : ℝ) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Nat.one_le_cast, Nat.one_le_iff_ne_zero, ← pos_iff_ne_zero, card_pos]
      refine ⟨fun _ => a₀, ?_⟩
      simp [Good, Cand]
    | insert x S hxS ih =>
      rw [prod_insert hxS]
      have hSk : #S + 1 ≤ k := by
        have := card_le_univ (insert x S); rwa [card_insert_of_notMem hxS] at this
      have hpowS : D ≤ d ^ #S := pow_le_pow_of_le_one hd.le hd₁ (by omega)
      let Y := (univ \ insert x S).filter (L.Adj x)
      have hYcard : #Y + #S + 1 ≤ k := by
        have h1 : #Y ≤ #(univ \ insert x S) := card_filter_le _ _
        rw [card_sdiff_of_subset (subset_univ _), card_insert_of_notMem hxS, card_univ] at h1
        omega
      let Bad : (β → α) → β → Finset α := fun f y =>
        {v ∈ s x | (#{w ∈ Cand f S y | G.Adj v w} : ℝ) < d * #(Cand f S y)}
      let Ext : (β → α) → Finset α := fun f =>
        (Cand f S x).filter (fun v => v ∉ S.image f ∧ ∀ y ∈ Y, v ∉ Bad f y)
      have hExt : ∀ f ∈ Good S, D / 4 * #(s x) ≤ (#(Ext f) : ℝ) := by
        intro f hf
        obtain ⟨-, -, -, hcand⟩ := mem_filter.1 hf
        have hCand_big : ∀ y ∉ S, D * #(s y) ≤ #(Cand f S y) := fun y hy =>
          (mul_le_mul_of_nonneg_right hpowS (Nat.cast_nonneg _)).trans (hcand y hy)
        have hBad : ∀ y ∈ Y, (#(Bad f y) : ℝ) < η * #(s x) := by
          intro y hy
          simp only [Y, mem_filter, mem_sdiff, mem_univ, true_and, mem_insert, not_or] at hy
          refine CliqueCounting.card_badVertices_lt G hd
            (mul_le_of_le_one_left (Nat.cast_nonneg _) hη₁) fun A hA hA' _ =>
            hs x y hy.2 A hA _ (filter_subset _ _) hA' ?_
          refine le_trans ?_ (hCand_big y hy.1.2)
          gcongr
          nlinarith
        have hsub : Cand f S x ⊆ S.image f ∪ Y.biUnion (Bad f) ∪ Ext f := by
          intro v hv
          by_contra hv'
          simp only [mem_union, not_or, mem_biUnion, not_exists, not_and] at hv'
          exact hv'.2 (mem_filter.2 ⟨hv, hv'.1.1, fun y hy => hv'.1.2 y hy⟩)
        have h1 : (#(Cand f S x) : ℝ) ≤ #S + ∑ y ∈ Y, (#(Bad f y) : ℝ) + #(Ext f) := by
          have := (card_le_card hsub).trans ((card_union_le _ _).trans
            (Nat.add_le_add_right ((card_union_le _ _).trans
              (Nat.add_le_add card_image_le card_biUnion_le)) _))
          exact_mod_cast this
        have h2 : ∑ y ∈ Y, (#(Bad f y) : ℝ) ≤ #Y * (η * #(s x)) := by
          rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum fun y hy => (hBad y hy).le
        have h3 := hCand_big x hxS
        have h4 := hsize x
        have h5 : ((#Y : ℕ) : ℝ) + #S + 1 ≤ k := by exact_mod_cast hYcard
        set N : ℝ := (#(s x) : ℝ)
        have hN : 0 ≤ N := Nat.cast_nonneg _
        have hY0 : (0 : ℝ) ≤ #Y := Nat.cast_nonneg _
        have hS0 : (0 : ℝ) ≤ #S := Nat.cast_nonneg _
        have e1 : 2 * #Y * (η * N) ≤ D * N := by
          have := mul_le_mul_of_nonneg_right hηd hN
          have : 2 * #Y * (η * N) ≤ 2 * k * η * N := by
            have : 0 ≤ η * N := by positivity
            nlinarith
          linarith
        nlinarith
      have hmem : ∀ f ∈ Good S, ∀ v ∈ Ext f, Function.update f x v ∈ Good (insert x S) := by
        intro f hf v hv
        obtain ⟨hpi, hinj, hadj, hcand⟩ := mem_filter.1 hf
        rw [Fintype.mem_piFinset] at hpi
        obtain ⟨hvC, hvS, hvB⟩ := mem_filter.1 hv
        have hvC' := mem_filter.1 hvC
        have hmemS : ∀ z ∈ S, f z ∈ s z := by
          intro z hz
          simpa [hz] using hpi z
        have hgood : ∀ y, y ∉ insert x S → L.Adj x y →
            d * #(Cand f S y) ≤ #{w ∈ Cand f S y | G.Adj v w} := by
          intro y hy hxy
          have hyY : y ∈ Y := by simp [Y, hy, hxy]
          exact le_of_not_gt fun h => hvB y hyY (mem_filter.2 ⟨hvC'.1, h⟩)
        have hcandShared : ∀ y ∉ S, d ^ #S * #(s y) ≤
            #(PartialEmbedding.candidates G L s f S y) := by
          simpa only [← hCandEq] using hcand
        have hvCShared : v ∈ PartialEmbedding.candidates G L s f S x := by
          simpa only [← hCandEq] using hvC
        have hgoodShared : ∀ y, y ∉ insert x S → L.Adj x y →
            d * #(PartialEmbedding.candidates G L s f S y) ≤
              #{w ∈ PartialEmbedding.candidates G L s f S y | G.Adj v w} := by
          simpa only [← hCandEq] using hgood
        obtain ⟨hinj', -, hadj', hcand'⟩ :=
          PartialEmbedding.extend G L s hd hd₁ S x hxS f v
            hinj hmemS hadj hcandShared hvCShared hvS hgoodShared
        have hcandFinal : ∀ y ∉ insert x S,
            d ^ #(insert x S) * #(s y) ≤ #(Cand (Function.update f x v) (insert x S) y) := by
          simpa only [← hCandEq] using hcand'
        have hfS : ∀ z, z ≠ x → Function.update f x v z = f z := fun z hz =>
          Function.update_of_ne hz _ _
        refine mem_filter.2 ⟨Fintype.mem_piFinset.2 (fun y => ?_), hinj', hadj', hcandFinal⟩
        · by_cases hyx : y = x
          · subst hyx; simpa using hvC'.1
          · rw [hfS y hyx]
            have := hpi y
            by_cases hyS : y ∈ S
            · simpa [hyS] using this
            · simpa [hyS, hyx] using this
      have hinj : #((Good S).sigma Ext) ≤ #(Good (insert x S)) := by
        refine card_le_card_of_injOn (fun p => Function.update p.1 x p.2) ?_ ?_
        · rintro ⟨f, v⟩ hp
          simp only [coe_sigma, Set.mem_sigma_iff, mem_coe] at hp
          exact hmem f hp.1 v hp.2
        · rintro ⟨f, v⟩ hp ⟨f', v'⟩ hp' h
          simp only [coe_sigma, Set.mem_sigma_iff, mem_coe] at hp hp'
          have hv : v = v' := by simpa using congrFun h x
          subst hv
          have hfx : ∀ g ∈ Good S, g x = a₀ := by
            intro g hg
            have := Fintype.mem_piFinset.1 (mem_filter.1 hg).1 x
            simpa [hxS] using this
          have : f = f' := by
            funext z
            by_cases hzx : z = x
            · subst hzx; rw [hfx f hp.1, hfx f' hp'.1]
            · have := congrFun h z
              simpa [Function.update_of_ne hzx] using this
          subst this; rfl
      rw [Finset.card_sigma] at hinj
      have hsum : ∑ f ∈ Good S, D / 4 * (#(s x) : ℝ) ≤ ∑ f ∈ Good S, (#(Ext f) : ℝ) :=
        sum_le_sum hExt
      rw [sum_const, nsmul_eq_mul] at hsum
      have hfin := (Nat.cast_le (α := ℝ)).2 hinj
      rw [Nat.cast_sum] at hfin
      have hc : (0 : ℝ) ≤ D / 4 * #(s x) := by positivity
      calc D / 4 * #(s x) * ∏ x ∈ S, (D / 4 * #(s x))
          ≤ D / 4 * #(s x) * #(Good S) := mul_le_mul_of_nonneg_left ih hc
        _ = #(Good S) * (D / 4 * #(s x)) := by ring
        _ ≤ _ := hsum.trans hfin
  have hfinal := key univ
  rw [prod_mul_distrib, prod_const, card_univ] at hfinal
  refine hfinal.trans ?_
  have hgood : ∀ f ∈ Good univ, Function.Injective f ∧ (∀ x, f x ∈ s x) ∧
      ∀ x y, L.Adj x y → G.Adj (f x) (f y) := by
    intro f hf
    obtain ⟨hpi, hinj, hadj, -⟩ := mem_filter.1 hf
    refine ⟨fun a b h => hinj (mem_coe.2 (mem_univ a)) (mem_coe.2 (mem_univ b)) h,
      fun x => by simpa using Fintype.mem_piFinset.1 hpi x,
      fun x y h => hadj x (mem_univ x) y (mem_univ y) h⟩
  have hle : Nat.card ↥(Good univ) ≤
      Nat.card {f : β ↪ α // (∀ x, f x ∈ s x) ∧ ∀ x y, L.Adj x y → G.Adj (f x) (f y)} := by
    refine Nat.card_le_card_of_injective
      (fun p => ⟨⟨p.1, (hgood p.1 p.2).1⟩, (hgood p.1 p.2).2⟩) ?_
    intro p q h
    have := congrArg (fun r => (r.1 : β → α)) h
    exact Subtype.ext this
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hle
  exact_mod_cast hle

/-- **Graph removal lemma, far form.** The contrapositive of Conlon–Fox,
*Graph removal lemmas*, [Theorem 1.1](https://arxiv.org/pdf/1211.3487v1).
For every finite graph `H` and every `ε > 0` there is `δ > 0` such that every finite graph on `n`
vertices that is `ε n²`-far from being `H`-free has at least `δ n ^ (card β)` labelled copies of
`H`. -/
theorem le_labelledCopyCount_of_deleteFar {β : Type} [Fintype β] (H : SimpleGraph β) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj], G.DeleteFar (fun G' ↦ H.Free G') (ε * (card α ^ 2 : ℕ)) →
        δ * card α ^ card β ≤ G.labelledCopyCount H := by
  classical
  set k := card β with hk
  rcases isEmpty_or_nonempty β with hβ | hβ
  · refine ⟨1, one_pos, fun α _ _ G _ _ => ?_⟩
    have hk0 : k = 0 := Fintype.card_eq_zero
    rw [hk0, pow_zero, mul_one, Nat.one_le_cast, Nat.one_le_iff_ne_zero, Ne,
      labelledCopyCount_eq_zero]
    exact fun h => h ⟨Hom.toCopy ⟨isEmptyElim, fun {a} => isEmptyElim a⟩ (fun a => isEmptyElim a)⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Fintype.card_pos
  set ε₁ : ℝ := min ε 1 with hε₁_def
  have hε₁ : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  set d : ℝ := ε₁ / 8 with hd_def
  have hd : 0 < d := by positivity
  have hd₁ : d ≤ 1 := by linarith
  set D : ℝ := d ^ k with hD_def
  have hD : 0 < D := by positivity
  set η : ℝ := min (ε₁ / 8) (D / (2 * k + 1)) with hη_def
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηε : η ≤ ε₁ / 8 := min_le_left _ _
  have hη₁ : η ≤ 1 := by linarith
  have hηd : 2 * k * η ≤ D := by
    have h1 : η ≤ D / (2 * k + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set l : ℕ := ⌈4 / ε₁⌉₊ with hl_def
  have hl : 4 / ε₁ ≤ l := Nat.le_ceil _
  set B : ℕ := SzemerediRegularity.bound η l with hB_def
  have hB : (0 : ℝ) < B := by positivity
  set T : ℕ := l + ⌈8 * k * B / D⌉₊ with hT_def
  set δ : ℝ := min (1 / ((T : ℝ) + 1) ^ k) ((D / 4) ^ k * (1 / (2 * B)) ^ k) with hδ_def
  have hδ1 : δ ≤ 1 / ((T : ℝ) + 1) ^ k := min_le_left _ _
  have hδ2 : δ ≤ (D / 4) ^ k * (1 / (2 * B)) ^ k := min_le_right _ _
  refine ⟨δ, by positivity, fun α _ _ G _ hG => ?_⟩
  have hδ0 : 0 ≤ δ := by positivity
  obtain hn | hn := Nat.eq_zero_or_pos (card α)
  · rw [hn, Nat.cast_zero, zero_pow (Fintype.card_ne_zero), mul_zero]
    positivity
  have hG₁ : G.DeleteFar (fun G' ↦ H.Free G') (ε₁ * (card α ^ 2 : ℕ)) :=
    hG.mono (by gcongr)
  have hnc : ¬ H.Free G := by
    intro h
    have := hG (s := ∅) (empty_subset _) (by simpa only [coe_empty, deleteEdges_empty] using h)
    rw [Finset.card_empty, Nat.cast_zero] at this
    have : (0 : ℝ) < ε * (card α ^ 2 : ℕ) := by positivity
    linarith
  rcases le_total (card α) T with hT' | hT'
  · have h1 : (1 : ℝ) ≤ G.labelledCopyCount H := by
      rw [Nat.one_le_cast, Nat.one_le_iff_ne_zero, Ne, labelledCopyCount_eq_zero]
      exact hnc
    calc δ * card α ^ k ≤ 1 / ((T : ℝ) + 1) ^ k * ((T : ℝ) + 1) ^ k := by
          gcongr
          exact_mod_cast hT'.trans (Nat.le_succ T)
      _ = 1 := by field_simp
      _ ≤ _ := h1
  · have : Nonempty α := Fintype.card_pos_iff.1 hn
    have hl' : l ≤ card α := le_trans (Nat.le_add_right _ _) hT'
    have hn8 : 8 * k * B / D ≤ card α := by
      refine (Nat.le_ceil _).trans ?_
      exact_mod_cast le_trans (Nat.le_add_left _ _) hT'
    obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G hη hl'
    have hP' : 4 / ε₁ ≤ #P.parts := hl.trans (Nat.cast_le.2 hP₂)
    have hedges := CliqueRemoval.regularityReduced_edges_card_aux' hε₁ hη hηε hP₁ hP₄ hP'
    have hnc' : ¬ H.Free (G.regularityReduced P η (ε₁ / 4)) := by
      intro h
      have := (deleteFar_iff.1 hG₁) regularityReduced_le h
      linarith
    obtain ⟨φ⟩ := not_not.1 hnc'
    let s : β → Finset α := fun x => P.part (φ x)
    have hs : ∀ x y, H.Adj x y → ∀ A ⊆ s x, ∀ B ⊆ s y, η * #(s x) ≤ #A → η * #(s y) ≤ #B →
        d ≤ G.edgeDensity A B := by
      intro x y hxy A hA B' hB' hA' hB''
      have hadj : (G.regularityReduced P η (ε₁ / 4)).Adj (φ x) (φ y) := by
        simpa using φ.toHom.map_adj hxy
      obtain ⟨-, X, hX, Y, hY, hxX, hyY, hXY, hu, hdens⟩ := hadj
      have h1 : s x = X := P.part_eq_of_mem hX hxX
      have h2 : s y = Y := P.part_eq_of_mem hY hyY
      rw [h1] at hA hA'
      rw [h2] at hB' hB''
      have := hu hA hB' (by rw [mul_comm]; exact hA') (by rw [mul_comm]; exact hB'')
      rw [abs_sub_lt_iff] at this
      linarith
    have hsize : ∀ x, 4 * k ≤ D * #(s x) := by
      intro x
      have hb := CliqueRemoval.card_bound hP₁ hP₃ (P.part_mem.2 (mem_univ (φ x)))
      rw [div_le_iff₀ (by positivity)] at hb hn8
      have : D * (card α) ≤ D * (#(s x) * (2 * B)) := by gcongr
      have h3 : 4 * k * (2 * B) ≤ D * #(s x) * (2 * B) := by nlinarith
      exact le_of_mul_le_mul_right h3 (by positivity)
    have hcount := card_copies_ge H G s hη hη₁ hd hd₁ hηd hsize hs
    have hinj : Nat.card {f : β ↪ α // (∀ x, f x ∈ s x) ∧ ∀ x y, H.Adj x y → G.Adj (f x) (f y)}
        ≤ G.labelledCopyCount H := by
      rw [labelledCopyCount, Fintype.card_eq_nat_card]
      refine Nat.card_le_card_of_injective
        (fun p => Hom.toCopy ⟨p.1, fun h => p.2.2 _ _ h⟩ p.1.injective) ?_
      intro p q h
      have := congrArg (fun c : H.Copy G => (c : β → α)) h
      exact Subtype.ext (DFunLike.coe_injective this)
    calc δ * card α ^ k ≤ (D / 4) ^ k * (1 / (2 * B)) ^ k * card α ^ k := by gcongr
      _ = (D / 4) ^ k * (card α / (2 * B : ℝ)) ^ k := by
          rw [mul_assoc, ← mul_pow, one_div_mul_eq_div]
      _ = (D / 4) ^ k * ∏ _x : β, (card α / (2 * B : ℝ)) := by
          rw [prod_const, card_univ, ← hk]
      _ ≤ (D / 4) ^ k * ∏ x, (#(s x) : ℝ) := by
          gcongr with x
          exact CliqueRemoval.card_bound hP₁ hP₃ (P.part_mem.2 (mem_univ _))
      _ ≤ _ := hcount
      _ ≤ _ := by exact_mod_cast hinj

/-- **Graph removal lemma.** See Conlon–Fox, *Graph removal lemmas*,
[Theorem 1.1](https://arxiv.org/pdf/1211.3487v1).
For every finite graph `H` and every `ε > 0` there is `δ > 0` such that every finite graph on `n`
vertices with fewer than `δ n ^ (card β)` labelled copies of `H` has an `H`-free subgraph obtained
by deleting fewer than `ε n²` edges. -/
theorem graph_removal {β : Type} [Fintype β] (H : SimpleGraph β) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj], (G.labelledCopyCount H : ℝ) < δ * card α ^ card β →
        ∃ G' ≤ G, ∃ _ : DecidableRel G'.Adj,
          (#G.edgeFinset - #G'.edgeFinset : ℝ) < ε * (card α ^ 2 : ℕ) ∧ H.Free G' := by
  obtain ⟨δ, hδ, h⟩ := le_labelledCopyCount_of_deleteFar H hε
  refine ⟨δ, hδ, fun α _ _ G _ hG => ?_⟩
  by_contra! h'
  refine hG.not_ge (h α G (deleteFar_iff.2 ?_))
  intro G' _ hG' hG''
  exact le_of_not_gt fun i ↦ hG'' (h' G' hG' _ i)

end GraphRemoval
