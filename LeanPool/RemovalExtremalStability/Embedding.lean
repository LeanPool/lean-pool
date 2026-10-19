/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Tactic
public import LeanPool.RemovalExtremalStability.CliqueCounting

/-!

Adapted from [jtraverso/turan-stability](https://github.com/jtraverso/turan-stability/blob/3eb99033cc931add291781f77b7446dcba8f5f9d/StabilityLib/Embedding.lean) (Palomar-registered source).
# The embedding lemma

Let `L` be a finite graph on `k` vertices with a proper colouring `c` by `r` colours, and let
`s : Fin r → Finset α` be parts of a graph `G` that are pairwise dense in a robust sense (or
pairwise `ε`-uniform and dense). Then `L` embeds into `G` with every vertex `x` of `L` mapped into
the part `s (c x)`. This is the "key lemma" of the regularity method, proved by greedy embedding.

* `Embedding.exists_embedding`: **embedding lemma, robust-density form.**
* `Embedding.exists_embedding_of_isUniform`: **embedding lemma, uniform form.**
* `Embedding.isContained_of_isUniform`: in the uniform setting, `L ⊑ G`.
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace Embedding

variable {α : Type*} (G : SimpleGraph α) [DecidableRel G.Adj]

/-- **Embedding lemma, robust-density form.** Let `L` be a graph on a finite type `β` with
`k = card β` vertices and a proper colouring `c : β → Fin r`. Suppose that for all colours
`i ≠ j`, all subsets `A ⊆ s i`, `B ⊆ s j` with `#A ≥ η #(s i)` and `#B ≥ η #(s j)` have edge
density at least `d`, where `0 < η ≤ 1`, `0 < d ≤ 1`, `2 k η ≤ d ^ k`, and every part has at least
`2 k / d ^ k` vertices. Then there is an injective map `f : β → α` sending each `x` into `s (c x)`
and edges of `L` to edges of `G`. -/
theorem exists_embedding {β : Type*} [Fintype β] (L : SimpleGraph β) {r : ℕ}
    (c : β → Fin r) (hc : ∀ x y, L.Adj x y → c x ≠ c y) (s : Fin r → Finset α) {η d : ℝ}
    (hη : 0 < η) (hη₁ : η ≤ 1) (hd : 0 < d) (hd₁ : d ≤ 1)
    (hηd : 2 * card β * η ≤ d ^ card β) (hsize : ∀ i, 2 * card β ≤ d ^ card β * #(s i))
    (hs : ∀ i j, i ≠ j → ∀ A ⊆ s i, ∀ B ⊆ s j, η * #(s i) ≤ #A → η * #(s j) ≤ #B →
      d ≤ G.edgeDensity A B) :
    ∃ f : β → α, Function.Injective f ∧ (∀ x, f x ∈ s (c x)) ∧
      ∀ x y, L.Adj x y → G.Adj (f x) (f y) := by
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · exact ⟨isEmptyElim, fun a => isEmptyElim a, fun a => isEmptyElim a, fun a => isEmptyElim a⟩
  have hk1 : (1 : ℝ) ≤ card β := by exact_mod_cast Fintype.card_pos
  have hD : 0 < d ^ card β := pow_pos hd _
  have hηD : η ≤ d ^ card β := by nlinarith
  let Cand : (β → α) → Finset β → β → Finset α := fun f S y =>
    {w ∈ s (c y) | ∀ z ∈ S, L.Adj z y → G.Adj (f z) w}
  let P : Finset β → Prop := fun S => ∃ f : β → α, Set.InjOn f S ∧ (∀ x ∈ S, f x ∈ s (c x)) ∧
    (∀ x ∈ S, ∀ y ∈ S, L.Adj x y → G.Adj (f x) (f y)) ∧
    ∀ y ∉ S, d ^ #S * #(s (c y)) ≤ #(Cand f S y)
  have hP : ∀ S, P S := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨b⟩ := hβ
      have hne : (s (c b)).Nonempty := by
        rw [← Finset.card_pos]
        by_contra h
        have := hsize (c b)
        rw [Nat.eq_zero_of_not_pos h] at this
        simp at this
        linarith
      obtain ⟨a, -⟩ := hne
      refine ⟨fun _ => a, by simp, by simp, by simp, fun y _ => ?_⟩
      simp [Cand]
    | insert x S hxS ih =>
      obtain ⟨f, hinj, hmem, hadj, hcand⟩ := ih
      have hSk : #S + 1 ≤ card β := by
        have := card_le_univ (insert x S); rwa [card_insert_of_notMem hxS] at this
      have hpowS : d ^ card β ≤ d ^ #S := pow_le_pow_of_le_one hd.le hd₁ (by omega)
      have hCand_big : ∀ y ∉ S, d ^ card β * #(s (c y)) ≤ #(Cand f S y) := fun y hy =>
        (mul_le_mul_of_nonneg_right hpowS (Nat.cast_nonneg _)).trans (hcand y hy)
      let Y := (univ \ insert x S).filter (L.Adj x)
      let Bad : β → Finset α := fun y =>
        {v ∈ s (c x) | (#{w ∈ Cand f S y | G.Adj v w} : ℝ) < d * #(Cand f S y)}
      have hBad : ∀ y ∈ Y, (#(Bad y) : ℝ) < η * #(s (c x)) := by
        intro y hy
        simp only [Y, mem_filter, mem_sdiff, mem_univ, true_and, mem_insert, not_or] at hy
        refine CliqueCounting.card_badVertices_lt G hd
          (mul_le_of_le_one_left (Nat.cast_nonneg _) hη₁) fun A hA hA' _ =>
          hs (c x) (c y) (hc x y hy.2) A hA _ (filter_subset _ _) hA' ?_
        refine le_trans ?_ (hCand_big y hy.1.2)
        gcongr
      have hYcard : #Y + #S + 1 ≤ card β := by
        have h1 : #Y ≤ #(univ \ insert x S) := card_filter_le _ _
        rw [card_sdiff_of_subset (subset_univ _), card_insert_of_notMem hxS, card_univ] at h1
        omega
      let Good := (Cand f S x).filter (fun v => v ∉ S.image f ∧ ∀ y ∈ Y, v ∉ Bad y)
      have hGood : Good.Nonempty := by
        by_contra hne
        rw [not_nonempty_iff_eq_empty] at hne
        have hsub : Cand f S x ⊆ S.image f ∪ Y.biUnion Bad := by
          intro v hv
          by_contra hv'
          simp only [mem_union, not_or, mem_biUnion, not_exists, not_and] at hv'
          have : v ∈ Good := mem_filter.2 ⟨hv, hv'.1, fun y hy => hv'.2 y hy⟩
          rw [hne] at this; simp at this
        have h1 : (#(Cand f S x) : ℝ) ≤ #S + ∑ y ∈ Y, (#(Bad y) : ℝ) := by
          have := (card_le_card hsub).trans ((card_union_le _ _).trans
            (Nat.add_le_add card_image_le card_biUnion_le))
          exact_mod_cast this
        have h2 : ∑ y ∈ Y, (#(Bad y) : ℝ) ≤ #Y * (η * #(s (c x))) := by
          rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum fun y hy => (hBad y hy).le
        have h3 := hCand_big x hxS
        have h4 := hsize (c x)
        have h5 : ((#Y : ℕ) : ℝ) + #S + 1 ≤ card β := by exact_mod_cast hYcard
        set N : ℝ := (#(s (c x)) : ℝ)
        set D := d ^ card β
        have hN : 0 ≤ N := Nat.cast_nonneg _
        have hY0 : (0 : ℝ) ≤ #Y := Nat.cast_nonneg _
        have hS0 : (0 : ℝ) ≤ #S := Nat.cast_nonneg _
        have e1 : 2 * card β * (#Y * (η * N)) ≤ #Y * (D * N) := by
          have := mul_le_mul_of_nonneg_right hηd hN
          nlinarith
        have e2 : 2 * card β * (#S : ℝ) ≤ #S * (D * N) := by nlinarith
        have e3 : (#Y + #S : ℝ) * (D * N) < 2 * card β * (D * N) := by
          have : 0 < D * N := by nlinarith
          nlinarith
        nlinarith
      obtain ⟨v, hv⟩ := hGood
      obtain ⟨hvC, hvS, hvB⟩ := mem_filter.1 hv
      have hvC' := mem_filter.1 hvC
      have hfS : ∀ z ∈ S, Function.update f x v z = f z := fun z hz =>
        Function.update_of_ne (by rintro rfl; exact hxS hz) _ _
      refine ⟨Function.update f x v, ?_, ?_, ?_, ?_⟩
      · rw [coe_insert, Set.injOn_insert (by simpa using hxS)]
        refine ⟨fun a ha b hb h => hinj ha hb ?_, ?_⟩
        · rwa [hfS a ha, hfS b hb] at h
        · rintro ⟨z, hz, hzv⟩
          rw [Function.update_self, hfS z hz] at hzv
          exact hvS (mem_image.2 ⟨z, hz, hzv⟩)
      · intro z hz
        rcases mem_insert.1 hz with rfl | hz
        · simpa using hvC'.1
        · rw [hfS z hz]; exact hmem z hz
      · have key : ∀ z ∈ S, L.Adj z x → G.Adj (f z) v := fun z hz h => hvC'.2 z hz h
        intro a ha b hb hab
        rcases mem_insert.1 ha with hax | ha' <;> rcases mem_insert.1 hb with hbx | hb'
        · subst hax; subst hbx; exact absurd hab (SimpleGraph.irrefl _)
        · subst hax; rw [Function.update_self, hfS b hb']; exact (key b hb' hab.symm).symm
        · subst hbx; rw [Function.update_self, hfS a ha']; exact key a ha' hab
        · rw [hfS a ha', hfS b hb']; exact hadj a ha' b hb' hab
      · intro y hy
        rw [mem_insert, not_or] at hy
        rw [card_insert_of_notMem hxS, pow_succ]
        by_cases hxy : L.Adj x y
        · have hyY : y ∈ Y := by simp [Y, hy.1, hy.2, hxy]
          have h1 : ¬ ((#{w ∈ Cand f S y | G.Adj v w} : ℝ) < d * #(Cand f S y)) := fun h =>
            hvB y hyY (mem_filter.2 ⟨hvC'.1, h⟩)
          push Not at h1
          have hsub : {w ∈ Cand f S y | G.Adj v w} ⊆
              Cand (Function.update f x v) (insert x S) y := by
            intro w hw
            simp only [Cand, mem_filter, mem_insert] at hw ⊢
            refine ⟨hw.1.1, ?_⟩
            rintro z (rfl | hz) hzy
            · simpa using hw.2
            · rw [hfS z hz]; exact hw.1.2 z hz hzy
          calc d ^ #S * d * (#(s (c y)) : ℝ) = d * (d ^ #S * #(s (c y))) := by ring
            _ ≤ d * #(Cand f S y) := by gcongr; exact hcand y hy.2
            _ ≤ _ := h1
            _ ≤ _ := by exact_mod_cast card_le_card hsub
        · have hsub : Cand f S y ⊆ Cand (Function.update f x v) (insert x S) y := by
            intro w hw
            simp only [Cand, mem_filter, mem_insert] at hw ⊢
            refine ⟨hw.1, ?_⟩
            rintro z (rfl | hz) hzy
            · exact absurd hzy hxy
            · rw [hfS z hz]; exact hw.2 z hz hzy
          calc d ^ #S * d * (#(s (c y)) : ℝ) ≤ d ^ #S * 1 * #(s (c y)) := by gcongr
            _ = d ^ #S * #(s (c y)) := by ring
            _ ≤ _ := hcand y hy.2
            _ ≤ _ := by exact_mod_cast card_le_card hsub
  obtain ⟨f, hinj, hmem, hadj, -⟩ := hP univ
  exact ⟨f, fun a b h => hinj (mem_coe.2 (mem_univ a)) (mem_univ b) h,
    fun x => hmem x (mem_univ x), fun x y h => hadj x (mem_univ x) y (mem_univ y) h⟩

/-- **Embedding lemma, uniform form.** Under the hypotheses of `exists_embedding`, with the
robust density condition replaced by: every pair of distinct parts is `ε`-uniform with edge
density at least `d + ε`, and `2 k ε ≤ d ^ k`. -/
theorem exists_embedding_of_isUniform {β : Type*} [Fintype β]
    (L : SimpleGraph β) {r : ℕ} (c : β → Fin r) (hc : ∀ x y, L.Adj x y → c x ≠ c y)
    (s : Fin r → Finset α) {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (hd₁ : d ≤ 1)
    (hεd : 2 * card β * ε ≤ d ^ card β) (hsize : ∀ i, 2 * card β ≤ d ^ card β * #(s i))
    (hu : ∀ i j, i ≠ j → G.IsUniform ε (s i) (s j))
    (hdens : ∀ i j, i ≠ j → d + ε ≤ G.edgeDensity (s i) (s j)) :
    ∃ f : β → α, Function.Injective f ∧ (∀ x, f x ∈ s (c x)) ∧
      ∀ x y, L.Adj x y → G.Adj (f x) (f y) := by
  refine exists_embedding G L c hc s (η := min ε 1) (lt_min hε one_pos) (min_le_right _ _) hd hd₁
    ((mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans hεd) hsize ?_
  intro i j hij A hA B hB hA' hB'
  have h1 := hdens i j hij
  have h2 : (G.edgeDensity (s i) (s j) : ℝ) ≤ 1 := by exact_mod_cast edgeDensity_le_one _ _ _
  rw [min_eq_left (by linarith)] at hA' hB'
  have := hu i j hij hA hB (by rw [mul_comm]; exact hA') (by rw [mul_comm]; exact hB')
  rw [abs_sub_lt_iff] at this
  linarith

/-- **Embedding lemma, containment form.** Under the hypotheses of
`exists_embedding_of_isUniform`, `L` is contained in `G` (`L ⊑ G`, Mathlib's
`SimpleGraph.IsContained`). -/
theorem isContained_of_isUniform {β : Type*} [Fintype β]
    (L : SimpleGraph β) {r : ℕ} (c : β → Fin r) (hc : ∀ x y, L.Adj x y → c x ≠ c y)
    (s : Fin r → Finset α) {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (hd₁ : d ≤ 1)
    (hεd : 2 * card β * ε ≤ d ^ card β) (hsize : ∀ i, 2 * card β ≤ d ^ card β * #(s i))
    (hu : ∀ i j, i ≠ j → G.IsUniform ε (s i) (s j))
    (hdens : ∀ i j, i ≠ j → d + ε ≤ G.edgeDensity (s i) (s j)) :
    L.IsContained G := by
  obtain ⟨f, hinj, -, hadj⟩ :=
    exists_embedding_of_isUniform G L c hc s hε hd hd₁ hεd hsize hu hdens
  exact ⟨Hom.toCopy (⟨f, fun h => hadj _ _ h⟩ : L →g G) hinj⟩

end Embedding
