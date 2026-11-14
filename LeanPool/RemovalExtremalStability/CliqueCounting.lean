/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Triangle.Counting
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Tactic

/-!

Adapted from [jtraverso/turan-stability](https://github.com/jtraverso/turan-stability/blob/3eb99033cc931add291781f77b7446dcba8f5f9d/StabilityLib/CliqueCounting.lean) (Palomar-registered source).
# The clique counting lemma

This file generalises Mathlib's triangle counting lemma (`SimpleGraph.triangle_counting'`,
`SimpleGraph.triangle_counting`) from triangles to cliques of any size `r`.

The parts are given by a family `s : Fin r → Finset α`. A tuple `x` with `x i ∈ s i` for every
`i` is a *transversal clique* if `G.Adj (x i) (x j)` for all `i ≠ j`.

* `CliqueCounting.card_transversalCliques_ge`: **counting lemma, robust-density form.** If, for
  all `i ≠ j`, every pair of subsets `A ⊆ s i`, `B ⊆ s j` with `#A ≥ η #(s i)` and
  `#B ≥ η #(s j)` has edge density at least `d`, `η ≤ 1` and `2 r η ≤ d ^ (r - 1)`, then at least
  `d ^ (r choose 2) / 2 ^ r · ∏ i, #(s i)` tuples are transversal cliques.
* `CliqueCounting.card_transversalCliques_ge_of_isUniform`: **counting lemma, uniform form.** The
  same conclusion when every pair `(s i, s j)` is `ε`-uniform (`SimpleGraph.IsUniform`) with edge
  density at least `d + ε`, and `2 r ε ≤ d ^ (r - 1)`.
* `CliqueCounting.card_cliqueFinset_ge`: **clique counting lemma.** For pairwise disjoint parts
  the same lower bound holds for the number of `r`-cliques of `G`, `#(G.cliqueFinset r)`.
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace CliqueCounting

variable {α : Type*} (G : SimpleGraph α) [DecidableRel G.Adj]

/-- Vertices of `S` with fewer than `d · #T` neighbours in `T` form a set of size `< η · #S`,
provided all large subsets of `S` have density at least `d` to `T`. -/
theorem card_badVertices_lt {η d : ℝ} (hd : 0 < d) {S T : Finset α} (hT : η * #T ≤ #T)
    (h : ∀ A ⊆ S, η * #S ≤ #A → η * #T ≤ #T → d ≤ G.edgeDensity A T) :
    (#{x ∈ S | (#{y ∈ T | G.Adj x y} : ℝ) < d * #T} : ℝ) < η * #S := by
  classical
  by_contra! hle
  set B := {x ∈ S | (#{y ∈ T | G.Adj x y} : ℝ) < d * #T} with hB
  have h1 := h B (filter_subset _ _) hle hT
  rw [edgeDensity_def] at h1
  push_cast at h1
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · rw [hBe] at h1; simp at h1; linarith
  have hlt : (#(G.interedges B T) : ℝ) < #B * #T * d := by
    refine (Nat.cast_le.2 <| (card_le_card <| subset_of_eq (Rel.interedges_eq_biUnion _)).trans
      card_biUnion_le).trans_lt ?_
    simp_rw [Nat.cast_sum, card_map]
    calc ∑ x ∈ B, (#{y ∈ T | G.Adj x y} : ℝ) < ∑ x ∈ B, d * #T :=
          sum_lt_sum_of_nonempty hBne fun x hx => (mem_filter.1 hx).2
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  have hTpos : (0 : ℝ) < #T := by
    rcases Nat.eq_zero_or_pos #T with h0 | h0
    · rw [h0, Nat.cast_zero, mul_zero, zero_mul] at hlt
      exact absurd hlt (not_lt.2 (Nat.cast_nonneg _))
    · exact_mod_cast h0
  have hBpos : (0 : ℝ) < #B := by exact_mod_cast hBne.card_pos
  rw [le_div_iff₀ (by positivity)] at h1
  linarith

/-- The statement of the counting lemma for `r` parts, with the extra hypothesis `η ≤ 1`. -/
def CountingStatement (r : ℕ) : Prop :=
  ∀ (s : Fin r → Finset α) (η d : ℝ), 0 < η → η ≤ 1 → 0 < d → 2 * r * η ≤ d ^ (r - 1) →
    (∀ i j, i ≠ j → ∀ A ⊆ s i, ∀ B ⊆ s j, η * #(s i) ≤ #A → η * #(s j) ≤ #B →
      d ≤ G.edgeDensity A B) →
    d ^ r.choose 2 / 2 ^ r * ∏ i, (#(s i) : ℝ) ≤
      #{x ∈ Fintype.piFinset s | ∀ i j, i ≠ j → G.Adj (x i) (x j)}

theorem countingStatement_of_le_one {r : ℕ} (hr : r ≤ 1) : CountingStatement G r := by
  intro s η d _ _ _ _ _
  have hsub : ∀ i j : Fin r, i = j := fun i j => by ext; omega
  rw [filter_true_of_mem fun x _ i j hij => absurd (hsub i j) hij, card_piFinset,
    Nat.choose_eq_zero_of_lt (by omega)]
  push_cast
  have hP : (0 : ℝ) ≤ ∏ i, (#(s i) : ℝ) := by positivity
  have : (1 : ℝ) / 2 ^ r ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  rw [pow_zero]
  nlinarith

theorem countingStatement_succ {r : ℕ} (hr : 1 ≤ r) (ih : CountingStatement G r) :
    CountingStatement G (r + 1) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  intro s η d hη hη1 hd hηd hs
  simp only [Nat.add_sub_cancel] at hηd ih ⊢
  push_cast at hηd
  set j1 : Fin (k + 1 + 1) := ⟨1, by omega⟩
  have hd1 : d ≤ 1 :=
    (hs 0 j1 (by simp [j1]) _ subset_rfl _ subset_rfl
      (mul_le_of_le_one_left (Nat.cast_nonneg _) hη1)
      (mul_le_of_le_one_left (Nat.cast_nonneg _) hη1)).trans
      (by exact_mod_cast edgeDensity_le_one _ _ _)
  have hdk : d ^ k ≤ 1 := pow_le_one₀ hd.le hd1
  have hdk1 : d ^ (k + 1) = d * d ^ k := by ring
  have hrη : ((k : ℝ) + 1) * η ≤ 1 / 2 := by nlinarith
  -- bad vertices
  let Bad : Fin (k + 1) → Finset α := fun i =>
    {x ∈ s 0 | (#{y ∈ s i.succ | G.Adj x y} : ℝ) < d * #(s i.succ)}
  have hBad : ∀ i, (#(Bad i) : ℝ) < η * #(s 0) := fun i =>
    card_badVertices_lt G hd (mul_le_of_le_one_left (Nat.cast_nonneg _) hη1)
      fun A hA hA' hT => hs 0 i.succ (Fin.succ_ne_zero i).symm A hA _ subset_rfl hA' hT
  let X := (s 0).filter (fun x => ∀ i, x ∉ Bad i)
  have hX : (#(s 0) : ℝ) / 2 ≤ #X := by
    have hsub : s 0 ⊆ X ∪ univ.biUnion Bad := by
      intro x hx
      by_cases h : ∀ i, x ∉ Bad i
      · exact mem_union_left _ (mem_filter.2 ⟨hx, h⟩)
      · push Not at h
        obtain ⟨i, hi⟩ := h
        exact mem_union_right _ (mem_biUnion.2 ⟨i, mem_univ _, hi⟩)
    have h1 : (#(s 0) : ℝ) ≤ #X + ∑ i, (#(Bad i) : ℝ) := by
      have := (card_le_card hsub).trans ((card_union_le _ _).trans
        (Nat.add_le_add_left card_biUnion_le _))
      exact_mod_cast this
    have h2 : ∑ i, (#(Bad i) : ℝ) ≤ ∑ _i : Fin (k + 1), η * #(s 0) :=
      sum_le_sum fun i _ => (hBad i).le
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    push_cast at h2
    have : (0 : ℝ) ≤ #(s 0) := Nat.cast_nonneg _
    nlinarith
  -- neighbourhoods
  let s' : α → Fin (k + 1) → Finset α := fun x i => {y ∈ s i.succ | G.Adj x y}
  let C' : α → Finset (Fin (k + 1) → α) := fun x =>
    {t ∈ Fintype.piFinset (s' x) | ∀ i j, i ≠ j → G.Adj (t i) (t j)}
  have hC' : ∀ x ∈ X, d ^ (k + 1).choose 2 / 2 ^ (k + 1) *
      (d ^ (k + 1) * ∏ i : Fin (k + 1), (#(s i.succ) : ℝ)) ≤ #(C' x) := by
    intro x hx
    have hx' := (mem_filter.1 hx).2
    have hs'card : ∀ i, d * #(s i.succ) ≤ #(s' x i) := fun i => by
      have := hx' i
      simp only [Bad, mem_filter, not_and, not_lt] at this
      exact this (mem_filter.1 hx).1
    have hη' : 2 * ((k : ℝ) + 1) * (η / d) ≤ d ^ k := by
      rw [mul_div_assoc', div_le_iff₀ hd]; nlinarith
    have hη'1 : η / d ≤ 1 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      have : 0 < η / d := div_pos hη hd
      nlinarith
    have := ih (s' x) (η / d) d (div_pos hη hd) hη'1 hd (by push_cast; exact hη') (by
      intro i j hij A hA B hB hA' hB'
      refine hs i.succ j.succ ((Fin.succ_injective _).ne hij) A
        (hA.trans (filter_subset _ _)) B (hB.trans (filter_subset _ _)) ?_ ?_
      · calc η * (#(s i.succ) : ℝ) = η / d * (d * #(s i.succ)) := by field_simp
          _ ≤ η / d * #(s' x i) := by gcongr; exact hs'card i
          _ ≤ _ := hA'
      · calc η * (#(s j.succ) : ℝ) = η / d * (d * #(s j.succ)) := by field_simp
          _ ≤ η / d * #(s' x j) := by gcongr; exact hs'card j
          _ ≤ _ := hB')
    refine le_trans ?_ this
    gcongr
    calc d ^ (k + 1) * ∏ i : Fin (k + 1), (#(s i.succ) : ℝ)
        = ∏ i : Fin (k + 1), (d * #(s i.succ)) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
      _ ≤ _ := prod_le_prod₀ (fun i _ => mul_nonneg hd.le (Nat.cast_nonneg _)) fun i _ => hs'card i
  -- prepend
  have hinj : #(X.sigma C') ≤
      #{x ∈ Fintype.piFinset s | ∀ i j, i ≠ j → G.Adj (x i) (x j)} := by
    refine card_le_card_of_injOn (fun p => Fin.cons p.1 p.2) ?_ ?_
    · rintro ⟨x, t⟩ hp
      simp only [coe_sigma, Set.mem_sigma_iff, mem_coe] at hp
      obtain ⟨hx, ht⟩ := hp
      simp only [C', mem_filter, Fintype.mem_piFinset, s'] at ht
      obtain ⟨ht1, ht2⟩ := ht
      simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset]
      refine ⟨fun i => Fin.cases (mem_filter.1 hx).1 (fun i => (ht1 i).1) i, ?_⟩
      intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (ht1 j).2
      | succ i =>
        induction j using Fin.cases with
        | zero => simpa using ((ht1 i).2).symm
        | succ j => simpa using ht2 i j fun h => hij (by rw [h])
    · rintro ⟨x, t⟩ _ ⟨y, u⟩ _ h
      simp only [Fin.cons_inj] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  rw [Finset.card_sigma] at hinj
  have hsum : ∑ x ∈ X, d ^ (k + 1).choose 2 / 2 ^ (k + 1) *
      (d ^ (k + 1) * ∏ i : Fin (k + 1), (#(s i.succ) : ℝ)) ≤ ∑ x ∈ X, (#(C' x) : ℝ) :=
    sum_le_sum hC'
  rw [sum_const, nsmul_eq_mul] at hsum
  have hfin := (Nat.cast_le (α := ℝ)).2 hinj
  rw [Nat.cast_sum] at hfin
  refine le_trans ?_ (hsum.trans hfin)
  rw [Fin.prod_univ_succ, Nat.choose_succ_succ (k + 1) 1, Nat.choose_one_right]
  have hK : (0 : ℝ) ≤ d ^ (k + 1).choose 2 / 2 ^ (k + 1) *
      (d ^ (k + 1) * ∏ i : Fin (k + 1), (#(s i.succ) : ℝ)) :=
    mul_nonneg (div_nonneg (pow_nonneg hd.le _) (pow_nonneg zero_le_two _))
      (mul_nonneg (pow_nonneg hd.le _) (prod_nonneg fun i _ => Nat.cast_nonneg _))
  calc d ^ (k + 1 + (k + 1).choose 2) / 2 ^ (k + 1 + 1) *
        ((#(s 0) : ℝ) * ∏ i : Fin (k + 1), (#(s i.succ) : ℝ))
      = (#(s 0) : ℝ) / 2 * (d ^ (k + 1).choose 2 / 2 ^ (k + 1) *
      (d ^ (k + 1) * ∏ i : Fin (k + 1), (#(s i.succ) : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hX hK

theorem countingStatement (r : ℕ) : CountingStatement G r := by
  rcases Nat.lt_or_ge r 1 with hr | hr
  · exact countingStatement_of_le_one G (by omega)
  induction r, hr using Nat.le_induction with
  | base => exact countingStatement_of_le_one G le_rfl
  | succ r hr ih => exact countingStatement_succ G hr ih


/-- **Clique counting lemma, robust-density form.** If any two of the parts `s i`, `s j`
(`i ≠ j`) have edge density at least `d` between all subsets of relative size at least `η`,
`η ≤ 1` and `2 r η ≤ d ^ (r - 1)`, then at least `d ^ (r choose 2) / 2 ^ r` of the tuples in
`∏ i, s i` are cliques. (Without `η ≤ 1` the hypothesis on subsets would be vacuous.) -/
theorem card_transversalCliques_ge {r : ℕ} (s : Fin r → Finset α) {η d : ℝ} (hη : 0 < η)
    (hη₁ : η ≤ 1) (hd : 0 < d) (hηd : 2 * r * η ≤ d ^ (r - 1))
    (hs : ∀ i j, i ≠ j → ∀ A ⊆ s i, ∀ B ⊆ s j, η * #(s i) ≤ #A → η * #(s j) ≤ #B →
      d ≤ G.edgeDensity A B) :
    d ^ r.choose 2 / 2 ^ r * ∏ i, (#(s i) : ℝ) ≤
      #{x ∈ Fintype.piFinset s | ∀ i j, i ≠ j → G.Adj (x i) (x j)} :=
  countingStatement G r s η d hη hη₁ hd hηd hs

/-- **Clique counting lemma, uniform form.** If every pair of distinct parts is `ε`-uniform with
edge density at least `d + ε`, and `2 r ε ≤ d ^ (r - 1)`, then at least
`d ^ (r choose 2) / 2 ^ r` of the tuples in `∏ i, s i` are cliques. -/
theorem card_transversalCliques_ge_of_isUniform {r : ℕ} (s : Fin r → Finset α) {ε d : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (hεd : 2 * r * ε ≤ d ^ (r - 1))
    (hu : ∀ i j, i ≠ j → G.IsUniform ε (s i) (s j))
    (hdens : ∀ i j, i ≠ j → d + ε ≤ G.edgeDensity (s i) (s j)) :
    d ^ r.choose 2 / 2 ^ r * ∏ i, (#(s i) : ℝ) ≤
      #{x ∈ Fintype.piFinset s | ∀ i j, i ≠ j → G.Adj (x i) (x j)} := by
  refine card_transversalCliques_ge G s (η := min ε 1) (lt_min hε one_pos)
    (min_le_right _ _) hd
    ((mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans hεd)
    ?_
  intro i j hij A hA B hB hA' hB'
  have h1 := hdens i j hij
  have h2 : (G.edgeDensity (s i) (s j) : ℝ) ≤ 1 := by exact_mod_cast edgeDensity_le_one _ _ _
  rw [min_eq_left (by linarith)] at hA' hB'
  have := hu i j hij hA hB (by rw [mul_comm]; exact hA') (by rw [mul_comm]; exact hB')
  rw [abs_sub_lt_iff] at this
  linarith

/-- **Clique counting lemma.** If `s : Fin r → Finset α` are pairwise disjoint sets of vertices,
every two of them `ε`-uniform with edge density at least `d + ε`, and `2 r ε ≤ d ^ (r - 1)`,
then `G` has at least `d ^ (r choose 2) / 2 ^ r · ∏ i, #(s i)` cliques of size `r`. -/
theorem card_cliqueFinset_ge [Fintype α] [DecidableEq α] {r : ℕ} (s : Fin r → Finset α)
    {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (hεd : 2 * r * ε ≤ d ^ (r - 1))
    (hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j))
    (hu : ∀ i j, i ≠ j → G.IsUniform ε (s i) (s j))
    (hdens : ∀ i j, i ≠ j → d + ε ≤ G.edgeDensity (s i) (s j)) :
    d ^ r.choose 2 / 2 ^ r * ∏ i, (#(s i) : ℝ) ≤ #(G.cliqueFinset r) := by
  refine (card_transversalCliques_ge_of_isUniform G s hε hd hεd hu hdens).trans ?_
  have key : ∀ x ∈ Fintype.piFinset s, ∀ i j, x i = x j → i = j := by
    intro x hx i j hij
    by_contra h
    rw [Fintype.mem_piFinset] at hx
    exact disjoint_left.1 (hdisj i j h) (hx i) (hij ▸ hx j)
  exact_mod_cast card_le_card_of_injOn (fun x => univ.image x) (by
    intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq] at hx
    obtain ⟨hx, hadj⟩ := hx
    simp only [coe_cliqueFinset]
    refine (isNClique_iff G).2 ⟨?_, ?_⟩
    · rw [isClique_iff, coe_image]
      rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩ hne
      exact hadj i j fun h => hne (by rw [h])
    · rw [card_image_of_injective _ fun i j h => key x hx i j h, card_univ, Fintype.card_fin]) (by
    intro x hx y hy hxy
    simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset] at hx hy
    funext i
    have : x i ∈ univ.image y := by
      simp only at hxy; rw [← hxy]; exact mem_image_of_mem _ (mem_univ _)
    obtain ⟨j, -, hj⟩ := mem_image.1 this
    obtain rfl : j = i := by
      by_contra h
      exact disjoint_left.1 (hdisj j i h) (hy.1 j) (hj ▸ hx.1 i)
    exact hj.symm)

end CliqueCounting
