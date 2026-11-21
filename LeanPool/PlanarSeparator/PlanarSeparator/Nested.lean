/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Division
public import LeanPool.PlanarSeparator.PlanarSeparator.Balance
public import LeanPool.PlanarSeparator.NestedDissection.Main

/-!
# Separator trees with boundary bounds

Generalized nested dissection (Lipton, Rose and Tarjan) needs a separator tree in which every
subtree with `m` vertices has a separator of `O(√m)` vertices and a *boundary* (the vertices
outside the subtree adjacent to it) of `O(√m)` vertices, and whose parts have at most `2m/3`
vertices. We construct such a tree for every graph with `c √m`-separators
(`PlanarSeparator.HasSqrtSeparators`), with the constants `α = β = T` for any
`T ≥ 40 (177 c + 1)` (`PlanarSeparator.exists_sepTree_of_separators`). For plane graphs
(`c = 6`) we take `T = 50000` (`PlanarSeparator.exists_sepTree`), so that the nested dissection
theorems apply to plane graphs (`PlanarSeparator.planar_nestedDissection_elimination`: Gaussian
elimination of a matrix whose nonzero pattern is a plane graph on `n` vertices, in the nested
dissection order and restricted to the filled pattern, costs `O(n ^ (3/2))` arithmetic
operations).

## The construction

The tree is built top-down. A vertex set `W` with `m ≤ T²` vertices is a leaf. Otherwise let `B`
be the boundary of `W`, with `#B ≤ T √m` by induction. We give each vertex of `W` the
weight `20/m` and each vertex of `B` the weight `20/#B`, and divide `W ∪ B` into pieces of weight
at most `1` by a set `S` of at most `177 c √m` vertices
(`PlanarSeparator.exists_division_of_separators`). Each piece has
at most `m/20` vertices of `W` and at most `#B/20` vertices of `B`. Grouping the pieces evenly for
both measures (`PlanarSeparator.exists_balanced_split`) gives the two parts: each has between
`0.4 m` and `0.55 m` vertices, and its boundary consists of vertices of `S` and at most `0.6 #B`
vertices of `B`. Since `0.6 < √0.4`, the boundary bound is inherited by the parts once
`177 c ≤ 0.03 T`. The separator of the node is `S ∩ W`.

## References

* R. J. Lipton, D. J. Rose, R. E. Tarjan, *Generalized nested dissection*, SIAM J. Numer. Anal.
  16 (1979), 346–358.
* R. J. Lipton, R. E. Tarjan, *A separator theorem for planar graphs*, SIAM J. Appl. Math. 36
  (1979), 177–189.
-/

@[expose] public section

namespace PlanarSeparator

open Finset NestedDissection NestedDissection.SepTree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {R : Kasteleyn.RotationSystem G}

/-- The constant `α = β` of the separator trees of plane graphs. -/
def treeConst : ℝ := 50000

omit [Fintype V] [DecidableEq V] in
/-- The number of elements of `T` with label in `J` is the sum over `J` of the sizes of the label
classes. -/
lemma card_filter_mem_eq_sum {ι : Type*} [DecidableEq ι] (T : Finset V) (κ : V → ι)
    (J : Finset ι) :
    #(T.filter fun v => κ v ∈ J) = ∑ i ∈ J, #(T.filter fun v => κ v = i) := by
  rw [card_eq_sum_card_fiberwise (f := κ) (s := T.filter fun v => κ v ∈ J) (t := J)
    fun v hv => by simpa using (mem_filter.1 hv).2]
  refine sum_congr rfl fun i hi => ?_
  congr 1
  ext v
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨⟨h1, hi⟩, rfl⟩

/-- The constant of the separator trees of a graph with `c √m`-separators. -/
def sepTreeConst (c : ℝ) : ℝ := 40 * (177 * c + 1)

/-- **Splitting a node.** Let `G` have `c √m`-separators and let `T ≥ 40 (177 c + 1)`. A vertex
set `W` with more than `T²` vertices and with a boundary of at most `T √(#W)` vertices is split by
at most `T √(#W)` of its vertices into two parts of at most `2/3` of its vertices, each with a
boundary of at most `T √m` vertices, `m` being the size of the part. -/
theorem exists_split_of_separators {c T : ℝ} (hG : HasSqrtSeparators G c) (hc : 0 ≤ c)
    (hT : sepTreeConst c ≤ T) {W : Finset V} (hm : T ^ 2 < (#W : ℝ))
    (hb : (#(bdry G W) : ℝ) ≤ T * √(#W : ℝ)) :
    ∃ s A A' : Finset V, s ∪ A ∪ A' = W ∧ Disjoint s A ∧ Disjoint s A' ∧ Disjoint A A' ∧
      (∀ x ∈ A, ∀ y ∈ A', ¬ G.Adj x y) ∧ (#s : ℝ) ≤ T * √(#W : ℝ) ∧
      3 * #A ≤ 2 * #W ∧ 3 * #A' ≤ 2 * #W ∧
      (#(bdry G A) : ℝ) ≤ T * √(#A : ℝ) ∧ (#(bdry G A') : ℝ) ≤ T * √(#A' : ℝ) := by
  classical
  have hT' : 7080 * c + 40 ≤ T := by simp only [sepTreeConst] at hT; linarith only [hT]
  have hTpos : 0 < T := by linarith only [hT', hc]
  set B := bdry G W
  set m : ℝ := (#W : ℝ) with hmdef
  set b : ℝ := (#B : ℝ) with hbdef
  set s := √m with hsdef
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hb0 : 0 ≤ b := Nat.cast_nonneg _
  have hss : s * s = m := Real.mul_self_sqrt hm0
  have hs : T ≤ s := by
    rw [hsdef, Real.le_sqrt hTpos.le hm0]
    exact hm.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hmpos : 0 < m := by rw [← hss]; exact mul_pos (hTpos.trans_le hs) (hTpos.trans_le hs)
  have hss' : T * s ≤ s * s := mul_le_mul_of_nonneg_right hs hs0
  have hbs : b ≤ T * s := hb
  set K : ℝ := 177 * c * s with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK1 : 10 * K ≤ s * s := by
    have : 1770 * c * s ≤ s * s :=
      mul_le_mul_of_nonneg_right (by linarith only [hT', hc, hs]) hs0
    linarith only [this, hKdef]
  have hK2 : K ≤ 3 / 100 * (T * s) := by
    have : 177 * c * s ≤ (3 / 100 * T) * s :=
      mul_le_mul_of_nonneg_right (by linarith only [hT', hc]) hs0
    linarith only [this, hKdef]
  have hWB : Disjoint W B := disjoint_right.2 fun y hy => (mem_bdry.1 hy).1
  -- the weights
  set μ : V → ℝ := fun v => if v ∈ W then 20 / m else if v ∈ B then 20 / b else 0
  have hμ : ∀ v, 0 ≤ μ v := fun v => by
    simp only [μ]
    split_ifs <;> positivity
  have hμW : ∀ v ∈ W, μ v = 20 / m := fun v hv => by simp [μ, hv]
  have hμB : ∀ v ∈ B, μ v = 20 / b := fun v hv => by
    simp [μ, hv, disjoint_right.1 hWB hv]
  have hsumμ : ∑ v ∈ W ∪ B, μ v ≤ 40 := by
    rw [sum_union hWB, sum_congr rfl hμW, sum_congr rfl hμB, sum_const, sum_const,
      nsmul_eq_mul, nsmul_eq_mul, ← hmdef, ← hbdef, mul_div_cancel₀ _ hmpos.ne']
    rcases eq_or_lt_of_le hb0 with h | h
    · rw [← h]
      norm_num
    · rw [mul_div_cancel₀ _ h.ne']
      norm_num
  obtain ⟨S, hSU, κ, hκ, hadj, hpiece, hsize⟩ := exists_division_of_separators hG hc μ hμ (W ∪ B)
  -- the size of the separator
  have hcardU : (#(W ∪ B) : ℝ) = m + b := by
    rw [card_union_of_disjoint hWB]
    push_cast
    rfl
  have hsqrt : √(#(W ∪ B) : ℝ) ≤ 3 / 2 * s := by
    rw [hcardU]
    calc √(m + b) ≤ √((3 / 2 * s) ^ 2) := Real.sqrt_le_sqrt (by
          rw [show (3 / 2 * s) ^ 2 = 9 / 4 * (s * s) by ring]
          linarith only [hbs, hss', hss, hm0])
      _ = 3 / 2 * s := Real.sqrt_sq (by positivity)
  have hS : (#S : ℝ) ≤ K := by
    have h1 : max 0 (3 * ∑ v ∈ W ∪ B, μ v - 2) ≤ 118 :=
      max_le (by norm_num) (by linarith only [hsumμ])
    have h2 := Real.sqrt_nonneg (#(W ∪ B) : ℝ)
    calc (#S : ℝ) ≤ c * √(#(W ∪ B) : ℝ) * max 0 (3 * ∑ v ∈ W ∪ B, μ v - 2) := hsize
      _ ≤ c * (3 / 2 * s) * 118 := by gcongr
      _ = K := by rw [hKdef]; ring
  -- the pieces and their two measures
  set I := ((W ∪ B) \ S).image κ
  set x : Finset V → ℝ := fun i => #((W \ S).filter fun v => κ v = i)
  set y : Finset V → ℝ := fun i => #((B \ S).filter fun v => κ v = i)
  have hWS : W \ S ⊆ (W ∪ B) \ S := sdiff_subset_sdiff subset_union_left subset_rfl
  have hBS : B \ S ⊆ (W ∪ B) \ S := sdiff_subset_sdiff subset_union_right subset_rfl
  have hpw : ∀ i, x i * (20 / m) ≤ 1 := fun i => by
    refine le_trans ?_ (hpiece i)
    calc x i * (20 / m) = ∑ v ∈ (W \ S).filter fun v => κ v = i, μ v := by
          rw [sum_congr rfl fun v hv => hμW v (mem_sdiff.1 (mem_filter.1 hv).1).1, sum_const,
            nsmul_eq_mul]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun v hv => mem_filter.2
          ⟨hWS (mem_filter.1 hv).1, (mem_filter.1 hv).2⟩) fun v _ _ => hμ v
  have hpb : ∀ i, y i * (20 / b) ≤ 1 := fun i => by
    refine le_trans ?_ (hpiece i)
    calc y i * (20 / b) = ∑ v ∈ (B \ S).filter fun v => κ v = i, μ v := by
          rw [sum_congr rfl fun v hv => hμB v (mem_sdiff.1 (mem_filter.1 hv).1).1, sum_const,
            nsmul_eq_mul]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun v hv => mem_filter.2
          ⟨hBS (mem_filter.1 hv).1, (mem_filter.1 hv).2⟩) fun v _ _ => hμ v
  have hxε : ∀ i ∈ I, x i ≤ m / 20 := fun i _ => by
    have := hpw i
    rw [mul_div_assoc', div_le_one hmpos] at this
    linarith only [this]
  have hyη : ∀ i ∈ I, y i ≤ b / 20 := fun i _ => by
    rcases eq_or_lt_of_le hb0 with h | h
    · have h' : (#B : ℝ) = 0 := h.symm
      have hB : B = ∅ := card_eq_zero.1 (by exact_mod_cast h')
      simp [y, hB, ← h]
    · have := hpb i
      rw [mul_div_assoc', div_le_one h] at this
      linarith only [this]
  have hsumx : ∑ i ∈ I, x i = #(W \ S) := by
    simp only [x]
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise fun v hv => mem_image_of_mem κ (hWS hv)]
  have hsumy : ∑ i ∈ I, y i = #(B \ S) := by
    simp only [y]
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise fun v hv => mem_image_of_mem κ (hBS hv)]
  have hY : (#(B \ S) : ℝ) ≤ b := by
    rw [hbdef]
    exact_mod_cast card_le_card sdiff_subset
  obtain ⟨J, hJI, hJ1, hJ2, hJ3, hJ4⟩ := exists_balanced_split x y I
    (fun i => Nat.cast_nonneg _) (fun i => Nat.cast_nonneg _) (by positivity) hxε hyη
    (by positivity) (c := 3 / 5 * b) (by rw [hsumy]; linarith only [hY, hb0])
  rw [hsumx] at hJ1 hJ2
  have hJ4' : (#(B \ S) : ℝ) - ∑ i ∈ J, y i ≤ 3 / 5 * b := by
    have := sum_sdiff hJI (f := y)
    rw [hsumy] at this
    linarith only [this, hJ4]
  -- the two parts
  set A := (W \ S).filter fun v => κ v ∈ J
  set A' := (W \ S).filter fun v => κ v ∉ J
  have hA : (#A : ℝ) = ∑ i ∈ J, x i := by
    simp only [A, x]
    rw [card_filter_mem_eq_sum, Nat.cast_sum]
  have hAA' : (#A : ℝ) + #A' = #(W \ S) := by
    exact_mod_cast card_filter_add_card_filter_not (s := W \ S) (p := fun v => κ v ∈ J)
  have hX : m - K ≤ #(W \ S) := by
    have h1 : #(W \ S) + #(W ∩ S) = #W := card_sdiff_add_card_inter W S
    have h2 : #(W ∩ S) ≤ #S := card_le_card inter_subset_right
    have : (#W : ℝ) ≤ #(W \ S) + #S := by exact_mod_cast (by omega : #W ≤ #(W \ S) + #S)
    linarith only [this, hS, hmdef]
  have hXm : (#(W \ S) : ℝ) ≤ m := by
    rw [hmdef]
    exact_mod_cast card_le_card sdiff_subset
  have hs531 : K / 2 ≤ m / 20 := by linarith only [hK1, hss]
  have hAlow : 2 / 5 * m ≤ #A := by linarith only [hA, hJ1, hX, hs531]
  have hAhigh : (#A : ℝ) ≤ 11 / 20 * m := by linarith only [hA, hJ2, hXm]
  have hA'low : 2 / 5 * m ≤ #A' := by linarith only [hAA', hA, hJ2, hX, hs531]
  have hA'high : (#A' : ℝ) ≤ 11 / 20 * m := by linarith only [hAA', hA, hJ1, hXm]
  -- the boundaries of the parts
  have hbdry : ∀ (p : Finset V → Prop) [DecidablePred p],
      bdry G ((W \ S).filter fun v => p (κ v)) ⊆ S ∪ (B \ S).filter fun v => p (κ v) := by
    intro p _ z hz
    obtain ⟨hzA, a, ha, haz⟩ := mem_bdry.1 hz
    obtain ⟨haWS, hpa⟩ := mem_filter.1 ha
    by_cases hzS : z ∈ S
    · exact mem_union_left _ hzS
    have hzU : z ∈ W ∪ B := by
      by_cases hzW : z ∈ W
      · exact mem_union_left _ hzW
      · exact mem_union_right _ (mem_bdry.2 ⟨hzW, a, (mem_sdiff.1 haWS).1, haz⟩)
    have hκz : κ a = κ z := hadj a (hWS haWS) z (mem_sdiff.2 ⟨hzU, hzS⟩) haz
    rcases mem_union.1 hzU with hzW | hzB
    · exact absurd (mem_filter.2 ⟨mem_sdiff.2 ⟨hzW, hzS⟩, hκz ▸ hpa⟩) hzA
    · exact mem_union_right _ (mem_filter.2 ⟨mem_sdiff.2 ⟨hzB, hzS⟩, hκz ▸ hpa⟩)
  have hyJ : (#((B \ S).filter fun v => κ v ∈ J) : ℝ) = ∑ i ∈ J, y i := by
    simp only [y]
    rw [card_filter_mem_eq_sum, Nat.cast_sum]
  have hyJ' : (#((B \ S).filter fun v => κ v ∉ J) : ℝ) = #(B \ S) - ∑ i ∈ J, y i := by
    rw [← hyJ]
    have := card_filter_add_card_filter_not (s := B \ S) (p := fun v => κ v ∈ J)
    have : (#((B \ S).filter fun v => κ v ∈ J) : ℝ) + #((B \ S).filter fun v => κ v ∉ J) =
        #(B \ S) := by exact_mod_cast this
    linarith only [this]
  have hbA : (#(bdry G A) : ℝ) ≤ K + 3 / 5 * b := by
    have := (card_le_card (hbdry (fun i => i ∈ J))).trans (card_union_le _ _)
    have : (#(bdry G A) : ℝ) ≤ #S + #((B \ S).filter fun v => κ v ∈ J) := by
      exact_mod_cast this
    linarith only [this, hS, hyJ, hJ3]
  have hbA' : (#(bdry G A') : ℝ) ≤ K + 3 / 5 * b := by
    have := (card_le_card (hbdry (fun i => i ∉ J))).trans (card_union_le _ _)
    have : (#(bdry G A') : ℝ) ≤ #S + #((B \ S).filter fun v => κ v ∉ J) := by
      exact_mod_cast this
    linarith only [this, hS, hyJ', hJ4']
  have hroot : ∀ a : ℝ, 2 / 5 * m ≤ a → 63 / 100 * s ≤ √a := fun a ha => by
    rw [Real.le_sqrt (by positivity) (by linarith only [ha, hm0]),
      show (63 / 100 * s) ^ 2 = 3969 / 10000 * (s * s) by ring]
    linarith only [ha, hm0, hss]
  refine ⟨W ∩ S, A, A', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext v
    simp only [A, A', mem_union, mem_inter, mem_filter, mem_sdiff]
    tauto
  · exact disjoint_left.2 fun v hv hvA => (mem_sdiff.1 (mem_filter.1 hvA).1).2 (mem_inter.1 hv).2
  · exact disjoint_left.2 fun v hv hvA => (mem_sdiff.1 (mem_filter.1 hvA).1).2 (mem_inter.1 hv).2
  · exact disjoint_filter_filter_not _ _ _
  · intro u hu v hv huv
    exact (mem_filter.1 hv).2 (hadj u (hWS (mem_filter.1 hu).1) v (hWS (mem_filter.1 hv).1) huv ▸
      (mem_filter.1 hu).2)
  · have : (#(W ∩ S) : ℝ) ≤ #S := by exact_mod_cast card_le_card inter_subset_right
    have hTs : 0 ≤ T * s := mul_nonneg hTpos.le hs0
    linarith only [this, hS, hK2, hTs]
  · have : (3 * #A : ℝ) ≤ 2 * #W := by linarith only [hAhigh, hmdef, hm0]
    exact_mod_cast this
  · have : (3 * #A' : ℝ) ≤ 2 * #W := by linarith only [hA'high, hmdef, hm0]
    exact_mod_cast this
  · have := mul_le_mul_of_nonneg_left (hroot _ hAlow) hTpos.le
    linarith only [hbA, hK2, hbs, this]
  · have := mul_le_mul_of_nonneg_left (hroot _ hA'low) hTpos.le
    linarith only [hbA', hK2, hbs, this]

/-- **Separator trees from separators.** Let `G` have `c √m`-separators and let
`T ≥ 40 (177 c + 1)`. Every vertex set `W` with a boundary of at most `T √(#W)` vertices is the
vertex set of a separator tree in which every subtree with `m` vertices has a separator (or leaf
set) of at most `T √m` vertices and a boundary of at most `T √m` vertices, and whose parts have
at most `2m/3` vertices. -/
theorem exists_sepTree_of_bdry_of_separators {c T : ℝ} (hG : HasSqrtSeparators G c)
    (hc : 0 ≤ c) (hT : sepTreeConst c ≤ T) (W : Finset V)
    (hW : (#(bdry G W) : ℝ) ≤ T * √(#W : ℝ)) :
    ∃ t : SepTree V, t.verts = W ∧ IsDissection G t ∧
      AllNodes (SqrtBound G T T) t ∧ AllNodes Shrinks t := by
  have hT0 : 0 < T := lt_of_lt_of_le (by simp only [sepTreeConst]; positivity) hT
  induction hn : #W using Nat.strong_induction_on generalizing W with
  | _ n ih =>
  by_cases hsmall : (#W : ℝ) ≤ T ^ 2
  · refine ⟨leaf W, rfl, trivial, ⟨?_, hW⟩, trivial⟩
    change (#W : ℝ) ≤ T * √(#W : ℝ)
    have h0 : (0 : ℝ) ≤ #W := Nat.cast_nonneg _
    have h1 : √(#W : ℝ) ≤ T := by
      rw [Real.sqrt_le_left hT0.le]
      exact hsmall
    have h2 := Real.mul_self_sqrt h0
    have h3 := Real.sqrt_nonneg (#W : ℝ)
    nlinarith
  push Not at hsmall
  obtain ⟨s, A, A', hunion, hsA, hsA', hAA', hadj, hs, hA, hA', hbA, hbA'⟩ :=
    exists_split_of_separators hG hc hT hsmall hW
  have hW0 : 0 < #W := by
    have : (0 : ℝ) < #W := lt_of_le_of_lt (by positivity) hsmall
    exact_mod_cast this
  obtain ⟨ta, hta, hda, hsa, hsha⟩ := ih #A (by omega) A hbA rfl
  obtain ⟨tb, htb, hdb, hsb, hshb⟩ := ih #A' (by omega) A' hbA' rfl
  have hverts : (node s ta tb).verts = W := by
    simp only [verts, hta, htb]
    exact hunion
  refine ⟨node s ta tb, hverts, ?_, ⟨⟨?_, ?_⟩, hsa, hsb⟩, ⟨?_, hsha, hshb⟩⟩
  · exact ⟨hta ▸ hsA, htb ▸ hsA', hta ▸ htb ▸ hAA', hta ▸ htb ▸ hadj, hda, hdb⟩
  · rw [hverts]
    exact hs
  · rw [hverts]
    exact hW
  · change 3 * #ta.verts ≤ 2 * #(node s ta tb).verts ∧ 3 * #tb.verts ≤ 2 * #(node s ta tb).verts
    rw [hverts, hta, htb]
    exact ⟨hA, hA'⟩

/-- **Separator trees from separators**, covering all vertices: a graph with `c √m`-separators
has a separator tree with separator and boundary bounds `T √m` at every subtree with `m`
vertices, for every `T ≥ 40 (177 c + 1)`, and parts of at most `2m/3` vertices. -/
theorem exists_sepTree_of_separators {c T : ℝ} (hG : HasSqrtSeparators G c) (hc : 0 ≤ c)
    (hT : sepTreeConst c ≤ T) :
    ∃ t : SepTree V, t.verts = univ ∧ IsDissection G t ∧
      AllNodes (SqrtBound G T T) t ∧ AllNodes Shrinks t :=
  exists_sepTree_of_bdry_of_separators hG hc hT univ (by
    rw [bdry_univ, card_empty, Nat.cast_zero]
    exact mul_nonneg ((by simp only [sepTreeConst]; positivity : (0 : ℝ) ≤ sepTreeConst c).trans
      hT) (Real.sqrt_nonneg _))

lemma sepTreeConst_six_le : sepTreeConst 6 ≤ treeConst := by
  norm_num [sepTreeConst, treeConst]

/-- **Splitting a node of a plane graph.** A vertex set `W` with more than `50000²` vertices and
with a boundary of at most `50000 √(#W)` vertices is split by at most `50000 √(#W)` of its
vertices into two parts of at most `2/3` of its vertices, each with a boundary of at most
`50000 √m` vertices, `m` being the size of the part. -/
theorem exists_split (hR : R.IsPlane) {W : Finset V} (hm : treeConst ^ 2 < (#W : ℝ))
    (hb : (#(bdry G W) : ℝ) ≤ treeConst * √(#W : ℝ)) :
    ∃ s A A' : Finset V, s ∪ A ∪ A' = W ∧ Disjoint s A ∧ Disjoint s A' ∧ Disjoint A A' ∧
      (∀ x ∈ A, ∀ y ∈ A', ¬ G.Adj x y) ∧ (#s : ℝ) ≤ treeConst * √(#W : ℝ) ∧
      3 * #A ≤ 2 * #W ∧ 3 * #A' ≤ 2 * #W ∧
      (#(bdry G A) : ℝ) ≤ treeConst * √(#A : ℝ) ∧ (#(bdry G A') : ℝ) ≤ treeConst * √(#A' : ℝ) :=
  exists_split_of_separators (hasSqrtSeparators_of_isPlane hR) (by norm_num) sepTreeConst_six_le
    hm hb

/-- **Separator trees of plane graphs.** Every vertex set `W` of a plane graph with a boundary of
at most `50000 √(#W)` vertices is the vertex set of a separator tree in which every subtree with
`m` vertices has a separator (or leaf set) of at most `50000 √m` vertices and a boundary of at
most `50000 √m` vertices, and whose parts have at most `2m/3` vertices. -/
theorem exists_sepTree_of_bdry (hR : R.IsPlane) (W : Finset V)
    (hW : (#(bdry G W) : ℝ) ≤ treeConst * √(#W : ℝ)) :
    ∃ t : SepTree V, t.verts = W ∧ IsDissection G t ∧
      AllNodes (SqrtBound G treeConst treeConst) t ∧ AllNodes Shrinks t :=
  exists_sepTree_of_bdry_of_separators (hasSqrtSeparators_of_isPlane hR) (by norm_num)
    sepTreeConst_six_le W hW

/-- **Separator trees of plane graphs** with separator and boundary bounds `50000 √m` at every
subtree with `m` vertices, and parts of at most `2m/3` vertices. -/
theorem exists_sepTree (hR : R.IsPlane) :
    ∃ t : SepTree V, t.verts = univ ∧ IsDissection G t ∧
      AllNodes (SqrtBound G treeConst treeConst) t ∧ AllNodes Shrinks t :=
  exists_sepTree_of_bdry hR univ (by
    rw [bdry_univ, card_empty, Nat.cast_zero]
    exact mul_nonneg (by norm_num [treeConst]) (Real.sqrt_nonneg _))

/-- **Nested dissection of plane graphs in `O(n ^ (3/2))` operations.** For a plane graph `G`
on `Fin n` there is a separator tree `t` such that, for every matrix `A` whose off-diagonal
nonzero entries are edges of `G`, elimination of `A` in the nested dissection order of `t`,
restricted to the filled pattern, computes the stages of Gaussian elimination with at most
`12 α (α + β)² n √n` arithmetic operations, where `α = β = 50000`. -/
theorem planar_nestedDissection_elimination {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) :
    ∃ (t : SepTree (Fin n)) (hd : IsDissection G t) (hv : t.verts = univ),
      ∀ {K : Type*} [Field K] (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        H = fill (G.comap (ndPerm t hd hv)) Fin.val →
        ∀ (A : Matrix (Fin n) (Fin n) K), (∀ i j, i ≠ j → A i j ≠ 0 → G.Adj i j) →
          (sparseCounted H (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) n).val =
              stage (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) n ∧
            ((sparseCounted H (A.submatrix (ndPerm t hd hv) (ndPerm t hd hv)) n).cost.total :
                ℝ) ≤ 12 * treeConst * (treeConst + treeConst) ^ 2 * (n * √n) := by
  obtain ⟨t, hv, hd, hsq, hs⟩ := exists_sepTree (G := G) hR
  exact ⟨t, hd, hv, fun H _ hH A hA =>
    nestedDissection_elimination (by norm_num [treeConst]) t hd hv hsq hs H hH A hA⟩

end PlanarSeparator
