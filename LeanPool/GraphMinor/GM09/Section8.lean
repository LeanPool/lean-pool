/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section4b
import Mathlib.Data.Set.Card

/-!
# Graph Minors IX, Section 8: Societies with No Large Transaction

This file formalizes Section 8 (pages 60–62) of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77, proving **(8.1)** (`theorem_8_1`):
every society `(G, Ω)` (with `ΩBar ≠ ∅` or `G = ⊥`) that has no transaction of cardinality `> k`
has a linear decomposition of depth `≤ k`.
-/

public section

namespace GraphMinor.GM09

open Set Graph GraphMinor GraphMinor.Surface GraphMinor.GM06

universe u v

variable {α : Type u} {β : Type v}

/-! ## Step 1: Clockwise enumerations of `ΩBar` and prefix/suffix fences -/

namespace CyclicPerm

variable (Ω : CyclicPerm α)

/-- Every nonempty cyclic permutation `Ω` has an injective enumeration `t : Fin n → α` of `ΩBar`
(where `n = ΩBar.ncard`) such that `List.ofFn t` is `Ω`-clockwise. -/
theorem exists_clockwise_enumeration (hne : Ω.bar.Nonempty) :
    ∃ (t : Fin Ω.bar.ncard → α),
      Function.Injective t ∧
      range t = Ω.bar ∧
      Ω.IsClockwiseSeq (List.ofFn t) := by
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨L, hL_len, hL_set, _, hL_cw⟩ :=
    Ω.exists_isClockwiseSeq_of_subset_bar Subset.rfl hw₀
  let t : Fin Ω.bar.ncard → α := fun i => L[i.1]'(by omega)
  have hofFn : List.ofFn t = L := by
    apply List.ext_getElem
    · simp [hL_len]
    · intro i hi₁ hi₂
      simp [t]
  have hinj : Function.Injective t := by
    intro i j hij
    ext
    exact (List.Nodup.getElem_inj_iff hL_cw.1).mp hij
  have hrange : range t = Ω.bar := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨i, rfl⟩
      rw [← hL_set, mem_ofPred_eq, List.mem_iff_getElem]
      exact ⟨i.1, by omega, rfl⟩
    · intro x hx
      rw [← hL_set, mem_ofPred_eq, List.mem_iff_getElem] at hx
      rcases hx with ⟨i, hi, rfl⟩
      exact ⟨⟨i, by omega⟩, rfl⟩
  exact ⟨t, hinj, hrange, hofFn ▸ hL_cw⟩

/-- The prefix set `A_j = {t_0, …, t_{j-1}}` of an enumeration `t : Fin n → α`. -/
def prefixSet {n : ℕ} (t : Fin n → α) (j : ℕ) : Set α :=
  {x : α | ∃ i : Fin n, i.1 < j ∧ t i = x}

/-- The suffix set `B_j = {t_j, …, t_{n-1}}` of an enumeration `t : Fin n → α`. -/
def suffixSet {n : ℕ} (t : Fin n → α) (j : ℕ) : Set α :=
  {x : α | ∃ i : Fin n, j ≤ i.1 ∧ t i = x}

@[simp]
theorem prefixSet_zero {n : ℕ} (t : Fin n → α) :
    prefixSet t 0 = ∅ := by
  ext x
  simp [prefixSet]

theorem suffixSet_zero {n : ℕ} (t : Fin n → α) :
    suffixSet t 0 = range t := by
  ext x
  simp [suffixSet]

theorem prefixSet_all {n : ℕ} (t : Fin n → α) :
    prefixSet t n = range t := by
  ext x
  simp only [prefixSet, mem_ofPred_eq, mem_range]
  exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩⟩

@[simp]
theorem suffixSet_all {n : ℕ} (t : Fin n → α) :
    suffixSet t n = ∅ := by
  ext x
  simp only [suffixSet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
  intro i hi
  omega

theorem prefixSet_mono {n : ℕ} (t : Fin n → α) {i j : ℕ} (hij : i ≤ j) :
    prefixSet t i ⊆ prefixSet t j := by
  rintro x ⟨r, hr, rfl⟩
  exact ⟨r, Nat.lt_of_lt_of_le hr hij, rfl⟩

theorem suffixSet_anti {n : ℕ} (t : Fin n → α) {i j : ℕ} (hij : i ≤ j) :
    suffixSet t j ⊆ suffixSet t i := by
  rintro x ⟨r, hr, rfl⟩
  exact ⟨r, Nat.le_trans hij hr, rfl⟩

theorem mem_prefixSet_succ {n : ℕ} (t : Fin n → α) (i : Fin n) :
    t i ∈ prefixSet t (i.1 + 1) :=
  ⟨i, Nat.lt_succ_self i.1, rfl⟩

theorem mem_suffixSet_self {n : ℕ} (t : Fin n → α) (i : Fin n) :
    t i ∈ suffixSet t i.1 :=
  ⟨i, le_rfl, rfl⟩

theorem prefixSet_union_suffixSet {n : ℕ} (t : Fin n → α) (j : ℕ) :
    prefixSet t j ∪ suffixSet t j = range t := by
  ext x
  simp only [prefixSet, suffixSet, mem_union, mem_ofPred_eq, mem_range]
  constructor
  · rintro (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) <;> exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    rcases lt_or_ge i.1 j with hlt | hge
    · exact Or.inl ⟨i, hlt, rfl⟩
    · exact Or.inr ⟨i, hge, rfl⟩

theorem disjoint_prefixSet_suffixSet {n : ℕ} {t : Fin n → α} (hinj : Function.Injective t) (j : ℕ) :
    Disjoint (prefixSet t j) (suffixSet t j) := by
  rw [disjoint_left]
  rintro x ⟨i₁, hi₁, rfl⟩ ⟨i₂, hi₂, heq⟩
  have h12 : i₁ = i₂ := hinj heq.symm
  subst h12
  omega

/-- "For $1 \le j \le n-1$, let $A_j = \{t_1, \dots, t_j\}$, $B_j = \{t_{j+1}, \dots, t_n\}$, so
that $(A_j, B_j)$ is a fence of $\Omega$." (Graph Minors IX, Section 8, page 60). -/
theorem isFence_prefixSet_suffixSet {n : ℕ} {t : Fin n → α}
    (hinj : Function.Injective t) (hrange : range t = Ω.bar)
    (hcw : Ω.IsClockwiseSeq (List.ofFn t)) (j : ℕ) :
    Ω.IsFence (prefixSet t j) (suffixSet t j) := by
  have hunion : prefixSet t j ∪ suffixSet t j = Ω.bar :=
    (prefixSet_union_suffixSet t j).trans hrange
  have hsubA : prefixSet t j ⊆ Ω.bar := subset_union_left.trans hunion.le
  have hsubB : suffixSet t j ⊆ Ω.bar := subset_union_right.trans hunion.le
  refine ⟨hsubA, hsubB, disjoint_prefixSet_suffixSet hinj j, hunion, ?_⟩
  -- Helper: if `i₁ < i₂ < k₁` and `i₁ < i₂ < k₂` with `k₁ ≠ k₂`, then `{t i₁, t i₂}` does not
  -- cross `{t k₁, t k₂}`.
  have hno_cross_ord : ∀ (i₁ i₂ k₁ k₂ : Fin n),
      i₁.1 < i₂.1 → i₂.1 < k₁.1 → i₂.1 < k₂.1 → k₁ ≠ k₂ →
      ¬ Ω.Crosses (t i₁) (t i₂) (t k₁) (t k₂) := by
    intro i₁ i₂ k₁ k₂ hi12 hik1 hik2 hk12 hcr
    have hlen : (List.ofFn t).length = n := List.length_ofFn
    have h_k1_in : t k₁ ∈ Ω.interval (t i₂) (t i₁) := by
      have h := Ω.mem_interval_of_lt hcw hi12 hik1 (by rw [hlen]; exact k₁.2)
      simp only [List.getElem_ofFn] at h
      exact Ω.mem_interval_rotate_left h
    have h_k2_in : t k₂ ∈ Ω.interval (t i₂) (t i₁) := by
      have h := Ω.mem_interval_of_lt hcw hi12 hik2 (by rw [hlen]; exact k₂.2)
      simp only [List.getElem_ofFn] at h
      exact Ω.mem_interval_rotate_left h
    rcases Ω.crosses_iff_interval.mp hcr with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact disjoint_left.mp (Ω.disjoint_interval_swap (t i₁) (t i₂)) h1 h_k1_in
    · exact disjoint_left.mp (Ω.disjoint_interval_swap (t i₁) (t i₂)) h1 h_k2_in
  rintro a₁ ⟨i₁, hi₁, rfl⟩ a₂ ⟨i₂, hi₂, rfl⟩ ha12 b₁ ⟨k₁, hk₁, rfl⟩ b₂ ⟨k₂, hk₂, rfl⟩ hb12 hcr
  have hi_ne : i₁ ≠ i₂ := fun h => ha12 (congrArg t h)
  have hk_ne : k₁ ≠ k₂ := fun h => hb12 (congrArg t h)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hi_ne) with hlt | hgt
  · exact hno_cross_ord i₁ i₂ k₁ k₂ hlt (by omega) (by omega) hk_ne hcr
  · exact hno_cross_ord i₂ i₁ k₁ k₂ hgt (by omega) (by omega) hk_ne hcr.swap_left

end CyclicPerm

/-! ## Step 2: Disjoint `A → B` paths across a fence form a transaction -/

namespace Society

variable (S : Society α β)

/-- Any family of `m` mutually vertex-disjoint `A → B` paths in `S.G` across a fence `(A, B)` of
`S.Ω` forms a transaction of cardinality `m` in `S`. -/
theorem isTransaction_range_of_isFromToPath {A B : Set α} (hfence : S.Ω.IsFence A B)
    {m : ℕ} {Q : Fin m → Graph α β}
    (hdisj : Pairwise (fun i j => Disjoint V(Q i) V(Q j)))
    (hQ : ∀ i : Fin m, IsFromToPath S.G (Q i) A B) :
    S.IsTransaction (range Q) ∧ (range Q).ncard = m := by
  have hQ_omega : ∀ i : Fin m, ∃ a ∈ A, ∃ b ∈ B, S.IsOmegaPathWithEnds (Q i) a b := by
    intro i
    obtain ⟨a, b, hP, ha_inter, hb_inter⟩ := hQ i
    have ha : a ∈ A := by
      have : a ∈ V(Q i) ∩ A := by rw [ha_inter]; exact mem_singleton a
      exact this.2
    have hb : b ∈ B := by
      have : b ∈ V(Q i) ∩ B := by rw [hb_inter]; exact mem_singleton b
      exact this.2
    have hab : a ≠ b := fun h => disjoint_left.mp hfence.2.2.1 ha (h ▸ hb)
    exact ⟨a, ha, b, hb, hP, hab, hfence.1 ha, hfence.2.1 hb⟩
  have hinj : Function.Injective Q := by
    intro i j hij
    by_contra hne
    obtain ⟨a, _, _, _, hPi⟩ := hQ_omega i
    have ha_i : a ∈ V(Q i) := hPi.1.left_mem
    have ha_j : a ∈ V(Q j) := hij ▸ ha_i
    exact disjoint_left.mp (hdisj hne) ha_i ha_j
  refine ⟨⟨A, B, ⟨⟨?_, ?_⟩, hfence, ?_⟩⟩, ?_⟩
  · rintro P ⟨i, rfl⟩
    obtain ⟨a, _, b, _, hPi⟩ := hQ_omega i
    exact ⟨a, b, hPi⟩
  · rintro P₁ ⟨i, rfl⟩ P₂ ⟨j, rfl⟩ hne
    exact hdisj (fun hij => hne (congrArg Q hij))
  · rintro P ⟨i, rfl⟩
    exact hQ_omega i
  · rw [Set.ncard_range_of_injective hinj, Nat.card_fin]

/-- If `(G, Ω)` has no transaction of cardinality `> k` and `(A, B)` is a fence of `Ω`, then
every family of `m` mutually disjoint `A → B` paths in `G` has `m ≤ k`. -/
theorem le_of_disjoint_fromToPaths_of_isFence {k : ℕ}
    (hno_trans : ∀ P_set : Set (Graph α β), S.IsTransaction P_set → P_set.ncard ≤ k)
    {A B : Set α} (hfence : S.Ω.IsFence A B)
    {m : ℕ} {Q : Fin m → Graph α β}
    (hdisj : Pairwise (fun i j => Disjoint V(Q i) V(Q j)))
    (hQ : ∀ i : Fin m, IsFromToPath S.G (Q i) A B) :
    m ≤ k := by
  obtain ⟨htrans, hcard⟩ := S.isTransaction_range_of_isFromToPath hfence hdisj hQ
  exact hcard ▸ hno_trans (range Q) htrans

/-! ## Step 3: Uncrossing separations and submodularity -/

/-- If `(Y₁, Z₁)` and `(Y₂, Z₂)` are separations of `G`, then `(Y₁ ∩ Y₂, Z₁ ∪ Z₂)` is a
separation of `G`. -/
theorem isGraphSeparation_inter_union {G Y₁ Z₁ Y₂ Z₂ : Graph α β}
    (h₁ : IsGraphSeparation G Y₁ Z₁) (h₂ : IsGraphSeparation G Y₂ Z₂) :
    IsGraphSeparation G (subgraphInter G Y₁ Y₂) (subgraphUnion G Z₁ Z₂) := by
  refine ⟨subgraphInter_le h₁.1, subgraphUnion_le h₁.2.1 h₂.2.1, ?_, ?_, ?_⟩
  · rw [vertexSet_subgraphInter, vertexSet_subgraphUnion]
    ext v
    simp only [mem_union, mem_inter_iff]
    constructor
    · rintro (⟨hv₁, _⟩ | hv₁ | hv₂)
      · exact h₁.1.vertexSet_mono hv₁
      · exact h₁.2.1.vertexSet_mono hv₁
      · exact h₂.2.1.vertexSet_mono hv₂
    · intro hvG
      rcases h₁.2.2.1.symm ▸ hvG with hv₁ | hv₁ <;>
      rcases h₂.2.2.1.symm ▸ hvG with hv₂ | hv₂
      · exact Or.inl ⟨hv₁, hv₂⟩
      · exact Or.inr (Or.inr hv₂)
      · exact Or.inr (Or.inl hv₁)
      · exact Or.inr (Or.inl hv₁)
  · rw [edgeSet_subgraphInter h₁.1 h₂.1, edgeSet_subgraphUnion h₁.2.1 h₂.2.1]
    ext e
    simp only [mem_union, mem_inter_iff]
    constructor
    · rintro (⟨he₁, _⟩ | he₁ | he₂)
      · exact h₁.1.edgeSet_mono he₁
      · exact h₁.2.1.edgeSet_mono he₁
      · exact h₂.2.1.edgeSet_mono he₂
    · intro heG
      rcases h₁.2.2.2.1.symm ▸ heG with he₁ | he₁ <;>
      rcases h₂.2.2.2.1.symm ▸ heG with he₂ | he₂
      · exact Or.inl ⟨he₁, he₂⟩
      · exact Or.inr (Or.inr he₂)
      · exact Or.inr (Or.inl he₁)
      · exact Or.inr (Or.inl he₁)
  · rw [edgeSet_subgraphInter h₁.1 h₂.1, edgeSet_subgraphUnion h₁.2.1 h₂.2.1, disjoint_union_right]
    exact ⟨h₁.2.2.2.2.mono_left inter_subset_left, h₂.2.2.2.2.mono_left inter_subset_right⟩

/-- If `(Y₁, Z₁)` and `(Y₂, Z₂)` are separations of `G`, then `(Y₁ ∪ Y₂, Z₁ ∩ Z₂)` is a
separation of `G`. -/
theorem isGraphSeparation_union_inter {G Y₁ Z₁ Y₂ Z₂ : Graph α β}
    (h₁ : IsGraphSeparation G Y₁ Z₁) (h₂ : IsGraphSeparation G Y₂ Z₂) :
    IsGraphSeparation G (subgraphUnion G Y₁ Y₂) (subgraphInter G Z₁ Z₂) :=
  IsGraphSeparation.symm (isGraphSeparation_inter_union (IsGraphSeparation.symm h₁)
    (IsGraphSeparation.symm h₂))

/-- Submodularity of vertex separator sizes for two separations `(Y₁, Z₁)` and `(Y₂, Z₂)` of a
finite graph `G`:
`|V((Y₁ ∩ Y₂) ∩ (Z₁ ∪ Z₂))| + |V((Y₁ ∪ Y₂) ∩ (Z₁ ∩ Z₂))| ≤ |V(Y₁ ∩ Z₁)| + |V(Y₂ ∩ Z₂)|`
(Graph Minors IX, Section 8, page 61). -/
theorem ncard_separator_inter_union_add_le {G Y₁ Z₁ Y₂ Z₂ : Graph α β} (hfin : V(G).Finite)
    (h₁ : IsGraphSeparation G Y₁ Z₁) (h₂ : IsGraphSeparation G Y₂ Z₂) :
    (V(subgraphInter G Y₁ Y₂) ∩ V(subgraphUnion G Z₁ Z₂)).ncard +
      (V(subgraphUnion G Y₁ Y₂) ∩ V(subgraphInter G Z₁ Z₂)).ncard ≤
      (V(Y₁) ∩ V(Z₁)).ncard + (V(Y₂) ∩ V(Z₂)).ncard := by
  let P := (V(Y₁) ∩ V(Y₂)) ∩ (V(Z₁) ∪ V(Z₂))
  let Q := (V(Y₁) ∪ V(Y₂)) ∩ (V(Z₁) ∩ V(Z₂))
  let S₁ := V(Y₁) ∩ V(Z₁)
  let S₂ := V(Y₂) ∩ V(Z₂)
  have hS₁_fin : S₁.Finite := hfin.subset (inter_subset_left.trans h₁.1.vertexSet_mono)
  have hS₂_fin : S₂.Finite := hfin.subset (inter_subset_left.trans h₂.1.vertexSet_mono)
  have hP_fin : P.Finite :=
    hfin.subset (inter_subset_left.trans (inter_subset_left.trans h₁.1.vertexSet_mono))
  have hQ_fin : Q.Finite :=
    hfin.subset (inter_subset_right.trans (inter_subset_left.trans h₁.2.1.vertexSet_mono))
  have hunion_sub : P ∪ Q ⊆ S₁ ∪ S₂ := by
    rintro x (⟨⟨hxY₁, hxY₂⟩, hxZ₁ | hxZ₂⟩ | ⟨hxY₁ | hxY₂, hxZ₁, hxZ₂⟩)
    · exact Or.inl ⟨hxY₁, hxZ₁⟩
    · exact Or.inr ⟨hxY₂, hxZ₂⟩
    · exact Or.inl ⟨hxY₁, hxZ₁⟩
    · exact Or.inr ⟨hxY₂, hxZ₂⟩
  have hinter_sub : P ∩ Q ⊆ S₁ ∩ S₂ := by
    rintro x ⟨⟨⟨hxY₁, hxY₂⟩, _⟩, ⟨_, hxZ₁, hxZ₂⟩⟩
    exact ⟨⟨hxY₁, hxZ₁⟩, ⟨hxY₂, hxZ₂⟩⟩
  have hle₁ : (P ∪ Q).ncard ≤ (S₁ ∪ S₂).ncard :=
    Set.ncard_le_ncard hunion_sub (hS₁_fin.union hS₂_fin)
  have hle₂ : (P ∩ Q).ncard ≤ (S₁ ∩ S₂).ncard :=
    Set.ncard_le_ncard hinter_sub (hS₁_fin.inter_of_left S₂)
  have heq_PQ := Set.ncard_union_add_ncard_inter P Q hP_fin hQ_fin
  have heq_S := Set.ncard_union_add_ncard_inter S₁ S₂ hS₁_fin hS₂_fin
  change P.ncard + Q.ncard ≤ S₁.ncard + S₂.ncard
  omega

/-- If `Y' ≤ Y ≤ S.G` and `V(Y).ncard + E(Y).ncard ≤ V(Y').ncard + E(Y').ncard`, then `Y' = Y`. -/
theorem eq_of_le_of_ncard_add_ge {Y' Y : Graph α β}
    (hY'Y : Y' ≤ Y) (hYG : Y ≤ S.G)
    (hcard : V(Y).ncard + E(Y).ncard ≤ V(Y').ncard + E(Y').ncard) :
    Y' = Y := by
  have hVY : V(Y).Finite := S.finite_V.subset hYG.vertexSet_mono
  have hEY : E(Y).Finite := S.finite_E.subset hYG.edgeSet_mono
  have hV_le : V(Y').ncard ≤ V(Y).ncard := Set.ncard_le_ncard hY'Y.vertexSet_mono hVY
  have hE_le : E(Y').ncard ≤ E(Y).ncard := Set.ncard_le_ncard hY'Y.edgeSet_mono hEY
  have hV_eq : V(Y') = V(Y) :=
    Set.eq_of_subset_of_ncard_le hY'Y.vertexSet_mono (by omega) hVY
  have hE_eq : E(Y') = E(Y) :=
    Set.eq_of_subset_of_ncard_le hY'Y.edgeSet_mono (by omega) hEY
  exact (Compatible.of_le_le (hY'Y.trans hYG) hYG).ext hV_eq hE_eq

/-- Uncrossing step from the proof of **(8.1)** (Graph Minors IX, Section 8, page 61):
"We claim that $Y_1 \subseteq Y_2 \subseteq \dots \subseteq Y_{n-1}$ and $Z_1 \supseteq Z_2
\supseteq \dots \supseteq Z_{n-1}$. For let $i, j$ satisfy $1 \le i \le j \le n-1$. Then
$(Y_i \cap Y_j, Z_i \cup Z_j)$ is a separation of $G$ with $A_i \subseteq V(Y_i \cap Y_j)$,
$B_i \subseteq V(Z_i \cup Z_j)$, and hence $$|V((Y_i \cap Y_j) \cap (Z_i \cup Z_j))| \ge
k_i.$$" -/
theorem lemma_8_1_uncross {A₁ B₁ A₂ B₂ : Set α} {Y₁ Z₁ Y₂ Z₂ : Graph α β} {k₁ k₂ : ℕ}
    (hA : A₁ ⊆ A₂) (hB : B₂ ⊆ B₁)
    (hsep₁ : IsGraphSeparation S.G Y₁ Z₁)
    (hA₁ : A₁ ⊆ V(Y₁)) (hB₁ : B₁ ⊆ V(Z₁))
    (hk₁ : (V(Y₁) ∩ V(Z₁)).ncard = k₁)
    (hmin_k₁ : ∀ Y Z : Graph α β, IsGraphSeparation S.G Y Z →
      A₁ ⊆ V(Y) → B₁ ⊆ V(Z) → k₁ ≤ (V(Y) ∩ V(Z)).ncard)
    (hmin_Y₁ : ∀ Y Z : Graph α β, IsGraphSeparation S.G Y Z →
      A₁ ⊆ V(Y) → B₁ ⊆ V(Z) → (V(Y) ∩ V(Z)).ncard = k₁ → Y ≤ Y₁ → Y = Y₁)
    (hsep₂ : IsGraphSeparation S.G Y₂ Z₂)
    (hA₂ : A₂ ⊆ V(Y₂)) (hB₂ : B₂ ⊆ V(Z₂))
    (hk₂ : (V(Y₂) ∩ V(Z₂)).ncard = k₂)
    (hmin_k₂ : ∀ Y Z : Graph α β, IsGraphSeparation S.G Y Z →
      A₂ ⊆ V(Y) → B₂ ⊆ V(Z) → k₂ ≤ (V(Y) ∩ V(Z)).ncard) :
    Y₁ ≤ Y₂ ∧ Z₂ ≤ Z₁ := by
  have hsep_iu := isGraphSeparation_inter_union hsep₁ hsep₂
  have hsep_ui := isGraphSeparation_union_inter hsep₁ hsep₂
  have hA₁_iu : A₁ ⊆ V(subgraphInter S.G Y₁ Y₂) :=
    subset_inter hA₁ (hA.trans hA₂)
  have hB₁_iu : B₁ ⊆ V(subgraphUnion S.G Z₁ Z₂) :=
    hB₁.trans subset_union_left
  have hA₂_ui : A₂ ⊆ V(subgraphUnion S.G Y₁ Y₂) :=
    hA₂.trans subset_union_right
  have hB₂_ui : B₂ ⊆ V(subgraphInter S.G Z₁ Z₂) :=
    subset_inter (hB.trans hB₁) hB₂
  have hge₁ : k₁ ≤ (V(subgraphInter S.G Y₁ Y₂) ∩ V(subgraphUnion S.G Z₁ Z₂)).ncard :=
    hmin_k₁ _ _ hsep_iu hA₁_iu hB₁_iu
  have hge₂ : k₂ ≤ (V(subgraphUnion S.G Y₁ Y₂) ∩ V(subgraphInter S.G Z₁ Z₂)).ncard :=
    hmin_k₂ _ _ hsep_ui hA₂_ui hB₂_ui
  have hsubmod := ncard_separator_inter_union_add_le S.finite_V hsep₁ hsep₂
  rw [hk₁, hk₂] at hsubmod
  have heq₁ : (V(subgraphInter S.G Y₁ Y₂) ∩ V(subgraphUnion S.G Z₁ Z₂)).ncard = k₁ := by omega
  have hY_inter_eq : subgraphInter S.G Y₁ Y₂ = Y₁ :=
    hmin_Y₁ (subgraphInter S.G Y₁ Y₂) (subgraphUnion S.G Z₁ Z₂) hsep_iu hA₁_iu hB₁_iu heq₁
      (subgraphInter_le_left hsep₁.1 hsep₂.1)
  have hY₁_le_Y₂ : Y₁ ≤ Y₂ :=
    hY_inter_eq ▸ subgraphInter_le_right hsep₁.1 hsep₂.1
  -- Deduce `Z₂ ≤ Z₁` as in lines 562–567 of the paper.
  have hZ₂_le_Z₁ : Z₂ ≤ Z₁ := by
    have h_inter_eq : V(Y₁) ∩ (V(Z₁) ∪ V(Z₂)) = V(Y₁) ∩ V(Z₁) := by
      have h_sub : V(Y₁) ∩ V(Z₁) ⊆ V(Y₁) ∩ (V(Z₁) ∪ V(Z₂)) :=
        inter_subset_inter_right _ subset_union_left
      have h_card : (V(Y₁) ∩ (V(Z₁) ∪ V(Z₂))).ncard ≤ (V(Y₁) ∩ V(Z₁)).ncard := by
        have h_lhs : V(Y₁) ∩ (V(Z₁) ∪ V(Z₂)) =
            V(subgraphInter S.G Y₁ Y₂) ∩ V(subgraphUnion S.G Z₁ Z₂) := by
          rw [hY_inter_eq, vertexSet_subgraphUnion]
        rw [h_lhs, heq₁, hk₁]
      have h_fin : (V(Y₁) ∩ (V(Z₁) ∪ V(Z₂))).Finite :=
        S.finite_V.subset (inter_subset_left.trans hsep₁.1.vertexSet_mono)
      exact (Set.eq_of_subset_of_ncard_le h_sub h_card h_fin).symm
    have hV_sub : V(Z₂) ⊆ V(Z₁) := by
      intro v hvZ₂
      have hvG : v ∈ V(S.G) := hsep₂.2.1.vertexSet_mono hvZ₂
      have hv_union : v ∈ V(Y₁) ∪ V(Z₁) := hsep₁.2.2.1.symm ▸ hvG
      rcases hv_union with hvY₁ | hvZ₁
      · have hv_in : v ∈ V(Y₁) ∩ (V(Z₁) ∪ V(Z₂)) := ⟨hvY₁, Or.inr hvZ₂⟩
        rw [h_inter_eq] at hv_in
        exact hv_in.2
      · exact hvZ₁
    have hE_sub : E(Z₂) ⊆ E(Z₁) := by
      intro e heZ₂
      have heG : e ∈ E(S.G) := hsep₂.2.1.edgeSet_mono heZ₂
      have he_union : e ∈ E(Y₁) ∪ E(Z₁) := hsep₁.2.2.2.1.symm ▸ heG
      rcases he_union with heY₁ | heZ₁
      · exfalso
        exact disjoint_left.mp hsep₂.2.2.2.2 (hY₁_le_Y₂.edgeSet_mono heY₁) heZ₂
      · exact heZ₁
    rw [(Compatible.of_le_le hsep₂.2.1 hsep₁.2.1).le_iff]
    exact ⟨hV_sub, hE_sub⟩
  exact ⟨hY₁_le_Y₂, hZ₂_le_Z₁⟩

/-! ## Step 4: Existence of a minimal Menger separation for `(A_j, B_j)` -/

/-- "Choose $k_j$ maximum so that there are $k_j$ mutually disjoint $A_j \to B_j$ paths in $G$.
Let $(Y_j, Z_j)$ be a separation of $G$ satisfying the following conditions (1) and (2). (1)
$A_j \subseteq V(Y_j)$, $B_j \subseteq V(Z_j)$, and $|V(Y_j \cap Z_j)| = k_j$. (This is
possible by Menger's theorem.) ... (2) *Subject to (1), $Y_j$ is minimal." (Graph Minors IX, Section
8, pages 60–61). -/
theorem exists_minimal_menger_separation {A B : Set α} {k : ℕ}
    (hA : A ⊆ V(S.G)) (hB : B ⊆ V(S.G))
    (hmax_paths : ∀ (m : ℕ) (Q : Fin m → Graph α β),
      Pairwise (fun i j => Disjoint V(Q i) V(Q j)) →
      (∀ i : Fin m, IsFromToPath S.G (Q i) A B) → m ≤ k) :
    ∃ (k₀ : ℕ) (Y Z : Graph α β),
      k₀ ≤ k ∧
      IsGraphSeparation S.G Y Z ∧
      A ⊆ V(Y) ∧ B ⊆ V(Z) ∧
      (V(Y) ∩ V(Z)).ncard = k₀ ∧
      (∀ Y' Z' : Graph α β, IsGraphSeparation S.G Y' Z' →
        A ⊆ V(Y') → B ⊆ V(Z') → k₀ ≤ (V(Y') ∩ V(Z')).ncard) ∧
      (∀ Y' Z' : Graph α β, IsGraphSeparation S.G Y' Z' →
        A ⊆ V(Y') → B ⊆ V(Z') → (V(Y') ∩ V(Z')).ncard = k₀ → Y' ≤ Y → Y' = Y) := by
  classical
  have : Finite V(S.G) := S.finite_V.to_subtype
  -- First, by Menger's theorem with `k + 1`, there exists an `(A, B)`-separation of order `≤ k`.
  have hex_sep : ∃ m : ℕ, ∃ Y Z : Graph α β,
      IsGraphSeparation S.G Y Z ∧ A ⊆ V(Y) ∧ B ⊆ V(Z) ∧ (V(Y) ∩ V(Z)).ncard = m ∧ m ≤ k := by
    rcases exists_fromToPaths_or_graphSeparation hA hB (k + 1) with ⟨Q, hdisj, hQ⟩ | ⟨Y, Z, hsep,
      _, hAY, hBZ, hlt⟩
    · have hle := hmax_paths (k + 1) Q hdisj hQ
      omega
    · exact ⟨(V(Y) ∩ V(Z)).ncard, Y, Z, hsep, hAY, hBZ, rfl, by omega⟩
  have hex_k₀ : ∃ m : ℕ, ∃ Y Z : Graph α β,
      IsGraphSeparation S.G Y Z ∧ A ⊆ V(Y) ∧ B ⊆ V(Z) ∧ (V(Y) ∩ V(Z)).ncard = m := by
    obtain ⟨m, Y, Z, hsep, hAY, hBZ, hcard, _⟩ := hex_sep
    exact ⟨m, Y, Z, hsep, hAY, hBZ, hcard⟩
  let k₀ := Nat.find hex_k₀
  have hk₀_spec := Nat.find_spec hex_k₀
  have hk₀_le : k₀ ≤ k := by
    obtain ⟨m, Y, Z, hsep, hAY, hBZ, hcard, hm_le⟩ := hex_sep
    exact (Nat.find_min' hex_k₀ ⟨Y, Z, hsep, hAY, hBZ, hcard⟩).trans hm_le
  have hk₀_min : ∀ Y' Z' : Graph α β, IsGraphSeparation S.G Y' Z' →
      A ⊆ V(Y') → B ⊆ V(Z') → k₀ ≤ (V(Y') ∩ V(Z')).ncard := by
    intro Y' Z' hsep' hAY' hBZ'
    exact Nat.find_min' hex_k₀ ⟨Y', Z', hsep', hAY', hBZ', rfl⟩
  -- Next, among all separations of order `k₀`, choose one minimizing `V(Y).ncard + E(Y).ncard`.
  have hex_size : ∃ s : ℕ, ∃ Y Z : Graph α β,
      IsGraphSeparation S.G Y Z ∧ A ⊆ V(Y) ∧ B ⊆ V(Z) ∧
      (V(Y) ∩ V(Z)).ncard = k₀ ∧ V(Y).ncard + E(Y).ncard = s := by
    obtain ⟨Y, Z, hsep, hAY, hBZ, hcard⟩ := hk₀_spec
    exact ⟨V(Y).ncard + E(Y).ncard, Y, Z, hsep, hAY, hBZ, hcard, rfl⟩
  let s₀ := Nat.find hex_size
  obtain ⟨Y, Z, hsep, hAY, hBZ, hcard, hs₀⟩ := Nat.find_spec hex_size
  refine ⟨k₀, Y, Z, hk₀_le, hsep, hAY, hBZ, hcard, hk₀_min, ?_⟩
  intro Y' Z' hsep' hAY' hBZ' hcard' hY'Y
  have hs_ge : s₀ ≤ V(Y').ncard + E(Y').ncard :=
    Nat.find_min' hex_size ⟨Y', Z', hsep', hAY', hBZ', hcard', rfl⟩
  exact S.eq_of_le_of_ncard_add_ge hY'Y hsep.1 (hs₀ ▸ hs_ge)

/-! ## Step 5: Constructing the linear decomposition from a nested chain of separations -/

/-- "Let $Y_n = Z_0 = G$, and let $Y_0$ and $Z_n$ be the null graph. For $1 \le i \le n$, let
$X_i = Y_i \cap Z_{i-1}$. We claim that $(X_i: 1 \le i \le n)$ is a linear decomposition of
$(G, \Omega)$."
(Graph Minors IX, Section 8, pages 61–62). -/
theorem isLinearDecomposition_of_nested_separations {n k : ℕ}
    {t : Fin n → α}
    (hinj : Function.Injective t)
    (hrange : range t = S.Ω.bar)
    (hcw : S.Ω.IsClockwiseSeq (List.ofFn t))
    {Y Z : ℕ → Graph α β}
    (hY0 : Y 0 = ⊥)
    (hYn : Y n = S.G)
    (hsep : ∀ j ≤ n, IsGraphSeparation S.G (Y j) (Z j))
    (hY_mono : ∀ i j, i ≤ j → j ≤ n → Y i ≤ Y j)
    (hZ_anti : ∀ i j, i ≤ j → j ≤ n → Z j ≤ Z i)
    (hpref : ∀ j ≤ n, CyclicPerm.prefixSet t j ⊆ V(Y j))
    (hsuff : ∀ j ≤ n, CyclicPerm.suffixSet t j ⊆ V(Z j))
    (hdepth : ∀ j, 1 ≤ j → j < n → (V(Y j) ∩ V(Z j)).ncard ≤ k) :
    let X : Fin n → Graph α β := fun i => subgraphInter S.G (Y (i.1 + 1)) (Z i.1)
    S.IsLinearDecomposition t X ∧
      ∀ i i' : Fin n, i < i' → (V(X i) ∩ V(X i')).ncard ≤ k := by
  intro X
  have hX_le_G : ∀ i : Fin n, X i ≤ S.G := fun i =>
    subgraphInter_le (hsep (i.1 + 1) (by omega)).1
  have hX_le_Y : ∀ i : Fin n, X i ≤ Y (i.1 + 1) := fun i =>
    subgraphInter_le_left (hsep (i.1 + 1) (by omega)).1 (hsep i.1 (by omega)).2.1
  have hX_le_Z : ∀ i : Fin n, X i ≤ Z i.1 := fun i =>
    subgraphInter_le_right (hsep (i.1 + 1) (by omega)).1 (hsep i.1 (by omega)).2.1
  -- Condition (i): `⋃_{i} X_i = S.G`.
  have hV_cover : ∀ m ≤ n, ∀ v ∈ V(Y m), ∃ i : Fin n, i.1 < m ∧ v ∈ V(X i) := by
    intro m
    induction m with
    | zero =>
      intro _ v hv
      rw [hY0] at hv
      exact hv.elim
    | succ m ih =>
      intro hm v hv
      by_cases hv_m : v ∈ V(Y m)
      · obtain ⟨i, hi, hvX⟩ := ih (by omega) v hv_m
        exact ⟨i, by omega, hvX⟩
      · have hvG : v ∈ V(S.G) := (hsep (m + 1) hm).1.vertexSet_mono hv
        have hv_union : v ∈ V(Y m) ∪ V(Z m) := (hsep m (by omega)).2.2.1.symm ▸ hvG
        have hvZm : v ∈ V(Z m) := hv_union.resolve_left hv_m
        exact ⟨⟨m, hm⟩, Nat.lt_succ_self m, hv, hvZm⟩
  have hE_cover : ∀ m ≤ n, ∀ e ∈ E(Y m), ∃ i : Fin n, i.1 < m ∧ e ∈ E(X i) := by
    intro m
    induction m with
    | zero =>
      intro _ e he
      rw [hY0] at he
      exact he.elim
    | succ m ih =>
      intro hm e he
      by_cases he_m : e ∈ E(Y m)
      · obtain ⟨i, hi, heX⟩ := ih (by omega) e he_m
        exact ⟨i, by omega, heX⟩
      · have heG : e ∈ E(S.G) := (hsep (m + 1) hm).1.edgeSet_mono he
        have he_union : e ∈ E(Y m) ∪ E(Z m) := (hsep m (by omega)).2.2.2.1.symm ▸ heG
        have heZm : e ∈ E(Z m) := he_union.resolve_left he_m
        refine ⟨⟨m, hm⟩, Nat.lt_succ_self m, ?_⟩
        change e ∈ E(subgraphInter S.G (Y (m + 1)) (Z m))
        rw [edgeSet_subgraphInter (hsep (m + 1) hm).1 (hsep m (by omega)).2.1]
        exact ⟨he, heZm⟩
  have hunion_eq : subgraphSUnion S.G (range X) = S.G := by
    have hsub_le : subgraphSUnion S.G (range X) ≤ S.G :=
      subgraphSUnion_le (by rintro _ ⟨i, rfl⟩; exact hX_le_G i)
    refine (Compatible.of_le_le hsub_le le_rfl).ext ?_ ?_
    · apply Subset.antisymm hsub_le.vertexSet_mono
      intro v hvG
      rw [← hYn] at hvG
      obtain ⟨i, _, hvXi⟩ := hV_cover n le_rfl v hvG
      rw [vertexSet_subgraphSUnion]
      exact mem_iUnion₂.mpr ⟨X i, ⟨i, rfl⟩, hvXi⟩
    · apply Subset.antisymm hsub_le.edgeSet_mono
      intro e heG
      rw [← hYn] at heG
      obtain ⟨i, _, heXi⟩ := hE_cover n le_rfl e heG
      rw [edgeSet_subgraphSUnion (by rintro _ ⟨j, rfl⟩; exact hX_le_G j)]
      exact mem_iUnion₂.mpr ⟨X i, ⟨i, rfl⟩, heXi⟩
  -- Condition (ii): For `i < i'`, `Disjoint E(X i) E(X i')`.
  have hedge_disj : ∀ i i' : Fin n, i < i' → Disjoint E(X i) E(X i') := by
    intro i i' hii'
    have h1 : E(X i) ⊆ E(Y (i.1 + 1)) := (hX_le_Y i).edgeSet_mono
    have h2 : E(X i') ⊆ E(Z (i.1 + 1)) :=
      (hX_le_Z i').edgeSet_mono.trans
        (hZ_anti (i.1 + 1) i'.1 (by omega) (by omega)).edgeSet_mono
    exact (hsep (i.1 + 1) (by omega)).2.2.2.2.mono h1 h2
  -- Condition (iii): For `i : Fin n`, `t i ∈ V(X i)`.
  have hmem_V : ∀ i : Fin n, t i ∈ V(X i) := fun i =>
    ⟨hpref (i.1 + 1) (by omega) (CyclicPerm.mem_prefixSet_succ t i),
      hsuff i.1 (by omega) (CyclicPerm.mem_suffixSet_self t i)⟩
  -- Condition (iv): For `i ≤ i' ≤ i''`, `subgraphInter S.G (X i) (X i'') ≤ X i'`.
  have hinter_le : ∀ i i' i'' : Fin n, i ≤ i' → i' ≤ i'' →
      subgraphInter S.G (X i) (X i'') ≤ X i' := by
    intro i i' i'' hii' hi'i''
    have hle₁ : subgraphInter S.G (X i) (X i'') ≤ Y (i'.1 + 1) :=
      (subgraphInter_le_left (hX_le_G i) (hX_le_G i'')).trans
        ((hX_le_Y i).trans (hY_mono (i.1 + 1) (i'.1 + 1) (by omega) (by omega)))
    have hle₂ : subgraphInter S.G (X i) (X i'') ≤ Z i'.1 :=
      (subgraphInter_le_right (hX_le_G i) (hX_le_G i'')).trans
        ((hX_le_Z i'').trans (hZ_anti i'.1 i''.1 (by omega) (by omega)))
    exact le_subgraphInter (hsep (i'.1 + 1) (by omega)).1 (hsep i'.1 (by omega)).2.1 hle₁ hle₂
  -- Depth bound: For `i < i'`, `(V(X i) ∩ V(X i')).ncard ≤ k`.
  have hdepth_le : ∀ i i' : Fin n, i < i' → (V(X i) ∩ V(X i')).ncard ≤ k := by
    intro i i' hii'
    have hsub : V(X i) ∩ V(X i') ⊆ V(Y (i.1 + 1)) ∩ V(Z (i.1 + 1)) :=
      inter_subset_inter (hX_le_Y i).vertexSet_mono
        ((hX_le_Z i').vertexSet_mono.trans
          (hZ_anti (i.1 + 1) i'.1 (by omega) (by omega)).vertexSet_mono)
    have hfin : (V(Y (i.1 + 1)) ∩ V(Z (i.1 + 1))).Finite :=
      S.finite_V.subset (inter_subset_left.trans (hsep (i.1 + 1) (by omega)).1.vertexSet_mono)
    exact (Set.ncard_le_ncard hsub hfin).trans
      (hdepth (i.1 + 1) (by omega) (by omega))
  exact ⟨⟨hinj, hrange, hcw, hX_le_G, hunion_eq, hedge_disj, hmem_V, hinter_le⟩, hdepth_le⟩

/-! ## Main Theorem: Graph Minors IX, (8.1) -/

/-- **Graph Minors IX, (8.1)** (page 60):
"Every society with no transaction of cardinality $>k$ has a linear decomposition of depth
$\le k$."

*Note on the hypothesis `hne : S.Ω.bar.Nonempty ∨ S.G = ⊥`:*
In a linear decomposition `({t₁, …, t_n}, (X_i : 1 ≤ i ≤ n))` of `(G, Ω)`, `{t₁, …, t_n} = ΩBar` and
`(i) ⋃ (X_i : 1 ≤ i ≤ n) = G`. When `ΩBar = ∅`, we must have `n = 0`, so the union `(i)` is the null
graph `⊥`, which equals `G` if and only if `G = ⊥`. When `ΩBar ≠ ∅`, `n = |ΩBar| ≥ 1` and the proof
in
the paper constructs a linear decomposition `(X_i : 1 ≤ i ≤ n)` of depth `≤ k` for any society
`(G, Ω)` with no transaction of cardinality `> k`. -/
theorem theorem_8_1_proof (S : Society α β) (hne : S.Ω.bar.Nonempty ∨ S.G = ⊥) (k : ℕ)
    (hno_trans : ∀ P_set : Set (Graph α β), S.IsTransaction P_set → P_set.ncard ≤ k) :
    S.HasLinearDecompositionOfDepthLE k := by
  classical
  by_cases hbar_ne : S.Ω.bar.Nonempty
  · obtain ⟨t, hinj, hrange, hcw⟩ := S.Ω.exists_clockwise_enumeration hbar_ne
    let n := S.Ω.bar.ncard
    have hn : 1 ≤ n := Set.ncard_pos S.Ω.finite_bar |>.mpr hbar_ne
    let A (j : ℕ) : Set α := CyclicPerm.prefixSet t j
    let B (j : ℕ) : Set α := CyclicPerm.suffixSet t j
    have hfence : ∀ j : ℕ, S.Ω.IsFence (A j) (B j) :=
      fun j => S.Ω.isFence_prefixSet_suffixSet hinj hrange hcw j
    have hA_sub_G : ∀ j : ℕ, A j ⊆ V(S.G) :=
      fun j => (hfence j).1.trans S.bar_subset
    have hB_sub_G : ∀ j : ℕ, B j ⊆ V(S.G) :=
      fun j => (hfence j).2.1.trans S.bar_subset
    have hmenger : ∀ j : ℕ,
        ∃ (k₀ : ℕ) (Y Z : Graph α β),
          k₀ ≤ k ∧
          IsGraphSeparation S.G Y Z ∧
          A j ⊆ V(Y) ∧ B j ⊆ V(Z) ∧
          (V(Y) ∩ V(Z)).ncard = k₀ ∧
          (∀ Y' Z' : Graph α β, IsGraphSeparation S.G Y' Z' →
            A j ⊆ V(Y') → B j ⊆ V(Z') → k₀ ≤ (V(Y') ∩ V(Z')).ncard) ∧
          (∀ Y' Z' : Graph α β, IsGraphSeparation S.G Y' Z' →
            A j ⊆ V(Y') → B j ⊆ V(Z') → (V(Y') ∩ V(Z')).ncard = k₀ → Y' ≤ Y → Y' = Y) := by
      intro j
      exact S.exists_minimal_menger_separation (hA_sub_G j) (hB_sub_G j)
        (fun m Q hdisj hQ => S.le_of_disjoint_fromToPaths_of_isFence hno_trans (hfence j) hdisj hQ)
    choose k_sep Y_raw Z_raw hk_le hsep_raw hA_raw hB_raw hcard_raw hmin_k_raw hmin_Y_raw
      using hmenger
    let Y (j : ℕ) : Graph α β :=
      if j = 0 then ⊥ else if j < n then Y_raw j else S.G
    let Z (j : ℕ) : Graph α β :=
      if j = 0 then S.G else if j < n then Z_raw j else ⊥
    have hY0 : Y 0 = ⊥ := by simp [Y]
    have hZ0 : Z 0 = S.G := by simp [Z]
    have hYn : Y n = S.G := by
      have hn_ne : n ≠ 0 := by omega
      simp [Y, hn_ne]
    have hZn : Z n = ⊥ := by
      have hn_ne : n ≠ 0 := by omega
      simp [Z, hn_ne]
    have hY_mid : ∀ j, 1 ≤ j → j < n → Y j = Y_raw j := by
      intro j hj1 hjn
      have hj_ne : j ≠ 0 := by omega
      simp [Y, hj_ne, hjn]
    have hZ_mid : ∀ j, 1 ≤ j → j < n → Z j = Z_raw j := by
      intro j hj1 hjn
      have hj_ne : j ≠ 0 := by omega
      simp [Z, hj_ne, hjn]
    have hsep_bot_G : IsGraphSeparation S.G ⊥ S.G :=
      ⟨bot_le, le_rfl, by simp, by simp, by simp⟩
    have hsep : ∀ j ≤ n, IsGraphSeparation S.G (Y j) (Z j) := by
      intro j hjn
      rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hj_pos
      · rw [hY0, hZ0]; exact hsep_bot_G
      · rcases lt_or_eq_of_le hjn with hlt | rfl
        · rw [hY_mid j hj_pos hlt, hZ_mid j hj_pos hlt]
          exact hsep_raw j
        · rw [hYn, hZn]; exact IsGraphSeparation.symm hsep_bot_G
    have hnest_mid : ∀ i j, 1 ≤ i → i ≤ j → j < n →
        Y_raw i ≤ Y_raw j ∧ Z_raw j ≤ Z_raw i := by
      intro i j _ hij _
      exact S.lemma_8_1_uncross
        (CyclicPerm.prefixSet_mono t hij)
        (CyclicPerm.suffixSet_anti t hij)
        (hsep_raw i) (hA_raw i) (hB_raw i) (hcard_raw i) (hmin_k_raw i) (hmin_Y_raw i)
        (hsep_raw j) (hA_raw j) (hB_raw j) (hcard_raw j) (hmin_k_raw j)
    have hY_mono : ∀ i j, i ≤ j → j ≤ n → Y i ≤ Y j := by
      intro i j hij hjn
      rcases eq_or_lt_of_le (Nat.zero_le i) with rfl | hi_pos
      · rw [hY0]; exact bot_le
      · rcases lt_or_eq_of_le hjn with hlt_j | rfl
        · rw [hY_mid i hi_pos (by omega), hY_mid j (by omega) hlt_j]
          exact (hnest_mid i j hi_pos hij hlt_j).1
        · rw [hYn]
          exact (hsep i hij).1
    have hZ_anti : ∀ i j, i ≤ j → j ≤ n → Z j ≤ Z i := by
      intro i j hij hjn
      rcases eq_or_lt_of_le (Nat.zero_le i) with rfl | hi_pos
      · rw [hZ0]
        exact (hsep j hjn).2.1
      · rcases lt_or_eq_of_le hjn with hlt_j | rfl
        · rw [hZ_mid i hi_pos (by omega), hZ_mid j (by omega) hlt_j]
          exact (hnest_mid i j hi_pos hij hlt_j).2
        · rw [hZn]; exact bot_le
    have hpref : ∀ j ≤ n, CyclicPerm.prefixSet t j ⊆ V(Y j) := by
      intro j hjn
      rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hj_pos
      · simp
      · rcases lt_or_eq_of_le hjn with hlt | rfl
        · rw [hY_mid j hj_pos hlt]; exact hA_raw j
        · rw [hYn]; exact hA_sub_G n
    have hsuff : ∀ j ≤ n, CyclicPerm.suffixSet t j ⊆ V(Z j) := by
      intro j hjn
      rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hj_pos
      · rw [hZ0]; exact hB_sub_G 0
      · rcases lt_or_eq_of_le hjn with hlt | rfl
        · rw [hZ_mid j hj_pos hlt]; exact hB_raw j
        · rw [CyclicPerm.suffixSet_all]; exact empty_subset _
    have hdepth : ∀ j, 1 ≤ j → j < n → (V(Y j) ∩ V(Z j)).ncard ≤ k := by
      intro j hj1 hjn
      rw [hY_mid j hj1 hjn, hZ_mid j hj1 hjn, hcard_raw j]
      exact hk_le j
    exact ⟨n, t, fun i => subgraphInter S.G (Y (i.1 + 1)) (Z i.1),
      S.isLinearDecomposition_of_nested_separations hinj hrange hcw
        hY0 hYn hsep hY_mono hZ_anti hpref hsuff hdepth⟩
  · -- Degenerate case: `S.Ω.bar = ∅` and `S.G = ⊥`.
    have hbar_empty : S.Ω.bar = ∅ := Set.not_nonempty_iff_eq_empty.mp hbar_ne
    have hG_bot : S.G = ⊥ := hne.resolve_left hbar_ne
    refine ⟨0, Fin.elim0, Fin.elim0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact fun i => i.elim0
    · simp [hbar_empty]
    · exact ⟨List.nodup_nil, fun v hv => by simp at hv, fun i hi => by simp at hi⟩
    · exact fun i => i.elim0
    · rw [hG_bot]
      exact le_bot_iff.mp (subgraphSUnion_le (by rintro _ ⟨i, _⟩; exact i.elim0))
    · exact fun i => i.elim0
    · exact fun i => i.elim0
    · exact fun i => i.elim0
    · exact fun i => i.elim0

end Society

export Society (theorem_8_1_proof)

end GraphMinor.GM09
