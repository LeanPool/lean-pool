/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.TreeLemma.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.Minimal

/-!
# A lemma about trees: Graph Minors IV, (2.1)

This file formalizes Graph Minors IV, (2.1) (pages 230–231), the minimal bad sequence lemma for a
countable sequence of disjoint rooted trees `T₁, T₂, …` and a graph `M` on their vertices.

Following the paper:
* `IsIncreasing T z`: a sequence `z₁, z₂, …` of vertices of `⋃ᵢ V(Tᵢ)` is *increasing* if `i < i'`
  whenever `j < j'`, `z_j ∈ V(Tᵢ)`, and `z_{j'} ∈ V(T_{i'})`.
* `V₀ T`: the non-root vertices `⋃ᵢ V(Tᵢ) \ {o(T₁), o(T₂), …}`.
* `IsSection T M z`: a *section* is an increasing sequence in `V₀ T` whose range is `M`-stable.
* If there is no section, `V₀ T` is `M`-rich and `X = {o(T₁), o(T₂), …}` satisfies (2.1).
* If there is a section, we define `minimalSectionSeq T M` (`x₁, x₂, …`) inductively by choosing at
  each step a candidate whose subtree has the minimum number of vertices, and prove claims (1)–(5)
  of the paper (`lemma_2_1_claim_1` through `lemma_2_1_claim_5`).
-/

public section

namespace GraphMinor.GM04

variable {ι : Type*}

/-! ### Disjoint sequences of trees and increasing sequences -/

/-- In a sequence of pairwise disjoint trees, each vertex belongs to at most one tree. -/
theorem tree_eq_of_mem_verts {T : ℕ → RootedTree ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    {i j : ℕ} {v : ι} (hi : v ∈ (T i).verts) (hj : v ∈ (T j).verts) : i = j := by
  by_contra hne
  exact Finset.disjoint_left.1 (hdisj hne) hi hj

/-- A sequence `z : ℕ → ι` is *increasing* with respect to `T` (Graph Minors IV, proof of (2.1),
page 230) if every term belongs to some `V(Tᵢ)` and `i < i'` whenever `j < j'`, `z j ∈ V(Tᵢ)`,
and `z j' ∈ V(T_{i'})`. -/
def IsIncreasing (T : ℕ → RootedTree ι) (z : ℕ → ι) : Prop :=
  (∀ j, ∃ i, z j ∈ (T i).verts) ∧
    ∀ ⦃j j' i i'⦄, j < j' → z j ∈ (T i).verts → z j' ∈ (T i').verts → i < i'

theorem IsIncreasing.le_of_le {T : ℕ → RootedTree ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    {z : ℕ → ι} (hz : IsIncreasing T z) {j j' i i' : ℕ} (hjj' : j ≤ j')
    (hi : z j ∈ (T i).verts) (hi' : z j' ∈ (T i').verts) : i ≤ i' := by
  rcases eq_or_lt_of_le hjj' with rfl | hlt
  · exact le_of_eq (tree_eq_of_mem_verts hdisj hi hi')
  · exact le_of_lt (hz.2 hlt hi hi')

theorem IsIncreasing.index_le_of_tree_le {T : ℕ → RootedTree ι} {z : ℕ → ι}
    (hz : IsIncreasing T z) {j j' i i' : ℕ}
    (hi : z j ∈ (T i).verts) (hi' : z j' ∈ (T i').verts) (hii' : i ≤ i') : j ≤ j' := by
  by_contra hlt
  have : i' < i := hz.2 (Nat.lt_of_not_ge hlt) hi' hi
  omega

theorem IsIncreasing.injective {T : ℕ → RootedTree ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    {z : ℕ → ι} (hz : IsIncreasing T z) : Function.Injective z := by
  intro j₁ j₂ hjeq
  rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
  · obtain ⟨i₁, hi₁⟩ := hz.1 j₁
    obtain ⟨i₂, hi₂⟩ := hz.1 j₂
    have hlt_i : i₁ < i₂ := hz.2 hlt hi₁ hi₂
    have heq_i : i₁ = i₂ := tree_eq_of_mem_verts hdisj hi₁ (hjeq ▸ hi₂)
    omega
  · rfl
  · obtain ⟨i₁, hi₁⟩ := hz.1 j₁
    obtain ⟨i₂, hi₂⟩ := hz.1 j₂
    have hlt_i : i₂ < i₁ := hz.2 hgt hi₂ hi₁
    have heq_i : i₁ = i₂ := tree_eq_of_mem_verts hdisj hi₁ (hjeq ▸ hi₂)
    omega

theorem IsIncreasing.infinite_range {T : ℕ → RootedTree ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    {z : ℕ → ι} (hz : IsIncreasing T z) : (Set.range z).Infinite :=
  Set.infinite_range_of_injective (hz.injective hdisj)

theorem IsIncreasing.range_subset {T : ℕ → RootedTree ι} {z : ℕ → ι} (hz : IsIncreasing T z) :
    Set.range z ⊆ ⋃ i, ((T i).verts : Set ι) := by
  rintro _ ⟨j, rfl⟩
  obtain ⟨i, hi⟩ := hz.1 j
  exact Set.mem_iUnion.2 ⟨i, hi⟩

theorem IsIncreasing.subsingleton_inter {T : ℕ → RootedTree ι} {z : ℕ → ι}
    (hz : IsIncreasing T z) (i : ℕ) : (Set.range z ∩ (T i).verts).Subsingleton := by
  rintro _ ⟨⟨j₁, rfl⟩, hj₁⟩ _ ⟨⟨j₂, rfl⟩, hj₂⟩
  rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
  · exact absurd (hz.2 hlt hj₁ hj₂) (lt_irrefl i)
  · rfl
  · exact absurd (hz.2 hgt hj₂ hj₁) (lt_irrefl i)

private theorem exists_tree_inter_nonempty_ge {T : ℕ → RootedTree ι} {Y : Set ι}
    (hY_inf : Y.Infinite) (hY_sub : Y ⊆ ⋃ i, ((T i).verts : Set ι)) (m : ℕ) :
    ∃ i, m ≤ i ∧ (Y ∩ (T i).verts).Nonempty := by
  have hfin : (⋃ i ∈ Finset.range m, (Y ∩ (T i).verts)).Finite := by
    refine Finset.finite_toSet (Finset.range m) |>.biUnion fun i _ ↦ ?_
    exact (T i).verts.finite_toSet.subset Set.inter_subset_right
  obtain ⟨y, hyY, hy_not_mem⟩ := Set.Infinite.exists_notMem_finite hY_inf hfin
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hY_sub hyY)
  refine ⟨i, ?_, y, hyY, hi⟩
  by_contra hlt
  apply hy_not_mem
  exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_of_not_ge hlt)) ⟨hyY, hi⟩

open Classical in
private noncomputable def nextTreeIdx (T : ℕ → RootedTree ι) (Y : Set ι)
    (hY_inf : Y.Infinite) (hY_sub : Y ⊆ ⋃ i, ((T i).verts : Set ι)) : ℕ → ℕ
  | 0 => Nat.find (exists_tree_inter_nonempty_ge hY_inf hY_sub 0)
  | k + 1 =>
    Nat.find (exists_tree_inter_nonempty_ge hY_inf hY_sub (nextTreeIdx T Y hY_inf hY_sub k + 1))

private theorem nextTreeIdx_lt_succ {T : ℕ → RootedTree ι} {Y : Set ι}
    (hY_inf : Y.Infinite) (hY_sub : Y ⊆ ⋃ i, ((T i).verts : Set ι)) (k : ℕ) :
    nextTreeIdx T Y hY_inf hY_sub k < nextTreeIdx T Y hY_inf hY_sub (k + 1) := by
  classical
  simp only [nextTreeIdx]
  exact (Nat.find_spec
    (exists_tree_inter_nonempty_ge hY_inf hY_sub (nextTreeIdx T Y hY_inf hY_sub k + 1))).1

private theorem strictMono_nextTreeIdx {T : ℕ → RootedTree ι} {Y : Set ι}
    (hY_inf : Y.Infinite) (hY_sub : Y ⊆ ⋃ i, ((T i).verts : Set ι)) :
    StrictMono (nextTreeIdx T Y hY_inf hY_sub) :=
  strictMono_nat_of_lt_succ (nextTreeIdx_lt_succ hY_inf hY_sub)

private theorem nextTreeIdx_nonempty {T : ℕ → RootedTree ι} {Y : Set ι}
    (hY_inf : Y.Infinite) (hY_sub : Y ⊆ ⋃ i, ((T i).verts : Set ι)) (k : ℕ) :
    (Y ∩ (T (nextTreeIdx T Y hY_inf hY_sub k)).verts).Nonempty := by
  classical
  cases k with
  | zero =>
    simp only [nextTreeIdx]
    exact (Nat.find_spec (exists_tree_inter_nonempty_ge hY_inf hY_sub 0)).2
  | succ k =>
    simp only [nextTreeIdx]
    exact (Nat.find_spec
      (exists_tree_inter_nonempty_ge hY_inf hY_sub (nextTreeIdx T Y hY_inf hY_sub k + 1))).2

private theorem exists_nextTreeIdx_eq_of_lt {T : ℕ → RootedTree ι} {Y : Set ι}
    (hY_inf : Y.Infinite) (hY_sub : Y ⊆ ⋃ i, ((T i).verts : Set ι)) :
    ∀ (k i : ℕ), i < nextTreeIdx T Y hY_inf hY_sub k → (Y ∩ (T i).verts).Nonempty →
      ∃ j < k, nextTreeIdx T Y hY_inf hY_sub j = i
  | 0, i, hlt, hne => by
    classical
    simp only [nextTreeIdx] at hlt
    have hmin := Nat.find_min (exists_tree_inter_nonempty_ge hY_inf hY_sub 0) hlt
    exact absurd ⟨Nat.zero_le i, hne⟩ hmin
  | k + 1, i, hlt, hne => by
    classical
    simp only [nextTreeIdx] at hlt
    have hmin := Nat.find_min
      (exists_tree_inter_nonempty_ge hY_inf hY_sub (nextTreeIdx T Y hY_inf hY_sub k + 1)) hlt
    have hle : i ≤ nextTreeIdx T Y hY_inf hY_sub k := by
      by_contra hgt
      exact hmin ⟨Nat.lt_of_not_ge hgt, hne⟩
    rcases eq_or_lt_of_le hle with rfl | hlt'
    · exact ⟨k, Nat.lt_succ_self k, rfl⟩
    · obtain ⟨j, hjk, hj⟩ := exists_nextTreeIdx_eq_of_lt hY_inf hY_sub k i hlt' hne
      exact ⟨j, Nat.lt_succ_of_lt hjk, hj⟩

/-- Every infinite subset `Y ⊆ ⋃ i, V(Tᵢ)` contains an increasing sequence; if furthermore
`Y` meets each `V(Tᵢ)` in at most one vertex, the sequence enumerates all of `Y`. -/
theorem exists_isIncreasing_of_infinite {T : ℕ → RootedTree ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    {Y : Set ι} (hY_inf : Y.Infinite) (hY_sub : Y ⊆ ⋃ i, ((T i).verts : Set ι)) :
    ∃ (z : ℕ → ι) (idx : ℕ → ℕ), StrictMono idx ∧ IsIncreasing T z ∧
      (∀ j, z j ∈ Y ∧ z j ∈ (T (idx j)).verts) ∧
      ((∀ i, (Y ∩ (T i).verts).Subsingleton) → Set.range z = Y) := by
  let idx := nextTreeIdx T Y hY_inf hY_sub
  have hmono : StrictMono idx := strictMono_nextTreeIdx hY_inf hY_sub
  let z : ℕ → ι := fun j ↦ (nextTreeIdx_nonempty hY_inf hY_sub j).choose
  have hz_spec : ∀ j, z j ∈ Y ∧ z j ∈ (T (idx j)).verts :=
    fun j ↦ (nextTreeIdx_nonempty hY_inf hY_sub j).choose_spec
  have hinc : IsIncreasing T z := by
    refine ⟨fun j ↦ ⟨idx j, (hz_spec j).2⟩, fun j j' i i' hlt hi hi' ↦ ?_⟩
    have hi_eq : i = idx j := tree_eq_of_mem_verts hdisj hi (hz_spec j).2
    have hi'_eq : i' = idx j' := tree_eq_of_mem_verts hdisj hi' (hz_spec j').2
    rw [hi_eq, hi'_eq]
    exact hmono hlt
  refine ⟨z, idx, hmono, hinc, hz_spec, fun hsub ↦ ?_⟩
  ext y
  constructor
  · rintro ⟨j, rfl⟩
    exact (hz_spec j).1
  · intro hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hY_sub hy)
    have hlt : i < idx (i + 1) := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (hmono.id_le (i + 1))
    obtain ⟨j, -, hj⟩ := exists_nextTreeIdx_eq_of_lt hY_inf hY_sub (i + 1) i hlt ⟨y, hy, hi⟩
    refine ⟨j, ?_⟩
    have hzj_verts : z j ∈ (T i).verts := hj ▸ (hz_spec j).2
    exact hsub i ⟨(hz_spec j).1, hzj_verts⟩ ⟨hy, hi⟩

/-! ### `V₀`, sections, and the inductive choice of `x₁, x₂, …` -/

/-- `V₀ = V(M) - {o(T₁), o(T₂), …}` (Graph Minors IV, proof of (2.1), page 230). -/
def V₀ (T : ℕ → RootedTree ι) : Set ι :=
  (⋃ i, ((T i).verts : Set ι)) \ Set.range fun i ↦ (T i).root

theorem mem_V₀_iff {T : ℕ → RootedTree ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts)) {v : ι} :
    v ∈ V₀ T ↔ ∃ i, v ∈ (T i).edges := by
  simp only [V₀, Set.mem_sdiff, Set.mem_iUnion, Finset.mem_coe, Set.mem_range, not_exists,
    RootedTree.mem_edges]
  constructor
  · rintro ⟨⟨i, hvi⟩, hnotroot⟩
    exact ⟨i, fun hr ↦ hnotroot i hr.symm, hvi⟩
  · rintro ⟨i, hne, hvi⟩
    refine ⟨⟨i, hvi⟩, fun k hvk ↦ hne ?_⟩
    have hki : k = i := tree_eq_of_mem_verts hdisj (hvk ▸ (T k).root_mem) hvi
    exact (hki ▸ hvk).symm

/-- A *section* (Graph Minors IV, proof of (2.1), page 231) is an increasing sequence in `V₀`
whose elements form an `M`-stable set. -/
def IsSection (T : ℕ → RootedTree ι) (M : SimpleGraph ι) (z : ℕ → ι) : Prop :=
  IsIncreasing T z ∧ (∀ j, z j ∈ V₀ T) ∧ M.IsIndepSet (Set.range z)

/-- If no sequence of elements of `Y ⊆ V₀` is a section, then `Y` is `M`-rich. -/
theorem isRich_of_no_section {T : ℕ → RootedTree ι} {M : SimpleGraph ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    {Y : Set ι} (hYV₀ : Y ⊆ V₀ T) (hno : ∀ z : ℕ → ι, (∀ j, z j ∈ Y) → ¬ IsSection T M z) :
    IsRich M Y := by
  intro Z hZY hZind
  by_contra hZinf
  have hZsub : Z ⊆ ⋃ i, ((T i).verts : Set ι) :=
    hZY.trans (hYV₀.trans Set.sdiff_subset)
  obtain ⟨z, _, _, hinc, hzZ, -⟩ := exists_isIncreasing_of_infinite hdisj hZinf hZsub
  have hzY : ∀ j, z j ∈ Y := fun j ↦ hZY (hzZ j).1
  have hz_range : Set.range z ⊆ Z := by rintro _ ⟨j, rfl⟩; exact (hzZ j).1
  exact hno z hzY ⟨hinc, fun j ↦ hYV₀ (hzY j), hZind.mono hz_range⟩

/-- `HasSectionPrefix T M s` says that there is a section whose first `s.length` terms are `s`. -/
def HasSectionPrefix (T : ℕ → RootedTree ι) (M : SimpleGraph ι) (s : List ι) : Prop :=
  ∃ z : ℕ → ι, IsSection T M z ∧ ∀ j (hj : j < s.length), z j = s[j]

/-- Given a prefix `s` of some section, we can extend `s` by a vertex `v` so that `s ++ [v]` is
still a prefix of a section, while no proper descendant `x` of `v` in its tree extends `s` to a
prefix of a section. -/
private theorem exists_minimal_section_step {T : ℕ → RootedTree ι} {M : SimpleGraph ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    {s : List ι} (hs : HasSectionPrefix T M s) :
    ∃ v : ι, HasSectionPrefix T M (s ++ [v]) ∧
      ∀ i, v ∈ (T i).verts → ∀ x ∈ (T i).subtreeAt v, x ≠ v →
        ¬ HasSectionPrefix T M (s ++ [x]) := by
  obtain ⟨z₀, hz₀_sec, hz₀_pre⟩ := hs
  let v₀ := z₀ s.length
  obtain ⟨i₀, hi₀⟩ := hz₀_sec.1.1 s.length
  have hv₀_cand : HasSectionPrefix T M (s ++ [v₀]) := by
    refine ⟨z₀, hz₀_sec, fun j hj ↦ ?_⟩
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
    · rw [List.getElem_append_left hlt]
      exact hz₀_pre j hlt
    · simp [v₀]
  let P : ι → Prop := fun v ↦ v ∈ (T i₀).subtreeAt v₀ ∧ HasSectionPrefix T M (s ++ [v])
  obtain ⟨v, ⟨hv_sub, hv_cand⟩, hv_min⟩ :=
    exists_minimalFor_of_wellFoundedLT P (fun w ↦ ((T i₀).subtreeAt w).card)
      ⟨v₀, (T i₀).self_mem_subtreeAt hi₀, hv₀_cand⟩
  refine ⟨v, hv_cand, fun i hvi x hxv hne hxcand ↦ ?_⟩
  have hii₀ : i = i₀ :=
    tree_eq_of_mem_verts hdisj hvi ((T i₀).subtreeAt_subset_verts v₀ hv_sub)
  subst hii₀
  have hreaches_v₀_v : (T i).Reaches v₀ v := (T i).mem_subtreeAt.1 hv_sub
  have hreaches_v_x : (T i).Reaches v x := (T i).mem_subtreeAt.1 hxv
  have hxP : P x :=
    ⟨(T i).mem_subtreeAt.2 (hreaches_v₀_v.trans (T i) hreaches_v_x), hxcand⟩
  have hlt_card : ((T i).subtreeAt x).card < ((T i).subtreeAt v).card :=
    (T i).subtreeAt_card_lt_of_reaches_of_ne hreaches_v_x hne.symm
  have hle_card := hv_min hxP (le_of_lt hlt_card)
  dsimp only at hle_card
  omega

private noncomputable def chooseNext (T : ℕ → RootedTree ι) (M : SimpleGraph ι) (s : List ι) : ι :=
  by
    classical
    exact if h : ∃ v : ι, HasSectionPrefix T M (s ++ [v]) ∧
        ∀ i, v ∈ (T i).verts → ∀ x ∈ (T i).subtreeAt v, x ≠ v →
          ¬ HasSectionPrefix T M (s ++ [x])
      then h.choose
      else (T 0).root

private noncomputable def sectionPrefix (T : ℕ → RootedTree ι) (M : SimpleGraph ι) : ℕ → List ι
  | 0 => []
  | k + 1 =>
    sectionPrefix T M k ++ [chooseNext T M (sectionPrefix T M k)]

/-- The inductively defined sequence `x₁, x₂, …` in the proof of (2.1) (page 231). -/
noncomputable def minimalSectionSeq (T : ℕ → RootedTree ι) (M : SimpleGraph ι) (k : ℕ) : ι :=
  chooseNext T M (sectionPrefix T M k)

private theorem length_sectionPrefix (T : ℕ → RootedTree ι) (M : SimpleGraph ι) :
    ∀ k : ℕ, (sectionPrefix T M k).length = k
  | 0 => rfl
  | k + 1 => by simp [sectionPrefix, length_sectionPrefix T M k]

private theorem getElem_sectionPrefix (T : ℕ → RootedTree ι) (M : SimpleGraph ι) :
    ∀ (k j : ℕ) (hj : j < (sectionPrefix T M k).length),
      (sectionPrefix T M k)[j] = minimalSectionSeq T M j
  | 0, _, hj => by contradiction
  | k + 1, j, hj => by
    have hlen : (sectionPrefix T M k).length = k := length_sectionPrefix T M k
    rw [length_sectionPrefix] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
    · have hlt' : j < (sectionPrefix T M k).length := hlen.symm ▸ hlt
      simp only [sectionPrefix, List.getElem_append_left hlt']
      exact getElem_sectionPrefix T M k j hlt'
    · simp [sectionPrefix, minimalSectionSeq, hlen]

private theorem hasSectionPrefix_sectionPrefix {T : ℕ → RootedTree ι} {M : SimpleGraph ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    (hsec : ∃ z, IsSection T M z) :
    ∀ k : ℕ, HasSectionPrefix T M (sectionPrefix T M k)
  | 0 => by
    obtain ⟨z, hz⟩ := hsec
    exact ⟨z, hz, fun _ hj ↦ by contradiction⟩
  | k + 1 => by
    have hk := hasSectionPrefix_sectionPrefix hdisj hsec k
    have hex := exists_minimal_section_step hdisj hk
    simp only [sectionPrefix, chooseNext, hex, ↓reduceDIte]
    exact hex.choose_spec.1

/-- Graph Minors IV, (2.1), claim (1) (page 231): for each `k`, there is a section whose first `k`
terms are `x₀, …, x_{k-1}`. -/
theorem lemma_2_1_claim_1 {T : ℕ → RootedTree ι} {M : SimpleGraph ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    (hsec : ∃ z, IsSection T M z) (k : ℕ) :
    ∃ z : ℕ → ι, IsSection T M z ∧ ∀ j < k, z j = minimalSectionSeq T M j := by
  obtain ⟨z, hz, hpre⟩ := hasSectionPrefix_sectionPrefix hdisj hsec k
  refine ⟨z, hz, fun j hjk ↦ ?_⟩
  have hjk' : j < (sectionPrefix T M k).length := (length_sectionPrefix T M k).symm ▸ hjk
  rw [hpre j hjk', getElem_sectionPrefix T M k j hjk']

/-- Graph Minors IV, (2.1), claim (2) (page 231): for each `k`, there is no section whose first
terms are `x₀, …, x_{k-1}, x` for any `x ∈ V(T^{x_k}) - {x_k}`. -/
theorem lemma_2_1_claim_2 {T : ℕ → RootedTree ι} {M : SimpleGraph ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    (hsec : ∃ z, IsSection T M z) (k i : ℕ)
    (hvi : minimalSectionSeq T M k ∈ (T i).verts)
    {x : ι} (hx : x ∈ (T i).subtreeAt (minimalSectionSeq T M k))
    (hne : x ≠ minimalSectionSeq T M k) :
    ¬ ∃ z : ℕ → ι, IsSection T M z ∧ (∀ j < k, z j = minimalSectionSeq T M j) ∧ z k = x := by
  have hk := hasSectionPrefix_sectionPrefix hdisj hsec k
  have hex := exists_minimal_section_step hdisj hk
  have hchoose : minimalSectionSeq T M k = hex.choose := by
    simp only [minimalSectionSeq, chooseNext, hex, ↓reduceDIte]
  have hnot : ¬ HasSectionPrefix T M (sectionPrefix T M k ++ [x]) := by
    rw [hchoose] at hvi hx hne
    exact hex.choose_spec.2 i hvi x hx hne
  rintro ⟨z, hz_sec, hz_pre, hzk⟩
  apply hnot
  refine ⟨z, hz_sec, fun j hj ↦ ?_⟩
  have hlen : (sectionPrefix T M k).length = k := length_sectionPrefix T M k
  rw [List.length_append, hlen, List.length_singleton] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
  · have hlt' : j < (sectionPrefix T M k).length := hlen.symm ▸ hlt
    rw [List.getElem_append_left hlt', getElem_sectionPrefix T M k j hlt', hz_pre j hlt]
  · simp [hlen, hzk]

/-- Graph Minors IV, (2.1), claim (3) (page 231): `x₁, x₂, …` is a section. -/
theorem lemma_2_1_claim_3 {T : ℕ → RootedTree ι} {M : SimpleGraph ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    (hsec : ∃ z, IsSection T M z) :
    IsSection T M (minimalSectionSeq T M) := by
  have hV₀ : ∀ j, minimalSectionSeq T M j ∈ V₀ T := by
    intro j
    obtain ⟨z, hz, hj⟩ := lemma_2_1_claim_1 hdisj hsec (j + 1)
    rw [← hj j (Nat.lt_succ_self j)]
    exact hz.2.1 j
  have hinc : IsIncreasing T (minimalSectionSeq T M) := by
    refine ⟨fun j ↦ Set.mem_iUnion.1 (Set.sdiff_subset (hV₀ j)),
      fun j j' i i' hlt hi hi' ↦ ?_⟩
    obtain ⟨z, hz, hj⟩ := lemma_2_1_claim_1 hdisj hsec (j' + 1)
    have hzj : z j = minimalSectionSeq T M j := hj j (Nat.lt_succ_of_lt hlt)
    have hzj' : z j' = minimalSectionSeq T M j' := hj j' (Nat.lt_succ_self j')
    exact hz.1.2 hlt (hzj.symm ▸ hi) (hzj'.symm ▸ hi')
  refine ⟨hinc, hV₀, ?_⟩
  rintro _ ⟨j₁, rfl⟩ _ ⟨j₂, rfl⟩ hne
  rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
  · obtain ⟨z, hz, hj⟩ := lemma_2_1_claim_1 hdisj hsec (j₂ + 1)
    have hzj₁ : z j₁ = minimalSectionSeq T M j₁ := hj j₁ (Nat.lt_succ_of_lt hlt)
    have hzj₂ : z j₂ = minimalSectionSeq T M j₂ := hj j₂ (Nat.lt_succ_self j₂)
    rw [← hzj₁, ← hzj₂]
    exact hz.2.2 ⟨j₁, rfl⟩ ⟨j₂, rfl⟩ (hzj₁.symm ▸ hzj₂.symm ▸ hne)
  · exact absurd rfl hne
  · obtain ⟨z, hz, hj⟩ := lemma_2_1_claim_1 hdisj hsec (j₁ + 1)
    have hzj₁ : z j₁ = minimalSectionSeq T M j₁ := hj j₁ (Nat.lt_succ_self j₁)
    have hzj₂ : z j₂ = minimalSectionSeq T M j₂ := hj j₂ (Nat.lt_succ_of_lt hgt)
    rw [← hzj₁, ← hzj₂]
    exact hz.2.2 ⟨j₁, rfl⟩ ⟨j₂, rfl⟩ (hzj₁.symm ▸ hzj₂.symm ▸ hne)

/-- Graph Minors IV, (2.1), claim (4) (page 231): for `j < j'`, if `z` is the head of an edge of
some `Tᵢ` with tail `x_{j'}`, then `x_j` is not `M`-adjacent to `z`. -/
theorem lemma_2_1_claim_4 {T : ℕ → RootedTree ι} {M : SimpleGraph ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    (hM : ∀ i i', i < i' → ∀ u ∈ (T i).verts, ∀ w ∈ (T i').verts, ∀ v,
      M.Adj u w → v ≠ (T i').root → (T i').Reaches v w → M.Adj u v)
    (hsec : ∃ z, IsSection T M z) {j j' i : ℕ} (hlt : j < j')
    {z : ι} (hz_edge : z ∈ (T i).edges)
    (hz_parent : (T i).parent z = minimalSectionSeq T M j') :
    ¬ M.Adj (minimalSectionSeq T M j) z := by
  have hx_sec := lemma_2_1_claim_3 hdisj hsec
  have hz_verts : z ∈ (T i).verts := (T i).mem_verts_of_mem_edges hz_edge
  have hxj'_verts : minimalSectionSeq T M j' ∈ (T i).verts :=
    hz_parent ▸ (T i).parent_mem z hz_verts
  obtain ⟨i₀, hxj_verts⟩ := hx_sec.1.1 j
  have hi₀_lt_i : i₀ < i := hx_sec.1.2 hlt hxj_verts hxj'_verts
  have hxj'_ne_root : minimalSectionSeq T M j' ≠ (T i).root := by
    intro hr
    exact (hx_sec.2.1 j').2 ⟨i, hr.symm⟩
  have hreaches : (T i).Reaches (minimalSectionSeq T M j') z :=
    hz_parent ▸ (T i).reaches_parent hz_verts
  intro hadj
  have hadj_x : M.Adj (minimalSectionSeq T M j) (minimalSectionSeq T M j') :=
    hM i₀ i hi₀_lt_i _ hxj_verts z hz_verts _ hadj hxj'_ne_root hreaches
  have hne : minimalSectionSeq T M j ≠ minimalSectionSeq T M j' :=
    (hx_sec.1.injective hdisj).ne (ne_of_lt hlt)
  exact hx_sec.2.2 ⟨j, rfl⟩ ⟨j', rfl⟩ hne hadj_x

/-- Graph Minors IV, (2.1), claim (5) (page 231): let `Y` be the set of heads of all edges of
`T₁ ∪ T₂ ∪ ⋯` with tails in `{x₁, x₂, …}`; then no sequence of elements of `Y` is a section. -/
theorem lemma_2_1_claim_5 {T : ℕ → RootedTree ι} {M : SimpleGraph ι}
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    (hM : ∀ i i', i < i' → ∀ u ∈ (T i).verts, ∀ w ∈ (T i').verts, ∀ v,
      M.Adj u w → v ≠ (T i').root → (T i').Reaches v w → M.Adj u v)
    (hsec : ∃ z, IsSection T M z)
    (y : ℕ → ι)
    (hy : ∀ j, ∃ i, y j ∈ (T i).edges ∧ (T i).parent (y j) ∈ Set.range (minimalSectionSeq T M)) :
    ¬ IsSection T M y := by
  intro hy_sec
  have hx_sec := lemma_2_1_claim_3 hdisj hsec
  obtain ⟨i₀, hy₀_edge, k, hy₀_parent⟩ := hy 0
  have hy₀_verts : y 0 ∈ (T i₀).verts := (T i₀).mem_verts_of_mem_edges hy₀_edge
  have hxk_verts : minimalSectionSeq T M k ∈ (T i₀).verts :=
    hy₀_parent ▸ (T i₀).parent_mem (y 0) hy₀_verts
  let w : ℕ → ι := fun j ↦ if j < k then minimalSectionSeq T M j else y (j - k)
  have hw_sec : IsSection T M w := by
    have hw_V₀ : ∀ j, w j ∈ V₀ T := by
      intro j
      dsimp only [w]
      split_ifs with hjk
      · exact hx_sec.2.1 j
      · exact hy_sec.2.1 (j - k)
    have hw_inc : IsIncreasing T w := by
      refine ⟨fun j ↦ Set.mem_iUnion.1 (Set.sdiff_subset (hw_V₀ j)),
        fun j₁ j₂ i₁ i₂ hlt hi₁ hi₂ ↦ ?_⟩
      dsimp only [w] at hi₁ hi₂
      split_ifs at hi₁ hi₂ with hj₁ hj₂ hj₂
      · exact hx_sec.1.2 hlt hi₁ hi₂
      · have hi₁_lt_i₀ : i₁ < i₀ := hx_sec.1.2 hj₁ hi₁ hxk_verts
        have hi₀_le_i₂ : i₀ ≤ i₂ :=
          hy_sec.1.le_of_le hdisj (Nat.zero_le (j₂ - k)) hy₀_verts hi₂
        omega
      · omega
      · exact hy_sec.1.2 (by omega : j₁ - k < j₂ - k) hi₁ hi₂
    refine ⟨hw_inc, hw_V₀, ?_⟩
    have hadj_lt : ∀ j₁ j₂, j₁ < j₂ → ¬ M.Adj (w j₁) (w j₂) := by
      intro j₁ j₂ hlt
      dsimp only [w]
      split_ifs with hj₁ hj₂ hj₂
      · have hne : minimalSectionSeq T M j₁ ≠ minimalSectionSeq T M j₂ :=
          (hx_sec.1.injective hdisj).ne (ne_of_lt hlt)
        exact hx_sec.2.2 ⟨j₁, rfl⟩ ⟨j₂, rfl⟩ hne
      · obtain ⟨i₂, hy_edge, m, hy_parent⟩ := hy (j₂ - k)
        have hy_verts : y (j₂ - k) ∈ (T i₂).verts := (T i₂).mem_verts_of_mem_edges hy_edge
        have hxm_verts : minimalSectionSeq T M m ∈ (T i₂).verts :=
          hy_parent ▸ (T i₂).parent_mem _ hy_verts
        have hi₀_le_i₂ : i₀ ≤ i₂ :=
          hy_sec.1.le_of_le hdisj (Nat.zero_le (j₂ - k)) hy₀_verts hy_verts
        have hk_le_m : k ≤ m :=
          hx_sec.1.index_le_of_tree_le hxk_verts hxm_verts hi₀_le_i₂
        exact lemma_2_1_claim_4 hdisj hM hsec (Nat.lt_of_lt_of_le hj₁ hk_le_m) hy_edge
          hy_parent.symm
      · omega
      · have hlt' : j₁ - k < j₂ - k := by omega
        have hne : y (j₁ - k) ≠ y (j₂ - k) := (hy_sec.1.injective hdisj).ne (ne_of_lt hlt')
        exact hy_sec.2.2 ⟨j₁ - k, rfl⟩ ⟨j₂ - k, rfl⟩ hne
    rintro _ ⟨j₁, rfl⟩ _ ⟨j₂, rfl⟩ hne hadj
    rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
    · exact hadj_lt j₁ j₂ hlt hadj
    · exact hne rfl
    · exact hadj_lt j₂ j₁ hgt hadj.symm
  have hy₀_sub : y 0 ∈ (T i₀).subtreeAt (minimalSectionSeq T M k) :=
    (T i₀).mem_subtreeAt.2 (hy₀_parent ▸ (T i₀).reaches_parent hy₀_verts)
  have hy₀_ne : y 0 ≠ minimalSectionSeq T M k :=
    hy₀_parent ▸ ((T i₀).parent_ne_self hy₀_edge).symm
  refine lemma_2_1_claim_2 hdisj hsec k i₀ hxk_verts hy₀_sub hy₀_ne ⟨w, hw_sec, ?_, ?_⟩
  · intro j hjk
    simp [w, hjk]
  · simp [w]

/-- Graph Minors IV, (2.1) (page 230). Let `T₁, T₂, …` be a countable sequence of disjoint trees,
and `M` be a graph on their vertices such that whenever `i < i'`, `u ∈ V(Tᵢ)` is `M`-adjacent to
`w ∈ V(T_{i'})`, and `v ∈ V(T_{i'}) - {o(T_{i'})}` lies on the path of `T_{i'}` from `o(T_{i'})`
to `w`, `u` is `M`-adjacent to `v`. If `{o(T₁), o(T₂), …}` is `M`-stable, then there is an infinite
`M`-stable set `X ⊆ ⋃ᵢ V(Tᵢ)` meeting each `V(Tᵢ)` in at most one vertex such that the set of heads
of all edges of `T₁ ∪ T₂ ∪ ⋯` with tails in `X` is `M`-rich. -/
theorem lemma_2_1 (T : ℕ → RootedTree ι) (M : SimpleGraph ι)
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    (hM : ∀ i i', i < i' → ∀ u ∈ (T i).verts, ∀ w ∈ (T i').verts, ∀ v,
      M.Adj u w → v ≠ (T i').root → (T i').Reaches v w → M.Adj u v)
    (hroot : M.IsIndepSet (Set.range fun i ↦ (T i).root)) :
    ∃ X : Set ι, X.Infinite ∧ M.IsIndepSet X ∧ X ⊆ ⋃ i, ((T i).verts : Set ι) ∧
      (∀ i, (X ∩ (T i).verts).Subsingleton) ∧
      IsRich M {v | ∃ i, v ∈ (T i).edges ∧ (T i).parent v ∈ X} := by
  by_cases hsec : ∃ z, IsSection T M z
  · have hx_sec := lemma_2_1_claim_3 hdisj hsec
    refine ⟨Set.range (minimalSectionSeq T M), hx_sec.1.infinite_range hdisj, hx_sec.2.2,
      hx_sec.1.range_subset, hx_sec.1.subsingleton_inter, ?_⟩
    refine isRich_of_no_section hdisj ?_ fun y hy ↦ lemma_2_1_claim_5 hdisj hM hsec y hy
    rintro v ⟨i, hve, -⟩
    exact (mem_V₀_iff hdisj).2 ⟨i, hve⟩
  · push Not at hsec
    have hinc_root : IsIncreasing T (fun i ↦ (T i).root) := by
      refine ⟨fun i ↦ ⟨i, (T i).root_mem⟩, fun j j' i i' hlt hi hi' ↦ ?_⟩
      have hji : j = i := tree_eq_of_mem_verts hdisj (T j).root_mem hi
      have hj'i' : j' = i' := tree_eq_of_mem_verts hdisj (T j').root_mem hi'
      omega
    refine ⟨Set.range fun i ↦ (T i).root, hinc_root.infinite_range hdisj, hroot,
      hinc_root.range_subset, hinc_root.subsingleton_inter, ?_⟩
    have hrich_V₀ : IsRich M (V₀ T) :=
      isRich_of_no_section hdisj Set.Subset.rfl fun z _ ↦ hsec z
    refine hrich_V₀.mono ?_
    rintro v ⟨i, hve, -⟩
    exact (mem_V₀_iff hdisj).2 ⟨i, hve⟩

end GraphMinor.GM04
