/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Applications.TreeSurgery
public import LeanPool.RareSubtreePatterns.Patterns.Complete

/-!
# Replacing a fringe subtree inside a root occurrence of `H_{r,k}`

Deterministic part of the proofs of Lemmas `lem:S_rary`(ii) and `lem:C_rary` (source lines
2670–2753 and 2768–2792; inventory P19, P21). Let `H_{r,k} ≺ T` (`r ≥ 1`) and let `u` be the
vertex of DFS index `ℓ` of `T`.

* `embeds_completeTree_replaceAt` (P21): if `k_u(T) ≠ r`, then `u` is not an internal vertex of the
  displayed copy of `H_{r,k}`, and replacing `T_u` by any tree preserves `H_{r,k} ≺ T`.
* `ReplaceClass r k T ℓ j` (P19): after replacing `T_u` by `S`, `H_{r,k} ≺ T[S/T_u]` holds iff
  `H_{r,j} ≺ S`. `exists_replaceClass`: every position has such a class `j ≤ k` — `j = 0` when `u`
  is a leaf of the displayed skeleton or lies in the grafted forest, `j = k - a` when `u` is an
  internal skeleton vertex at depth `a` (the paper's "the displayed skeleton already provides a
  complete `r`-ary continuation of height `k - a`").
* `classCount_le` (P19, the count of skeleton vertices): for `j ≥ 1` at most
  `r^{k-j}` positions of `T` are of class `j` (there are `r^a` skeleton vertices at depth `a`).
-/

@[expose] public section

open scoped ENNReal

namespace PoissonDeclumping.PlaneTree

/-- `Embeds (H_{r,a}) (H_{r,a})`. -/
theorem embeds_completeTree_self {r : ℕ} (hr : 1 ≤ r) : ∀ a : ℕ,
    Embeds (completeTree r a) (completeTree r a)
  | 0 => by simpa using Embeds.leaf (node [])
  | a + 1 => by
    rw [embeds_completeTree_succ_iff hr]
    refine ⟨by simp [completeTree_succ, rootDegree], fun U hU => ?_⟩
    rw [completeTree_succ, children_node] at hU
    rw [List.eq_of_mem_replicate hU]
    exact embeds_completeTree_self hr a

/-- `H_{r,a} ≺ H_{r,b}` implies `a ≤ b` (`r ≥ 1`). -/
theorem le_of_embeds_completeTree {r : ℕ} (hr : 1 ≤ r) : ∀ {a b : ℕ},
    Embeds (completeTree r a) (completeTree r b) → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | a + 1, 0, h => by
    rw [embeds_completeTree_succ_iff hr] at h
    simp [rootDegree] at h
    omega
  | a + 1, b + 1, h => by
    rw [embeds_completeTree_succ_iff hr] at h
    have hmem : completeTree r b ∈ (completeTree r (b + 1)).children := by
      rw [completeTree_succ, children_node]
      exact List.mem_replicate.2 ⟨by omega, rfl⟩
    have := le_of_embeds_completeTree hr (h.2 _ hmem)
    omega

/-- A leaf supports no `H_{r,j}` with `j ≥ 1` (`r ≥ 1`). -/
theorem not_embeds_completeTree_leaf {r j : ℕ} (hr : 1 ≤ r) (hj : 1 ≤ j) :
    ¬Embeds (completeTree r j) (node []) := by
  intro h
  have := le_of_embeds_completeTree hr (b := 0) (by simpa using h)
  omega

/-- **P21.** If `H_{r,k} ≺ T` and the vertex `u` of DFS index `ℓ` has `k_u(T) ≠ r`, then `u` is
not an internal vertex of the displayed copy of `H_{r,k}`, so arbitrary re-grafting at `u`
preserves `H_{r,k} ≺ ·` (source lines 2775–2783). Valid for every `r` (for `r = 0` the pattern is
a single vertex). -/
theorem embeds_completeTree_replaceAt {r : ℕ} : ∀ (k : ℕ) {T : PlaneTree} {ℓ : ℕ},
    Embeds (completeTree r k) T → ℓ < T.vertexCount → (fringeAt T ℓ).rootDegree ≠ r →
    ∀ S : PlaneTree, Embeds (completeTree r k) (replaceAt T ℓ S)
  | 0, T, ℓ, _, _, _, S => by simpa using Embeds.leaf (replaceAt T ℓ S)
  | k + 1, T, ℓ, hT, hℓ, hdeg, S => by
    rcases Nat.eq_zero_or_pos r with hr0 | hr
    · subst hr0
      simpa [completeTree_succ] using Embeds.leaf (replaceAt T ℓ S)
    rw [embeds_completeTree_succ_iff hr] at hT ⊢
    rcases ℓ with _ | ℓ
    · exact absurd hT.1 (by rwa [fringeAt_zero] at hdeg)
    obtain ⟨ts⟩ := T
    rw [vertexCount_node_eq] at hℓ
    obtain ⟨pre, t, post, q, rfl, hq, rfl⟩ := exists_append_of_lt_forestSize ts ℓ (by omega)
    rw [fringeAt_node_append pre post t hq] at hdeg
    rw [replaceAt_node_append pre post t hq]
    simp only [rootDegree_node, children_node, List.length_append, List.length_cons] at hT ⊢
    refine ⟨hT.1, fun U hU => ?_⟩
    rcases List.mem_append.1 hU with hU | hU
    · exact hT.2 U (List.mem_append_left _ hU)
    rcases List.mem_cons.1 hU with rfl | hU
    · exact embeds_completeTree_replaceAt k (hT.2 t (by simp)) hq hdeg S
    · exact hT.2 U (by simp [hU])

/-- The class `j` of the DFS position `ℓ` of `T` with respect to `H_{r,k}`: re-grafting any `S`
at the vertex `u_{ℓ+1}(T)` gives `H_{r,k} ≺ T[S/T_{u_{ℓ+1}}]` iff `H_{r,j} ≺ S`. -/
def ReplaceClass (r k : ℕ) (T : PlaneTree) (ℓ j : ℕ) : Prop :=
  ∀ S : PlaneTree, Embeds (completeTree r k) (replaceAt T ℓ S) ↔ Embeds (completeTree r j) S

/-- The class of a position inside a child: if `H_{r,k+1} ≺ node (pre ++ t :: post)`, the
position `forestSize pre + q + 1` has class `j` w.r.t. `H_{r,k+1}` iff the position `q` of `t`
has class `j` w.r.t. `H_{r,k}`. -/
theorem replaceClass_succ_node_append {r k : ℕ} (hr : 1 ≤ r) {pre post : List PlaneTree}
    {t : PlaneTree} (hT : Embeds (completeTree r (k + 1)) (node (pre ++ t :: post))) {q : ℕ}
    (hq : q < t.vertexCount) (j : ℕ) :
    ReplaceClass r (k + 1) (node (pre ++ t :: post)) (forestSize pre + q + 1) j ↔
      ReplaceClass r k t q j := by
  rw [embeds_completeTree_succ_iff hr] at hT
  simp only [rootDegree_node, children_node] at hT
  have key : ∀ S, Embeds (completeTree r (k + 1))
      (replaceAt (node (pre ++ t :: post)) (forestSize pre + q + 1) S) ↔
        Embeds (completeTree r k) (replaceAt t q S) := by
    intro S
    rw [replaceAt_node_append pre post t hq, embeds_completeTree_succ_iff hr]
    simp only [rootDegree_node, children_node]
    constructor
    · rintro ⟨-, h⟩
      exact h _ (by simp)
    · intro h
      refine ⟨by simpa using hT.1, fun U hU => ?_⟩
      rcases List.mem_append.1 hU with hU | hU
      · exact hT.2 U (List.mem_append_left _ hU)
      rcases List.mem_cons.1 hU with rfl | hU
      · exact h
      · exact hT.2 U (by simp [hU])
  simp only [ReplaceClass, key]

/-- At the root (`ℓ = 0`) the class is `k`, and only `k`. -/
theorem replaceClass_zero_iff {r k : ℕ} (hr : 1 ≤ r) (T : PlaneTree) (j : ℕ) :
    ReplaceClass r k T 0 j ↔ j = k := by
  constructor
  · intro h
    have h1 := (h (completeTree r j)).2 (embeds_completeTree_self hr j)
    have h2 := (h (completeTree r k)).1
      (by rw [replaceAt_zero]; exact embeds_completeTree_self hr k)
    rw [replaceAt_zero] at h1
    exact le_antisymm (le_of_embeds_completeTree hr h2) (le_of_embeds_completeTree hr h1)
  · rintro rfl S
    rw [replaceAt_zero]

/-- **Classification (P19).** If `H_{r,k} ≺ T` (`r ≥ 1`), every DFS position of `T` has a class
`j ≤ k`. -/
theorem exists_replaceClass {r : ℕ} (hr : 1 ≤ r) : ∀ (k : ℕ) {T : PlaneTree} {ℓ : ℕ},
    Embeds (completeTree r k) T → ℓ < T.vertexCount → ∃ j ≤ k, ReplaceClass r k T ℓ j
  | 0, T, ℓ, _, _ => ⟨0, le_rfl, fun S => by
      simp only [completeTree_zero]
      exact ⟨fun _ => Embeds.leaf S, fun _ => Embeds.leaf _⟩⟩
  | k + 1, T, ℓ, hT, hℓ => by
    rcases ℓ with _ | ℓ
    · exact ⟨k + 1, le_rfl, (replaceClass_zero_iff hr T _).2 rfl⟩
    obtain ⟨ts⟩ := T
    rw [vertexCount_node_eq] at hℓ
    obtain ⟨pre, t, post, q, rfl, hq, rfl⟩ := exists_append_of_lt_forestSize ts ℓ (by omega)
    have ht : Embeds (completeTree r k) t := by
      rw [embeds_completeTree_succ_iff hr] at hT
      exact hT.2 t (by simp)
    obtain ⟨j, hj, hcl⟩ := exists_replaceClass hr k ht hq
    exact ⟨j, by omega, (replaceClass_succ_node_append hr hT hq j).2 hcl⟩

/-- The number of DFS positions of `T` of class `j` (with respect to `H_{r,k}`). -/
noncomputable def classCount (r k : ℕ) (T : PlaneTree) (j : ℕ) : ℝ≥0∞ :=
  ∑ ℓ ∈ Finset.range T.vertexCount, {ℓ | ReplaceClass r k T ℓ j}.indicator 1 ℓ

/-- The bound `r^{k-j}` (for `j ≤ k`, else `0`) on the number of positions of class `j ≥ 1`:
the internal skeleton vertices at depth `k - j`. -/
def classBound (r k j : ℕ) : ℕ := if j ≤ k then r ^ (k - j) else 0

theorem indicator_one_eq_of_iff {α β : Type*} {s : Set α} {t : Set β} {a : α} {b : β}
    (h : a ∈ s ↔ b ∈ t) : s.indicator (1 : α → ℝ≥0∞) a = t.indicator 1 b := by
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (h.1 ha)]
    rfl
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem (fun hb => ha (h.2 hb))]

/-- **Count of skeleton positions (P19).** If `H_{r,k} ≺ T` (`r ≥ 1`) and `j ≥ 1`, at most
`r^{k-j}` DFS positions of `T` have class `j` (none if `j > k`). -/
theorem classCount_le {r : ℕ} (hr : 1 ≤ r) : ∀ (k : ℕ) {T : PlaneTree} {j : ℕ},
    Embeds (completeTree r k) T → 1 ≤ j → classCount r k T j ≤ classBound r k j
  | 0, T, j, _, hj => by
    have hnot : ∀ ℓ, ℓ ∉ {ℓ | ReplaceClass r 0 T ℓ j} := by
      intro ℓ h
      exact not_embeds_completeTree_leaf hr hj ((h (node [])).1 (by simpa using Embeds.leaf _))
    simp [classCount, Set.indicator_of_notMem (hnot _)]
  | k + 1, T, j, hT, hj => by
    obtain ⟨ts⟩ := T
    have hT' := hT
    rw [embeds_completeTree_succ_iff hr] at hT'
    simp only [rootDegree_node, children_node] at hT'
    rw [classCount, vertexCount_node_eq, Finset.sum_range_succ']
    have hdec : ∑ q ∈ Finset.range (forestSize ts),
        {ℓ | ReplaceClass r (k + 1) (node ts) ℓ j}.indicator 1 (q + 1) =
          (ts.map fun t => classCount r k t j).sum :=
      sum_range_forestSize ts _ _ fun pre t post q h1 h2 => by
        subst h1
        exact indicator_one_eq_of_iff (replaceClass_succ_node_append hr hT h2 j)
    rw [hdec]
    have hsum : (ts.map fun t => classCount r k t j).sum ≤ r * (classBound r k j : ℝ≥0∞) := by
      have := List.sum_le_length_nsmul (ts.map fun t => classCount r k t j)
        (classBound r k j : ℝ≥0∞) (fun x hx => by
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
          exact classCount_le hr k (hT'.2 t ht) hj)
      rwa [List.length_map, hT'.1, nsmul_eq_mul] at this
    by_cases hjk : j = k + 1
    · subst hjk
      have h0 : {ℓ | ReplaceClass r (k + 1) (node ts) ℓ (k + 1)}.indicator
          (1 : ℕ → ℝ≥0∞) 0 ≤ 1 := Set.indicator_le_self' (fun _ _ => zero_le) 0
      have hb : classBound r k (k + 1) = 0 := by simp [classBound]
      have hb' : classBound r (k + 1) (k + 1) = 1 := by simp [classBound]
      rw [hb] at hsum
      rw [hb']
      simp only [Nat.cast_zero, mul_zero, nonpos_iff_eq_zero] at hsum
      rw [hsum, zero_add]
      exact_mod_cast h0
    · have h0 : {ℓ | ReplaceClass r (k + 1) (node ts) ℓ j}.indicator (1 : ℕ → ℝ≥0∞) 0 = 0 :=
        Set.indicator_of_notMem (fun h => hjk ((replaceClass_zero_iff hr _ j).1 h)) _
      rw [h0, add_zero]
      refine hsum.trans ?_
      by_cases hjk' : j ≤ k
      · have e1 : classBound r k j = r ^ (k - j) := by simp [classBound, hjk']
        have e2 : classBound r (k + 1) j = r ^ (k + 1 - j) := by
          simp [classBound, show j ≤ k + 1 by omega]
        rw [e1, e2, show k + 1 - j = (k - j) + 1 by omega, pow_succ]
        push_cast
        rw [mul_comm]
      · have e1 : classBound r k j = 0 := by simp [classBound, hjk']
        rw [e1]
        simp

end PoissonDeclumping.PlaneTree
