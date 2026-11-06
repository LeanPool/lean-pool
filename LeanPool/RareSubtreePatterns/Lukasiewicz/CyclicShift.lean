/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Lukasiewicz.Coding
public import LeanPool.RareSubtreePatterns.Bienayme.Defs
public import Mathlib.Data.Set.Finite.List

import Mathlib.Tactic.Linarith

/-!
# Cyclic shifts of DFS sequences and the walk bridge

The combinatorial core of `eq:shifts` (source lines 718–730), as used in Lemma `lem:RW` and
Corollary `cor:cyclicshift` (source lines 751–831).

* `Lukasiewicz.bridgeSet n` is the set of sequences `(x_1, …, x_n)` of integers `≥ -1` with
  `x_1 + ⋯ + x_n = -1`, i.e. the possible values of `(X_1, …, X_n)` on `{S_n = -1}`. It is
  finite (`Lukasiewicz.bridgeSet_finite`), and so is the set of trees with `n` vertices
  (`PlaneTree.finite_vertexCount_eq`).
* `(T, i) ↦ 𝐱^{(i)}(T)`, the `i`-th cyclic shift of the DFS sequence, is a bijection from
  `{trees with n vertices} × {0, …, n-1}` onto `bridgeSet n` (`PlaneTree.shiftEquiv`), by the
  cycle lemma and the Łukasiewicz coding.
* The Bienaymé weight of `T` is the product of the step masses `μ_{x+1}` along any cyclic shift
  of `𝐱(T)` (`PlaneTree.weight_eq_prod_rotate`), which gives the weighted form of `eq:shifts`
  (`PlaneTree.tsum_sum_weight_mul_rotate`) and the Kemperman/Dwass identity
  `n · P(|𝒯| = n) = P(S_n = -1)` (`PlaneTree.natCast_mul_tsum_weight_eq`).
-/

@[expose] public section

open scoped ENNReal

namespace PoissonDeclumping

namespace Lukasiewicz

/-- The sequences `(x_1, …, x_n) ∈ ℤ_{≥ -1}^n` with `x_1 + ⋯ + x_n = -1`. -/
def bridgeSet (n : ℕ) : Set (List ℤ) := {x | x.length = n ∧ (∀ a ∈ x, -1 ≤ a) ∧ x.sum = -1}

/-- Lists of a fixed length with entries in a finite set form a finite set. -/
theorem finite_length_eq_of_mem {s : Set ℤ} (hs : s.Finite) (n : ℕ) :
    {x : List ℤ | x.length = n ∧ ∀ a ∈ x, a ∈ s}.Finite := by
  have := hs.to_subtype
  refine ((List.finite_length_eq s n).image (List.map Subtype.val)).subset ?_
  rintro x ⟨hl, hx⟩
  refine ⟨x.attach.map fun a => ⟨a.1, hx a.1 a.2⟩, by simp [hl], ?_⟩
  simp [List.map_map, Function.comp_def]

/-- Every entry of a bridge sequence of length `n` is at most `n`. -/
theorem le_of_mem_bridgeSet {n : ℕ} {x : List ℤ} (hx : x ∈ bridgeSet n) {a : ℤ} (ha : a ∈ x) :
    a ≤ n := by
  obtain ⟨hl, hge, hs⟩ := hx
  have hp := List.perm_cons_erase ha
  have hsum := hp.sum_eq
  rw [List.sum_cons, hs] at hsum
  have hb := neg_length_le_sum (l := x.erase a) (fun b hb => hge b (List.mem_of_mem_erase hb))
  rw [List.length_erase_of_mem ha, hl] at hb
  have : (((n - 1 : ℕ) : ℤ)) ≤ n := by omega
  linarith

theorem bridgeSet_finite (n : ℕ) : (bridgeSet n).Finite := by
  refine (finite_length_eq_of_mem (Set.finite_Icc (-1 : ℤ) n) n).subset ?_
  intro x hx
  exact ⟨hx.1, fun a ha => ⟨hx.2.1 a ha, le_of_mem_bridgeSet hx ha⟩⟩

instance (n : ℕ) : Finite (bridgeSet n) := (bridgeSet_finite n).to_subtype

theorem one_le_of_mem_bridgeSet {n : ℕ} {x : List ℤ} (hx : x ∈ bridgeSet n) : 1 ≤ n := by
  obtain ⟨hl, -, hs⟩ := hx
  rcases x with _ | ⟨a, x⟩
  · simp at hs
  · simp at hl
    omega

/-- Undoing a rotation: `(l.rotate i).rotate ((|l| - i) % |l|) = l` for `i < |l|`. -/
theorem rotate_rotate_sub_mod {α : Type*} (l : List α) {i : ℕ} (hi : i < l.length) :
    (l.rotate i).rotate ((l.length - i) % l.length) = l := by
  rw [List.rotate_rotate]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · rw [Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel' hi.le, List.rotate_length]

theorem sub_mod_sub_mod {n i : ℕ} (hi : i < n) : (n - (n - i) % n) % n = i := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · rw [Nat.mod_eq_of_lt (by omega : n - i < n), Nat.sub_sub_self hi.le, Nat.mod_eq_of_lt hi]

end Lukasiewicz

namespace PlaneTree

open Lukasiewicz

/-- Every cyclic shift of `𝐱(T)` is a bridge sequence of length `|T|`. -/
theorem rotate_dfsSeq_mem_bridgeSet (T : PlaneTree) (i : ℕ) :
    T.dfsSeq.rotate i ∈ bridgeSet T.vertexCount :=
  ⟨by rw [List.length_rotate, length_dfsSeq],
    fun a ha => neg_one_le_of_mem_dfsSeq (List.mem_rotate.mp ha),
    by rw [(List.rotate_perm _ _).sum_eq, sum_dfsSeq]⟩

/-- There are finitely many plane trees with `n` vertices. -/
theorem finite_vertexCount_eq (n : ℕ) : {T : PlaneTree | T.vertexCount = n}.Finite := by
  refine Set.Finite.of_finite_image ((bridgeSet_finite n).subset ?_)
    (dfsSeq_injective.injOn)
  rintro _ ⟨T, hT, rfl⟩
  have := rotate_dfsSeq_mem_bridgeSet T 0
  rwa [List.rotate_zero, hT] at this

instance (n : ℕ) : Finite {T : PlaneTree // T.vertexCount = n} :=
  (finite_vertexCount_eq n).to_subtype

/-- The cyclic-shift map `(T, i) ↦ 𝐱^{(i)}(T)` on trees with `n` vertices. -/
def shiftMap (n : ℕ) : {T : PlaneTree // T.vertexCount = n} × Fin n → bridgeSet n :=
  fun p => ⟨p.1.1.dfsSeq.rotate p.2, by
    have := rotate_dfsSeq_mem_bridgeSet p.1.1 p.2
    rwa [p.1.2] at this⟩

@[simp] theorem coe_shiftMap (n : ℕ) (p : {T : PlaneTree // T.vertexCount = n} × Fin n) :
    (shiftMap n p : List ℤ) = p.1.1.dfsSeq.rotate p.2 := rfl

/-- **Cyclic shifts and the walk bridge.** `(T, i) ↦ 𝐱^{(i)}(T)` is a bijection from
`{T : |T| = n} × {0, …, n-1}` onto the sequences in `ℤ_{≥ -1}^n` with sum `-1`. -/
theorem shiftMap_bijective (n : ℕ) : Function.Bijective (shiftMap n) := by
  constructor
  · rintro ⟨⟨T, hT⟩, i⟩ ⟨⟨U, hU⟩, j⟩ h
    have h' : T.dfsSeq.rotate i = U.dfsSeq.rotate j := congrArg Subtype.val h
    have hn : 1 ≤ n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
    set x := T.dfsSeq.rotate i with hx
    have hTl : T.dfsSeq.length = n := by rw [length_dfsSeq, hT]
    have hUl : U.dfsSeq.length = n := by rw [length_dfsSeq, hU]
    have hxl : x.length = n := by rw [hx, List.length_rotate, hTl]
    have hxT : x.rotate ((n - i) % n) = T.dfsSeq := by
      have := rotate_rotate_sub_mod T.dfsSeq (i := i) (by rw [hTl]; exact i.2)
      rwa [hTl] at this
    have hxU : x.rotate ((n - j) % n) = U.dfsSeq := by
      have := rotate_rotate_sub_mod U.dfsSeq (i := j) (by rw [hUl]; exact j.2)
      rw [hUl] at this
      rw [h', this]
    have hmem := rotate_dfsSeq_mem_bridgeSet T i
    rw [hT, ← hx] at hmem
    obtain ⟨-, hge, hs⟩ := hmem
    obtain ⟨k, -, huniq⟩ := existsUnique_zeta_rotate_eq_length hge (by omega) hs
    have hi' := huniq ((n - i) % n)
      ⟨by rw [hxl]; exact Nat.mod_lt _ (by omega), by rw [hxT, zeta_dfsSeq, hT, hxl]⟩
    have hj' := huniq ((n - j) % n)
      ⟨by rw [hxl]; exact Nat.mod_lt _ (by omega), by rw [hxU, zeta_dfsSeq, hU, hxl]⟩
    have hij : (i : ℕ) = j := by
      rw [← sub_mod_sub_mod i.2, ← sub_mod_sub_mod j.2, hi', hj']
    have hTU : T = U := dfsSeq_injective (by rw [← hxT, ← hxU, hi', hj'])
    subst hTU
    exact Prod.ext rfl (Fin.ext hij)
  · rintro ⟨x, hxl, hge, hs⟩
    have hn : 1 ≤ n := one_le_of_mem_bridgeSet ⟨hxl, hge, hs⟩
    obtain ⟨k, ⟨hk, hz⟩, -⟩ := existsUnique_zeta_rotate_eq_length hge (by omega) hs
    obtain ⟨T, hT, hTn⟩ := exists_dfsSeq_eq_take
      (fun a ha => hge a (List.mem_rotate.mp ha)) hz
    rw [List.take_of_length_le (by rw [List.length_rotate])] at hT
    refine ⟨(⟨T, by rw [hTn, hxl]⟩, ⟨(n - k) % n, Nat.mod_lt _ (by omega)⟩), ?_⟩
    apply Subtype.ext
    simp only [coe_shiftMap, hT]
    rw [← hxl]
    exact rotate_rotate_sub_mod x hk

/-- The bijection `(T, i) ↦ 𝐱^{(i)}(T)` behind `eq:shifts`. -/
noncomputable def shiftEquiv (n : ℕ) :
    {T : PlaneTree // T.vertexCount = n} × Fin n ≃ bridgeSet n :=
  Equiv.ofBijective _ (shiftMap_bijective n)

@[simp] theorem coe_shiftEquiv_apply (n : ℕ) (p : {T : PlaneTree // T.vertexCount = n} × Fin n) :
    (shiftEquiv n p : List ℤ) = p.1.1.dfsSeq.rotate p.2 := rfl

/-- The Bienaymé weight is the product of the step masses `P(X = x) = μ_{x+1}` along the DFS
sequence. -/
theorem weight_eq_prod_dfsSeq (μ : PMF ℕ) (T : PlaneTree) :
    weight μ T = (T.dfsSeq.map fun a => μ (a + 1).toNat).prod := by
  simp [weight, dfsSeq, List.map_map, Function.comp_def]

/-- The Bienaymé weight is the product of the step masses along any cyclic shift of the DFS
sequence: the weight of `(T, i)` equals the walk weight of its image `𝐱^{(i)}(T)`. -/
theorem weight_eq_prod_rotate (μ : PMF ℕ) (T : PlaneTree) (i : ℕ) :
    weight μ T = ((T.dfsSeq.rotate i).map fun a => μ (a + 1).toNat).prod := by
  rw [weight_eq_prod_dfsSeq, List.map_rotate, (List.rotate_perm _ _).prod_eq]

/-- **Weighted form of `eq:shifts`.** For every test function `g`, summing
`P_μ(T) g(𝐱^{(i)}(T))` over trees with `n` vertices and shifts `i < n` gives the sum of
`P(X_1 = x_1, …, X_n = x_n) g(𝐱)` over sequences `𝐱 ∈ ℤ_{≥ -1}^n` with sum `-1`. -/
theorem tsum_sum_weight_mul_rotate (μ : PMF ℕ) (n : ℕ) (g : List ℤ → ℝ≥0∞) :
    ∑' T : {T : PlaneTree // T.vertexCount = n}, ∑ i : Fin n,
        weight μ T.1 * g (T.1.dfsSeq.rotate i) =
      ∑' x : bridgeSet n, (x.1.map fun a => μ (a + 1).toNat).prod * g x.1 := by
  rw [← (shiftEquiv n).tsum_eq]
  simp_rw [← tsum_fintype (L := SummationFilter.unconditional (Fin n))]
  rw [← ENNReal.tsum_prod]
  refine tsum_congr fun p => ?_
  rw [coe_shiftEquiv_apply, ← weight_eq_prod_rotate]

/-- **Kemperman / Dwass identity** (`n · P(|𝒯| = n) = P(S_n = -1)`), in terms of weights. -/
theorem natCast_mul_tsum_weight_eq (μ : PMF ℕ) (n : ℕ) :
    (n : ℝ≥0∞) * ∑' T : PlaneTree, (if T.vertexCount = n then weight μ T else 0) =
      ∑' x : bridgeSet n, (x.1.map fun a => μ (a + 1).toNat).prod := by
  have h := tsum_sum_weight_mul_rotate μ n (fun _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.tsum_mul_left] at h
  rw [← h]
  congr 1
  symm
  refine (tsum_subtype {T : PlaneTree | T.vertexCount = n} (weight μ)).trans ?_
  refine tsum_congr fun T => ?_
  simp [Set.indicator_apply]

end PlaneTree

end PoissonDeclumping
