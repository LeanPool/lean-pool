/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.SumOfSetsInSeveralDimensions.AffineDim
public import LeanPool.SumOfSetsInSeveralDimensions.LowerBoundFunction
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Fin
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Linarith
import LeanPool.SumOfSetsInSeveralDimensions.AffineDimSumset
import LeanPool.SumOfSetsInSeveralDimensions.LowerBound
import LeanPool.SumOfSetsInSeveralDimensions.LowerBoundValues

/-!
# Sets with a small sumset

Section 3 of Ruzsa's paper. Let `e₀, …, e_(d-1)` be the unit vectors of `ℝ^d`, let `1 ≤ m ≤ n`
and `n ≥ d + 1`, and put `t = n - m` and `c = d - 1 - t` when `t < d - 1`, `c = 0` otherwise. The
sets

* `B = {0, e₀, …, (n - d) e₀} ∪ {e₁, …, e_(d-1)}`,
* `A = {0, e₀, …, (m - 1 - c) e₀} ∪ {e₁, …, e_c}`

have `|A| = m`, `|B| = n`, `B` has affine dimension `d`, and `|A + B| = G_d(m, n)`. With
Ruzsa's theorem, this shows that `G_d(m, n)` is the least size of such a sumset.

The paper takes `A = {0, e₀, …, (m - 1) e₀}` when `t ≥ d`, which is the case `c = 0`. Its count
of `|A + B|` when `t < d` lists the sums `e_i + e_j` with `i, j ≤ c`, but the sums with `i ≤ c`
and `c < j` also occur; its final value `G_d(m, n)` is correct.

## Main definitions

* `axisUnionBasis e k c`: the set `{0, e₀, …, k e₀} ∪ {e₁, …, e_c}` in `ℝ^(e + 1)`.

## Main statements

* `exists_card_add_eq_sumsetCardLowerBound`: for `1 ≤ d`, `1 ≤ m ≤ n` and `d + 1 ≤ n`, there are
  `A, B ⊆ ℝ^d` with `|A| = m`, `|B| = n`, `B` of affine dimension `d` and `|A + B| = G_d(m, n)`.
-/

public section

namespace SumOfSetsInSeveralDimensions

open Finset
open scoped Pointwise

variable {e : ℕ}

/-- The points `i e₀` of `ℝ^(e + 1)` with `i ≤ k`. -/
noncomputable def axisPoints (e k : ℕ) : Finset (Fin (e + 1) → ℝ) :=
  (range (k + 1)).image fun i : ℕ ↦ Pi.single 0 (i : ℝ)

/-- The unit vectors `e_(j + 1)` of `ℝ^(e + 1)` with `j < c`. -/
noncomputable def unitVectors (e c : ℕ) : Finset (Fin (e + 1) → ℝ) :=
  ({j : Fin e | (j : ℕ) < c} : Finset (Fin e)).image fun j ↦ Pi.single j.succ 1

/-- The set `{0, e₀, …, k e₀} ∪ {e₁, …, e_c}` of `ℝ^(e + 1)`. -/
noncomputable def axisUnionBasis (e k c : ℕ) : Finset (Fin (e + 1) → ℝ) :=
  axisPoints e k ∪ unitVectors e c

lemma card_axisPoints (e k : ℕ) : #(axisPoints e k) = k + 1 := by
  rw [axisPoints, card_image_of_injective, card_range]
  intro a b h
  simpa using congr_fun h 0

lemma card_unitVectors {c : ℕ} (hc : c ≤ e) : #(unitVectors e c) = c := by
  rw [unitVectors, card_image_of_injective, Fin.card_filter_val_lt, min_eq_right hc]
  intro i j h
  simpa [Pi.single_apply] using congr_fun h i.succ

lemma disjoint_axisPoints_unitVectors (k c : ℕ) :
    Disjoint (axisPoints e k) (unitVectors e c) := by
  rw [disjoint_left]
  intro x hx hx'
  obtain ⟨i, -, rfl⟩ := mem_image.1 hx
  obtain ⟨j, -, h⟩ := mem_image.1 hx'
  simpa using congr_fun h j.succ

lemma card_axisUnionBasis (k : ℕ) {c : ℕ} (hc : c ≤ e) : #(axisUnionBasis e k c) = k + 1 + c := by
  rw [axisUnionBasis, card_union_of_disjoint (disjoint_axisPoints_unitVectors k c),
    card_axisPoints, card_unitVectors hc]

lemma axisPoints_mono {k l : ℕ} (hkl : k ≤ l) : axisPoints e k ⊆ axisPoints e l := by
  apply image_subset_image
  grind

lemma unitVectors_mono {c c' : ℕ} (hcc' : c ≤ c') : unitVectors e c ⊆ unitVectors e c' := by
  apply image_subset_image
  intro j
  simp only [mem_filter, mem_univ, true_and]
  grind

lemma axisPoints_add_axisPoints_subset (k l : ℕ) :
    axisPoints e k + axisPoints e l ⊆ axisPoints e (k + l) := by
  intro z hz
  obtain ⟨_, hx, _, hy, rfl⟩ := mem_add.1 hz
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hy
  refine mem_image.2 ⟨i + j, by grind, ?_⟩
  rw [Nat.cast_add, Pi.single_add]

/-- The set `axisUnionBasis e k e` contains `0`, `e₀` and all of `e₁, …, e_e`, so it has affine
dimension `e + 1` when `k ≥ 1`. -/
lemma affineDim_axisUnionBasis {k : ℕ} (hk : 1 ≤ k) :
    (axisUnionBasis e k e).affineDim = e + 1 := by
  have h0 : (0 : Fin (e + 1) → ℝ) ∈ axisUnionBasis e k e :=
    mem_union_left _ (mem_image.2 ⟨0, by simp, by simp⟩)
  suffices h : Submodule.span ℝ
      ((· -ᵥ (0 : Fin (e + 1) → ℝ)) '' (axisUnionBasis e k e : Set (Fin (e + 1) → ℝ))) = ⊤ by
    rw [affineDim_eq_finrank_vectorSpan, vectorSpan_eq_span_vsub_set_right ℝ (mem_coe.2 h0),
      h, finrank_top, Module.finrank_fin_fun]
  rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin (e + 1))).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  refine ⟨Pi.single i 1, ?_, by simp⟩
  induction i using Fin.cases with
  | zero => exact mem_union_left _ (mem_image.2 ⟨1, by grind, by simp⟩)
  | succ j => exact mem_union_right _ (mem_image.2 ⟨j, by simp, rfl⟩)

private lemma card_add_self_le {α : Type*} [AddCommMonoid α] [DecidableEq α] (S : Finset α) :
    #(S + S) ≤ (#S + 1).choose 2 := by
  rw [← card_sym2]
  refine (card_le_card ?_).trans (card_image_le (f := Sym2.lift ⟨(· + ·), add_comm⟩))
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hz
  exact mem_image.2 ⟨s(a, b), mk_mem_sym2_iff.2 ⟨ha, hb⟩, rfl⟩

private lemma card_unitVectors_add_le {c : ℕ} (hc : c ≤ e) :
    #(unitVectors e c + unitVectors e e) ≤ (c + 1).choose 2 + c * (e - c) := by
  have hsub : unitVectors e c + unitVectors e e ⊆ (unitVectors e c + unitVectors e c) ∪
      (unitVectors e c + (unitVectors e e \ unitVectors e c)) := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hz
    by_cases hbc : b ∈ unitVectors e c
    · exact mem_union_left _ (add_mem_add ha hbc)
    · exact mem_union_right _ (add_mem_add ha (mem_sdiff.2 ⟨hb, hbc⟩))
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add ?_ ?_))
  · simpa [card_unitVectors hc] using card_add_self_le (unitVectors e c)
  · refine card_add_le.trans_eq ?_
    rw [card_sdiff_of_subset (unitVectors_mono hc), card_unitVectors hc, card_unitVectors le_rfl]

/-- If `c = 0` or `p ≤ q`, then the sum of `{0, …, q e₀} ∪ {e₁, …, e_c}` and
`{0, …, p e₀} ∪ {e₁, …, e_e}` lies in `{0, …, (p + q) e₀} ∪ ({0, …, q e₀} + {e₁, …, e_e}) ∪
({e₁, …, e_c} + {e₁, …, e_e})`. -/
private lemma axisUnionBasis_add_axisUnionBasis_subset {p q c : ℕ} (hcq : c = 0 ∨ p ≤ q)
    (hc : c ≤ e) :
    axisUnionBasis e q c + axisUnionBasis e p e ⊆ axisPoints e (q + p) ∪
      (axisPoints e q + unitVectors e e) ∪ (unitVectors e c + unitVectors e e) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hz
  simp only [mem_union]
  obtain ha | ha := mem_union.1 ha <;> obtain hb | hb := mem_union.1 hb
  · exact Or.inl (Or.inl (axisPoints_add_axisPoints_subset q p (add_mem_add ha hb)))
  · exact Or.inl (Or.inr (add_mem_add ha hb))
  · obtain rfl | hpq := hcq
    · simp [unitVectors] at ha
    · rw [add_comm a b]
      exact Or.inl (Or.inr (add_mem_add (axisPoints_mono hpq hb) (unitVectors_mono hc ha)))
  · exact Or.inr (add_mem_add ha hb)

private lemma card_axisUnionBasis_add_le {p q c : ℕ} (hcq : c = 0 ∨ p ≤ q) (hc : c ≤ e) :
    #(axisUnionBasis e q c + axisUnionBasis e p e) ≤
      q + p + 1 + (q + 1) * e + (c + 1).choose 2 + c * (e - c) := by
  grind [card_le_card (axisUnionBasis_add_axisUnionBasis_subset hcq hc),
    card_union_le (axisPoints e (q + p) ∪ (axisPoints e q + unitVectors e e))
      (unitVectors e c + unitVectors e e),
    card_union_le (axisPoints e (q + p)) (axisPoints e q + unitVectors e e),
    card_add_le (s := axisPoints e q) (t := unitVectors e e), card_axisPoints e (q + p),
    card_axisPoints e q, card_unitVectors (e := e) le_rfl, card_unitVectors_add_le hc]

private lemma two_mul_choose_two_add_one (c : ℕ) : 2 * (c + 1).choose 2 = (c + 1) * c := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm (c + 1),
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self c)]

/-- The construction when `t = n - m ≥ e`: `A = {0, e₀, …, (m - 1) e₀}`. -/
private lemma exists_card_add_le_of_le {m n : ℕ} (hm : 1 ≤ m) (hn : e + 2 ≤ n) (hmn : m + e ≤ n) :
    ∃ A B : Finset (Fin (e + 1) → ℝ), #A = m ∧ #B = n ∧ B.affineDim = e + 1 ∧
      #(A + B) ≤ sumsetCardLowerBound (e + 1) m n := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hm
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine ⟨axisUnionBasis e a 0, axisUnionBasis e (a + r) e, by simp [card_axisUnionBasis],
    by rw [card_axisUnionBasis _ le_rfl]; grind, affineDim_axisUnionBasis (by grind), ?_⟩
  rw [sumsetCardLowerBound_of_add_le (by grind), Nat.add_sub_cancel]
  grind [card_axisUnionBasis_add_le (e := e) (p := a + r) (q := a) (Or.inl rfl) (Nat.zero_le e),
    Nat.choose_eq_zero_of_lt (by grind : 0 + 1 < 2)]

/-- The construction when `t = n - m < e`: with `c = e - t`, `A = {0, …, p e₀} ∪ {e₁, …, e_c}`
and `B = {0, …, p e₀} ∪ {e₁, …, e_e}` for `p = n - 1 - e`. -/
private lemma exists_card_add_le_of_lt {m n : ℕ} (hmn : m ≤ n) (hn : e + 2 ≤ n) (hnm : n < m + e) :
    ∃ A B : Finset (Fin (e + 1) → ℝ), #A = m ∧ #B = n ∧ B.affineDim = e + 1 ∧
      #(A + B) ≤ sumsetCardLowerBound (e + 1) m n := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt (by grind : t < e)
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le (by grind : c + 2 ≤ m)
  refine ⟨axisUnionBasis (t + c + 1) p (c + 1), axisUnionBasis (t + c + 1) p (t + c + 1),
    by rw [card_axisUnionBasis _ (by grind)]; grind,
    by rw [card_axisUnionBasis _ le_rfl]; grind, affineDim_axisUnionBasis (by grind), ?_⟩
  have h := two_mul_sumsetCardLowerBound_add_add (d := t + c + 1 + 1) (m := c + 2 + p)
    (n := c + 2 + p + t) (by grind) (by grind) (by grind)
  rw [Nat.add_sub_cancel_left] at h
  apply (card_axisUnionBasis_add_le (Or.inr le_rfl) (by grind)).trans
  rw [(by grind : t + c + 1 - (c + 1) = t)]
  nlinarith [two_mul_choose_two_add_one (c + 1)]

/-- For `1 ≤ m ≤ n` and `e + 2 ≤ n`, there are `A, B ⊆ ℝ^(e + 1)` with `|A| = m`, `|B| = n`, `B`
of affine dimension `e + 1` and `|A + B| ≤ G_(e + 1)(m, n)`. -/
lemma exists_card_add_le_sumsetCardLowerBound {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : e + 2 ≤ n) :
    ∃ A B : Finset (Fin (e + 1) → ℝ), #A = m ∧ #B = n ∧ B.affineDim = e + 1 ∧
      #(A + B) ≤ sumsetCardLowerBound (e + 1) m n := by
  obtain hmn' | hnm := le_or_gt (m + e) n
  · exact exists_card_add_le_of_le hm hn hmn'
  · exact exists_card_add_le_of_lt hmn hn hnm

/-- **The sets of Section 3.** For `1 ≤ d`, `1 ≤ m ≤ n` and `d + 1 ≤ n`, there are `A, B ⊆ ℝ^d`
with `|A| = m`, `|B| = n`, `B` of affine dimension `d` and
`|A + B| = n + ∑ j ∈ {1, …, m - 1}, min d (n - j)`. -/
theorem exists_card_add_eq_sumsetCardLowerBound {d m n : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hmn : m ≤ n) (hn : d + 1 ≤ n) :
    ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧ B.affineDim = d ∧
      #(A + B) = sumsetCardLowerBound d m n := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨A, B, hA, hB, hBdim, hAB⟩ := exists_card_add_le_sumsetCardLowerBound hm hmn hn
  refine ⟨A, B, hA, hB, hBdim, le_antisymm hAB ?_⟩
  have hA' : A.Nonempty := card_pos.1 (by grind)
  have h := card_add_sum_min_le_card_add (A := B) (B := A) hA' (by grind)
    (affineDim_add_eq_of_left_eq hA' hBdim)
  rwa [add_comm B, hA, hB, ← sumsetCardLowerBound_eq] at h

end SumOfSetsInSeveralDimensions
