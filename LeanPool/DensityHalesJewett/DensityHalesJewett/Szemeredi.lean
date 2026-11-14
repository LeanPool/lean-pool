/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import LeanPool.DensityHalesJewett.DensityHalesJewett.UniformFibers
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Combinatorics.Pigeonhole

/-!
# Arithmetic progressions from combinatorial lines

The digital transfer from density Hales--Jewett to Szemerédi's theorem on finite intervals, using
Mathlib's fixed-length base encoding `finFunctionFinEquiv`. It turns a dimension `m` in which
density Hales--Jewett holds for `k` letters into the threshold `2 * k ^ m / δ` for progressions of
length `k`.
-/

@[expose] public section

open Finset
open Combinatorics

namespace Combinatorics

/-- An arithmetic progression of length `k` with nonzero common difference in an additive monoid. -/
@[ext]
structure ArithmeticProgression (α : Type*) [AddMonoid α] (k : ℕ) where
  /-- The initial term of the arithmetic progression. -/
  start : α
  /-- The common difference of the arithmetic progression. -/
  diff : α
  diff_ne_zero : diff ≠ 0

namespace ArithmeticProgression

/-- The term of `P` indexed by `i`. -/
def term {α : Type*} [AddMonoid α] {k : ℕ} (P : ArithmeticProgression α k)
    (i : Fin k) : α :=
  P.start + (i : ℕ) • P.diff

/-- The proposition that every term of `P` belongs to `s`, for `s` of any type with a membership
relation, such as `Set α` or `Finset α`. -/
def IsSubset {α S : Type*} [AddMonoid α] [Membership α S] {k : ℕ} (P : ArithmeticProgression α k)
    (s : S) : Prop :=
  ∀ i, P.term i ∈ s

end ArithmeticProgression
end Combinatorics

namespace DensityHalesJewett

namespace Line

/-- A base-encoded combinatorial line gives an arithmetic progression with nonzero common
difference. The encoding is Mathlib's `finFunctionFinEquiv`, which reads a word as the base-`k`
digits of a natural number. -/
lemma baseEncode_isArithmeticProgression {k m : ℕ} (hk : 1 ≤ k)
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    ∃ P : Combinatorics.ArithmeticProgression ℕ k,
      ∀ a, P.term a = (finFunctionFinEquiv (l a) : ℕ) := by
  let d := ∑ i : Fin m, if l.idxFun i = none then k ^ (i : ℕ) else 0
  refine ⟨
    { start := (finFunctionFinEquiv (l ⟨0, hk⟩) : ℕ)
      diff := d
      diff_ne_zero := ?_ }, ?_⟩
  · obtain ⟨i, hi⟩ := l.proper
    exact Nat.ne_of_gt (sum_pos' (fun _ _ ↦ Nat.zero_le _)
      ⟨i, mem_univ i, by simp [hi, Nat.zero_lt_of_lt hk]⟩)
  · intro a
    change (finFunctionFinEquiv (l ⟨0, hk⟩) : ℕ) + (a : ℕ) • d
      = (finFunctionFinEquiv (l a) : ℕ)
    simp only [finFunctionFinEquiv_apply]
    rw [nsmul_eq_mul, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    cases hli : l.idxFun i <;> simp [Combinatorics.Line.coe_apply, hli]

end Line

/-- Fewer than `K` elements of `A ⊆ range N` lie beyond the last complete block of length `K`. -/
lemma card_sdiff_range_div_mul_lt {K N : ℕ} (hK : 0 < K) {A : Finset ℕ} (hAN : A ⊆ range N) :
    #(A \ range (N / K * K)) < K := by
  have h : A \ range (N / K * K) ⊆ Ico (N / K * K) N := fun x hx ↦ by
    rw [mem_sdiff, mem_range] at hx
    exact mem_Ico.2 ⟨not_lt.1 hx.2, mem_range.1 (hAN hx.1)⟩
  refine (card_le_card h).trans_lt ?_
  rw [Nat.card_Ico]
  have := Nat.mod_add_div' N K
  have := Nat.mod_lt N hK
  omega

/-- The elements of `A` below `Q * K` with quotient `q < Q` by `K` form the block of `A` between
`q * K` and `q * K + K`. -/
lemma filter_inter_range_div_eq {K Q q : ℕ} (hK : 0 < K) (A : Finset ℕ) (hq : q < Q) :
    {x ∈ A ∩ range (Q * K) | x / K = q} = A ∩ Ico (q * K) (q * K + K) := by
  have := Nat.mul_le_mul_right K hq
  rw [Nat.succ_mul] at this
  ext x
  have hx : x / K = q ↔ q * K ≤ x ∧ x < q * K + K := by
    rw [Nat.div_eq_iff hK]
    omega
  simp only [mem_filter, mem_inter, mem_range, mem_Ico, hx]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, by omega⟩, h.2⟩⟩

/-- A sufficiently dense initial interval has a block of `K` consecutive numbers with at least
half the ambient density. -/
lemma exists_dense_digitBlock {K : ℕ} (hK : 0 < K) {δ : ℝ} (hδ : 0 < δ)
    {N : ℕ} (hN : 2 * K / δ ≤ N) {A : Finset ℕ} (hAN : A ⊆ range N)
    (hA : δ * N ≤ #A) :
    ∃ q : ℕ, δ / 2 * K ≤ #(A ∩ Ico (q * K) (q * K + K)) := by
  have hS : δ / 2 * N ≤ #(A ∩ range (N / K * K)) := by
    rw [← card_inter_add_card_sdiff A (range (N / K * K))] at hA
    push_cast at hA
    nlinarith [(div_le_iff₀ hδ).1 hN, (Nat.cast_lt (α := ℝ)).2 (card_sdiff_range_div_mul_lt hK hAN)]
  have hmaps (x) (hx : x ∈ A ∩ range (N / K * K)) : x / K ∈ range (N / K) :=
    mem_range.2 ((Nat.div_lt_iff_lt_mul hK).2 (mem_range.1 (mem_inter.1 hx).2))
  obtain ⟨x, hx⟩ : (A ∩ range (N / K * K)).Nonempty := card_pos.1 <| mod_cast
    (mul_pos (half_pos hδ) ((div_pos (by positivity) hδ).trans_le hN)).trans_le hS
  obtain ⟨q, hq, hcard⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps ⟨_, hmaps x hx⟩
    (b := δ / 2 * K) (by
      rw [card_range, nsmul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.div_mul_le_self N K : ((N / K : ℕ) : ℝ) * K ≤ N) (half_pos hδ).le])
  exact ⟨q, hcard.trans_eq (by rw [filter_inter_range_div_eq hK A (mem_range.1 hq)])⟩

end DensityHalesJewett

namespace Combinatorics.ArithmeticProgression

/-- The digital transfer from density Hales--Jewett to Szemerédi's theorem: if density
Hales--Jewett holds for `k` letters and density `δ / 2` in dimension `m`, then for
`n ≥ 2 * k ^ m / δ` every subset of `range n` with at least `δ * n` elements contains an
arithmetic progression of length `k`. -/
theorem exists_of_isDHJDimension {k m : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ)
    (hm : DensityHalesJewett.IsDHJDimension k (δ / 2) m) {n : ℕ} (hn : 2 * (k : ℝ) ^ m / δ ≤ n)
    (A : Finset ℕ) (hAn : A ⊆ range n) (hAδ : δ * n ≤ #A) :
    ∃ P : ArithmeticProgression ℕ k, P.IsSubset A := by
  classical
  obtain ⟨q, hq⟩ := DensityHalesJewett.exists_dense_digitBlock (pow_pos hk m) hδ
    (by simpa using hn) hAn hAδ
  let e : (Fin m → Fin k) ↪ ℕ :=
    finFunctionFinEquiv.toEmbedding.trans (Fin.valEmbedding.trans (addLeftEmbedding (q * k ^ m)))
  have he : univ.map e = Ico (q * k ^ m) (q * k ^ m + k ^ m) := by
    rw [← map_map, ← map_map, map_univ_equiv, Fin.map_valEmbedding_univ, Nat.Iio_eq_range,
      ← Nat.Ico_zero_eq_range, map_add_left_Ico, add_zero]
  obtain ⟨l, hl⟩ := hm (univ.filter ((· ∈ A) ∘ e)) <| by
    rwa [← card_map e, ← filter_map, he, filter_mem_eq_inter, inter_comm, ← Nat.cast_pow]
  obtain ⟨P, hP⟩ := DensityHalesJewett.Line.baseEncode_isArithmeticProgression hk l
  refine ⟨⟨q * k ^ m + P.start, P.diff, P.diff_ne_zero⟩, ?_⟩
  intro a
  have h := (mem_filter.1 (hl a)).2
  simp only [e, Function.comp_apply, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
    Fin.valEmbedding_apply, addLeftEmbedding_apply, ← hP] at h
  simpa [term, add_assoc] using h

end Combinatorics.ArithmeticProgression
