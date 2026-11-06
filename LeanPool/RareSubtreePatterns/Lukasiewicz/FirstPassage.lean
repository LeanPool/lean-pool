/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import Mathlib.Data.List.Rotate
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Find

import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# First passage times of integer sequences and the cycle lemma

Section 2.1 of the paper (source lines 685–690) defines, for a sequence
`𝐱 = (x_i)_{i ≥ 1}` of integers, the first passage time
`ζ(𝐱) = inf {k ≥ 1 : x_1 + ⋯ + x_k = -1}`, with `inf ∅ = +∞`; for a finite sequence it is
defined in the same way (the index `k` ranging over the available positions). Here a finite
sequence is a `List ℤ` and `+∞` is `none`.

We also prove the cycle lemma (the combinatorial core of `eq:shifts`, source lines 718–730):
a sequence of `n ≥ 1` integers that are all `≥ -1` and sum to `-1` has exactly one cyclic
shift whose first passage time to `-1` is `n`.
-/

@[expose] public section

namespace PoissonDeclumping.Lukasiewicz

/-- The first passage time `ζ(𝐱)` of a finite integer sequence to `-1`: the least `k ≥ 1`
(with `k ≤ x.length`) such that `x_1 + ⋯ + x_k = -1`, and `none` (the paper's `+∞`) if there is
no such `k`. -/
noncomputable def zeta (x : List ℤ) : Option ℕ := by
  classical
  exact if h : ∃ k, 1 ≤ k ∧ k ≤ x.length ∧ (x.take k).sum = -1 then some (Nat.find h) else none

/-- Characterization of `ζ(𝐱) = m`. -/
theorem zeta_eq_some_iff {x : List ℤ} {m : ℕ} :
    zeta x = some m ↔ 1 ≤ m ∧ m ≤ x.length ∧ (x.take m).sum = -1 ∧
      ∀ j, 1 ≤ j → j < m → (x.take j).sum ≠ -1 := by
  classical
  unfold zeta
  split_ifs with h
  · rw [Option.some.injEq, Nat.find_eq_iff]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h2, h3, fun j hj1 hjm hs => h4 j hjm ⟨hj1, by omega, hs⟩⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2, h3⟩, fun j hjm ⟨hj1, _, hs⟩ => h4 j hj1 hjm hs⟩
  · simp only [false_iff]
    rintro ⟨h1, h2, h3, -⟩
    exact h ⟨m, h1, h2, h3⟩

/-- `ζ(𝐱) = +∞` exactly when no partial sum `x_1 + ⋯ + x_k`, `1 ≤ k ≤ length`, equals `-1`. -/
theorem zeta_eq_none_iff {x : List ℤ} :
    zeta x = none ↔ ∀ k, 1 ≤ k → k ≤ x.length → (x.take k).sum ≠ -1 := by
  classical
  unfold zeta
  split_ifs with h
  · simp only [false_iff]
    intro h'
    obtain ⟨k, h1, h2, h3⟩ := h
    exact h' k h1 h2 h3
  · simp only [true_iff]
    intro k h1 h2 h3
    exact h ⟨k, h1, h2, h3⟩

/-- Skip-freeness: for a sequence with increments `≥ -1`, if the partial sums of indices
`1 ≤ j < m` avoid `-1`, then all partial sums of indices `j < m` are nonnegative. -/
theorem sum_take_nonneg_of_ne {x : List ℤ} (hx : ∀ a ∈ x, -1 ≤ a) {m : ℕ}
    (h : ∀ j, 1 ≤ j → j < m → (x.take j).sum ≠ -1) : ∀ j < m, 0 ≤ (x.take j).sum := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have ih := ih (by omega)
    have hne := h (j + 1) (by omega) hj
    rcases lt_or_ge j x.length with hjl | hjl
    · rw [List.sum_take_succ _ _ hjl] at hne ⊢
      have := hx _ (List.getElem_mem hjl)
      omega
    · rw [List.take_of_length_le (by omega)] at hne ⊢
      rw [List.take_of_length_le hjl] at ih
      exact ih

/-- If all proper partial sums are nonnegative, then the first passage to `-1` is at the end. -/
theorem zeta_eq_length_iff {y : List ℤ} (hy : ∀ a ∈ y, -1 ≤ a) (hn : 1 ≤ y.length)
    (hs : y.sum = -1) : zeta y = some y.length ↔ ∀ j < y.length, 0 ≤ (y.take j).sum := by
  rw [zeta_eq_some_iff]
  constructor
  · rintro ⟨-, -, -, h⟩
    exact sum_take_nonneg_of_ne hy h
  · intro h
    refine ⟨hn, le_rfl, by rw [List.take_length]; exact hs, fun j _ hj => ?_⟩
    have := h j hj
    omega

/-- A sequence with increments `≥ -1` has partial sums `≥ -length`. -/
theorem neg_length_le_sum {l : List ℤ} (hl : ∀ a ∈ l, -1 ≤ a) : -(l.length : ℤ) ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have := ih (fun b hb => hl b (by simp [hb]))
    simp only [List.length_cons, List.sum_cons]
    push_cast
    linarith

/-- The partial sums of the cyclic shift `x.rotate i` before the wrap-around point. -/
theorem sum_take_rotate_of_le {x : List ℤ} {i j : ℕ} (hi : i ≤ x.length)
    (hj : j ≤ x.length - i) :
    ((x.rotate i).take j).sum = (x.take (i + j)).sum - (x.take i).sum := by
  rw [List.rotate_eq_drop_append_take hi, List.take_append_of_le_length (by simpa using hj),
    List.take_add, List.sum_append]
  omega

/-- The partial sums of the cyclic shift `x.rotate i` after the wrap-around point. -/
theorem sum_take_rotate_of_ge {x : List ℤ} {i j : ℕ} (hi : i ≤ x.length) (hj : j ≤ i) :
    ((x.rotate i).take (x.length - i + j)).sum = x.sum - (x.take i).sum + (x.take j).sum := by
  have hd : (x.drop i).length = x.length - i := List.length_drop
  rw [List.rotate_eq_drop_append_take hi, ← hd, List.take_append, List.take_of_length_le (by omega),
    Nat.add_sub_cancel_left, List.take_take, min_eq_left hj, List.sum_append]
  have : x.sum = (x.take i).sum + (x.drop i).sum := by
    rw [← List.sum_append, List.take_append_drop]
  omega

/-- The partial sums of a cyclic shift are nonnegative before time `n` exactly when the
rotation index is the first minimum of the partial sums `S_0, …, S_{n-1}`. -/
theorem rotate_partial_sums_nonneg_iff {x : List ℤ} (hs : x.sum = -1) {i : ℕ}
    (hi : i < x.length) :
    (∀ j < x.length, 0 ≤ ((x.rotate i).take j).sum) ↔
      (∀ l, i ≤ l → l < x.length → (x.take i).sum ≤ (x.take l).sum) ∧
        (∀ l < i, (x.take i).sum < (x.take l).sum) := by
  constructor
  · intro h
    refine ⟨fun l hil hl => ?_, fun l hl => ?_⟩
    · have := h (l - i) (by omega)
      rw [sum_take_rotate_of_le hi.le (by omega), Nat.add_sub_cancel' hil] at this
      linarith
    · have := h (x.length - i + l) (by omega)
      rw [sum_take_rotate_of_ge hi.le hl.le, hs] at this
      linarith
  · rintro ⟨h1, h2⟩ j hj
    rcases lt_or_ge j (x.length - i) with hji | hji
    · rw [sum_take_rotate_of_le hi.le hji.le]
      have := h1 (i + j) (by omega) (by omega)
      linarith
    · obtain ⟨j', rfl⟩ : ∃ j', j = x.length - i + j' := ⟨j - (x.length - i), by omega⟩
      rw [sum_take_rotate_of_ge hi.le (by omega), hs]
      have := h2 j' (by omega)
      linarith

/-- **Cycle lemma.** A sequence of `n ≥ 1` integers, all `≥ -1`, with sum `-1`, has exactly one
cyclic shift `x.rotate i` (`0 ≤ i < n`) whose first passage time to `-1` is `n`. -/
theorem existsUnique_zeta_rotate_eq_length {x : List ℤ} (hx : ∀ a ∈ x, -1 ≤ a)
    (hn : 1 ≤ x.length) (hs : x.sum = -1) :
    ∃! i, i < x.length ∧ zeta (x.rotate i) = some x.length := by
  classical
  have key : ∀ i < x.length, zeta (x.rotate i) = some x.length ↔
      (∀ l, i ≤ l → l < x.length → (x.take i).sum ≤ (x.take l).sum) ∧
        (∀ l < i, (x.take i).sum < (x.take l).sum) := by
    intro i hi
    have h := zeta_eq_length_iff (y := x.rotate i) (fun a ha => hx a (List.mem_rotate.mp ha))
      (by rwa [List.length_rotate]) (by rw [(List.rotate_perm x i).sum_eq, hs])
    rw [List.length_rotate] at h
    rw [h, rotate_partial_sums_nonneg_iff hs hi]
  set S : ℕ → ℤ := fun l => (x.take l).sum with hS
  obtain ⟨l₀, hl₀, hmin⟩ := Finset.exists_min_image (Finset.range x.length) S
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hex : ∃ l, l < x.length ∧ S l = S l₀ := ⟨l₀, Finset.mem_range.mp hl₀, rfl⟩
  have hfi : Nat.find hex < x.length := (Nat.find_spec hex).1
  have hgood : zeta (x.rotate (Nat.find hex)) = some x.length := by
    rw [key _ hfi]
    refine ⟨fun l _ hl => ?_, fun l hl => ?_⟩
    · change S _ ≤ S l
      rw [(Nat.find_spec hex).2]
      exact hmin l (Finset.mem_range.mpr hl)
    · change S _ < S l
      rw [(Nat.find_spec hex).2]
      have hlt : l < x.length := lt_trans hl hfi
      exact lt_of_le_of_ne (hmin l (Finset.mem_range.mpr hlt))
        (Ne.symm fun he => Nat.find_min hex hl ⟨hlt, he⟩)
  refine ⟨Nat.find hex, ⟨hfi, hgood⟩, ?_⟩
  rintro i ⟨hi, hz⟩
  obtain ⟨h1, h2⟩ := (key i hi).mp hz
  obtain ⟨g1, g2⟩ := (key _ hfi).mp hgood
  rcases lt_trichotomy i (Nat.find hex) with hlt | heq | hgt
  · have := g2 i hlt
    have := h1 (Nat.find hex) hlt.le hfi
    linarith
  · exact heq
  · have := h2 _ hgt
    have := g1 i hgt.le hi
    linarith

end PoissonDeclumping.Lukasiewicz
