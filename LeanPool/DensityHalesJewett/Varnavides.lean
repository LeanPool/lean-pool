/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.Szemeredi
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Many arithmetic progressions in dense sets

Varnavides' averaging argument turns Szemerédi's theorem, the existence of one arithmetic
progression in a dense set, into a quadratic lower bound on the number of such progressions. The
bound is explicit in a threshold `m` for Szemerédi's theorem at half the density and a natural
bound `N` for `1 / δ`.
-/

@[expose] public section

open Finset

namespace Combinatorics.ArithmeticProgression

/-- The pairs `(a, d)` that parametrize nonconstant `k`-term arithmetic progressions
contained in `A`. -/
def containedProgressions (k n : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ range n).filter fun (a, d) ↦ d ≠ 0 ∧ ∀ i : Fin k, a + i * d ∈ A

/-- The indices at which the finite progression parametrized by `(a, d)` meets `A`. -/
def indicesIn (m : ℕ) (A : Finset ℕ) : ℕ × ℕ → Finset ℕ
  | (a, d) => (range m).filter fun i ↦ a + i * d ∈ A

/-- Finite progressions of length `m`, positive difference at most `D`, and lying in
`range n`. We use the slightly stronger endpoint condition `a + m * d ≤ n`. -/
def grids (m n D : ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ Icc 1 D).filter fun (a, d) ↦ a + m * d ≤ n

/-- Incidences between a grid and one of its indices whose image lies in `A`. -/
def gridIncidences (m n D : ℕ) (A : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (grids m n D ×ˢ range m).filter fun ((a, d), i) ↦ a + i * d ∈ A

lemma card_gridIncidences (m n D : ℕ) (A : Finset ℕ) :
    #(gridIncidences m n D A) = ∑ p ∈ grids m n D, #(indicesIn m A p) := by
  simp only [gridIncidences, indicesIn, card_filter, sum_product]

/-- The grids on which `A` has density at least `δ`. -/
noncomputable def denseGrids (δ : ℝ) (m n D : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (grids m n D).filter fun p ↦ δ * m ≤ #(indicesIn m A p)

lemma card_grids_le (m n D : ℕ) : #(grids m n D) ≤ n * D :=
  (card_filter_le _ _).trans_eq (by simp)

/-- A grid that is not dense has fewer than `δ * m` incidences, and a dense one has at most
`m`. -/
lemma card_gridIncidences_le {δ : ℝ} (hδ : 0 ≤ δ) (m n D : ℕ) (A : Finset ℕ) :
    (#(gridIncidences m n D A) : ℝ) ≤ δ * m * #(grids m n D) + m * #(denseGrids δ m n D A) := by
  rw [card_gridIncidences, Nat.cast_sum]
  calc ∑ p ∈ grids m n D, (#(indicesIn m A p) : ℝ)
      ≤ ∑ p ∈ grids m n D, (δ * m + if δ * m ≤ #(indicesIn m A p) then (m : ℝ) else 0) := by
        gcongr with p
        have hm : (#(indicesIn m A p) : ℝ) ≤ m :=
          mod_cast (card_filter_le _ _).trans_eq (card_range m)
        split_ifs with h
        · linarith [mul_nonneg hδ (Nat.cast_nonneg m)]
        · linarith
    _ = δ * m * #(grids m n D) + m * #(denseGrids δ m n D A) := by
        simp [sum_add_distrib, sum_ite, denseGrids, mul_comm]

/-- Every point `a` of `A` at distance at least `W ≥ m * D` from the ends of `range n` lies on
the grid with difference `d` at index `i`, for each `d ≤ D` and `i < m`. -/
lemma le_card_gridIncidences {m n D W : ℕ} (hW : m * D ≤ W) {A : Finset ℕ}
    (hAn : A ⊆ range n) : #(A ∩ Icc W (n - W)) * D * m ≤ #(gridIncidences m n D A) := by
  have hcard : #(((A ∩ Icc W (n - W)) ×ˢ Icc 1 D) ×ˢ range m) = #(A ∩ Icc W (n - W)) * D * m := by
    simp
  rw [← hcard]
  refine card_le_card_of_injOn (fun ((a, d), i) ↦ ((a - i * d, d), i)) ?_ ?_
  · rintro ⟨⟨a, d⟩, i⟩ hx
    simp only [mem_coe, mem_product, mem_inter, mem_Icc, mem_range] at hx
    obtain ⟨⟨⟨haA, haW, han⟩, hd, hdD⟩, hi⟩ := hx
    obtain ⟨hid, hmd⟩ : i * d ≤ W ∧ m * d ≤ W :=
      ⟨(Nat.mul_le_mul hi.le hdD).trans hW, (Nat.mul_le_mul_left m hdD).trans hW⟩
    simp only [gridIncidences, grids, mem_coe, mem_filter, mem_product, mem_range, mem_Icc]
    refine ⟨⟨⟨⟨(Nat.sub_le _ _).trans_lt (mem_range.1 (hAn haA)), hd, hdD⟩, by omega⟩, hi⟩, ?_⟩
    rwa [Nat.sub_add_cancel (hid.trans haW)]
  · rintro ⟨⟨a, d⟩, i⟩ hx ⟨⟨a', d'⟩, i'⟩ hy h
    simp only [mem_coe, mem_product, mem_inter, mem_Icc, mem_range] at hx hy
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h, rfl⟩, rfl⟩ := h
    have hid : i * d ≤ W := (Nat.mul_le_mul hx.2.le hx.1.2.2).trans hW
    simp only [Prod.mk.injEq, and_true]
    omega

lemma card_le_card_inter_Icc_add {n : ℕ} (W : ℕ) {A : Finset ℕ} (hAn : A ⊆ range n) :
    #A ≤ #(A ∩ Icc W (n - W)) + 2 * W := by
  have h : A \ Icc W (n - W) ⊆ range W ∪ Ico (n - W) n := by
    intro x hx
    have := mem_range.1 (hAn (mem_sdiff.1 hx).1)
    simp only [mem_sdiff, mem_Icc, mem_union, mem_range, mem_Ico] at hx ⊢
    omega
  have := (card_le_card h).trans (card_union_le _ _)
  rw [card_range, Nat.card_Ico] at this
  rw [← card_inter_add_card_sdiff A (Icc W (n - W))]
  omega

/-- Double counting the incidences: a positive proportion of the grids are dense. -/
lemma le_card_denseGrids {δ : ℝ} (hδ : 0 < δ) {m n D W : ℕ} (hm : 0 < m) (hW : m * D ≤ W)
    (hWn : 8 * W ≤ δ * n) {A : Finset ℕ} (hAn : A ⊆ range n) (hA : δ * n ≤ #A) :
    δ / 4 * n * D ≤ #(denseGrids (δ / 2) m n D A) := by
  have hm' : (0 : ℝ) < m := mod_cast hm
  have hcard : (#A : ℝ) ≤ #(A ∩ Icc W (n - W)) + 2 * W :=
    mod_cast card_le_card_inter_Icc_add W hAn
  have h : (δ * n - 2 * W) * D * m ≤
      δ / 2 * m * (n * D) + m * #(denseGrids (δ / 2) m n D A) :=
    calc (δ * n - 2 * W) * D * m
        ≤ #(A ∩ Icc W (n - W)) * D * m := by
          gcongr
          linarith
      _ ≤ #(gridIncidences m n D A) := mod_cast le_card_gridIncidences hW hAn
      _ ≤ δ / 2 * m * #(grids m n D) + m * #(denseGrids (δ / 2) m n D A) :=
          card_gridIncidences_le (half_pos hδ).le m n D A
      _ ≤ δ / 2 * m * (n * D) + m * #(denseGrids (δ / 2) m n D A) := by
          gcongr
          exact mod_cast card_grids_le m n D
  refine le_of_mul_le_mul_left ?_ hm'
  nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) D) hm'.le) (sub_nonneg.2 hWn)]

/-- A progression among the indices at which a dense grid meets `A` gives a progression in
`A`. -/
lemma exists_mem_containedProgressions {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} {m n D : ℕ}
    (hS : ∀ B : Finset ℕ, B ⊆ range m → δ * m ≤ #B →
      ∃ P : ArithmeticProgression ℕ k, P.IsSubset B)
    {A : Finset ℕ} (hAn : A ⊆ range n) {a d : ℕ} (hp : (a, d) ∈ denseGrids δ m n D A) :
    ∃ P : ArithmeticProgression ℕ k, P.start < m ∧ P.diff < m ∧
      (a + P.start * d, P.diff * d) ∈ containedProgressions k n A := by
  simp only [denseGrids, grids, mem_filter, mem_product, mem_Icc] at hp
  obtain ⟨⟨⟨-, hd, -⟩, -⟩, hdense⟩ := hp
  obtain ⟨P, hP⟩ := hS (indicesIn m A (a, d)) (filter_subset _ _) hdense
  have h (i : Fin k) : P.start + i * P.diff < m ∧ a + (P.start + i * P.diff) * d ∈ A := by
    simpa [indicesIn, term] using hP i
  have h₀ := h ⟨0, by omega⟩
  have h₁ := h ⟨1, by omega⟩
  simp only [zero_mul, add_zero, one_mul] at h₀ h₁
  refine ⟨P, h₀.1, by omega, ?_⟩
  simp only [containedProgressions, mem_filter, mem_product, mem_range]
  refine ⟨⟨mem_range.1 (hAn h₀.2), ?_⟩, mul_ne_zero P.diff_ne_zero (by omega), ?_⟩
  · have := mem_range.1 (hAn h₁.2)
    rw [add_mul] at this
    omega
  · intro i
    convert (h i).2 using 1
    ring

/-- A pair is the image of at most `m ^ 2` pairs `(a, d)` under
`(a, d) ↦ (a + (P a d).start * d, (P a d).diff * d)`, when the first terms and the differences of
the progressions `P a d` are below `m`. -/
private lemma card_filter_eq_le {k m : ℕ} {S : Finset (ℕ × ℕ)}
    {P : ℕ → ℕ → ArithmeticProgression ℕ k} {f : ℕ × ℕ → ℕ × ℕ}
    (hf : ∀ a d, f (a, d) = (a + (P a d).start * d, (P a d).diff * d))
    (hP : ∀ a d, (a, d) ∈ S → (P a d).start < m ∧ (P a d).diff < m) (y : ℕ × ℕ) :
    #(S.filter fun p ↦ f p = y) ≤ m ^ 2 := by
  refine (card_le_card_of_injOn (t := range m ×ˢ range m)
    (fun (a, d) ↦ ((P a d).start, (P a d).diff)) ?_ ?_).trans_eq (by simp [sq])
  · rintro ⟨a, d⟩ hp
    obtain ⟨hstart, hdiff⟩ := hP a d (mem_filter.1 hp).1
    simp [hstart, hdiff]
  · rintro ⟨a, d⟩ hp ⟨a', d'⟩ hr h
    simp only [mem_coe, mem_filter, hf] at hp hr
    obtain ⟨hstart, hdiff⟩ := Prod.mk.inj h
    obtain ⟨ha, hd⟩ := Prod.mk.inj (hp.2.trans hr.2.symm)
    rw [hstart] at ha
    rw [hdiff] at hd
    obtain rfl : d = d' :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (P a' d').diff_ne_zero) hd
    rw [Nat.add_right_cancel ha]

/-- Each dense grid contains a progression, and a progression lies on at most `m ^ 2` grids. -/
lemma card_denseGrids_le {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} {m n : ℕ} (D : ℕ)
    (hS : ∀ B : Finset ℕ, B ⊆ range m → δ * m ≤ #B →
      ∃ P : ArithmeticProgression ℕ k, P.IsSubset B)
    {A : Finset ℕ} (hAn : A ⊆ range n) :
    #(denseGrids δ m n D A) ≤ #(containedProgressions k n A) * m ^ 2 := by
  have : Nonempty (ArithmeticProgression ℕ k) := ⟨⟨0, 1, one_ne_zero⟩⟩
  choose! P hP using fun a d ↦
    exists_mem_containedProgressions (a := a) (d := d) (D := D) hk hS hAn
  let f : ℕ × ℕ → ℕ × ℕ := fun (a, d) ↦ (a + (P a d).start * d, (P a d).diff * d)
  calc #(denseGrids δ m n D A)
      ≤ m ^ 2 * #((denseGrids δ m n D A).image f) :=
        card_le_mul_card_image _ _ fun y _ ↦
          card_filter_eq_le (fun _ _ ↦ rfl) (fun a d hp ↦ ⟨(hP a d hp).1, (hP a d hp).2.1⟩) y
    _ ≤ m ^ 2 * #(containedProgressions k n A) := by
        gcongr
        exact image_subset_iff.2 fun (a, d) hp ↦ (hP a d hp).2.2
    _ = #(containedProgressions k n A) * m ^ 2 := mul_comm _ _

/-- Varnavides' averaging argument over grids of difference at most `D`: if every subset of
`range m` with at least `δ / 2 * m` elements contains an arithmetic progression of length `k`
and `8 * (m * D) ≤ δ * n`, then a subset of `range n` with at least `δ * n` elements contains at
least `δ / 4 * n * D / m ^ 2` such progressions. -/
lemma le_card_containedProgressions_mul {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) {m n D : ℕ}
    (hm : 0 < m)
    (hS : ∀ B : Finset ℕ, B ⊆ range m → δ / 2 * m ≤ #B →
      ∃ P : ArithmeticProgression ℕ k, P.IsSubset B)
    (hD : 8 * ((m * D : ℕ) : ℝ) ≤ δ * n) {A : Finset ℕ} (hAn : A ⊆ range n) (hA : δ * n ≤ #A) :
    δ / 4 * n * D ≤ #(containedProgressions k n A) * m ^ 2 :=
  (le_card_denseGrids hδ hm le_rfl hD hAn hA).trans (mod_cast card_denseGrids_le hk D hS hAn)

private lemma exists_mul_le_lt {C n : ℕ} (hC : 0 < C) (hn : C ≤ n) :
    ∃ D : ℕ, (1 : ℝ) ≤ D ∧ (C : ℝ) * D ≤ n ∧ (n : ℝ) < C * (D + 1) :=
  ⟨n / C, mod_cast Nat.div_pos hn hC, mod_cast Nat.mul_div_le n C,
    mod_cast Nat.lt_mul_div_succ n hC⟩

/-- Varnavides' averaging argument: if every subset of `range m` with at least `δ / 2 * m`
elements contains an arithmetic progression of length `k`, and `N` is a natural bound for
`1 / δ`, then for `n ≥ T ≥ 128 * m ^ 3 * N ^ 2` a subset of `range n` with at least `δ * n`
elements contains at least `n ^ 2 / T` such progressions. -/
theorem sq_div_le_card_containedProgressions {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) {m : ℕ}
    (hm : 0 < m)
    (hS : ∀ B : Finset ℕ, B ⊆ range m → δ / 2 * m ≤ #B →
      ∃ P : ArithmeticProgression ℕ k, P.IsSubset B)
    {N : ℕ} (hN : 1 / δ ≤ N) {T n : ℕ} (hT : 128 * m ^ 3 * N ^ 2 ≤ T) (hn : T ≤ n)
    (A : Finset ℕ) (hAn : A ⊆ range n) (hA : δ * n ≤ #A) :
    (n : ℝ) ^ 2 / T ≤ #(containedProgressions k n A) := by
  have hδN : 1 ≤ δ * N := by rwa [div_le_iff₀' hδ] at hN
  have hN₀ : 0 < N := by exact_mod_cast (one_div_pos.2 hδ).trans_le hN
  have hCT : 16 * m * N ≤ 128 * m ^ 3 * N ^ 2 :=
    calc 16 * m * N = 16 * (m * N) := by ring
      _ ≤ 128 * (m ^ 3 * N ^ 2) := Nat.mul_le_mul (by norm_num)
          (Nat.mul_le_mul (Nat.le_self_pow three_ne_zero m) (Nat.le_self_pow two_ne_zero N))
      _ = 128 * m ^ 3 * N ^ 2 := by ring
  obtain ⟨D, hD, hCD, hnCD⟩ :=
    exists_mul_le_lt (C := 16 * m * N) (by positivity) (hCT.trans (hT.trans hn))
  push_cast at hCD hnCD
  have h := le_card_containedProgressions_mul hk hδ hm hS (D := D) (by push_cast; nlinarith)
    hAn hA
  rw [div_le_iff₀ (by exact_mod_cast (by positivity : 0 < 128 * m ^ 3 * N ^ 2).trans_le hT)]
  calc (n : ℝ) ^ 2 ≤ n * (2 * (16 * m * N) * D) := by
        rw [sq]
        gcongr
        nlinarith [mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 16 * m * N)]
    _ ≤ n * (2 * (16 * m * N) * D) * (δ * N) := le_mul_of_one_le_right (by positivity) hδN
    _ = δ / 4 * n * D * (128 * m * N ^ 2) := by ring
    _ ≤ #(containedProgressions k n A) * m ^ 2 * (128 * m * N ^ 2) := by gcongr
    _ = #(containedProgressions k n A) * ((128 * m ^ 3 * N ^ 2 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ #(containedProgressions k n A) * T := by gcongr

end Combinatorics.ArithmeticProgression
