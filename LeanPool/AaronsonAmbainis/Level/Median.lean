/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A median, and a power-mean inequality

Two elementary facts with no cube in them:

* `exists_median` — a real function on a nonempty finite type has a median `m`: at least half of
  the points have `f ≤ m`, and at least half have `m ≤ f` (Lemma 7.8 of the paper);
* `sum_sq_cube_le` — `(∑ z²)^3 ≤ #s · (∑ |z|^3)^2`, that is, `(E z²)^3 ≤ (E |z|^3)^2`
  (Lemma 7.9 of the paper).
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Level

open Finset

/-- A real function on a nonempty finite type has a median (Lemma 7.8 of the paper). -/
theorem exists_median {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    ∃ m : ℝ, Fintype.card X ≤ 2 * (univ.filter (fun x => f x ≤ m)).card ∧
      Fintype.card X ≤ 2 * (univ.filter (fun x => m ≤ f x)).card := by
  classical
  -- the values `v` of `f` with `#X ≤ 2 #{f ≤ v}`
  obtain ⟨S, hS⟩ : ∃ S : Finset ℝ, S = (univ.image f).filter
      (fun v => Fintype.card X ≤ 2 * (univ.filter (fun x => f x ≤ v)).card) := ⟨_, rfl⟩
  have hmem : ∀ v, v ∈ S ↔ (∃ x, f x = v) ∧
      Fintype.card X ≤ 2 * (univ.filter (fun x => f x ≤ v)).card := by
    intro v
    rw [hS, Finset.mem_filter, Finset.mem_image]
    simp
  -- the largest value of `f` belongs to `S`
  obtain ⟨x1, -, hx1⟩ := Finset.exists_max_image univ f univ_nonempty
  have hne : S.Nonempty := by
    refine ⟨f x1, (hmem _).mpr ⟨⟨x1, rfl⟩, ?_⟩⟩
    have hall : univ.filter (fun x => f x ≤ f x1) = univ :=
      Finset.filter_true_of_mem (fun x _ => hx1 x (mem_univ _))
    rw [hall, Finset.card_univ]
    omega
  -- the least element of `S` is a median
  refine ⟨S.min' hne, ((hmem _).mp (S.min'_mem hne)).2, ?_⟩
  by_contra hcon
  have hsplit : (univ.filter (fun x => f x < S.min' hne)).card
      + (univ.filter (fun x => S.min' hne ≤ f x)).card = Fintype.card X := by
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset X))
      (fun x => f x < S.min' hne)
    simp only [not_lt, Finset.card_univ] at h
    exact h
  have hlow : (univ.filter (fun x => f x < S.min' hne)).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨x2, hx2, hx2max⟩ := Finset.exists_max_image _ f hlow
  have hx2lt : f x2 < S.min' hne := (Finset.mem_filter.mp hx2).2
  have hsub : univ.filter (fun x => f x < S.min' hne) ⊆ univ.filter (fun x => f x ≤ f x2) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨mem_univ _, hx2max x hx⟩
  have hcard := Finset.card_le_card hsub
  have hx2S : f x2 ∈ S := (hmem _).mpr ⟨⟨x2, rfl⟩, by omega⟩
  exact absurd (S.min'_le _ hx2S) (not_le.mpr hx2lt)

/-- A power-mean inequality: `(∑ z²)^3 ≤ #s · (∑ |z|^3)^2` (Lemma 7.9 of the paper). -/
theorem sum_sq_cube_le {α : Type*} (s : Finset α) (z : α → ℝ) :
    (∑ i ∈ s, z i ^ 2) ^ 3 ≤ (s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := by
  have hA : 0 ≤ ∑ i ∈ s, z i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- `(∑ z²)² ≤ (∑ |z|)(∑ |z|^3)`
  have h1 : (∑ i ∈ s, z i ^ 2) ^ 2 ≤ (∑ i ∈ s, |z i|) * (∑ i ∈ s, |z i| ^ 3) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i _ => abs_nonneg _)
      (fun i _ => pow_nonneg (abs_nonneg _) 3)
      (fun i _ => by
        rw [← sq_abs (z i)]
        exact le_of_eq (by ring))
  -- `(∑ |z|)² ≤ #s ∑ z²`
  have h2 : (∑ i ∈ s, |z i|) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, z i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => |z i|)
    simp only [sq_abs] at h
    exact h
  rcases hA.eq_or_lt with h0 | hpos
  · rw [← h0]
    have : (0 : ℝ) ≤ (s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := by positivity
    simpa using this
  · have h3 : ((∑ i ∈ s, z i ^ 2) ^ 2) ^ 2
        ≤ ((∑ i ∈ s, |z i|) * (∑ i ∈ s, |z i| ^ 3)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    have h4 : ((∑ i ∈ s, |z i|) * (∑ i ∈ s, |z i| ^ 3)) ^ 2
        ≤ ((s.card : ℝ) * ∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have h5 : (∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, z i ^ 2) ^ 3
        ≤ (∑ i ∈ s, z i ^ 2) * ((s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2) := by
      calc (∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, z i ^ 2) ^ 3
          = ((∑ i ∈ s, z i ^ 2) ^ 2) ^ 2 := by ring
        _ ≤ ((s.card : ℝ) * ∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := h3.trans h4
        _ = (∑ i ∈ s, z i ^ 2) * ((s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2) := by ring
    exact le_of_mul_le_mul_left h5 hpos

end Level
end AaronsonAmbainis
