/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem

/-! # Uniform counts for small or prescribed polynomial values -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem polynomial_eval_fiber_card_le {Q : ℤ[X]} (hQ : 0 < Q.natDegree)
    (S : Finset ℤ) (a : ℤ) : (S.filter (fun n => Q.eval n = a)).card ≤ Q.natDegree := by
  have hdeg := Polynomial.natDegree_pos_iff_degree_pos.mp hQ
  calc
    _ ≤ (Q - C a).roots.toFinset.card := by
      apply card_le_card
      intro n hn
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots_sub_C hdeg).mpr (mem_filter.mp hn).2)
    _ ≤ (Q - C a).roots.card := Multiset.toFinset_card_le _
    _ ≤ _ := Polynomial.card_roots_sub_C' hdeg

theorem polynomial_natAbs_fiber_card_le {Q : ℤ[X]} (hQ : 0 < Q.natDegree)
    (S : Finset ℤ) (a : ℕ) : (S.filter (fun n => (Q.eval n).natAbs = a)).card ≤ 2 * Q.natDegree :=
        by
  have hcover : S.filter (fun n => (Q.eval n).natAbs = a) ⊆
      S.filter (fun n => Q.eval n = (a : ℤ)) ∪ S.filter (fun n => Q.eval n = -(a : ℤ)) := by
    intro n hn
    obtain ⟨hnS, hnQ⟩ := mem_filter.mp hn
    have H : (Q.eval n).natAbs = (a : ℤ).natAbs := by simpa only [Int.natAbs_natCast] using hnQ
    rcases Int.natAbs_eq_natAbs_iff.mp H with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hnS, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hnS, h⟩)
  calc
    _ ≤ (S.filter (fun n => Q.eval n = (a : ℤ)) ∪ S.filter (fun n => Q.eval n = -(a : ℤ))).card :=
      card_le_card hcover
    _ ≤ (S.filter (fun n => Q.eval n = (a : ℤ))).card +
        (S.filter (fun n => Q.eval n = -(a : ℤ))).card := card_union_le _ _
    _ ≤ Q.natDegree + Q.natDegree := add_le_add
      (polynomial_eval_fiber_card_le hQ S _) (polynomial_eval_fiber_card_le hQ S _)
    _ = _ := by omega

theorem polynomial_natAbs_image_card_bound {Q : ℤ[X]} (hQ : 0 < Q.natDegree) (S : Finset ℤ) :
    S.card ≤ 2 * Q.natDegree * (S.image (fun n => (Q.eval n).natAbs)).card :=
  Finset.card_le_mul_card_image S _ (fun a _ => polynomial_natAbs_fiber_card_le hQ S a)

theorem polynomial_natAbs_preimage_card_le {Q : ℤ[X]} (hQ : 0 < Q.natDegree)
    (S : Finset ℤ) (T : Finset ℕ) :
    (S.filter (fun n => (Q.eval n).natAbs ∈ T)).card ≤ 2 * Q.natDegree * T.card := by
  apply (polynomial_natAbs_image_card_bound hQ _).trans
  apply Nat.mul_le_mul_left
  apply card_le_card
  intro a ha
  obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
  exact (mem_filter.mp hn).2

/-- The count is independent of the coefficients and of the location of the
finite set. This handles values near roots without a root-location hypothesis. -/
theorem polynomial_small_values_card_le {Q : ℤ[X]} (hQ : 0 < Q.natDegree)
    (S : Finset ℤ) {T : ℝ} (hT : 0 ≤ T) :
    ((S.filter (fun n => ((Q.eval n).natAbs : ℝ) ≤ T)).card : ℝ) ≤
      2 * Q.natDegree * (T + 1) := by
  have Heq : S.filter (fun n => ((Q.eval n).natAbs : ℝ) ≤ T) =
      S.filter (fun n => (Q.eval n).natAbs ∈ range (⌊T⌋₊ + 1)) := by
    apply filter_congr
    intro n hn
    rw [mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hT]
  rw [Heq]
  have H := polynomial_natAbs_preimage_card_le hQ S (range (⌊T⌋₊ + 1))
  rw [card_range] at H
  have H' : ((S.filter (fun n => (Q.eval n).natAbs ∈ range (⌊T⌋₊ + 1))).card : ℝ) ≤
      2 * Q.natDegree * ((⌊T⌋₊ : ℝ) + 1) := by exact_mod_cast H
  exact H'.trans (mul_le_mul_of_nonneg_left (by linarith [Nat.floor_le hT]) (by positivity))

end NairTenenbaum
