/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Layered
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

/-!
# Weight caps in `F₅^k` (ledger L16.5)

`wcap k s = {c ∈ {0,1,2}^k : #{i : c i = 1} = s}` is a cap in `F₅^k`, of size `C(k,s) · 2^(k-s)`,
and for every
`k` some `s ≤ k` gives size at least `3^k / (k+1)`.
-/

@[expose] public section

namespace GapExtremal

open Finset

/-- The ternary digits `{0, 1, 2} ⊆ F₅`. -/
def tern : Finset F5 := {0, 1, 2}

/-- Number of coordinates equal to `1`. -/
def ones {k : ℕ} (c : Fin k → F5) : ℕ := (univ.filter fun i => c i = 1).card

/-- The weight cap. -/
def wcap (k s : ℕ) : Finset (Fin k → F5) := (Fintype.piFinset fun _ => tern).filter fun c =>
  ones c = s

theorem coord2 : ∀ x y : F5, x ∈ tern → y ∈ tern → x + 2 * (y - x) ∈ tern →
    (if y = 1 then 1 else 0 : ℕ) = (if x = 1 then 1 else 0) + (if x ≠ y then 1 else 0) := by
  decide

theorem coord3 : ∀ x y : F5, x ∈ tern → y ∈ tern → x + 3 * (y - x) ∈ tern →
    (if x + 3 * (y - x) = 1 then 1 else 0 : ℕ) = (if x = 1 then 1 else 0) + (if x ≠ y then 1 else
      0) := by
  decide

theorem coord4 : ∀ x y : F5, x ∈ tern → y ∈ tern → x + 4 * (y - x) ∈ tern →
    (if x = 1 then 1 else 0 : ℕ) = (if y = 1 then 1 else 0) + (if x ≠ y then 1 else 0) := by
  decide

theorem t_cases : ∀ t : F5, t ≠ 0 → t ≠ 1 → t = 2 ∨ t = 3 ∨ t = 4 := by decide

theorem ones_eq_sum {k : ℕ} (c : Fin k → F5) : ones c = ∑ i, (if c i = 1 then 1 else 0 : ℕ) := by
  rw [ones, Finset.card_filter]

/-- **L16.5.** Weight caps are caps. -/
theorem isCap_wcap (k s : ℕ) : IsCap F5 (wcap k s : Set (Fin k → F5)) := by
  intro P hP R hR hne t ht0 ht1 hS
  simp only [wcap, Finset.coe_filter, Fintype.mem_piFinset, Set.mem_ofPred_eq] at hP hR hS
  obtain ⟨hPt, hPw⟩ := hP
  obtain ⟨hRt, hRw⟩ := hR
  obtain ⟨hSt, hSw⟩ := hS
  have hD : 0 < ∑ i, (if P i ≠ R i then 1 else 0 : ℕ) := by
    obtain ⟨i, hi⟩ : ∃ i, P i ≠ R i := by
      by_contra h; push Not at h; exact hne (funext h)
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by simp [hi]⟩
  have hc : ∀ i, (P + t • (R - P)) i = P i + t * (R i - P i) := fun i => by simp
  rcases t_cases t ht0 ht1 with rfl | rfl | rfl
  · have : ones R = ones P + ∑ i, (if P i ≠ R i then 1 else 0 : ℕ) := by
      rw [ones_eq_sum, ones_eq_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => coord2 _ _ (hPt i) (hRt i) (hc i ▸ hSt i)
    omega
  · have : ones (P + (3 : F5) • (R - P)) = ones P + ∑ i, (if P i ≠ R i then 1 else 0 : ℕ) := by
      rw [ones_eq_sum, ones_eq_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc i]
      exact coord3 _ _ (hPt i) (hRt i) (hc i ▸ hSt i)
    omega
  · have : ones P = ones R + ∑ i, (if P i ≠ R i then 1 else 0 : ℕ) := by
      rw [ones_eq_sum, ones_eq_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => coord4 _ _ (hPt i) (hRt i) (hc i ▸ hSt i)
    omega

/-- The weight cap as a disjoint union over the set of `1`-coordinates. -/
theorem wcap_eq_biUnion (k s : ℕ) :
    wcap k s = (powersetCard s (univ : Finset (Fin k))).biUnion fun S =>
      Fintype.piFinset fun i => if i ∈ S then ({1} : Finset F5) else {0, 2} := by
  ext c
  simp only [wcap, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_biUnion,
    Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨ht, hw⟩
    refine ⟨univ.filter fun i => c i = 1, hw, fun i => ?_⟩
    by_cases h : c i = 1
    · simp [h]
    · have := ht i
      simp only [tern, Finset.mem_insert, Finset.mem_singleton] at this
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, ite_false, Finset.mem_insert,
        Finset.mem_singleton]
      tauto
  · rintro ⟨S, hS, hc⟩
    have hones : (univ.filter fun i => c i = 1) = S := by
      ext i
      have := hc i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h1
        by_contra hi
        rw [ite_eq_right hi] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h <;> rw [h] at h1 <;> revert h1 <;> decide
      · intro hi
        rw [ite_eq_left hi] at this
        simpa using this
    refine ⟨fun i => ?_, by rw [ones, hones, hS]⟩
    have := hc i
    split_ifs at this
    · simp only [Finset.mem_singleton] at this; simp [tern, this]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h <;> simp [tern, h]

theorem card_wcap (k s : ℕ) : (wcap k s).card = k.choose s * 2 ^ (k - s) := by
  rw [wcap_eq_biUnion, Finset.card_biUnion]
  · have : ∀ S ∈ powersetCard s (univ : Finset (Fin k)),
        (Fintype.piFinset fun i => if i ∈ S then ({1} : Finset F5) else {0, 2}).card = 2 ^ (k - s)
          := by
      intro S hS
      rw [Fintype.card_piFinset]
      have hSc := (Finset.mem_powersetCard.mp hS).2
      calc ∏ i, (if i ∈ S then ({1} : Finset F5) else {0, 2}).card
          = ∏ i, (if i ∈ S then 1 else 2) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            split_ifs <;> decide
        _ = 2 ^ (k - s) := by
            rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
            congr 1
            rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
            simp [hSc]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  · intro S hS S' hS' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro c hc hc'
    simp only [Fintype.mem_piFinset] at hc hc'
    apply hne
    ext i
    have h1 := hc i
    have h2 := hc' i
    constructor
    · intro hi
      rw [ite_eq_left hi] at h1
      by_contra hi'
      rw [ite_eq_right hi'] at h2
      simp only [Finset.mem_singleton] at h1
      simp only [Finset.mem_insert, Finset.mem_singleton, h1] at h2
      revert h2; decide
    · intro hi
      rw [ite_eq_left hi] at h2
      by_contra hi'
      rw [ite_eq_right hi'] at h1
      simp only [Finset.mem_singleton] at h2
      simp only [Finset.mem_insert, Finset.mem_singleton, h2] at h1
      revert h1; decide

theorem sum_card_wcap (k : ℕ) : ∑ s ∈ range (k + 1), k.choose s * 2 ^ (k - s) = 3 ^ k := by
  have := (add_pow (1 : ℕ) 2 k)
  rw [show (1 : ℕ) + 2 = 3 by norm_num] at this
  rw [this]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [one_pow, one_mul, mul_comm, Nat.cast_id]

/-- Some weight gives at least the average `3^k / (k+1)`. -/
theorem exists_large_wcap (k : ℕ) : ∃ s ≤ k, 3 ^ k ≤ (k + 1) * (wcap k s).card := by
  obtain ⟨s, hs, h⟩ := Finset.exists_le_of_sum_le (s := range (k + 1)) (by simp)
    (f := fun _ => 3 ^ k) (g := fun s => (k + 1) * (k.choose s * 2 ^ (k - s))) (by
      rw [← Finset.mul_sum, sum_card_wcap, Finset.sum_const, Finset.card_range, smul_eq_mul])
  exact ⟨s, Nat.lt_succ_iff.mp (Finset.mem_range.mp hs), by rw [card_wcap]; exact h⟩

end GapExtremal
