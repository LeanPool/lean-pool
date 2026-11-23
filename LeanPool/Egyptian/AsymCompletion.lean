/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Asymptotic

/-!
# Sorting a finite prefix into a replacement expansion

This implements the multiset union used in the proof of Theorem 4. Inserting
one denominator at a time preserves the total reciprocal sum, sorts ties, and
shifts the infinite tail by exactly one position. The proof tracks order
statistics, so equal denominators require no separate argument.
-/

@[expose] public section

namespace Egyptian

open Filter
open scoped Topology BigOperators

/-- The insertion position of x exists in any expansion with convergent
reciprocal sum: an infinite sequence bounded above by x would have a
nonzero lower bound on all its summands. -/
private theorem exists_ge_den {q : ℚ} {d : ℕ → ℕ} (hd : Expansion q d) (x : ℕ) :
    ∃ j, x ≤ d j := by
  have hpos : (0 : ℝ) < 1 / (x + 1 : ℝ) := by positivity
  obtain ⟨j, hj⟩ := (hd.2.2.summable.tendsto_atTop_zero.eventually_lt_const hpos).exists
  by_contra! h
  have hsmall := h j
  have hdj := hd.1 j
  have hdx : (d j : ℝ) ≤ x + 1 := by exact_mod_cast (by omega : d j ≤ x+1)
  exact (not_le_of_gt hj) (one_div_le_one_div_of_le (by positivity) hdx)

private def insertAt (x J : ℕ) (d : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < J then d i else if i = J then x else d (i-1)

private theorem insertAt_tail (x J : ℕ) (d : ℕ → ℕ) (i : ℕ) (hi : J ≤ i) :
    insertAt x J d (i+1) = d i := by
  simp [insertAt, show ¬ i+1 < J by omega, show i+1 ≠ J by omega]

private theorem expansion_insertAt {q : ℚ} {d : ℕ → ℕ} {x J : ℕ}
    (hd : Expansion q d) (hx : 2 ≤ x) (hxJ : x ≤ d J)
    (hJ : ∀ i < J, d i < x) : Expansion (q + unit x) (insertAt x J d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold insertAt
    split_ifs <;> first | exact hd.1 _ | exact hx
  · apply monotone_nat_of_le_succ
    intro i
    by_cases hi : i < J
    · rw [insertAt, ite_eq_left hi]
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with hlt | heq
      · simp only [insertAt, ite_eq_left hlt]
        exact hd.2.1 (Nat.le_succ i)
      · change i+1 = J at heq
        simpa [insertAt, heq] using (hJ i hi).le
    · rw [insertAt_tail _ _ _ _ (by omega)]
      by_cases heq : i = J
      · simpa [insertAt, heq] using hxJ
      · simpa [insertAt, hi, heq] using hd.2.1 (Nat.sub_le i 1)
  · let e := insertAt x J d
    have he (i : ℕ) : e (i+(J+1)) = d (i+J) := by
      exact insertAt_tail _ _ _ (i+J) (by omega)
    have hpre : (∑ i ∈ Finset.range J, 1/(e i : ℝ)) = ∑ i ∈ Finset.range J, 1/(d i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [e, insertAt, Finset.mem_range.1 hi]
    have hsum := (hasSum_nat_add_iff' (f := fun i => 1/(d i : ℝ)) J).2 hd.2.2
    apply (hasSum_nat_add_iff' (f := fun i => 1/(e i : ℝ)) (J+1)).1
    simp only [he, Finset.sum_range_succ, hpre, Rat.cast_add]
    have hlast : e J = x := by simp [e, insertAt]
    rw [hlast]
    simpa [unit, add_sub_add_right_eq_sub] using hsum

/-- For every finite prefix of a nondecreasing expansion, merge that prefix
into an arbitrary expansion d of the residual. The result is itself an
expansion, its first k order statistics dominate the original ones in
reciprocal value, and it agrees with d after the k-position shift. -/
theorem sorted_completion {μ : ℚ} {a d : ℕ → ℕ} (hmin : ∀ i, 2 ≤ a i)
    (hmono : Monotone a)
    (hd : Expansion μ d) (k : ℕ) :
    ∃ c, Expansion (μ + recipSum (prefixTuple a k)) c ∧
      (∀ i < k, c i ≤ a i) ∧ (∀ᶠ j in atTop, c (k+j) = d j) := by
  classical
  induction k with
  | zero =>
    exact ⟨d, by simpa [recipSum, prefixTuple] using hd, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨e, he, hle, hshift⟩ := ih
    let x := a k
    have hex := exists_ge_den he x
    let J := Nat.find hex
    have hJ : x ≤ e J := Nat.find_spec hex
    have hlow (i : ℕ) (hi : i < J) : e i < x :=
      lt_of_not_ge (Nat.find_min hex hi)
    let c := insertAt x J e
    refine ⟨c, ?_, ?_, ?_⟩
    · simpa [prefixTuple, recipSum, List.range_succ, add_assoc, x]
        using expansion_insertAt he (hmin k) hJ hlow
    · intro i hi
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hik | hik
      · by_cases hlt : i < J
        · simpa [c, insertAt, hlt] using hle i hik
        · by_cases heq : i = J
          · exact (by simpa [c, insertAt, heq] using hJ : c i ≤ e i) |>.trans (hle i hik)
          · exact (by simpa [c, insertAt, hlt, heq] using he.2.1 (Nat.sub_le i 1) :
              c i ≤ e i) |>.trans (hle i hik)
      · subst i
        by_cases hlt : k < J
        · simpa [c, insertAt, hlt] using (hlow k hlt).le
        · by_cases heq : k = J
          · simp [c, insertAt, heq, x]
          · have hk : k-1 < k := by omega
            exact (by simp [c, insertAt, hlt, heq] : c k = e (k-1)) ▸
              (hle (k-1) hk).trans (hmono (Nat.sub_le k 1))
    · filter_upwards [eventually_ge_atTop J, hshift] with j hj h
      change insertAt x J e (k+1+j) = d j
      rw [show k+1+j = (k+j)+1 by omega, insertAt_tail _ _ _ _ (by omega), h]

end Egyptian
