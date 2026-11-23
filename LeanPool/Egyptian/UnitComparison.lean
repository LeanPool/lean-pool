/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Comparison
public import LeanPool.Egyptian.Defs

/-!
# Finite extremality of a unit-fraction tail

Kovač–Tang use the classical theorem of Curtiss, Takenouchi, and Nathanson at
the unit boundary. We deduce it from the paper's product–sum comparison. Each
competitor prefix leaves a strictly positive integer after clearing denominators.
-/

@[expose] public section

namespace Egyptian

open Finset

/-- Integral numerator of the error after clearing denominators.
This finite recurrence is the cleared-numerator calculation of §3. -/
private theorem cleared (T : ℕ) (hT : 0 < T) (d : ℕ → ℕ) (k : ℕ)
    (hd : ∀ i < k, 0 < d i) :
    ∃ z : ℤ, (1 / (T : ℝ) - ∑ i ∈ range k, 1 / (d i : ℝ)) *
      ((T : ℝ) * ∏ i ∈ range k, (d i : ℝ)) = z := by
  induction k with
  | zero =>
    exact ⟨1, by simp [Nat.ne_of_gt hT]⟩
  | succ k ih =>
    obtain ⟨z, hz⟩ := ih (fun i hi => hd _ (by omega))
    refine ⟨z * (d k : ℤ) - T * ∏ i ∈ range k, (d i : ℤ), ?_⟩
    push_cast
    rw [sum_range_succ, prod_range_succ, ← hz]
    field_simp [(Nat.cast_pos.mpr (hd k (by omega)) : (0 : ℝ) < d k).ne']
    ring

private theorem competitorBound (T : ℕ) (hT : 0 < T) (d : ℕ → ℕ) (k : ℕ)
    (hd : ∀ i < k, 0 < d i)
    (hlt : (∑ i ∈ range k, 1 / (d i : ℝ)) < 1 / (T : ℝ)) :
    (∑ i ∈ range k, 1 / (d i : ℝ)) + 1 / (T : ℝ) *
      ∏ i ∈ range k, (1 / (d i : ℝ)) ≤ 1 / (T : ℝ) := by
  have pos : (0 : ℝ) < T * ∏ i ∈ range k, (d i : ℝ) :=
    mul_pos (Nat.cast_pos.mpr hT) (prod_pos (fun i hi => Nat.cast_pos.mpr (hd i (mem_range.mp hi))))
  obtain ⟨z, hz⟩ := cleared T hT d k hd
  have hzpos : (0 : ℝ) < z := hz ▸ mul_pos (sub_pos.mpr hlt) pos
  have hz1 : (1 : ℤ) ≤ z := by exact_mod_cast (show (0 : ℤ) < z by exact_mod_cast hzpos)
  have hr : (1 : ℝ) ≤ z := by exact_mod_cast hz1
  rw [← hz] at hr
  have hh := (div_le_iff₀ pos).mpr hr
  simp only [one_div, prod_inv_distrib, mul_inv_rev, mul_comm] at hh ⊢
  linarith only [hh]

private theorem iter_pos (T : ℕ) (hT : 0 < T) (i : ℕ) : 0 < unitIter T i := by
  induction i with
  | zero => exact hT
  | succ i ih => exact Nat.mul_pos ih (Nat.succ_pos _)

private theorem refProduct (T k : ℕ) :
    T * ∏ i ∈ range k, (unitIter T i + 1) = unitIter T k := by
  induction k with
  | zero => simp [unitIter]
  | succ k ih => rw [prod_range_succ, ← mul_assoc, ih]; rfl

theorem unitPrefixSum (T k : ℕ) (hT : 0 < T) :
    (∑ i ∈ range k, (1 / ((unitIter T i : ℝ) + 1))) =
      1 / (T : ℝ) - 1 / (unitIter T k : ℝ) := by
  induction k with
  | zero => simp [unitIter]
  | succ k ih =>
    rw [sum_range_succ, ih]
    simp only [unitIter, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have h := (Nat.cast_pos.mpr (iter_pos T hT k) : (0 : ℝ) < unitIter T k)
    field_simp [h.ne', (by positivity : (0 : ℝ) < unitIter T k + 1).ne']
    ring

/-- Competing with the greedy approximation to 1/T at any length. Equality of
the two reciprocal sums forces term-by-term equality, also with repetitions. -/
theorem unitFiniteComparison (T m : ℕ) (hT : 0 < T) (d : ℕ → ℕ)
    (hd : ∀ i < m, 0 < d i)
    (hm : ∀ i, i + 1 < m → d i ≤ d (i + 1))
    (hs : (∑ i ∈ range m, 1 / (d i : ℝ)) < 1 / (T : ℝ)) :
    (∑ i ∈ range m, 1 / (d i : ℝ)) ≤ ∑ i ∈ range m, 1 / ((unitIter T i : ℝ) + 1) ∧
    ((∑ i ∈ range m, 1 / ((unitIter T i : ℝ) + 1)) ≤ ∑ i ∈ range m, 1 / (d i : ℝ) →
      ∀ i < m, d i = unitIter T i + 1) := by
  let a (i : ℕ) : ℝ := 1 / ((unitIter T i : ℝ) + 1)
  let b (i : ℕ) : ℝ := 1 / (d i : ℝ)
  have ref (k : ℕ) :
      (∑ i ∈ range k, a i) + (1 / (T : ℝ)) * ∏ i ∈ range k, a i = 1 / (T : ℝ) := by
    dsimp [a]
    rw [unitPrefixSum T k hT]
    have ht : (T : ℝ) * ∏ i ∈ range k, ((unitIter T i : ℝ) + 1) = unitIter T k := by
      exact_mod_cast refProduct T k
    simp only [one_div, prod_inv_distrib]
    rw [← mul_inv, ht, sub_add_cancel]
  have comp (k : ℕ) (hk : k ≤ m) :
      (∑ i ∈ range k, b i) + (1 / (T : ℝ)) * ∏ i ∈ range k, b i ≤ 1 / (T : ℝ) := by
    apply competitorBound T hT d k (fun i hi => hd i (by omega))
    exact lt_of_le_of_lt (sum_le_sum_of_subset_of_nonneg (range_mono hk)
      (fun i _ _ => by positivity)) hs
  have both := variableComparison a b (fun _ => 1 / (T : ℝ)) (1 / (T : ℝ)) m
    (fun i _ => by dsimp [a]; positivity)
    (fun i hi => one_div_pos.mpr (Nat.cast_pos.mpr (hd i hi)))
    (fun i hi => one_div_le_one_div_of_le (Nat.cast_pos.mpr (hd i (by omega)))
      (Nat.cast_le.mpr (hm i hi)))
    (fun _ _ _ => one_div_pos.mpr (Nat.cast_pos.mpr hT))
    (fun k _ _ => ref k) (fun k _ hk => comp k hk) m le_rfl
  refine ⟨both.1, ?_⟩
  intro he i hi
  have same := both.2 he i hi
  simp only [a, b, one_div, inv_inj] at same
  exact_mod_cast same.symm

end Egyptian
