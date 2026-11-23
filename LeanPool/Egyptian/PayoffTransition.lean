/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Comparison
public import LeanPool.Egyptian.Payoff
import Mathlib.Tactic.Positivity.Finset

/-!
# The comparison at the first decrease of a cleared numerator

The inputs are the reciprocal terms `v i`. Multiplying the reciprocal
remainder by the common denominator supplies precisely the prefix inequalities
used here. The final index is written as `m+1`, so that the last denominator
has index `m`.
-/

@[expose] public section

namespace Egyptian.Payoff

open Finset

/-- The continuous comparison terms from the paper. -/
noncomputable def reference (t : ℝ) (i : ℕ) : ℝ := 1 / (orbit t i + 1)

theorem reference_pos {t : ℝ} (ht : 1 ≤ t) (i : ℕ) : 0 < reference t i := by
  have := one_le_orbit ht i
  unfold reference
  positivity

theorem reference_sum {t : ℝ} (ht : 1 ≤ t) (k : ℕ) :
    (∑ i ∈ range k, reference t i) = 1 / t - 1 / orbit t k := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    rw [sum_range_succ, ih, orbit, phi, reference]
    have h := one_le_orbit ht k
    field_simp [show orbit t k ≠ 0 by linarith, show orbit t k + 1 ≠ 0 by linarith]
    ring

theorem reference_prod {t : ℝ} (ht : 1 ≤ t) (k : ℕ) :
    (∏ i ∈ range k, reference t i) = t / orbit t k := by
  induction k with
  | zero => simp [orbit, show t ≠ 0 by linarith]
  | succ k ih =>
    rw [prod_range_succ, ih, orbit, phi, reference, div_mul_eq_div_div, mul_one_div]

/-- The no-decrease bound, in the positive-remainder form. -/
theorem no_decrease {t : ℝ} (ht : 1 ≤ t) (v : ℕ → ℝ) (m : ℕ)
    (hv : ∀ i < m, 0 < v i) (hm : ∀ i, i + 1 < m → v (i + 1) ≤ v i)
    (hc : ∀ k, 0 < k → k ≤ m →
      (∑ i ∈ range k, v i) + (1 / t) * ∏ i ∈ range k, v i ≤ 1 / t) :
    1 / orbit t m ≤ 1/t - ∑ i ∈ range m, v i := by
  have h := variableComparison (reference t) v (fun _ => 1/t) (1/t) m
    (fun i _ => reference_pos ht i) hv hm (fun _ _ _ => by positivity)
    (fun k _ _ => by rw [reference_sum ht, reference_prod ht]; field_simp; ring) hc
  have he := (h m le_rfl).1
  rw [reference_sum ht] at he
  linarith

/-- At the first fall to the fraction δ of the initial numerator, the
remainder is strictly larger than δ times the continuous reference error. -/
theorem first_decrease {t δ : ℝ} (ht : 1 ≤ t) (hd : 0 < δ) (hd' : δ < 1)
    (v : ℕ → ℝ) (m : ℕ) (hv : ∀ i < m + 1, 0 < v i)
    (hm : ∀ i, i + 1 < m + 1 → v (i + 1) ≤ v i)
    (hc : ∀ k, 0 < k → k ≤ m →
      (∑ i ∈ range k, v i) + (1 / t) * ∏ i ∈ range k, v i ≤ 1 / t)
    (hc' : (∑ i ∈ range (m + 1), v i) + (δ / t) * ∏ i ∈ range (m + 1), v i ≤ 1 / t) :
    δ / orbit t (m+1) < 1/t - ∑ i ∈ range (m+1), v i := by
  let a i := if i = m then 1/(orbit t m + δ) else reference t i
  let c k := if k = m+1 then δ/t else 1/t
  have ht' : 0 < t := by linarith
  have hq : 0 < orbit t m := by have := one_le_orbit ht m; linarith
  have hqd : 0 < orbit t m + δ := by positivity
  have hq1 : 0 < orbit t m + 1 := by positivity
  have sa (k : ℕ) (hk : k ≤ m) : (∑ i ∈ range k, a i) = 1/t - 1/orbit t k :=
    (sum_congr rfl (fun i hi => ite_eq_right (by have := mem_range.mp hi; omega))).trans
      (reference_sum ht k)
  have pa (k : ℕ) (hk : k ≤ m) : (∏ i ∈ range k, a i) = t / orbit t k :=
    (prod_congr rfl (fun i hi => ite_eq_right (by have := mem_range.mp hi; omega))).trans
      (reference_prod ht k)
  have h := variableComparison a v c (1/t) (m+1) (by
      intro i _
      dsimp [a]
      split
      · positivity
      · exact reference_pos ht i) hv hm (by
      intro k _ _
      dsimp [c]
      split <;> positivity) (by
      intro k _ hk
      by_cases he : k = m+1
      · subst k
        rw [sum_range_succ, prod_range_succ, sa m le_rfl, pa m le_rfl]
        simp only [a, c, ite_true]
        field_simp
        ring
      · have hkm : k ≤ m := by omega
        rw [sa _ hkm, pa _ hkm]
        simp only [c, ite_eq_right he]
        field_simp
        ring) (by
      intro k hk hkm
      by_cases he : k = m+1
      · simpa [c, he] using hc'
      · simpa [c, he] using hc k hk (by omega))
  have hs := (h (m+1) le_rfl).1
  rw [sum_range_succ (f := a), sa m le_rfl] at hs
  simp only [a, ite_true] at hs
  have hlast : δ / orbit t (m+1) < 1/orbit t m - 1/(orbit t m + δ) := by
    rw [orbit, phi]
    field_simp
    nlinarith [mul_pos (mul_pos hq hd) (sub_pos.mpr hd')]
  linarith

end Egyptian.Payoff
