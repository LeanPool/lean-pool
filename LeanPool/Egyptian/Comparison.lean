/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A finite product–sum comparison with equality

This proves the variable-coefficient comparison in §3 of Kovač–Tang. The
logarithmic tangent inequality and finite summation by parts give the weak
majorization step and its strict equality case in a single argument. Only
the competitor needs to be ordered in this formulation.
-/

@[expose] public section

namespace Egyptian

open Finset

private theorem weighted_prefix (d w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i, i + 1 < n → w i ≤ w (i + 1))
    (hp : ∀ k < n, 0 ≤ ∑ i ∈ range k, d i) :
    ∑ i ∈ range n, d i * w i ≤ (∑ i ∈ range n, d i) * w (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have old := ih (fun i hi => hw i (by omega)) (fun k hk => hp k (by omega))
      simp only [Nat.succ_sub_one] at old ⊢
      rw [sum_range_succ (n := n+1), sum_range_succ (n := n+1), add_mul]
      exact add_le_add (old.trans (mul_le_mul_of_nonneg_left
        (hw n (by omega)) (hp (n + 1) (by omega)))) le_rfl

/-- If all shorter prefixes of a dominate those of b, a crossing at n forces
a strict reverse product inequality unless the two vectors coincide. -/
private theorem crossing {n : ℕ} {a b : ℕ → ℝ}
    (ha : ∀ i < n, 0 < a i) (hb : ∀ i < n, 0 < b i)
    (hm : ∀ i, i + 1 < n → b (i + 1) ≤ b i)
    (hp : ∀ k < n, ∑ i ∈ range k, b i ≤ ∑ i ∈ range k, a i)
    (hc : ∑ i ∈ range n, a i ≤ ∑ i ∈ range n, b i)
    (hd : ∃ i < n, a i ≠ b i) :
    ∏ i ∈ range n, a i < ∏ i ∈ range n, b i := by
  obtain ⟨j, hj, hjd⟩ := hd
  let d i := a i - b i
  let w i := (b i)⁻¹
  have bound := weighted_prefix d w n
    (fun i hi => inv_anti₀ (hb (i + 1) hi) (hm i hi))
    (fun k hk => by simpa [d, sum_sub_distrib] using sub_nonneg.mpr (hp k hk))
  have total : ∑ i ∈ range n, d i ≤ 0 := by
    simpa [d, sum_sub_distrib] using sub_nonpos.mpr hc
  have last : 0 ≤ w (n - 1) := (inv_pos.mpr (hb _ (by omega))).le
  have tangent (i : ℕ) (hi : i < n) :
      Real.log (a i / b i) ≤ d i * w i := by
    calc
      _ ≤ a i / b i - 1 := Real.log_le_sub_one_of_pos (div_pos (ha _ hi) (hb _ hi))
      _ = _ := by dsimp [d, w]; field_simp [(hb i hi).ne']
  have strict : Real.log (a j / b j) < d j * w j := by
    calc
      _ < a j / b j - 1 := Real.log_lt_sub_one_of_pos (div_pos (ha _ hj) (hb _ hj))
        (fun h => hjd ((div_eq_one_iff_eq (hb _ hj).ne').mp h))
      _ = _ := by dsimp [d, w]; field_simp [(hb j hj).ne']
  have logs := sum_lt_sum (s := range n) (fun i hi => tangent i (mem_range.mp hi))
    ⟨j, mem_range.mpr hj, strict⟩
  have neg : ∑ i ∈ range n, Real.log (a i / b i) < 0 :=
    logs.trans_le (bound.trans (mul_nonpos_of_nonpos_of_nonneg total last))
  have hlogs : (∑ i ∈ range n, Real.log (a i / b i)) =
      ∑ i ∈ range n, (Real.log (a i) - Real.log (b i)) :=
    sum_congr rfl fun i hi =>
      Real.log_div (ha i (mem_range.mp hi)).ne' (hb i (mem_range.mp hi)).ne'
  rw [hlogs] at neg
  rw [sum_sub_distrib, sub_neg, ← Real.log_prod (fun i hi => (ha i (mem_range.mp hi)).ne'),
    ← Real.log_prod (fun i hi => (hb i (mem_range.mp hi)).ne')] at neg
  exact (Real.log_lt_log_iff (prod_pos (fun i hi => ha i (mem_range.mp hi)))
    (prod_pos (fun i hi => hb i (mem_range.mp hi)))).mp neg

/-- Paper's variable comparison, with equality exactly at a matching prefix.
The coefficient c k represents βₖ u. All sums and products at k are taken
over indices strictly below k. -/
theorem variableComparison (a b c : ℕ → ℝ) (u : ℝ) (m : ℕ)
    (ha : ∀ i < m, 0 < a i) (hb : ∀ i < m, 0 < b i)
    (hm : ∀ i, i + 1 < m → b (i + 1) ≤ b i)
    (hc : ∀ k, 0 < k → k ≤ m → 0 < c k)
    (href : ∀ k, 0 < k → k ≤ m →
      (∑ i ∈ range k, a i) + c k * ∏ i ∈ range k, a i = u)
    (hcomp : ∀ k, 0 < k → k ≤ m →
      (∑ i ∈ range k, b i) + c k * ∏ i ∈ range k, b i ≤ u) :
    ∀ k ≤ m, (∑ i ∈ range k, b i) ≤ ∑ i ∈ range k, a i ∧
      ((∑ i ∈ range k, a i) ≤ ∑ i ∈ range k, b i → ∀ i < k, a i = b i) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    by_cases h : (∑ i ∈ range k, a i) ≤ ∑ i ∈ range k, b i
    · have same : ∀ i < k, a i = b i := by
        by_contra! diff
        have hkpos : 0 < k := by obtain ⟨i, hi, _⟩ := diff; omega
        have lt := crossing (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
          (fun i hi => hm i (by omega)) (fun j hj => (ih j hj (by omega)).1) h diff
        have := mul_lt_mul_of_pos_left lt (hc k hkpos hk)
        linarith [href k hkpos hk, hcomp k hkpos hk]
      exact ⟨(sum_congr rfl (fun i hi => (same i (mem_range.mp hi)).symm)).le, fun _ => same⟩
    · exact ⟨(lt_of_not_ge h).le, fun contra => (h contra).elim⟩

end Egyptian
