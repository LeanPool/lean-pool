/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.Fekete.DeBruijnErdos
public import Mathlib.Analysis.PSeries

/-!
# Sharpness of the de Bruijn–Erdős condition

For a nonnegative monotone error `f`, the condition `∑ f n / n ^ 2 < ∞` in the de Bruijn–Erdős
theorem cannot be weakened. If the series diverges, the sequence
`u n = n * ∑_{i ≤ n} f i / i ^ 2` satisfies `u (m + n) ≤ u m + u n + f (m + n)` for *all* `m, n`
while `u n / n → ∞` (a variant of Füredi–Ruzsa, Claim 7). Together with
`NearlySubadditive.tendsto_atBot_or_exists_tendsto_of_summable` this gives an exact
characterisation: `∑ f n / n ^ 2 < ∞` if and only if no nearly `f`-subadditive sequence has
`u n / n → ∞`.

## Main statements

* `NearlySubadditive.witness`, `NearlySubadditive.witness_le_add`,
  `NearlySubadditive.tendsto_witness_div`: the construction.
* `summable_div_sq_iff_forall_not_tendsto_atTop`: the characterisation.

## TODO

Füredi and Ruzsa prove more (Theorem 4 of the journal version, Theorem 6 of the arXiv preprint):
when the series diverges there is a nearly `f`-subadditive sequence whose slopes `u n / n` take
every rational value.

## References

* [Z. Füredi, I. Z. Ruzsa, *Nearly subadditive sequences*][FurediRuzsa2020]
-/

@[expose] public section

noncomputable section

open Filter Finset
open scoped Topology

namespace NearlySubadditive

/-- The Füredi–Ruzsa witness `n * ∑_{i ≤ n} f i / i ^ 2`: a nearly `f`-subadditive sequence with
`u n / n → ∞` when `∑ f n / n ^ 2` diverges. -/
def witness (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  n * ∑ i ∈ range (n + 1), f i / (i : ℝ) ^ 2

variable {f : ℕ → ℝ}

/-- A block of `∑ f i / i ^ 2` above `m` is at most `f (m + n) * (1 / m - 1 / (m + n))`. -/
private theorem sum_block_le (hf0 : 0 ≤ f) (hf : Monotone f) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ∑ k ∈ range n, f (m + 1 + k) / ((m + 1 + k : ℕ) : ℝ) ^ 2 ≤
      f (m + n) * (1 / m - 1 / (m + n : ℕ)) := by
  have := sum_Ioc_inv_sq_le_sub (α := ℝ) hm.ne' (Nat.le_add_right m n)
  rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range,
    show m + n + 1 - (m + 1) = n by omega] at this
  rw [one_div, one_div]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left this (hf0 _))
  rw [mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (hf (by have := mem_range.1 hk; omega)) (sq_nonneg _)

/-- **A variant of Füredi–Ruzsa, Claim 7.** The witness is nearly `f`-subadditive for all pairs,
including those with an index `0`. Claim 7 sets `f 1 = a 1 = 0` and uses positive indices only.
Here the sum keeps the term `f 1 / 1 ^ 2`, which adds `n * f 1` to the witness: this preserves the
defect inequality and shifts every slope `u n / n` with `n > 0` by the constant `f 1`. -/
theorem witness_le_add (hf0 : 0 ≤ f) (hf : Monotone f) (m n : ℕ) :
    witness f (m + n) ≤ witness f m + witness f n + f (m + n) := by
  set A : ℕ → ℝ := fun p ↦ ∑ i ∈ range (p + 1), f i / (i : ℝ) ^ 2
  have hA : ∀ p q, A (p + q) = A p + ∑ k ∈ range q, f (p + 1 + k) / ((p + 1 + k : ℕ) : ℝ) ^ 2 :=
    fun p q ↦ by
      change ∑ i ∈ range (p + q + 1), _ = _
      rw [show p + q + 1 = p + 1 + q by omega]
      exact sum_range_add _ _ _
  have hw : ∀ p, witness f p = p * A p := fun _ ↦ rfl
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa [hw] using hf0 n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [hw] using hf0 m
  have h1 := sum_block_le hf0 hf hm n
  have h2 := sum_block_le hf0 hf hn m
  rw [add_comm n m] at h2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 := hA m n
  have e2 := hA n m
  rw [add_comm n m] at e2
  rw [hw, hw, hw]
  push_cast at h1 h2 e1 e2 ⊢
  have key : (m : ℝ) * (f (m + n) * (1 / m - 1 / (m + n))) +
      n * (f (m + n) * (1 / n - 1 / (m + n))) = f (m + n) := by
    field_simp; ring
  have b1 := mul_le_mul_of_nonneg_left h1 hmR.le
  have b2 := mul_le_mul_of_nonneg_left h2 hnR.le
  have p1 := congrArg (fun t ↦ (m : ℝ) * t) e1
  have p2 := congrArg (fun t ↦ (n : ℝ) * t) e2
  simp only [mul_add] at p1 p2
  rw [add_mul]
  linarith

/-- If `∑ f n / n ^ 2` diverges, the witness has `u n / n → ∞`. -/
theorem tendsto_witness_div (hf0 : 0 ≤ f)
    (hfs : ¬ Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) :
    Tendsto (fun n ↦ witness f n / n) atTop atTop := by
  have hA : Tendsto (fun n ↦ ∑ i ∈ range n, f i / (i : ℝ) ^ 2) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n ↦ div_nonneg (hf0 n) (sq_nonneg _)).1 hfs
  refine ((tendsto_add_atTop_iff_nat 1).2 hA).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [witness, this]

/-- The witness is nearly `f`-subadditive on every window. -/
theorem nearlySubadditive_witness (hf0 : 0 ≤ f) (hf : Monotone f) (μ : ℝ) (N : ℕ) :
    NearlySubadditive f μ N (witness f) :=
  .of_le_add fun m n _ _ ↦ witness_le_add hf0 hf m n

end NearlySubadditive

open NearlySubadditive in
/-- **Sharpness of de Bruijn–Erdős.** For a nonnegative monotone `f`, `∑ f n / n ^ 2 < ∞` if and
only if no sequence with `u (m + n) ≤ u m + u n + f (m + n)` for all `m, n` has `u n / n → ∞`. -/
theorem summable_div_sq_iff_forall_not_tendsto_atTop (hf0 : 0 ≤ f) (hf : Monotone f) :
    (Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) ↔
      ∀ u : ℕ → ℝ, (∀ m n, u (m + n) ≤ u m + u n + f (m + n)) →
        ¬ Tendsto (fun n ↦ u n / n) atTop atTop := by
  refine ⟨fun hfs u hu htop ↦ ?_, fun H ↦ ?_⟩
  · have h : NearlySubadditive f 2 0 u := .of_le_add fun m n _ _ ↦ hu m n
    rcases h.tendsto_atBot_or_exists_tendsto_of_summable one_lt_two hf hfs with hbot | ⟨L, hL⟩
    · exact hbot.not_tendsto disjoint_atBot_atTop htop
    · exact not_tendsto_atTop_of_tendsto_nhds hL htop
  · by_contra hfs
    exact H _ (witness_le_add hf0 hf)
      (tendsto_witness_div hf0 hfs)
