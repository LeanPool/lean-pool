/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential bounds in a normed algebra

Bounds for `NormedSpace.exp`, its finite Taylor remainders, and products of exponentials.
These estimates form a common analytic foundation for BCH and product-formula errors.

## Main results

* `norm_exp_le`: the exponential norm is bounded by the real exponential of the norm.
* `norm_sub_sum_le_real_exp_tail`: a factorial coefficient bound controls a series tail.
* `norm_exp_sub_sum_le`: the Taylor remainder is bounded by the scalar exponential tail.
* `real_exp_sub_sum_le_geometric`: a factorial-geometric bound for every scalar tail.
* `norm_exp_mul_exp_sub_one_le`: a product estimate independent of convergence thresholds.
* `TrotterError.exp_neg_mul_self`, `TrotterError.exp_mul_neg_self`: inverse cancellation.
* `exp_log_two_denominator_bounds`: positivity and upper bound for the BCH denominator.
-/

@[expose] public section

open Finset NormedSpace

namespace TrotterError

/-- `exp (-x) * exp x = 1`. -/
lemma exp_neg_mul_self {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (x : 𝔸) :
    exp (-x) * exp x = 1 := by
  simpa using (exp_add_of_commute (Commute.refl x).neg_left).symm

/-- `exp x * exp (-x) = 1`. -/
lemma exp_mul_neg_self {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (x : 𝔸) :
    exp x * exp (-x) = 1 := by
  simpa using (exp_add_of_commute (Commute.refl x).neg_right).symm

end TrotterError

namespace FQFP

/-- The BCH convergence denominator lies in `(0, 1]` on the nonnegative convergence range. -/
lemma exp_log_two_denominator_bounds {s : ℝ} (hs : 0 ≤ s) (h : s < Real.log 2) :
    0 < 2 - Real.exp s ∧ 2 - Real.exp s ≤ 1 := by
  have he : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono h
         _ = 2 := Real.exp_log (by norm_num)
  constructor
  · linarith only [he]
  · linarith only [Real.add_one_le_exp s, hs]

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- Each term of the exponential series is bounded by `‖a‖^n / n!`. -/
lemma norm_exp_term_le [NormOneClass 𝔸] (a : 𝔸) (n : ℕ) :
    ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ ≤ ‖a‖ ^ n / Nat.factorial n := by
  rw [norm_smul, norm_inv, ← Rat.norm_cast_real, Real.norm_eq_abs, inv_mul_eq_div]
  norm_cast
  gcongr
  exact norm_pow_le ..

/-- The exponential norm is bounded by the real exponential of the norm. -/
lemma norm_exp_le [NormOneClass 𝔸] (a : 𝔸) : ‖exp a‖ ≤ Real.exp ‖a‖ := by
  rw [NormedSpace.exp_eq_tsum ℚ, Real.exp_eq_exp_ℝ,
    ← (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq]
  have hnsumm : Summable fun n ↦ ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ :=
    (Real.summable_pow_div_factorial ‖a‖).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (norm_exp_term_le a)
  calc
    _ ≤ ∑' n, ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ := norm_tsum_le_tsum_norm hnsumm
    _ ≤ ∑' n, ‖a‖ ^ n / Nat.factorial n :=
      hnsumm.tsum_le_tsum (norm_exp_term_le a) (Real.summable_pow_div_factorial ‖a‖)

variable [CompleteSpace 𝔸]

/-! ### The real exponential series and its tails -/

/-- The real exponential series sums to `Real.exp`. -/
lemma hasSum_real_exp (r : ℝ) :
    HasSum (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ * r ^ n) (Real.exp r) := by
  simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
    (exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) r)

/-- The tail of the real exponential series after the first `k` terms sums to `Real.exp r`
minus the corresponding partial sum. -/
lemma hasSum_real_exp_tail (r : ℝ) (k : ℕ) :
    HasSum (fun n : ℕ => (Nat.factorial (n + k) : ℝ)⁻¹ * r ^ (n + k))
      (Real.exp r - ∑ i ∈ range k, (Nat.factorial i : ℝ)⁻¹ * r ^ i) := by
  have h := hasSum_real_exp r
  have hsumm : Summable fun n : ℕ => (Nat.factorial (n + k) : ℝ)⁻¹ * r ^ (n + k) :=
    (summable_nat_add_iff k).mpr h.summable
  rw [hsumm.hasSum_iff]
  have hsplit := h.summable.sum_add_tsum_nat_add k
  rw [h.tsum_eq] at hsplit
  linarith

/-! ### Bounds for the exponential series -/

/-- A factorial coefficient majorant controls every tail of a convergent homogeneous series. -/
lemma norm_sub_sum_le_real_exp_tail {B : Type*} [NormedAddCommGroup B]
    (u : ℕ → B) (p : B) (s : ℝ) (ht : HasSum u p)
    (hu : ∀ n, ‖u n‖ ≤ s ^ n / Nat.factorial n) (n : ℕ) :
    ‖p - ∑ i ∈ range n, u i‖ ≤
      Real.exp s - ∑ i ∈ range n, s ^ i / Nat.factorial i := by
  have heq : p - ∑ i ∈ range n, u i = ∑' k, u (k + n) := by
    have h := ht.summable.sum_add_tsum_nat_add n
    rw [ht.tsum_eq] at h
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)
  rw [heq]
  refine tsum_of_norm_bounded ?_ fun k ↦ hu (k + n)
  simpa only [div_eq_inv_mul] using hasSum_real_exp_tail s n

/-- The parametrized exponential remainder bound: the tail of the exponential series after
the first `n` terms is bounded by the corresponding tail of the real exponential series. -/
theorem norm_exp_sub_sum_le [NormOneClass 𝔸] (x : 𝔸) (n : ℕ) :
    ‖exp x - ∑ i ∈ range n, (Nat.factorial i : ℚ)⁻¹ • x ^ i‖
      ≤ Real.exp ‖x‖ - ∑ i ∈ range n, ‖x‖ ^ i / Nat.factorial i :=
  norm_sub_sum_le_real_exp_tail _ _ _
    (exp_series_hasSum_exp' (𝕂 := ℚ) x) (norm_exp_term_le x) n

/-- `‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1` in any complete normed algebra. -/
theorem norm_exp_sub_one_le [NormOneClass 𝔸] (x : 𝔸) :
    ‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  simpa using norm_exp_sub_sum_le x 1

/-- The distance from a product of exponentials to `1` is bounded by the scalar exponential
at the sum of the norms, minus `1`. -/
theorem norm_exp_mul_exp_sub_one_le [NormOneClass 𝔸] (a b : 𝔸) :
    ‖exp a * exp b - 1‖ ≤ Real.exp (‖a‖ + ‖b‖) - 1 := by
  rw [show exp a * exp b - 1 = (exp a - 1) * exp b + (exp b - 1) by
    noncomm_ring]
  calc
    _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
    _ ≤ (Real.exp ‖a‖ - 1) * Real.exp ‖b‖ + (Real.exp ‖b‖ - 1) :=
      add_le_add
        (mul_le_mul (norm_exp_sub_one_le a) (norm_exp_le b) (norm_nonneg _)
          (sub_nonneg.mpr (Real.one_le_exp (norm_nonneg a))))
        (norm_exp_sub_one_le b)
    _ = Real.exp (‖a‖ + ‖b‖) - 1 := by
      rw [Real.exp_add]
      ring

/-- **The BCH smallness condition**: `‖exp a * exp b - 1‖ < 1` when `‖a‖ + ‖b‖ < log 2`, which is
what puts `exp a * exp b` inside the ball where the log series converges. -/
theorem norm_exp_mul_exp_sub_one_lt_one [NormOneClass 𝔸] (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖exp a * exp b - 1‖ < 1 := by
  refine (norm_exp_mul_exp_sub_one_le a b).trans_lt ?_
  have h := Real.exp_strictMono hab
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  linarith

/-- **The BCH smallness condition, one-sided form**: `‖exp a - 1‖ < 1` when `‖a‖ < log 2`. -/
theorem norm_exp_sub_one_lt_one [NormOneClass 𝔸] (a : 𝔸) (ha : ‖a‖ < Real.log 2) :
    ‖exp a - 1‖ < 1 := by
  have h := norm_exp_mul_exp_sub_one_lt_one a (0 : 𝔸) (by simpa using ha)
  simpa [exp_zero] using h

/-! ### Taylor remainders of the real exponential

A factorial-geometric majorant controls every real exponential tail on `[0, 1)`.
Its low-order specializations give polynomial bounds on smaller intervals.

These are statements about `Real.exp` alone, so they carry no algebra variables. -/

/-- A factorial-geometric majorant for the real exponential tail. -/
theorem real_exp_sub_sum_le_geometric {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (n : ℕ) :
    Real.exp s - ∑ i ∈ range n, (Nat.factorial i : ℝ)⁻¹ * s ^ i ≤
      s ^ n / ((Nat.factorial n : ℝ) * (1 - s)) := by
  have ht := hasSum_real_exp_tail s n
  have hg := ((hasSum_geometric_of_lt_one hs hs1).mul_left (s ^ n)).mul_right
    (Nat.factorial n : ℝ)⁻¹
  have hc : ∀ k : ℕ, (Nat.factorial (k + n) : ℝ)⁻¹ * s ^ (k + n) ≤
      s ^ n * s ^ k * (Nat.factorial n : ℝ)⁻¹ := by
    intro k
    have hf : (Nat.factorial n : ℝ) ≤ Nat.factorial (k + n) := by
      exact_mod_cast Nat.factorial_le (show n ≤ k + n by lia)
    have hi := inv_anti₀ (by positivity : (0 : ℝ) < Nat.factorial n) hf
    calc _ ≤ (Nat.factorial n : ℝ)⁻¹ * s ^ (k + n) :=
            mul_le_mul_of_nonneg_right hi (pow_nonneg hs _)
         _ = _ := by
           ring
  calc
    _ ≤ s ^ n * (1 - s)⁻¹ * (Nat.factorial n : ℝ)⁻¹ := by
      rw [← ht.tsum_eq, ← hg.tsum_eq]
      exact ht.summable.tsum_le_tsum hc hg.summable
    _ = _ := by
      rw [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Every exponential tail of order at least two is bounded by its first omitted power
on the nonnegative half-radius ball. -/
lemma real_exp_sub_sum_le_pow {s : ℝ} (hs : 0 ≤ s) (hs_half : s < 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) :
    Real.exp s - ∑ i ∈ range n, s ^ i / Nat.factorial i ≤ s ^ n := by
  have hf : (2 : ℝ) ≤ Nat.factorial n := by
    exact_mod_cast (show 2 ≤ Nat.factorial n from Nat.factorial_le hn)
  have hd : 1 ≤ (Nat.factorial n : ℝ) * (1 - s) := by
    have h := mul_le_mul_of_nonneg_right hf (show 0 ≤ 1 - s by linarith only [hs_half])
    linarith only [h, hs_half]
  calc
    _ ≤ s ^ n / ((Nat.factorial n : ℝ) * (1 - s)) := by
      simpa only [div_eq_inv_mul] using
        real_exp_sub_sum_le_geometric hs (show s < 1 by linarith only [hs_half]) n
    _ ≤ s ^ n := by
      rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)]
      exact le_mul_of_one_le_right (pow_nonneg hs n) hd

/-- **Third-order Taylor remainder of `Real.exp`, `1/(1 - r)` form**:
`exp r - 1 - r - r²/2 ≤ r³ / (6 (1 - r))` for `0 ≤ r < 1`. -/
theorem real_exp_third_order_le_div {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.exp r - 1 - r - r ^ 2 / 2 ≤ r ^ 3 / (6 * (1 - r)) := by
  simpa [sum_range_succ, Nat.factorial, sub_eq_add_neg, div_eq_mul_inv,
    add_comm, add_left_comm, add_assoc, mul_comm] using real_exp_sub_sum_le_geometric hr hr1 3

/-- **Third-order Taylor remainder of `Real.exp`, cubic form**:
`exp r - 1 - r - r²/2 ≤ r³` for `0 ≤ r < 5/6`. -/
theorem real_exp_third_order_le_cube {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 5 / 6) :
    Real.exp r - 1 - r - r ^ 2 / 2 ≤ r ^ 3 := by
  have hr1' : r < 1 := by linarith
  calc Real.exp r - 1 - r - r ^ 2 / 2 ≤ r ^ 3 / (6 * (1 - r)) :=
        real_exp_third_order_le_div hr hr1'
    _ ≤ r ^ 3 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 6 * (1 - r))]
        nlinarith [sq_nonneg r, pow_nonneg hr 3]

/-- The real exponential tail is bounded by the first omitted power on `[0, 3/4)`. -/
lemma real_exp_fourth_order_le_quartic {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 3 / 4) :
    Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 ≤ s ^ 4 := by
  have ht := real_exp_sub_sum_le_geometric hs (show s < 1 by linarith only [hs1]) 4
  norm_num [sum_range_succ, Nat.factorial] at ht
  calc _ ≤ s ^ 4 / (24 * (1 - s)) := by linarith only [ht]
       _ ≤ s ^ 4 := by
         rw [div_le_iff₀ (by linarith only [hs1] : (0 : ℝ) < 24 * (1 - s))]
         nlinarith only [mul_nonneg (pow_nonneg hs 4)
           (show 0 ≤ 24 * (1 - s) - 1 by linarith only [hs1])]

/-- The real exponential tail is bounded by the first omitted power on `[0, 3/4)`. -/
lemma real_exp_fifth_order_le_quintic {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 3 / 4) :
    Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24 ≤ s ^ 5 := by
  have ht := real_exp_sub_sum_le_geometric hs (show s < 1 by linarith only [hs1]) 5
  norm_num [sum_range_succ, Nat.factorial] at ht
  calc _ ≤ s ^ 5 / (120 * (1 - s)) := by linarith only [ht]
       _ ≤ s ^ 5 := by
         rw [div_le_iff₀ (by linarith only [hs1] : (0 : ℝ) < 120 * (1 - s))]
         nlinarith only [mul_nonneg (pow_nonneg hs 5)
           (show 0 ≤ 120 * (1 - s) - 1 by linarith only [hs1])]

/-- The quadratic real exponential error on `[0, 1]`. -/
lemma real_exp_sub_one_sub_id_le_sq {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp s - 1 - s ≤ s ^ 2 := by
  have h := Real.norm_exp_sub_one_sub_id_le
    (show ‖s‖ ≤ 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hs] using hs1)
  have he : 0 ≤ Real.exp s - 1 - s := by
    linarith only [Real.add_one_le_exp s]
  simpa [Real.norm_eq_abs, abs_of_nonneg he, abs_of_nonneg hs] using h

/-- A radius bound controls every power of the scalar exponential increment. -/
lemma real_exp_sub_one_pow_le_of_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1) (n : ℕ) : (Real.exp s - 1) ^ n ≤ (1 + t) ^ n * s ^ n := by
  have htail := real_exp_sub_one_sub_id_le_sq hs (hst.trans ht)
  have he0 : 0 ≤ Real.exp s - 1 := by linarith only [Real.add_one_le_exp s, hs]
  calc
    _ ≤ (s + s ^ 2) ^ n := pow_le_pow_left₀ he0 (by linarith only [htail]) n
    _ = (1 + s) ^ n * s ^ n := by rw [show s + s ^ 2 = (1 + s) * s by ring, mul_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl (1 : ℝ)) hst) n)
      (pow_nonneg hs n)

/-- On the unit interval the exponential increment is at most twice the input. -/
lemma real_exp_sub_one_le_two_mul {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp s - 1 ≤ 2 * s := by
  simpa only [pow_one, one_add_one_eq_two] using real_exp_sub_one_pow_le_of_le hs hs1 le_rfl 1

/-! ### Taylor remainders in a normed algebra

The low-order cases of `norm_exp_sub_sum_le` written in the form every caller uses: the remainder
after subtracting `1 + x` (resp. `1 + x + x²/2`). These are the second- and third-order inputs of
the BCH estimates in `FQFP.Analysis.Normed.Algebra.BCH.Basic` and
`FQFP.Analysis.Normed.Algebra.BCH.Commutator`. -/

section ExpRemainder

variable [NormOneClass 𝔸]

/-- **Second-order Taylor remainder of `exp`**:
`‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖`. -/
theorem norm_exp_sub_one_sub_id_le (x : 𝔸) :
    ‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ := by
  simpa [sum_range_succ, Nat.factorial, sub_add_eq_sub_sub] using norm_exp_sub_sum_le x 2

/-- The error after the linear part of a product of two exponentials is bounded by the
quadratic scalar exponential remainder at the sum of the norms. -/
theorem norm_exp_mul_exp_sub_one_sub_add_le (a b : 𝔸) :
    ‖exp a * exp b - 1 - (a + b)‖ ≤
      Real.exp (‖a‖ + ‖b‖) - 1 - (‖a‖ + ‖b‖) := by
  rw [show exp a * exp b - 1 - (a + b) =
    (exp a - 1) * (exp b - 1) + (exp a - 1 - a) + (exp b - 1 - b) by
      noncomm_ring]
  calc
    _ ≤ ‖exp a - 1‖ * ‖exp b - 1‖ + ‖exp a - 1 - a‖ + ‖exp b - 1 - b‖ := by
      grw [norm_add_le, norm_add_le, norm_mul_le]
    _ ≤ (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) +
        (Real.exp ‖a‖ - 1 - ‖a‖) + (Real.exp ‖b‖ - 1 - ‖b‖) :=
      add_le_add (add_le_add
        (mul_le_mul (norm_exp_sub_one_le a) (norm_exp_sub_one_le b) (norm_nonneg _)
          (sub_nonneg.mpr (Real.one_le_exp (norm_nonneg a))))
        (norm_exp_sub_one_sub_id_le a)) (norm_exp_sub_one_sub_id_le b)
    _ = Real.exp (‖a‖ + ‖b‖) - 1 - (‖a‖ + ‖b‖) := by
      rw [Real.exp_add]
      ring

/-- **Third-order Taylor remainder of `exp`**:
`‖exp x - 1 - x - x²/2‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖²/2`. -/
theorem norm_exp_sub_one_sub_id_sub_sq_le (x : 𝔸) :
    ‖exp x - 1 - x - (2 : ℚ)⁻¹ • x ^ 2‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 := by
  simpa [sum_range_succ, Nat.factorial, sub_add_eq_sub_sub] using norm_exp_sub_sum_le x 3

/-- The exponential Taylor error is bounded by the corresponding real tail. -/
lemma norm_exp_sub_cubic_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [CompleteSpace 𝔸] [NormOneClass 𝔸] (x : 𝔸) :
    ‖exp x - 1 - x - (2 : ℚ)⁻¹ • x ^ 2 - (6 : ℚ)⁻¹ • x ^ 3‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2
      - ‖x‖ ^ 3 / 6 := by
  simpa [sum_range_succ, Nat.factorial, sub_eq_add_neg, div_eq_mul_inv,
    add_smul, smul_add, add_comm, add_left_comm, add_assoc, neg_smul, neg_one_smul] using
      FQFP.norm_exp_sub_sum_le x 4

/-- The exponential Taylor error is bounded by the corresponding real tail. -/
lemma norm_exp_sub_quartic_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [CompleteSpace 𝔸] [NormOneClass 𝔸] (x : 𝔸) :
    ‖exp x - 1 - x - (2 : ℚ)⁻¹ • x ^ 2 - (6 : ℚ)⁻¹ • x ^ 3 - (24 : ℚ)⁻¹ • x ^ 4‖ ≤ Real.exp ‖x‖ -
      1 - ‖x‖ - ‖x‖ ^ 2 / 2 - ‖x‖ ^ 3 / 6 - ‖x‖ ^ 4 / 24 := by
  simpa [sum_range_succ, Nat.factorial, sub_eq_add_neg, div_eq_mul_inv,
    add_smul, smul_add, add_comm, add_left_comm, add_assoc, neg_smul, neg_one_smul] using
      FQFP.norm_exp_sub_sum_le x 5

end ExpRemainder

end

end FQFP
