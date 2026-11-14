/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ScalesConcentration.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Weights

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Concentration for scale arrays — geometric weight sums (Step 1 input)

The row weights `wt t k j = 3^{-t |k-j|}` are summable over `j ∈ ℤ` with
`∑_j wt t k j = (1 + 3^{-t}) / (1 - 3^{-t}) ≤ 3 / t` for `t ∈ (0, 1]`.

## Deviation from the paper's constant

The paper (`e.YktoZk.twosided`, Step 1) uses the *sharp* bound
`∑_{ℓ∈ℤ} 3^{-(s/2)|ℓ|} ≤ 4 s⁻¹`, which forces the threshold prefactor `6` in
`e.no.bad.scales.twosided`.  The sharp bound requires `log 3 > 1.055`, a
delicate numeric estimate.  We instead prove the clean bound
`∑_{ℓ∈ℤ} 3^{-t|ℓ|} ≤ 3/t` (i.e. `≤ 6 s⁻¹` with `t = s/2`), which needs only
`log 3 > 1`.  This inflates the final threshold prefactor from `6` to `9`
(`6 = 2·3` becomes `9 = 3·3`), a documented and harmless change of universal
constant; the exponential rate is unaffected.
-/

namespace Algsuperdiff.Section4.Probability.ScalesConcentration

open MeasureTheory Finset Real
open scoped ENNReal NNReal

lemma log_three_gt_one : 1 < Real.log 3 := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  exact lt_trans Real.exp_one_lt_d9 (by norm_num)

lemma log_three_lt_two : Real.log 3 < 2 := by
  rw [log_lt_iff_lt_exp (by norm_num)]
  have := Real.quadratic_le_exp_of_nonneg (x := (2 : ℝ)) (by norm_num)
  nlinarith [this]

/-- The transcendental core of the geometric bound: `3^{-t} ≤ (3-t)/(3+t)` for
`t ∈ (0,1]`, proved via the quadratic lower bound `exp x ≥ 1 + x + x²/2`. -/
lemma three_rpow_neg_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (3 : ℝ) ^ (-t) ≤ (3 - t) / (3 + t) := by
  have hL : 1 < Real.log 3 := log_three_gt_one
  have hL2 : Real.log 3 < 2 := log_three_lt_two
  have h3t : (3 : ℝ) ^ t = Real.exp (t * Real.log 3) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
  have hquad := Real.quadratic_le_exp_of_nonneg (x := t * Real.log 3)
    (by positivity)
  have h3tpos : 0 < (3 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have key : (3 + t) ≤ (3 - t) * (3 : ℝ) ^ t := by
    rw [h3t]
    nlinarith [hquad, hL, hL2, ht, ht1, sq_nonneg (t * Real.log 3),
      mul_pos ht (lt_trans one_pos hL), sq_nonneg t,
      mul_nonneg ht.le (sq_nonneg (Real.log 3))]
  rw [Real.rpow_neg (by norm_num), ← one_div]
  rw [div_le_div_iff₀ h3tpos (by linarith)]
  nlinarith [key, h3tpos]

/-- The `ℤ`-summability of `ℓ ↦ q^{|ℓ|}` for `q ∈ [0,1)`. -/
lemma summable_pow_natAbs {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun ℓ : ℤ => q ^ ℓ.natAbs) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using summable_geometric_of_lt_one hq0 hq1
  · have : (fun n : ℕ => q ^ (-(n : ℤ)).natAbs) = fun n : ℕ => q ^ n := by
      funext n; simp
    rw [this]; exact summable_geometric_of_lt_one hq0 hq1

/-- The `ℕ⁺`-sum of a geometric series equals `q/(1-q)`. -/
lemma tsum_pnat_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' n : ℕ+, q ^ (n : ℕ) = q / (1 - q) := by
  have hstep : ∑' n : ℕ+, q ^ (n : ℕ) = ∑' n : ℕ, q ^ (n + 1) :=
    tsum_pnat_eq_tsum_succ (f := fun n => q ^ n)
  rw [hstep]
  have : (fun n : ℕ => q ^ (n + 1)) = fun n : ℕ => q * q ^ n := by
    funext n; rw [pow_succ]; ring
  rw [this, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  rw [div_eq_mul_inv]

/-- The `ℤ`-sum of `q^{|ℓ|}` equals `(1+q)/(1-q)`. -/
lemma tsum_int_pow_natAbs {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' ℓ : ℤ, q ^ ℓ.natAbs = (1 + q) / (1 - q) := by
  have hsum := summable_pow_natAbs hq0 hq1
  have heven : ∀ n : ℤ, q ^ (-n).natAbs = q ^ n.natAbs := by
    intro n; simp [Int.natAbs_neg]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (f := fun ℓ : ℤ => q ^ ℓ.natAbs)
    (fun n => heven n) hsum]
  have hpnat : ∑' n : ℕ+, q ^ ((n : ℤ)).natAbs = q / (1 - q) := by
    have : (fun n : ℕ+ => q ^ ((n : ℤ)).natAbs) = fun n : ℕ+ => q ^ (n : ℕ) := by
      funext n; simp
    rw [this]; exact tsum_pnat_geometric hq0 hq1
  rw [hpnat]
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hne : (1 - q) ≠ 0 := ne_of_gt h1q
  simp only [Int.natAbs_zero, pow_zero, nsmul_eq_mul, Nat.cast_ofNat]
  rw [eq_div_iff hne, add_mul, one_mul, mul_assoc, div_mul_cancel₀ q hne]
  ring

/-- **Geometric weight bound** (Step 1 input): for `t ∈ (0,1]`,
`∑_{ℓ∈ℤ} 3^{-t|ℓ|} ≤ 3/t`. -/
lemma tsum_three_rpow_neg_abs_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∑' ℓ : ℤ, (3 : ℝ) ^ (-(t * (ℓ.natAbs : ℝ))) ≤ 3 / t := by
  set q : ℝ := (3 : ℝ) ^ (-t) with hq
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : q < 1 := by
    rw [hq]; rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2 (by linarith)
  have hpow : ∀ ℓ : ℤ, (3 : ℝ) ^ (-(t * (ℓ.natAbs : ℝ))) = q ^ ℓ.natAbs := by
    intro ℓ
    rw [hq, ← Real.rpow_natCast ((3 : ℝ) ^ (-t)) ℓ.natAbs,
      ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  simp_rw [hpow]
  rw [tsum_int_pow_natAbs hq0 hq1]
  have h1q : (0 : ℝ) < 1 - q := by linarith
  rw [div_le_div_iff₀ h1q ht]
  have hqle : q ≤ (3 - t) / (3 + t) := by rw [hq]; exact three_rpow_neg_le ht ht1
  have h3t : (0 : ℝ) < 3 + t := by linarith
  have hqle' : q * (3 + t) ≤ 3 - t := by
    rw [le_div_iff₀ h3t] at hqle; linarith [hqle]
  nlinarith [hqle', hq0, ht, h1q]

end Algsuperdiff.Section4.Probability.ScalesConcentration
