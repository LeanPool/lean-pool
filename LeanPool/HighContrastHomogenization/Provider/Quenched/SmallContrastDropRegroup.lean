/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRecursionShape

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastDropRegroup

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The drop slots of the weak value against the iteration sum

The two depth sums of `weakValueSharpMajorant_le_three_group_summed_at_level` that carry the
hatted mean
drops are

  `∑_{j ≤ H_w} 3^{-μ j} · Dr j`      (the linear slot of the per-scale budget)

and

  `∑_{j ≤ H_w} 3^{-ν j} · √(2d · Dr j)`   (the rooted slot).

Both are converted here into the drop-history sum

  `T_n = ∑_{k ∈ [1,n]} (3^{-μ})^{n-k} (F(k-1) - F(k))`

that the iteration decay consumes, using the mean-drop carrier's own
shape `Dr j ≤ c_D (F(n-j) - F(n))` (`meanDrop2ValueIsotropy` is exactly `4d` times
that drop times reference constants).  The rooted slot is first regrouped by
Cauchy–Schwarz, which is what keeps the drops *linear* in the recursion — the
printed mechanism of HC (4.17).
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- A geometric series is below the inverse of its gap. -/
theorem geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ j ∈ Finset.range M, r ^ j ≤ (1 - r)⁻¹ := by
  have hden : 0 < 1 - r := by linarith only [hr1]
  have hid : ∀ M : ℕ, (∑ j ∈ Finset.range M, r ^ j) * (1 - r) = 1 - r ^ M := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, add_mul, ih]
        ring
  have hrM : (0 : ℝ) ≤ r ^ M := pow_nonneg hr0 M
  have hS : (∑ j ∈ Finset.range M, r ^ j) * (1 - r) ≤ 1 := by
    rw [hid M]
    linarith only [hrM]
  have hinv : (1 - r)⁻¹ * (1 - r) = 1 := inv_mul_cancel₀ (ne_of_gt hden)
  by_contra hcon
  push Not at hcon
  nlinarith only [hcon, hden, hS, hinv]

/-- The drop-history sum of the iteration lemma is nonnegative. -/
theorem iteration_sum_nonneg {F : ℕ → ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p) {r : ℝ} (hr0 : 0 ≤ r) (n : ℕ) :
    0 ≤ ∑ k ∈ Finset.Icc 1 n, r ^ (n - k) * (F (k - 1) - F k) := by
  refine Finset.sum_nonneg fun k _ => ?_
  exact mul_nonneg (pow_nonneg hr0 _)
    (sub_nonneg.mpr (hFmono _ _ (Nat.sub_le _ _)))

/-- **The linear drop slot against the iteration sum.** -/
theorem weak_drop_sum_le_iteration {F : ℕ → ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    {mu : ℝ} (hmu : 0 < mu) {n Hw : ℕ} (hHw : Hw + 1 ≤ n)
    {cD : ℝ} (hcD0 : 0 ≤ cD) {Dr : ℕ → ℝ}
    (hDr : ∀ j ∈ Finset.range (Hw + 1), Dr j ≤ cD * (F (n - j) - F n)) :
    ∑ j ∈ Finset.range (Hw + 1), (3 : ℝ) ^ (-mu * (j : ℝ)) * Dr j ≤
      cD * ((1 - (3 : ℝ) ^ (-mu))⁻¹ *
        ∑ k ∈ Finset.Icc 1 n, ((3 : ℝ) ^ (-mu)) ^ (n - k) * (F (k - 1) - F k)) := by
  classical
  set r : ℝ := (3 : ℝ) ^ (-mu) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hmu])
  have hstep1 : ∑ j ∈ Finset.range (Hw + 1), (3 : ℝ) ^ (-mu * (j : ℝ)) * Dr j ≤
      cD * ∑ j ∈ Finset.range (Hw + 1), r ^ j * (F (n - j) - F n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [rpow_weight_eq_pow, ← hr]
    have hrj : (0 : ℝ) ≤ r ^ j := le_of_lt (pow_pos hr0 j)
    calc r ^ j * Dr j ≤ r ^ j * (cD * (F (n - j) - F n)) :=
          mul_le_mul_of_nonneg_left (hDr j hj) hrj
      _ = cD * (r ^ j * (F (n - j) - F n)) := by ring
  have hstep2 := lagged_drop_sum_le (F := F) hFmono (r := r) hr0.le hr1
    (n := n) (N := Hw + 1) hHw
  exact le_trans hstep1 (mul_le_mul_of_nonneg_left hstep2 hcD0)

/-- **The rooted drop slot against the iteration sum.**  The Cauchy–Schwarz
regroup turns the square of the rooted sum into a *linear* multiple of the
drop-history sum. -/
theorem weak_rooted_drop_sum_sq_le {F : ℕ → ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    {nu : ℝ} (hnu : 0 < nu) {n Hw : ℕ} (hHw : Hw + 1 ≤ n)
    {c cD : ℝ} (hc : 0 ≤ c) (hcD0 : 0 ≤ cD) {Dr : ℕ → ℝ}
    (hDr0 : ∀ j, 0 ≤ Dr j)
    (hDr : ∀ j ∈ Finset.range (Hw + 1), Dr j ≤ cD * (F (n - j) - F n)) :
    (∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-nu * (j : ℝ)) * Real.sqrt (c * Dr j)) ^ 2 ≤
      (1 - (3 : ℝ) ^ (-nu))⁻¹ *
        (c * (cD * ((1 - (3 : ℝ) ^ (-nu))⁻¹ *
          ∑ k ∈ Finset.Icc 1 n,
            ((3 : ℝ) ^ (-nu)) ^ (n - k) * (F (k - 1) - F k)))) := by
  classical
  set r : ℝ := (3 : ℝ) ^ (-nu) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hnu])
  have hden : 0 < 1 - r := by linarith only [hr1]
  have hinv0 : (0 : ℝ) ≤ (1 - r)⁻¹ := le_of_lt (inv_pos.mpr hden)
  -- rewrite the real-power weights as natural powers
  have hrw : ∑ j ∈ Finset.range (Hw + 1),
      (3 : ℝ) ^ (-nu * (j : ℝ)) * Real.sqrt (c * Dr j) =
      ∑ j ∈ Finset.range (Hw + 1), r ^ j * Real.sqrt (c * Dr j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rpow_weight_eq_pow, ← hr]
  rw [hrw]
  -- Cauchy–Schwarz
  have hcs := sum_weighted_sqrt_sq_le (Finset.range (Hw + 1))
    (fun j => r ^ j) Dr (fun j _ => le_of_lt (pow_pos hr0 j))
    (fun j _ => hDr0 j) hc
  -- the total weight and the linear drop slot
  have hw : ∑ j ∈ Finset.range (Hw + 1), r ^ j ≤ (1 - r)⁻¹ :=
    geom_sum_le_inv_one_sub hr0.le hr1 _
  have hlin : ∑ j ∈ Finset.range (Hw + 1), r ^ j * Dr j ≤
      cD * ((1 - r)⁻¹ *
        ∑ k ∈ Finset.Icc 1 n, r ^ (n - k) * (F (k - 1) - F k)) := by
    have h := weak_drop_sum_le_iteration hFmono (mu := nu) hnu hHw hcD0 hDr
    rw [← hr] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rpow_weight_eq_pow, ← hr]
  have hlin0 : 0 ≤ ∑ j ∈ Finset.range (Hw + 1), r ^ j * Dr j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (le_of_lt (pow_pos hr0 j)) (hDr0 j)
  calc (∑ j ∈ Finset.range (Hw + 1), r ^ j * Real.sqrt (c * Dr j)) ^ 2
      ≤ (∑ j ∈ Finset.range (Hw + 1), r ^ j) *
          (c * ∑ j ∈ Finset.range (Hw + 1), r ^ j * Dr j) := hcs
    _ ≤ (1 - r)⁻¹ * (c * ∑ j ∈ Finset.range (Hw + 1), r ^ j * Dr j) := by
        refine mul_le_mul_of_nonneg_right hw (mul_nonneg hc hlin0)
    _ ≤ (1 - r)⁻¹ * (c * (cD * ((1 - r)⁻¹ *
          ∑ k ∈ Finset.Icc 1 n, r ^ (n - k) * (F (k - 1) - F k)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hinv0
        exact mul_le_mul_of_nonneg_left hlin hc

end

end HCPolySupport.HighContrast.Quenched
