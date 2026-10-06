/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalChainGeometricHead

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.FractionalChainPhysicalHead

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast

open scoped ENNReal

private theorem fractionalChainPhysicalCutoff
    {r L a : ℝ} (hr : 0 < r) (hL : 0 < L) (ha : 0 < a) {n : ℕ}
    (h : r < (1 / 2 : ℝ) ^ n * L) :
    (r / L) ^ a * ((2 : ℝ) ^ a) ^ n < 1 := by
  have hdiv : r / L < (1 / 2 : ℝ) ^ n :=
    (div_lt_iff₀ hL).2 (by simpa [mul_comm] using h)
  have hmul : (r / L) * (2 : ℝ) ^ n < 1 := by
    exact (lt_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).1
      (by simpa [one_div] using hdiv)
  have hpos : 0 < (r / L) * (2 : ℝ) ^ n :=
    mul_pos (div_pos hr hL) (pow_pos (by norm_num) _)
  have hp := Real.rpow_lt_rpow hpos.le hmul ha
  rw [Real.one_rpow] at hp
  calc
    (r / L) ^ a * ((2 : ℝ) ^ a) ^ n =
        ((r / L) * (2 : ℝ) ^ n) ^ a := by
      rw [Real.mul_rpow (div_nonneg hr.le hL.le) (pow_nonneg (by norm_num) _),
        ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    _ < 1 := hp

private theorem inv_ratio_rpow_eq
    {r L a : ℝ} (hr : 0 < r) (hL : 0 < L) :
    ((r / L) ^ a)⁻¹ = L ^ a * r ^ (-a) := by
  rw [Real.div_rpow hr.le hL.le, inv_div, Real.rpow_neg hr.le]
  rw [div_eq_mul_inv]

private theorem one_le_outer_mul_kernel
    {r D a : ℝ} (hr : 0 < r) (hD : r < D) (ha : 0 < a) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (D ^ a) * ENNReal.ofReal (r ^ (-a)) := by
  have hDpos : 0 < D := lt_trans hr hD
  have hpow : 1 < (D / r) ^ a := by
    have hratio : 1 < D / r := (lt_div_iff₀ hr).2 (by simpa using hD)
    simpa using Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) hratio ha
  have hreal : 1 ≤ D ^ a * r ^ (-a) := by
    calc
      1 ≤ (D / r) ^ a := hpow.le
      _ = D ^ a * r ^ (-a) := by
        rw [Real.div_rpow hDpos.le hr.le, Real.rpow_neg hr.le,
          div_eq_mul_inv]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hDpos.le a)]
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hreal

/-- A geometric chain whose level-`n` support lies within the physical
distance `2⁻ⁿ L` has total growing weight controlled by the Riesz kernel
`r⁻ᵃ`, uniformly up to the explicit outer scales `D` and `L`. -/
theorem tsum_fractionalChainPhysicalHead_le
    {r L D a : ℝ} (hr : 0 < r) (hL : 0 < L) (hD : r < D) (ha : 0 < a)
    (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n, P n → r < (1 / 2 : ℝ) ^ n * L) :
    (∑' n : ℕ, if P n then ENNReal.ofReal (((2 : ℝ) ^ a) ^ n) else 0) ≤
      ENNReal.ofReal (D ^ a) * ENNReal.ofReal (r ^ (-a)) +
        ENNReal.ofReal (L ^ a) * ENNReal.ofReal (r ^ (-a)) *
          ENNReal.ofReal (((2 : ℝ) ^ a) / ((2 : ℝ) ^ a - 1)) := by
  let X : ℝ := (r / L) ^ a
  let q : ℝ := (2 : ℝ) ^ a
  have hX : 0 < X := Real.rpow_pos_of_pos (div_pos hr hL) _
  have hq : 1 < q := by
    exact Real.one_lt_rpow (by norm_num) ha
  have hcut : ∀ n, (if P n then ENNReal.ofReal (q ^ n) else 0) ≤
      (if X * q ^ n < 1 then ENNReal.ofReal (q ^ n) else 0) := by
    intro n
    by_cases hn : P n
    · rw [ite_eq_left hn, ite_eq_left]
      exact fractionalChainPhysicalCutoff hr hL ha (hP n hn)
    · simp only [ite_eq_right hn, zero_le]
  have hhead := tsum_geometric_of_mul_pow_lt_one_le hX hq
  have hsum : (∑' n : ℕ, if P n then ENNReal.ofReal (q ^ n) else 0) ≤
      1 + (ENNReal.ofReal X)⁻¹ * ENNReal.ofReal (q / (q - 1)) :=
    le_trans (ENNReal.tsum_le_tsum hcut) hhead
  have hInv : (ENNReal.ofReal X)⁻¹ =
      ENNReal.ofReal (L ^ a) * ENNReal.ofReal (r ^ (-a)) := by
    rw [← ENNReal.ofReal_inv_of_pos hX]
    unfold X
    rw [inv_ratio_rpow_eq hr hL,
      ENNReal.ofReal_mul (Real.rpow_nonneg hL.le a)]
  change (∑' n : ℕ, if P n then ENNReal.ofReal (q ^ n) else 0) ≤ _
  calc
    (∑' n : ℕ, if P n then ENNReal.ofReal (q ^ n) else 0) ≤
        1 + (ENNReal.ofReal X)⁻¹ * ENNReal.ofReal (q / (q - 1)) := hsum
    _ ≤ ENNReal.ofReal (D ^ a) * ENNReal.ofReal (r ^ (-a)) +
        (ENNReal.ofReal X)⁻¹ * ENNReal.ofReal (q / (q - 1)) :=
      add_le_add (one_le_outer_mul_kernel hr hD ha) le_rfl
    _ = _ := by rw [hInv]

end HCPolySupport.HighContrast
