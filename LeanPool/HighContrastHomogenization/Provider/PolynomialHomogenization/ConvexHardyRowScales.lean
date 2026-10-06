/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyBallChain

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyRowScales

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Common chain lengths for Whitney rows

When the top triadic scale is no larger than the sandwich radius, every finer
row has a unique compatible dyadic chain length.  Distinct triadic rows have
distinct lengths because consecutive triadic scales differ by more than the
factor allowed in the initial chain radius.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

private theorem exists_chainLength_for_positive_scale {rho r : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho) :
    ∃ N : ℕ,
      r ≤ convexHardyBallChainRadius rho N 0 ∧
        convexHardyBallChainRadius rho N 0 < 2 * r := by
  have hratioPos : 0 < r / rho := div_pos hr hrho
  have hratioLe : r / rho ≤ 1 := (div_le_one hrho).2 hrle
  obtain ⟨N, hlower, hupper⟩ :=
    exists_nat_pow_near_of_lt_one hratioPos hratioLe
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, ?_, ?_⟩
  · rw [convexHardyBallChainRadius, convexHardyBallChainScale_zero]
    calc
      r = rho * (r / rho) := by field_simp [hrho.ne']
      _ ≤ rho * (1 / 2 : ℝ) ^ N :=
        mul_le_mul_of_nonneg_left hupper hrho.le
      _ = (1 / 2 : ℝ) ^ N * rho := mul_comm _ _
  · rw [convexHardyBallChainRadius, convexHardyBallChainScale_zero]
    have hpow : (1 / 2 : ℝ) ^ N < 2 * (r / rho) := by
      calc
        (1 / 2 : ℝ) ^ N =
            2 * (1 / 2 : ℝ) ^ (N + 1) := by
          rw [pow_succ]
          ring
        _ < 2 * (r / rho) := mul_lt_mul_of_pos_left hlower (by norm_num)
    calc
      (1 / 2 : ℝ) ^ N * rho < (2 * (r / rho)) * rho :=
        mul_lt_mul_of_pos_right hpow hrho
      _ = 2 * r := by field_simp [hrho.ne']

private theorem triadic_scales_not_within_two {a b : ℤ} (hab : a < b) :
    ¬(3 : ℝ) ^ b < 2 * (3 : ℝ) ^ a := by
  intro hlt
  have habOne : a + 1 ≤ b := by omega
  have hmono : (3 : ℝ) ^ (a + 1) ≤ (3 : ℝ) ^ b :=
    zpow_le_zpow_right₀ (by norm_num) habOne
  have hthree : (3 : ℝ) ^ (a + 1) = 3 * (3 : ℝ) ^ a := by
    rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hapos : 0 < (3 : ℝ) ^ a := by positivity
  rw [hthree] at hmono
  linarith only [hmono, hlt, hapos]

/-- All rows below a triadic top scale admit compatible initial dyadic radii,
and their chain lengths can be selected injectively. -/
theorem exists_injective_convexHardyRowChainLengths {rho : ℝ} (hrho : 0 < rho)
    {n : ℤ} (hnrho : (3 : ℝ) ^ n ≤ rho) :
    ∃ N : {a : ℤ // a ≤ n} → ℕ,
      (∀ a : {a : ℤ // a ≤ n}, (3 : ℝ) ^ (a : ℤ) ≤
          convexHardyBallChainRadius rho (N a) 0 ∧
        convexHardyBallChainRadius rho (N a) 0 <
          2 * (3 : ℝ) ^ (a : ℤ)) ∧
      Function.Injective N := by
  have hexists : ∀ a : {a : ℤ // a ≤ n}, ∃ k : ℕ,
      (3 : ℝ) ^ (a : ℤ) ≤ convexHardyBallChainRadius rho k 0 ∧
        convexHardyBallChainRadius rho k 0 <
          2 * (3 : ℝ) ^ (a : ℤ) := by
    intro a
    apply exists_chainLength_for_positive_scale hrho (by positivity)
    exact (zpow_le_zpow_right₀ (by norm_num) a.property).trans hnrho
  choose N hN using hexists
  refine ⟨N, hN, ?_⟩
  intro a b hNb
  apply Subtype.ext
  apply le_antisymm
  · by_contra hba
    have hab : (b : ℤ) < a := lt_of_not_ge hba
    apply triadic_scales_not_within_two hab
    calc
      (3 : ℝ) ^ (a : ℤ) ≤
          convexHardyBallChainRadius rho (N a) 0 := (hN a).1
      _ = convexHardyBallChainRadius rho (N b) 0 := by rw [hNb]
      _ < 2 * (3 : ℝ) ^ (b : ℤ) := (hN b).2
  · by_contra hab
    have hba : (a : ℤ) < b := lt_of_not_ge hab
    apply triadic_scales_not_within_two hba
    calc
      (3 : ℝ) ^ (b : ℤ) ≤
          convexHardyBallChainRadius rho (N b) 0 := (hN b).1
      _ = convexHardyBallChainRadius rho (N a) 0 := by rw [hNb]
      _ < 2 * (3 : ℝ) ^ (a : ℤ) := (hN a).2

end

end HighContrast
end HCPolySupport
