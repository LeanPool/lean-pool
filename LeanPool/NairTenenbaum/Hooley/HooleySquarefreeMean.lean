/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleySquarefreePowerBound
public import LeanPool.NairTenenbaum.Smooth.MomentOrderOptimization

/-! # The sharp squarefree reciprocal Hooley mean

For every `η>sqrt(2t)`, the reciprocal sum over squarefree integers is
`O((log x)^(2^t−t) exp(η sqrt(log₂ x log₃ x)))`.
The integer moment order is chosen by a proved asymptotic optimization.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial Filter
open scoped Topology

theorem momentPower_eq_log_cost {K t x : ℝ} {q : ℕ} (hKq : 0 < K * (q : ℝ))
    (hx : 1 < x) :
    (K * q) ^ q * (Real.log x) ^ ((2 : ℝ) ^ t - t + t / q) =
      (Real.log x) ^ ((2 : ℝ) ^ t - t) *
        Real.exp ((q : ℝ) * Real.log (K * q) + t * Real.log (Real.log x) / q) := by
  have hl := Real.log_pos hx
  rw [Real.rpow_add hl, Real.exp_add, Real.exp_nat_mul, Real.exp_log hKq,
    Real.rpow_def_of_pos hl (t / q)]
  rw [show Real.log (Real.log x) * (t / q) = t * Real.log (Real.log x) / q by ring]
  ring

theorem eventually_squarefreeHooleyRootSum_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t η : ℝ} (ht : 1 ≤ t)
    (hη : Real.sqrt (2 * t) < η) :
    ∀ᶠ x : ℝ in atTop, squarefreeHooleyRootSum Q t x ≤
      ((2 : ℝ) ^ t * Real.exp 1) * ((Real.log x) ^ ((2 : ℝ) ^ t - t) *
        Real.exp (η * Real.sqrt (Real.log (Real.log x) * Real.log (Real.log (Real.log x))))) := by
  obtain ⟨K, x₀, hK, hx₀, hbound⟩ := exists_squarefreeHooleyRootSum_power_bound hQ hirr ht
  have HK : 0 < K := by linarith
  have Hcost := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_exists_momentOrderCost_le HK (by linarith : 0 < t) hη (max 3 ⌈2 * t⌉₊))
  filter_upwards [eventually_gt_atTop x₀, Hcost] with x hx hcost
  obtain ⟨q, hqN, hcost⟩ := hcost
  have hq : 2 < q := by omega
  have hqt : 2 * t ≤ (q : ℝ) := (Nat.le_ceil (2 * t)).trans
    (by exact_mod_cast ((le_max_right 3 ⌈2 * t⌉₊).trans hqN))
  have H := hbound q hq hqt x hx
  have hKq : 0 < K * (q : ℝ) := mul_pos HK (by exact_mod_cast (show 0 < q by omega))
  rw [momentPower_eq_log_cost hKq (hx₀.trans hx)] at H
  apply H.trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcost)
      (Real.rpow_nonneg (Real.log_pos (hx₀.trans hx)).le _)) (by positivity)

theorem exists_squarefreeHooleyRootSum_sharp_bound {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t η : ℝ} (ht : 1 ≤ t)
    (hη : Real.sqrt (2 * t) < η) :
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ x : ℝ, x₀ < x →
      squarefreeHooleyRootSum Q t x ≤ C * ((Real.log x) ^ ((2 : ℝ) ^ t - t) *
        Real.exp (η * Real.sqrt (Real.log (Real.log x) * Real.log (Real.log (Real.log x))))) := by
  obtain ⟨x₁, H⟩ := eventually_atTop.mp (eventually_squarefreeHooleyRootSum_le hQ hirr ht hη)
  refine ⟨max 2 x₁, (2 : ℝ) ^ t * Real.exp 1, lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    by positivity, fun x hx => H x ((le_max_right _ _).trans hx.le)⟩

end NairTenenbaum
