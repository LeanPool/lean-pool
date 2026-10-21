/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Nth
import LeanPool.IwaniecLinearSieve.PrimeSums.Error
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The `r`-th prime is `O(r log r)`

From `θ(x) ≥ x / 2` for large `x` (a consequence of `theta_asymp`) and `θ(x) ≤ π(x) log x`.
-/

@[expose] public section

open Real Filter Topology

namespace IwaniecLinearSieve

theorem log_le_div_eight {K : ℝ} (hK : 256 ≤ K) : log K ≤ K / 8 := by
  have hK0 : 0 < K := by linarith
  have hs : 16 ≤ √K := (le_sqrt (by norm_num) hK0.le).2 (by linarith)
  have h1 : log K = 2 * log √K := by rw [log_sqrt hK0.le]; ring
  have h2 := log_le_sub_one_of_pos (sqrt_pos.2 hK0)
  have h3 := sq_sqrt hK0.le
  nlinarith

/-- The `r`-th prime `p_r = Nat.nth Nat.Prime (r - 1)` satisfies `p_r ≤ C r log r`. -/
theorem nth_prime_le : ∃ C, ∀ r : ℕ, 2 ≤ r → (Nat.nth Nat.Prime (r - 1) : ℝ) ≤ C * r * log r := by
  obtain ⟨Cθ, -, hθ⟩ := theta_asymp
  obtain ⟨X, hX⟩ := eventually_atTop.1
    ((by simpa using tendsto_pntE.const_mul Cθ :
      Tendsto (fun x ↦ Cθ * pntE x) atTop (𝓝 0)).eventually (eventually_lt_nhds one_half_pos))
  set K := max X 256
  have hK : 256 ≤ K := le_max_right _ _
  refine ⟨K, fun r hr ↦ ?_⟩
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlogr : 1 / 2 ≤ log r := by
    have := log_two_gt_d9
    have := log_le_log (by norm_num) hr'
    linarith
  set x := K * r * log r with hx
  have hxK : K ≤ x := by
    rw [hx, mul_assoc]
    refine le_mul_of_one_le_right (by linarith) ?_
    nlinarith
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  -- `θ x ≥ x / 2`
  have hθx : x / 2 ≤ Chebyshev.theta x := by
    have h1 := hθ x hx2
    have h2 := hX x ((le_max_left _ _).trans hxK)
    rw [abs_le] at h1
    nlinarith
  -- `log x ≤ K / 8 + 2 log r`
  have hlogx : log x ≤ K / 8 + 2 * log r := by
    have hlr0 : 0 < log r := by linarith
    rw [hx, log_mul (by positivity) hlr0.ne', log_mul (by positivity) (by positivity)]
    have h1 := log_le_div_eight hK
    have h2 := log_le_sub_one_of_pos hlr0
    linarith
  have hlogx0 : 0 < log x := log_pos (by linarith)
  -- hence `π x ≥ x / (2 log x) ≥ r`
  have hπ : (r : ℝ) ≤ Nat.primeCounting ⌊x⌋₊ := by
    have h1 := Chebyshev.theta_le_pi_mul_log' x
    have h2 : (r : ℝ) * (2 * log x) ≤ x := by
      rw [hx]
      have : 2 * log x ≤ K * log r := by nlinarith
      nlinarith
    nlinarith
  have hcount : r - 1 < Nat.count Nat.Prime (⌊x⌋₊ + 1) := by
    have : r ≤ Nat.primeCounting ⌊x⌋₊ := by exact_mod_cast hπ
    simp only [Nat.primeCounting, Nat.primeCounting'] at this
    omega
  have hnth := Nat.nth_lt_of_lt_count hcount
  calc (Nat.nth Nat.Prime (r - 1) : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.lt_succ_iff.1 hnth
    _ ≤ x := Nat.floor_le hx0.le

end IwaniecLinearSieve
