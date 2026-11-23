/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.AsymptoticDefs
public import LeanPool.Egyptian.Payoff

/-!
# Growth of a terminal ray

This is equation (terminal-ray-growth) in Kovač and Tang. Numbering the first
term by zero in Lean puts the normalization factor at `2^(N+1)`.
-/

@[expose] public section

namespace Egyptian

open Filter
open scoped Topology

/-- Adding 1 to the orbit does not change the normalized logarithmic limit. -/
theorem log_succ_orbit_tendsto {t : ℝ} (ht : 1 ≤ t) :
    Tendsto (fun j : ℕ => Real.log (Payoff.orbit t j + 1) / 2^j)
      atTop (𝓝 (Payoff.value t)) := by
  have hlo := Payoff.normalized_tendsto ht
  have hzero : Tendsto (fun j : ℕ => Real.log 2 / 2^j) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).const_mul (Real.log 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo (by simpa using hlo.add hzero)
  · intro j
    have h := Payoff.one_le_orbit ht j
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith)
      (show Payoff.orbit t j ≤ Payoff.orbit t j + 1 by linarith)) (by positivity)
  · intro j
    have h := Payoff.one_le_orbit ht j
    change Real.log (Payoff.orbit t j + 1) / 2 ^ j ≤
      Real.log (Payoff.orbit t j) / 2 ^ j + Real.log 2 / 2 ^ j
    rw [← add_div, ← Real.log_mul (by linarith : Payoff.orbit t j ≠ 0) (by norm_num)]
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) (by positivity)

/-- A ray of depth N and terminal remainder 1/T has limiting growth
exp(H(T)/2^(N+1)). This makes the factor of two relative to its Bellman
score explicit. -/
theorem terminal_growth {b : ℕ → ℕ} {T N : ℕ} (hT : 1 ≤ T)
    (htail : ∀ j, b (N + j) = unitIter T j + 1) :
    Tendsto (growth b) atTop (𝓝 (Real.exp (Payoff.value (T : ℝ) / 2^(N+1)))) := by
  apply (tendsto_add_atTop_iff_nat N).mp
  have h := (log_succ_orbit_tendsto (t := (T : ℝ)) (by exact_mod_cast hT)).div_const
    ((2 : ℝ)^(N+1))
  apply (Real.continuous_exp.continuousAt.tendsto.comp h).congr
  intro j
  change Real.exp ((Real.log (Payoff.orbit (T : ℝ) j + 1) / 2^j) / 2^(N+1)) = growth b (j+N)
  have ho := Payoff.one_le_orbit (t := (T : ℝ)) (by exact_mod_cast hT) j
  rw [growth, Nat.add_comm j N, htail, Nat.cast_add, Nat.cast_one, real_unitIter,
    Real.rpow_def_of_pos (by linarith : 0 < Payoff.orbit (T : ℝ) j + 1)]
  congr 1
  rw [show N+j+1 = j+(N+1) by omega, pow_add]
  ring

theorem benchmark_growth_exists {q : ℚ} {b : ℕ → ℕ} (hb : Benchmark q b) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (growth b) atTop (𝓝 L) := by
  obtain ⟨_, N, T, _, hT, _, htail, _⟩ := hb
  exact ⟨_, Real.exp_pos _, terminal_growth (by omega : 1 ≤ T) htail⟩

end Egyptian
