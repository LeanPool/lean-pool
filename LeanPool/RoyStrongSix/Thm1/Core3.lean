/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# The core of Theorem 1, part 3: the logarithmic inequality of the independent branch

Combining the analytic upper bound (`interpDet_bound`, with `R = 2`)

  `Ψ₁ ≤ N! Bᴺ / 2^{M(N − Mⁿ) − Σt}`

with Liouville's lower bound (`liouville_det`)

  `1 ≤ Ψ₁ Eᴺ (N! (E H)ᴺ)^{k−1}`,

we get, when `2Mⁿ ≤ N` and `Σt ≤ N T_J` (`log_ineq`):

  `(M/2 − T_J) log 2 ≤ k log N + log B + k log E + k log H`.
-/

@[expose] public section

namespace LeanPool

namespace StrongSix.Thm1

theorem log_factorial_le (N : ℕ) : Real.log N.factorial ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
  have hpos : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  calc Real.log N.factorial ≤ Real.log ((N : ℝ) ^ N) := Real.log_le_log hpos h
    _ = N * Real.log N := by rw [Real.log_pow]

/-- **The logarithmic inequality.** -/
theorem log_ineq {N M n TJ k tsum : ℕ} {Ψ₁ B E H : ℝ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hB : 1 ≤ B)
    (hE : 1 ≤ E) (hH : 1 ≤ H) (hMN : 2 * M ^ n ≤ N) (hts : tsum ≤ N * TJ)
    (hup : Ψ₁ ≤ N.factorial * B ^ N / 2 ^ (M * (N - M ^ n) - tsum))
    (hlow : 1 ≤ Ψ₁ * E ^ N * (N.factorial * (E * H) ^ N) ^ (k - 1)) :
    ((M : ℝ) / 2 - TJ) * Real.log 2 ≤
      k * Real.log N + Real.log B + k * Real.log E + k * Real.log H := by
  set K0 := M * (N - M ^ n) - tsum with hK0
  set Z : ℝ := E ^ N * (N.factorial * (E * H) ^ N) ^ (k - 1) with hZ
  have hfac : (1 : ℝ) ≤ N.factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hZpos : 0 < Z := by positivity
  have h2pos : (0 : ℝ) < 2 ^ K0 := by positivity
  -- `2^{K0} ≤ N! Bᴺ Z`
  have hmain : (2 : ℝ) ^ K0 ≤ N.factorial * B ^ N * Z := by
    have h1 : 1 ≤ Ψ₁ * Z := by rw [hZ, ← mul_assoc]; exact hlow
    have h2 : Ψ₁ * Z ≤ N.factorial * B ^ N / 2 ^ K0 * Z := mul_le_mul_of_nonneg_right hup hZpos.le
    have h3 : 1 ≤ N.factorial * B ^ N / 2 ^ K0 * Z := h1.trans h2
    rw [div_mul_eq_mul_div, le_div_iff₀ h2pos, one_mul] at h3
    exact h3
  -- take logarithms
  have hlog := Real.log_le_log h2pos hmain
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlE : 0 ≤ Real.log E := Real.log_nonneg hE
  have hlH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hlf := log_factorial_le N
  have hBpos : 0 < B := by linarith
  have hEpos : 0 < E := by linarith
  have hHpos : 0 < H := by linarith
  have hfpos : (0 : ℝ) < N.factorial := by linarith
  rw [Real.log_pow, Real.log_mul (by positivity) hZpos.ne', Real.log_mul hfpos.ne' (by positivity),
    Real.log_pow, hZ, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul hfpos.ne' (by positivity), Real.log_pow, Real.log_mul hEpos.ne' hHpos.ne'] at hlog
  -- `K0 ≥ N (M/2 − T_J)`
  have hK0 : (N : ℝ) * ((M : ℝ) / 2 - TJ) ≤ K0 := by
    have hsub : (N : ℝ) / 2 ≤ ((N - M ^ n : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      have : (2 : ℝ) * (M : ℝ) ^ n ≤ N := by exact_mod_cast hMN
      push_cast
      linarith
    have hK0' : ((M * (N - M ^ n) : ℕ) : ℝ) - tsum ≤ K0 := by
      rw [hK0]
      rcases le_or_gt tsum (M * (N - M ^ n)) with h | h
      · rw [Nat.cast_sub h]
      · rw [Nat.sub_eq_zero_of_le h.le]
        have : ((M * (N - M ^ n) : ℕ) : ℝ) < tsum := by exact_mod_cast h
        simp only [Nat.cast_zero]; linarith
    have hts' : (tsum : ℝ) ≤ N * TJ := by exact_mod_cast hts
    have hM : (M : ℝ) * (N / 2) ≤ ((M * (N - M ^ n) : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)
    nlinarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm1 : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub hk]; simp
  rw [hkm1] at hlog
  -- assemble: `N (M/2 − T_J) log 2 ≤ N (k log N + log B + k log E + k log H)`
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : (N : ℝ) * (((M : ℝ) / 2 - TJ) * Real.log 2) ≤
      N * (k * Real.log N + Real.log B + k * Real.log E + k * Real.log H) := by
    have e1 : (N : ℝ) * (((M : ℝ) / 2 - TJ) * Real.log 2) ≤ K0 * Real.log 2 := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hK0 hl2.le
    refine e1.trans (hlog.trans ?_)
    have hkm : 0 ≤ (k : ℝ) - 1 := by linarith
    nlinarith [mul_nonneg hkm (mul_nonneg hNpos.le hlogN), mul_nonneg hkm (mul_nonneg hNpos.le hlE),
      mul_nonneg hkm (mul_nonneg hNpos.le hlH), mul_nonneg hNpos.le hlH]
  exact le_of_mul_le_mul_left key hNpos

end StrongSix.Thm1

end LeanPool
