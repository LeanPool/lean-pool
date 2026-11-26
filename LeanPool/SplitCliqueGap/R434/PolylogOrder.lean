/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.UniformOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! Quantitative rounding at the endpoint density. -/

@[expose] public section

namespace GapExtremal.R434

open Real

/-- The explicit amplitude from fitting the product order to the target order. -/
noncomputable def orderAmplitude (A K c : ℝ) :=
  exp (-(2 * log A + 2 + 2*c + log (27*(1+K)) - (5/2)*log c))

theorem joint_order_parameters (H : ℕ → ℕ) (A K c W : ℝ)
    (hA : 1 ≤ A) (hK : 0 ≤ K) (hc : 0 < c) (hW : 10 ≤ W)
    (hH : ∀ j : ℕ, 1 ≤ j → 1 ≤ H j ∧ (H j : ℝ) ≤ A * (j : ℝ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ m j : ℕ,
      1 ≤ m ∧ Odd m ∧ 1 ≤ j ∧ H j * m ^ (2*j) ≤ n ∧ W/2*(j : ℝ) ≤ m ∧
      sqrt c / (A * exp 1) * n / sqrt (log n) ≤ (m : ℝ)^(2*j) ∧
      orderAmplitude A K c * n^2 / (log n)^(5/2 : ℝ) * exp (-2 * sqrt (c * log n)) ≤
        exp (-c * (j : ℝ)) * (m : ℝ)^(4*j) /
          (27 * (1 + K * (j : ℝ)^3 * (m : ℝ)^2)) := by
  let C := 27 * (1 + K)
  have hC : 0 < C := by dsimp [C]; positivity
  let b := 2 * log A + 2 + 2*c + log C - (5/2)*log c
  obtain ⟨N,hN⟩ := rounded_order_witness H A c hA hc W hW 0 hH
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨m,j,hm,_,hod,hj,horder,hw,hnpos,ht,hjt,hL,hround,hshort⟩ := hN n hn
  let t := sqrt (log n / c)
  simp only [Nat.cast_zero, zero_add] at ht
  change 2 ≤ t at ht
  change (j : ℝ) ≤ t at hjt
  change log n = c*t^2 at hL
  change _ ≤ 2*(log A + log t + 1) at hround
  change _ ≤ c*(t+2) at hshort
  have htpos : 0 < t := by linarith
  have hLpos : 0 < log n := hL ▸ by positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp : 0 < (m : ℝ) := by linarith
  have hjp : 0 < (j : ℝ) := by linarith
  refine ⟨m,j,hm,hod,hj,horder,hw,?_,?_⟩
  · have hAl : 0 < A := by linarith
    have hs : sqrt (log n) = sqrt c*t := by rw [hL,sqrt_mul hc.le,sqrt_sq htpos.le]
    have hlogbd : log n ≤ log (A * exp 1 * t * (m : ℝ)^(2*j)) := by
      rw [log_mul (by positivity) (pow_ne_zero _ hp.ne'),
        log_mul (by positivity) htpos.ne', log_mul hAl.ne' (exp_pos 1).ne',log_exp,log_pow]
      push_cast
      linarith only [hround]
    have hnle := (log_le_log_iff hnpos (by positivity)).mp hlogbd
    rw [hs]
    apply (div_le_iff₀ (by positivity)).mpr
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hp' := mul_le_mul_of_nonneg_left hnle (sqrt_nonneg c)
    linarith only [hp']
  have hLj : log (j : ℝ) ≤ log t := log_le_log hjp hjt
  have hct : c*(j : ℝ) ≤ c*t := mul_le_mul_of_nonneg_left hjt hc.le
  have hroot : sqrt (c*log n) = c*t := by
    rw [hL, show c*(c*t^2)=(c*t)^2 by ring, sqrt_sq (by positivity)]
  have hlog : log (log n) = log c + 2 * log t := by
    conv_lhs => rw [hL, log_mul hc.ne' (pow_ne_zero _ htpos.ne'), log_pow]
    norm_num
  let D := 27*(1+K*(j : ℝ)^3*(m : ℝ)^2)
  have hD : 0 < D := by dsimp [D]; positivity
  have hprod : 1 ≤ (j : ℝ)^3*(m : ℝ)^2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj1) (one_le_pow₀ hm1)
  have hDlog : log D ≤ log C + 3*log (j : ℝ) + 2*log (m : ℝ) := by
    have hle : D ≤ C*(j : ℝ)^3*(m : ℝ)^2 := by dsimp [D,C]; nlinarith only [hprod]
    have h := log_le_log hD hle
    rw [log_mul (by positivity : C*(j : ℝ)^3 ≠ 0) (pow_ne_zero _ hp.ne'),
      log_mul hC.ne' (pow_ne_zero _ hjp.ne'), log_pow, log_pow] at h
    exact_mod_cast h
  change exp (-b) * (n : ℝ)^2 / (log n)^(5/2 : ℝ) * exp (-2 * sqrt (c*log n)) ≤
    exp (-c*(j : ℝ)) * (m : ℝ)^(4*j) / D
  apply (log_le_log_iff (by positivity) (by positivity)).mp
  rw [log_mul (by positivity) (by positivity), log_div (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_exp, log_pow, log_rpow hLpos,
    log_exp, hroot, hlog, log_div (by positivity) hD.ne',
    log_mul (by positivity) (by positivity), log_exp, log_pow]
  push_cast
  dsimp [b]
  linarith only [hround,hshort,hDlog,hLj,hct]

theorem polylog_order_parameters (H : ℕ → ℕ) (A K c W : ℝ)
    (hA : 1 ≤ A) (hK : 0 ≤ K) (hc : 0 < c) (hW : 10 ≤ W)
    (hH : ∀ j : ℕ, 1 ≤ j → 1 ≤ H j ∧ (H j : ℝ) ≤ A * (j : ℝ)) :
    ∃ k : ℝ, 0 < k ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ m j : ℕ,
      1 ≤ m ∧ Odd m ∧ 1 ≤ j ∧ H j * m ^ (2*j) ≤ n ∧ W/2*(j : ℝ) ≤ m ∧
      k * n^2 / (log n)^(5/2 : ℝ) * exp (-2 * sqrt (c * log n)) ≤
        exp (-c * (j : ℝ)) * (m : ℝ)^(4*j) /
          (27 * (1 + K * (j : ℝ)^3 * (m : ℝ)^2)) := by
  exact ⟨orderAmplitude A K c, exp_pos _, by
    obtain ⟨N,hN⟩ := joint_order_parameters H A K c W hA hK hc hW hH
    refine ⟨N,fun n hn => ?_⟩
    obtain ⟨m,j,hm,hod,hj,hsize,hw,_,hg⟩ := hN n hn
    exact ⟨m,j,hm,hod,hj,hsize,hw,hg⟩⟩

end GapExtremal.R434
