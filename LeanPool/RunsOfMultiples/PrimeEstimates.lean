/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.PrimeInput
public import Mathlib.NumberTheory.Chebyshev

/-!
# Elementary prime estimates from Chebyshev bounds

The lower theta bound and prime interval estimates use Mathlib without the entropy upper bound.
-/

@[expose] public section

open Finset Real Chebyshev

namespace RunsOfMultiples

lemma primesUpTo_eq (m : ℕ) : primesUpTo m = Nat.primesLE m := by
  ext p
  simp [primesUpTo, Nat.mem_primesLE]

lemma sum_primesUpTo_eq_theta (m : ℕ) : ∑ p ∈ primesUpTo m, log (p : ℝ) = θ m := by
  rw [primesUpTo_eq, theta_eq_sum_primesLE_log]

/-- `log x ≤ k x^(1/k)` for `x ≥ 0`, in the form we use. -/
lemma log_le_mul_rpow {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) : log x ≤ ε⁻¹ * x ^ ε := by
  have := log_le_rpow_div hx hε
  rwa [div_eq_inv_mul] at this

lemma log_two_le_one : log (2 : ℝ) ≤ 1 := by
  have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

/-- Chebyshev lower bound in the form `θ(m) ≥ (log 2 / 2) m - C`. -/
theorem theta_lower : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, log 2 / 2 * m - C ≤ θ m := by
  have hl2 : 0 < log (2 : ℝ) := log_pos one_lt_two
  set A : ℝ := (24 / log 2) ^ (4 : ℕ) with hA
  refine ⟨log 2 / 2 * A + 1, by positivity, fun m => ?_⟩
  by_cases hm : (m : ℝ) < A
  · have : log 2 / 2 * (m : ℝ) ≤ log 2 / 2 * A := by gcongr
    have := theta_nonneg (m : ℝ)
    linarith
  push Not at hm
  have hA1 : 1 ≤ A := by
    rw [hA]
    apply one_le_pow₀
    rw [le_div_iff₀ hl2]
    linarith [log_two_le_one]
  have hm1 : (1 : ℝ) ≤ m := hA1.trans hm
  have hm0 : (0 : ℝ) < m := by linarith
  set r : ℝ := (m : ℝ) ^ ((1 : ℝ) / 4) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : 1 ≤ r := one_le_rpow hm1 (by norm_num)
  -- m = r^4 and √m = r^2
  have hm4 : (m : ℝ) = r ^ (4 : ℕ) := by
    rw [hr, ← rpow_natCast, ← rpow_mul hm0.le]
    norm_num
  have hsq : √(m : ℝ) = r ^ (2 : ℕ) := by
    rw [hm4, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sqrt_sq (by positivity)]
  have hlogm : log (m : ℝ) ≤ 4 * r := by
    have := log_le_mul_rpow hm0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [← hr] at this
    linarith [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num]
  have hlogm1 : log ((m : ℝ) + 1) ≤ 1 + 4 * r := by
    have h2m : (m : ℝ) + 1 ≤ 2 * m := by linarith
    have := log_le_log (by linarith) h2m
    rw [log_mul two_ne_zero hm0.ne'] at this
    linarith [log_two_le_one]
  -- r ≥ 24 / log 2
  have hr24 : 24 / log 2 ≤ r := by
    have h1 : A ^ ((1 : ℝ) / 4) ≤ r := rpow_le_rpow (by positivity) hm (by norm_num)
    have h2 : A ^ ((1 : ℝ) / 4) = 24 / log 2 := by
      rw [hA, ← rpow_natCast, ← rpow_mul (by positivity)]
      norm_num
    linarith
  have hθ := theta_ge m
  have hlogm0 : 0 ≤ log (m : ℝ) := log_nonneg hm1
  -- error terms are at most 1 + 12 r^3 ≤ 1 + (log 2 / 2) m
  have herr : log ((m : ℝ) + 1) + 2 * √(m : ℝ) * log m ≤ 1 + log 2 / 2 * m := by
    have h1 : 2 * √(m : ℝ) * log m ≤ 8 * r ^ (3 : ℕ) := by
      rw [hsq]
      have := mul_le_mul_of_nonneg_left hlogm (show (0 : ℝ) ≤ 2 * r ^ (2 : ℕ) by positivity)
      nlinarith only [this]
    have h2 : r ≤ r ^ (3 : ℕ) := by
      calc r = r ^ (1 : ℕ) := by simp
        _ ≤ r ^ (3 : ℕ) := pow_le_pow_right₀ hr1 (by norm_num)
    have h3 : 12 * r ^ (3 : ℕ) ≤ log 2 / 2 * m := by
      rw [hm4]
      have : 24 ≤ log 2 * r := by
        rw [div_le_iff₀ hl2] at hr24
        linarith
      have h3' : 0 ≤ r ^ (3 : ℕ) := by positivity
      nlinarith only [mul_le_mul_of_nonneg_right this h3']
    linarith only [hlogm1, h1, h2, h3]
  have hA0 : 0 ≤ log 2 / 2 * A := by positivity
  linarith

/-- At least `q^(3/4)` primes in `(q, 4q]` for large `q`. -/
theorem many_primes : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    (q : ℝ) ^ ((3 : ℝ) / 4) ≤ (((Ioc q (4 * q)).filter Nat.Prime).card : ℝ) := by
  have hl2 : 0 < log (2 : ℝ) := log_pos one_lt_two
  set B : ℝ := (48 / log 2) ^ (8 : ℕ) with hB
  refine ⟨⌈B⌉₊, fun q hq => ?_⟩
  have hqB : B ≤ q := (Nat.le_ceil B).trans (by exact_mod_cast hq)
  have hB1 : 1 ≤ B := by
    rw [hB]
    apply one_le_pow₀
    rw [le_div_iff₀ hl2]
    linarith [log_two_le_one]
  have hq1 : (1 : ℝ) ≤ q := hB1.trans hqB
  have hq0 : (0 : ℝ) < q := by linarith
  set P := (Ioc q (4 * q)).filter Nat.Prime with hP
  -- θ(4q) - θ(q) = ∑_{p ∈ P} log p ≤ |P| log (4q)
  have hsplit : θ ((4 * q : ℕ) : ℝ) = θ (q : ℝ) + ∑ p ∈ P, log (p : ℝ) := by
    rw [theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log]
    have hsub : Nat.primesLE q ⊆ Nat.primesLE (4 * q) := Nat.primesLE_mono (by omega)
    rw [← sum_sdiff hsub, add_comm]
    congr 2
    ext p
    simp only [mem_sdiff, Nat.mem_primesLE, hP, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by by_contra h; exact h3 ⟨by omega, h2⟩, h1⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h2, h3⟩, fun h => by omega⟩
  have hPle : ∑ p ∈ P, log (p : ℝ) ≤ P.card * log (4 * q) := by
    have : ∑ p ∈ P, log (p : ℝ) ≤ ∑ p ∈ P, log (4 * (q : ℝ)) := by
      refine sum_le_sum fun p hp => ?_
      rw [hP, mem_filter, mem_Ioc] at hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
      exact log_le_log hp0 (by exact_mod_cast hp.1.2)
    rwa [sum_const, nsmul_eq_mul] at this
  have hlo := theta_ge (4 * q)
  have hup := theta_le_log4_mul_x hq0.le
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
    norm_num
  push_cast at hlo hsplit
  -- abbreviations
  set r : ℝ := (q : ℝ) ^ ((1 : ℝ) / 8) with hr
  have hr1 : 1 ≤ r := one_le_rpow hq1 (by norm_num)
  have hq8 : (q : ℝ) = r ^ (8 : ℕ) := by
    rw [hr, ← rpow_natCast, ← rpow_mul hq0.le]
    norm_num
  have hq34 : (q : ℝ) ^ ((3 : ℝ) / 4) = r ^ (6 : ℕ) := by
    rw [hr, ← rpow_natCast, ← rpow_mul hq0.le]
    norm_num
  have hsq : √(4 * (q : ℝ)) = 2 * r ^ (4 : ℕ) := by
    rw [hq8, show (8 : ℕ) = 4 * 2 by rfl, pow_mul, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
      ← mul_pow, sqrt_sq (by positivity)]
  -- ℓ = log (8q) bounds both logarithms, and ℓ ≤ 16 r
  set ℓ : ℝ := log (8 * (q : ℝ)) with hℓ
  have hℓ1 : log (4 * (q : ℝ) + 1) ≤ ℓ := log_le_log (by positivity) (by linarith)
  have hℓ2 : log (4 * (q : ℝ)) ≤ ℓ := log_le_log (by positivity) (by linarith)
  have hl4q : 0 < log (4 * (q : ℝ)) := log_pos (by linarith)
  have hℓr : ℓ ≤ 16 * r := by
    have h := log_le_mul_rpow (show (0 : ℝ) ≤ 8 * q by positivity)
      (show (0 : ℝ) < 1 / 8 by norm_num)
    rw [mul_rpow (by norm_num) hq0.le, ← hr] at h
    have h8 : (8 : ℝ) ^ ((1 : ℝ) / 8) ≤ 2 := by
      rw [show (2 : ℝ) = ((2 : ℝ) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) by
        rw [← rpow_natCast, ← rpow_mul (by norm_num)]; norm_num]
      exact rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    have : ((1 : ℝ) / 8)⁻¹ = 8 := by norm_num
    rw [this] at h
    nlinarith only [h, h8, show (0 : ℝ) ≤ r by positivity]
  have hr48 : 48 / log 2 ≤ r := by
    have h1 : B ^ ((1 : ℝ) / 8) ≤ r := rpow_le_rpow (by positivity) hqB (by norm_num)
    have h2 : B ^ ((1 : ℝ) / 8) = 48 / log 2 := by
      rw [hB, ← rpow_natCast, ← rpow_mul (by positivity)]
      norm_num
    linarith
  have hr48' : 48 ≤ log 2 * r := by
    rw [div_le_iff₀ hl2] at hr48
    linarith
  -- main inequality: |P| log(4q) ≥ 2 q log 2 - ℓ (1 + 4 r^4) ≥ r^6 ℓ ≥ r^6 log (4q)
  have hmain : r ^ (6 : ℕ) * log (4 * (q : ℝ)) ≤ P.card * log (4 * (q : ℝ)) := by
    have hℓ0 : 0 ≤ ℓ := hl4q.le.trans hℓ2
    have hsq' : 2 * √(4 * (q : ℝ)) * log (4 * (q : ℝ)) ≤ 4 * r ^ (4 : ℕ) * ℓ := by
      rw [hsq]
      have h := mul_le_mul_of_nonneg_left hℓ2 (show 0 ≤ 4 * r ^ (4 : ℕ) by positivity)
      nlinarith only [h]
    have hr46 : r ^ (4 : ℕ) ≤ r ^ (6 : ℕ) := pow_le_pow_right₀ hr1 (by norm_num)
    have hr06 : 1 ≤ r ^ (6 : ℕ) := one_le_pow₀ hr1
    -- ℓ (1 + 4 r^4 + r^6) ≤ 6 r^6 ℓ ≤ 96 r^7 ≤ 2 log 2 · r^8
    have hbig : ℓ * (1 + 4 * r ^ (4 : ℕ) + r ^ (6 : ℕ)) ≤ 2 * log 2 * r ^ (8 : ℕ) := by
      have e1 : ℓ * (1 + 4 * r ^ (4 : ℕ) + r ^ (6 : ℕ)) ≤ 6 * r ^ (6 : ℕ) * ℓ := by
        have hsum : 1 + 4 * r ^ (4 : ℕ) + r ^ (6 : ℕ) ≤ 6 * r ^ (6 : ℕ) := by
          linarith only [hr06, hr46]
        nlinarith only [mul_le_mul_of_nonneg_left hsum hℓ0]
      have e2 : 6 * r ^ (6 : ℕ) * ℓ ≤ 96 * r ^ (7 : ℕ) := by
        have : 0 ≤ 6 * r ^ (6 : ℕ) := by positivity
        have := mul_le_mul_of_nonneg_left hℓr this
        nlinarith only [this]
      have e3 : 96 * r ^ (7 : ℕ) ≤ 2 * log 2 * r ^ (8 : ℕ) := by
        have h7 : 0 ≤ r ^ (7 : ℕ) := by positivity
        have : r ^ (8 : ℕ) = r ^ (7 : ℕ) * r := by ring
        rw [this]
        nlinarith only [mul_le_mul_of_nonneg_right hr48' h7]
      linarith
    have hθ : 4 * (q : ℝ) * log 2 - log (4 * q + 1) - 2 * √(4 * (q : ℝ)) * log (4 * q) ≤
        θ (q : ℝ) + ∑ p ∈ P, log (p : ℝ) := by
      rw [← hsplit]; exact hlo
    rw [hlog4] at hup
    have : r ^ (6 : ℕ) * log (4 * (q : ℝ)) ≤ r ^ (6 : ℕ) * ℓ :=
      mul_le_mul_of_nonneg_left hℓ2 (by positivity)
    have hq8' : log 2 * (q : ℝ) = log 2 * r ^ (8 : ℕ) := by rw [hq8]
    linarith only [hθ, hup, hPle, hℓ1, hsq', hbig, this, hq8']
  rw [hq34]
  exact le_of_mul_le_mul_right hmain hl4q

end RunsOfMultiples
