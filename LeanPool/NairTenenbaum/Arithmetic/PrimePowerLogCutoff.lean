/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SmoothLogRootBound

/-! # A logarithmic cutoff for prime-power divisibility -/

@[expose] public section

namespace NairTenenbaum

open Finset Real

/-- The exponent cutoff used to truncate the prime-power logarithmic expansion. -/
noncomputable def primePowerLogCutoff (N : ℝ) (p : ℕ) : ℕ := ⌊Real.log N / Real.log p⌋₊

theorem factorization_le_primePowerLogCutoff {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    {N : ℝ} (hsize : (n : ℝ) ≤ N) : n.factorization p ≤ primePowerLogCutoff N p := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have Hpow : (p : ℝ) ^ n.factorization p ≤ N := by
    apply le_trans _ hsize
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.ordProj_dvd n p)
  apply Nat.le_floor
  apply (le_div_iff₀ (Real.log_pos hp₁)).mpr
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos hp₀ _) Hpow

theorem primePowerLogCutoff_mul_log_le {N : ℝ} (hN : 1 ≤ N) {p : ℕ} (hp : p.Prime) :
    (primePowerLogCutoff N p : ℝ) * Real.log p ≤ Real.log N := by
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact (le_div_iff₀ (Real.log_pos hp₁)).mp (Nat.floor_le
    (div_nonneg (Real.log_nonneg hN) (Real.log_pos hp₁).le))

theorem smoothLogRootError_le_prime_count (Q : Polynomial ℤ) {N K z : ℝ}
    (hN : 1 ≤ N) (hK : 0 ≤ K)
    (hroot : ∀ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, ∀ ν : ℕ, 0 < ν →
      (rootCount Q (p ^ ν) : ℝ) ≤ K) :
    smoothLogRootError Q z (primePowerLogCutoff N) ≤
      K * (((range (⌊z⌋₊ + 1)).filter Nat.Prime).card : ℝ) * Real.log N := by
  unfold smoothLogRootError
  calc
    _ ≤ ∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, K * Real.log N := by
      apply sum_le_sum
      intro p hp
      have hp' := (mem_filter.mp hp).2
      have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)
      have HS : (∑ ν ∈ Icc 1 (primePowerLogCutoff N p), (rootCount Q (p ^ ν) : ℝ)) ≤
          (primePowerLogCutoff N p : ℝ) * K := by
        calc
          _ ≤ ∑ _ν ∈ Icc 1 (primePowerLogCutoff N p), K :=
            sum_le_sum (fun ν hν => hroot p hp ν (mem_Icc.mp hν).1)
          _ = _ := by simp
      have HC := mul_le_mul_of_nonneg_left (primePowerLogCutoff_mul_log_le hN hp') hK
      nlinarith [mul_le_mul_of_nonneg_right HS hl]
    _ = _ := by simp; ring

/-- The exponent cutoff is supplied by a bound on the actual polynomial
values; it is not an extra distributional hypothesis. -/
theorem polynomialSmoothLogMass_le_log_cutoff (Q : Polynomial ℤ) {x y z N : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hQ : ∀ n ∈ shortInterval x y, Q.eval (n : ℤ) ≠ 0)
    (hsize : ∀ n ∈ shortInterval x y, ((Q.eval (n : ℤ)).natAbs : ℝ) ≤ N) :
    polynomialSmoothLogMass Q x y z ≤
      (y + 1) * smoothLogRootMain Q z (primePowerLogCutoff N) +
        smoothLogRootError Q z (primePowerLogCutoff N) := by
  apply polynomialSmoothLogMass_le_root_terms Q hx hy hz hQ
  intro p hp n hn
  exact factorization_le_primePowerLogCutoff (Int.natAbs_ne_zero.mpr (hQ n hn))
    (mem_filter.mp hp).2 (hsize n hn)

end NairTenenbaum
