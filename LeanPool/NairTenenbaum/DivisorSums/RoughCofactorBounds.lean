/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.RoughMass

/-! # Prime-factor counts of the rough cofactor in Theorem 2 -/

@[expose] public section

namespace NairTenenbaum

open Real

theorem rough_bigOmega_lt_of_lt_pow {n k : ℕ} (hn : n ≠ 0) {z : ℝ} (hz : 1 ≤ z)
    (hrough : ∀ p ∈ n.primeFactors, z ≤ (p : ℝ)) (hsize : (n : ℝ) < z ^ k) :
    bigOmega n < k := by
  by_contra! h
  exact (not_lt_of_ge ((pow_le_pow_right₀ hz h).trans
    (rough_pow_bigOmega_le hn (by linarith) hrough))) hsize

theorem log_le_bigOmega_mul_log {n : ℕ} (hn : n ≠ 0) {P : ℝ} (hP : 1 ≤ P)
    (hprimes : ∀ p ∈ n.primeFactors, (p : ℝ) ≤ P) :
    Real.log n ≤ (bigOmega n : ℝ) * Real.log P := by
  have H : ∀ l : List ℕ, (∀ p ∈ l, (p : ℝ) ≤ P) → (l.prod : ℝ) ≤ P ^ l.length := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      intro hl
      simp only [List.prod_cons, Nat.cast_mul, List.length_cons, pow_succ]
      exact (mul_le_mul (hl p (by simp)) (ih (fun q hq => hl q (by simp [hq])))
        (Nat.cast_nonneg _) (by linarith : 0 ≤ P)).trans_eq (mul_comm _ _)
  have H' : (n : ℝ) ≤ P ^ bigOmega n := by
    simpa only [bigOmega, Nat.prod_primeFactorsList hn] using
      H n.primeFactorsList (fun p hp => hprimes p
          (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp))
  have HL := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ) < n) H'
  simpa only [Real.log_pow] using HL

theorem small_divisor_coprime_rough {d b : ℕ} (hd : 0 < d) (hb : b ≠ 0) {z : ℝ}
    (hdz : (d : ℝ) ≤ z) (hrough : ∀ p ∈ b.primeFactors, z < (p : ℝ)) : d.Coprime b := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpb
  have H := hrough p (Nat.mem_primeFactors.mpr ⟨hp, hpb, hb⟩)
  have Hp : (p : ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd hd hpd
  linarith

theorem rough_cofactor_mul_divisor_le {a b d : ℕ} (hd : 0 < d) (hb : b ≠ 0) {z : ℝ}
    (hdz : (d : ℝ) ≤ z) (hrough : ∀ p ∈ b.primeFactors, z < (p : ℝ)) (hdab : d ∣ a * b)
    (ha : a ≠ 0) : d * b ≤ a * b := by
  have hda := (small_divisor_coprime_rough hd hb hdz hrough).dvd_of_dvd_mul_right hdab
  exact Nat.mul_le_mul_right b (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hda)

theorem rough_cofactor_bigOmega_le {b k : ℕ} (hb : b ≠ 0) {A C y : ℝ}
    (hy : 1 ≤ y) (hC : 1 ≤ C) (hA : A < C ^ k)
    (hsize : (b : ℝ) ≤ A * y ^ k) (hrough : ∀ p ∈ b.primeFactors, C * y ≤ (p : ℝ)) :
    bigOmega b ≤ k - 1 := by
  have Hsize : (b : ℝ) < (C * y) ^ k := by
    rw [mul_pow]
    exact hsize.trans_lt (mul_lt_mul_of_pos_right hA (pow_pos (by linarith : 0 < y) k))
  have H := rough_bigOmega_lt_of_lt_pow hb (by nlinarith : 1 ≤ C * y) hrough Hsize
  omega

theorem rough_cofactor_bigOmega_le_of_window_divisor {n b d k : ℕ} (hb : b ≠ 0)
    (hk : 2 ≤ k) {A C y : ℝ} (hy : 1 ≤ y) (hC : 1 ≤ C) (hA : 2 * A < C ^ (k - 1))
    (hsize : (n : ℝ) ≤ A * y ^ k) (hdiv : d * b ≤ n) (hd : y / 2 < (d : ℝ))
    (hrough : ∀ p ∈ b.primeFactors, C * y ≤ (p : ℝ)) :
    bigOmega b ≤ k - 2 := by
  have hy₀ : 0 < y := by linarith
  have hb₀ : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
  have HD : (y / 2) * (b : ℝ) < A * y ^ k := by
    apply (mul_lt_mul_of_pos_right hd hb₀).trans_le
    exact (by exact_mod_cast hdiv : (d : ℝ) * b ≤ n).trans hsize
  have hp : y ^ k = y ^ (k - 1) * y := by rw [← pow_succ]; congr 1; omega
  have HB : (b : ℝ) < 2 * A * y ^ (k - 1) := by rw [hp] at HD; nlinarith
  have HC : (b : ℝ) < (C * y) ^ (k - 1) := by
    rw [mul_pow]
    exact HB.trans (mul_lt_mul_of_pos_right hA (pow_pos hy₀ _))
  have H := rough_bigOmega_lt_of_lt_pow hb (by nlinarith : 1 ≤ C * y) hrough HC
  omega

end NairTenenbaum
