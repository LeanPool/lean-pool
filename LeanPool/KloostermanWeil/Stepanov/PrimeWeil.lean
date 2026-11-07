/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Stepanov.SpectralBound
public import LeanPool.KloostermanWeil.Weil.PrimeFoundation


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# The prime Kloosterman bound

Combines the spectral and point-count arguments to prove Weil’s bound (1948),
following Harcos (2015), Theorem 1, for odd primes. The case `p=2` is proved
separately.
-/

@[expose] public section

namespace KloostermanWeil.Stepanov

open KloostermanWeil.Carlitz
open KloostermanWeil

theorem carlitzAlpha_norm_eq_sqrt_prime
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0)
    (m : {m : ZMod p // m ≠ 0}) :
    ‖carlitzAlpha p (m.1 ^ 2 * c)‖ = Real.sqrt p := by
  let A := carlitzAlpha p (m.1 ^ 2 * c)
  let B := carlitzBeta p (m.1 ^ 2 * c)
  have hAsq : ‖A‖ ^ 2 ≤ (p : ℝ) :=
    carlitzAlpha_norm_sq_le_prime p hpodd c hc m
  have hBsq : ‖B‖ ^ 2 ≤ (p : ℝ) :=
    carlitzBeta_norm_sq_le_prime p hpodd c hc m
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (show 0 < p from (show p.Prime from Fact.out).pos)
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = p :=
    Real.sq_sqrt hpR.le
  have hA : ‖A‖ ≤ Real.sqrt p :=
    (sq_le_sq₀ (norm_nonneg A) (Real.sqrt_nonneg _)).mp (by
      rw [hsqrtSq]
      exact hAsq)
  have hB : ‖B‖ ≤ Real.sqrt p :=
    (sq_le_sq₀ (norm_nonneg B) (Real.sqrt_nonneg _)).mp (by
      rw [hsqrtSq]
      exact hBsq)
  have ht : m.1 ^ 2 * c ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 m.2) hc
  have hAB : ‖A‖ * ‖B‖ = (p : ℝ) := by
    rw [← norm_mul]
    simpa [A, B] using congrArg norm
      (carlitzAlpha_mul_beta p ht)
  have hp_le : (p : ℝ) ≤ ‖A‖ * Real.sqrt p := by
    calc
      (p : ℝ) = ‖A‖ * ‖B‖ := hAB.symm
      _ ≤ ‖A‖ * Real.sqrt p :=
        mul_le_mul_of_nonneg_left hB (norm_nonneg A)
  have hsqrt_le : Real.sqrt p ≤ ‖A‖ := by
    have hmul :
        Real.sqrt p * Real.sqrt p ≤ ‖A‖ * Real.sqrt p := by
      rw [show Real.sqrt p * Real.sqrt p = (p : ℝ) by
        rw [← pow_two]
        exact hsqrtSq]
      exact hp_le
    exact le_of_mul_le_mul_right hmul (Real.sqrt_pos.2 hpR)
  exact le_antisymm hA hsqrt_le

theorem carlitzBeta_norm_eq_sqrt_prime
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0)
    (m : {m : ZMod p // m ≠ 0}) :
    ‖carlitzBeta p (m.1 ^ 2 * c)‖ = Real.sqrt p := by
  let A := carlitzAlpha p (m.1 ^ 2 * c)
  let B := carlitzBeta p (m.1 ^ 2 * c)
  have hA := carlitzAlpha_norm_eq_sqrt_prime p hpodd c hc m
  have ht : m.1 ^ 2 * c ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 m.2) hc
  have hAB : ‖A‖ * ‖B‖ = (p : ℝ) := by
    rw [← norm_mul]
    simpa [A, B] using congrArg norm
      (carlitzAlpha_mul_beta p ht)
  have hsqrtpos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 (by
    exact_mod_cast (show 0 < p from (show p.Prime from Fact.out).pos))
  rw [show ‖A‖ = Real.sqrt p by simpa [A] using hA] at hAB
  have hsqrtSq : Real.sqrt (p : ℝ) * Real.sqrt p = p := by
    rw [← pow_two]
    exact Real.sq_sqrt (by
      exact_mod_cast (show 0 ≤ p from Nat.zero_le p))
  apply (mul_left_cancel₀ hsqrtpos.ne')
  rw [hAB, hsqrtSq]

theorem oneParameterPrimeWeil_odd
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (a : ZMod p) (ha : a ≠ 0) :
    ‖kloostermanSumPrime p a 1‖ ≤ 2 * Real.sqrt p := by
  let m : {m : ZMod p // m ≠ 0} := ⟨1, one_ne_zero⟩
  have hA := carlitzAlpha_norm_eq_sqrt_prime p hpodd a ha m
  have hB := carlitzBeta_norm_eq_sqrt_prime p hpodd a ha m
  have hadd := carlitzAlpha_add_beta p ha
  have hk : Kext p 1 a =
      -(carlitzAlpha p a + carlitzBeta p a) := by
    have hneg := congrArg Neg.neg hadd
    simpa using hneg.symm
  rw [← Kext_one_eq_kloostermanSumPrime]
  rw [hk]
  rw [norm_neg]
  calc
    ‖carlitzAlpha p a + carlitzBeta p a‖
        ≤ ‖carlitzAlpha p a‖ + ‖carlitzBeta p a‖ := norm_add_le _ _
    _ = 2 * Real.sqrt p := by
      have hsum :
          ‖carlitzAlpha p a‖ + ‖carlitzBeta p a‖ =
            Real.sqrt p + Real.sqrt p := by
        simpa [m] using congrArg₂ (fun x y : ℝ => x + y) hA hB
      rw [hsum]
      ring

theorem oneParameterPrimeWeil_two
    (a : ZMod 2) :
    ‖kloostermanSumPrime 2 a 1‖ ≤ 2 * Real.sqrt 2 := by
  unfold kloostermanSumPrime
  calc
    ‖∑ x : ZMod 2,
        if x = 0 then 0 else
          ZMod.stdAddChar (1 * x + a * x⁻¹)‖
        ≤ ∑ x : ZMod 2,
            ‖if x = 0 then (0 : ℂ) else
              ZMod.stdAddChar (1 * x + a * x⁻¹)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : ZMod 2, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases h0 : x = 0
      · simp [h0]
      · simp [h0]
    _ = 2 := by norm_num [ZMod.card]
    _ ≤ 2 * Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg (2 : ℝ)]

/-- One-parameter prime Kloosterman–Weil bound, including characteristic two. -/
theorem oneParameterPrimeWeil_proved :
    OneParameterPrimeWeil := by
  intro p hp a ha
  rcases (show p.Prime from Fact.out).eq_two_or_odd' with rfl | hpodd
  · exact oneParameterPrimeWeil_two a
  · exact oneParameterPrimeWeil_odd p hpodd a ha


end KloostermanWeil.Stepanov
