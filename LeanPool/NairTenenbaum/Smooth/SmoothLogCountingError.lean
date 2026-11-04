/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimePowerLogCutoff
public import LeanPool.NairTenenbaum.Polynomials.PrimitivePrimePowerRoots
public import Mathlib.NumberTheory.Chebyshev

/-! # A linear error for the small-prime logarithmic mass

The prime-counting estimate absorbs all prime-power congruence errors,
including the finitely many primes dividing the discriminant.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset Real Filter

theorem card_primes_up_to_eq (z : ℝ) :
    ((range (⌊z⌋₊ + 1)).filter Nat.Prime).card = Nat.primeCounting ⌊z⌋₊ := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

theorem exists_smoothLogRootError_linear_bound {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    (hD : Q.discr ≠ 0) {A C β : ℝ} (hA : 1 ≤ A) (hC : 1 ≤ C) (hβ : 0 < β) (g : ℕ) :
    ∃ x₀ B : ℝ, 1 < x₀ ∧ 0 ≤ B ∧ ∀ x y : ℝ, x₀ < x → x ^ β ≤ y →
      smoothLogRootError Q (C * y) (primePowerLogCutoff (A * x ^ g)) ≤ B * y := by
  let K : ℝ := (max Q.natDegree (Q.discr.natAbs ^ 3) : ℕ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let D : ℝ := ((g : ℝ) + 1) / β
  have hDpos : 0 < D := div_pos (by positivity) hβ
  let b : ℝ := Real.log 4 + 1
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨z₀, Hz⟩ := eventually_atTop.mp (Chebyshev.eventually_primeCounting_le (ε := 1) (by
    norm_num))
  obtain ⟨x₁, HX⟩ := eventually_atTop.mp ((tendsto_rpow_atTop hβ).eventually (eventually_ge_atTop
      (z₀ + 1)))
  let x₀ := max 2 (max A x₁)
  refine ⟨x₀, K * b * C * D, lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    mul_nonneg (mul_nonneg (mul_nonneg hK hb.le) (by linarith)) hDpos.le,
    fun x y hx hy => ?_⟩
  have hx₂ : 2 < x := (le_max_left _ _).trans_lt hx
  have hxA : A < x := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hx)
  have hx₁ : x₁ < x := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hx)
  have hy₁ : 1 < y := (Real.one_lt_rpow (by linarith : 1 < x) hβ).trans_le hy
  have hyz : y ≤ C * y := by nlinarith
  have hz₁ : 1 < C * y := hy₁.trans_le hyz
  have hzbig : z₀ ≤ C * y := by linarith [HX x hx₁.le]
  have hN : 1 ≤ A * x ^ g := by nlinarith [one_le_pow₀ (show 1 ≤ x by linarith) (n := g)]
  have Herror := smoothLogRootError_le_prime_count Q (z := C * y) hN hK
    (fun p hp ν _ => by
      dsimp [K]
      exact_mod_cast primitive_rootCount_prime_pow_uniform hQ hD (mem_filter.mp hp).2 ν)
  rw [card_primes_up_to_eq] at Herror
  have Hprime := Hz (C * y) hzbig
  have hlogz : 0 < Real.log (C * y) := Real.log_pos hz₁
  have Hlogx : β * Real.log x ≤ Real.log (C * y) := by
    have H := Real.log_le_log (Real.rpow_pos_of_pos (by linarith : 0 < x) β) (hy.trans hyz)
    rwa [Real.log_rpow (by linarith : 0 < x)] at H
  have HlogA : Real.log A ≤ Real.log x := Real.log_le_log (by linarith) hxA.le
  have HlogN : Real.log (A * x ^ g) ≤ D * Real.log (C * y) := by
    rw [Real.log_mul (by linarith : A ≠ 0) (pow_ne_zero _ (by linarith : x ≠ 0)), Real.log_pow]
    have H := mul_le_mul_of_nonneg_left Hlogx (show 0 ≤ ((g : ℝ) + 1) / β by positivity)
    have HE : ((g : ℝ) + 1) / β * (β * Real.log x) = ((g : ℝ) + 1) * Real.log x := by field_simp
    rw [HE] at H
    dsimp [D]
    nlinarith
  have Hratio : Real.log (A * x ^ g) / Real.log (C * y) ≤ D :=
    (div_le_iff₀ hlogz).mpr HlogN
  calc
    _ ≤ K * (Nat.primeCounting ⌊C * y⌋₊ : ℝ) * Real.log (A * x ^ g) := Herror
    _ ≤ K * (b * (C * y) / Real.log (C * y)) * Real.log (A * x ^ g) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hprime hK) (Real.log_nonneg hN)
    _ = (K * b * C * y) * (Real.log (A * x ^ g) / Real.log (C * y)) := by ring
    _ ≤ (K * b * C * y) * D :=
      mul_le_mul_of_nonneg_left Hratio (by positivity)
    _ = _ := by ring

end NairTenenbaum
