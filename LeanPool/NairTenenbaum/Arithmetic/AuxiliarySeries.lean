/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.AuxiliaryFunctions
public import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic.Positivity

/-! # Convergence of the auxiliary Euler products

The prime-power geometric estimates and the finite Euler product used in the
preliminary lemmas of §4. No summability over all positive integers is assumed.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- The geometric ratio controlling the local series of `f_h(n)/n`. -/
noncomputable def auxiliaryRatio (ε : ℝ) (γ p : ℕ) : ℝ := (p : ℝ) ^ ((γ : ℝ) * ε - 1)

theorem auxiliaryRatio_nonneg (ε : ℝ) (γ p : ℕ) : 0 ≤ auxiliaryRatio ε γ p := by
  unfold auxiliaryRatio
  positivity

theorem auxiliaryRatio_lt_one {ε : ℝ} {γ p : ℕ} (hp : p.Prime)
    (hγε : (γ : ℝ) * ε < 1) : auxiliaryRatio ε γ p < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (sub_neg.mpr hγε)

theorem auxiliaryLocal_div_pow_le {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    auxiliaryLocal A B ε γ p ν / (p : ℝ) ^ ν ≤ B * auxiliaryRatio ε γ p ^ ν := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc
    auxiliaryLocal A B ε γ p ν / (p : ℝ) ^ ν ≤
        (B * ((p : ℝ) ^ ε) ^ (γ * ν)) / (p : ℝ) ^ ν := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (auxiliaryLocal_le_geometric hA hB hε γ p ν).trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (le_min hA (by positivity)) (min_le_right _ _) _)
          (zero_le_one.trans hB))
    _ = B * auxiliaryRatio ε γ p ^ ν := by
      rw [auxiliaryRatio, Real.rpow_sub hp₀, Real.rpow_one, div_pow, pow_mul,
        Real.rpow_natCast_mul hp₀.le, ← Real.rpow_pow_comm hp₀.le]
      ring

theorem auxiliaryLocal_summable {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (hγε : (γ : ℝ) * ε < 1) {p : ℕ} (hp : p.Prime) :
    Summable (fun ν : ℕ => auxiliaryLocal A B ε γ p ν / (p : ℝ) ^ ν) :=
  Summable.of_nonneg_of_le
    (fun ν => div_nonneg (auxiliaryLocal_nonneg hA (zero_le_one.trans hB) _ _ _) (by positivity))
    (auxiliaryLocal_div_pow_le hA hB hε γ hp)
    ((summable_geometric_of_lt_one (auxiliaryRatio_nonneg ε γ p)
      (auxiliaryRatio_lt_one hp hγε)).mul_left B)

/-- A uniform-in-exponent tail bound for a fixed prime. -/
theorem auxiliaryLocal_tail_le {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (hγε : (γ : ℝ) * ε < 1) {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑' ν : ℕ, auxiliaryLocal A B ε γ p (ν + N) / (p : ℝ) ^ (ν + N)) ≤
      B * auxiliaryRatio ε γ p ^ N / (1 - auxiliaryRatio ε γ p) := by
  have hr₀ := auxiliaryRatio_nonneg ε γ p
  have hr₁ := auxiliaryRatio_lt_one hp hγε
  have hg := (summable_geometric_of_lt_one hr₀ hr₁).mul_left (B * auxiliaryRatio ε γ p ^ N)
  have hf := (summable_nat_add_iff N).mpr (auxiliaryLocal_summable hA hB hε γ hγε hp)
  calc
    _ ≤ ∑' ν : ℕ, (B * auxiliaryRatio ε γ p ^ N) * auxiliaryRatio ε γ p ^ ν := by
      apply Summable.tsum_le_tsum _ hf hg
      intro ν
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using
        auxiliaryLocal_div_pow_le hA hB hε γ hp (ν + N)
    _ = B * auxiliaryRatio ε γ p ^ N / (1 - auxiliaryRatio ε γ p) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr₀ hr₁]
      rfl

/-- Finite Euler product over the integers whose prime factors belong to `s`. -/
theorem auxiliary_smooth_hasSum {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (hγε : (γ : ℝ) * ε < 1) (s : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers s => auxiliary A B ε γ n / (n : ℝ))
      (∏ p ∈ s.filter Nat.Prime, ∑' ν : ℕ, auxiliaryLocal A B ε γ p ν / (p : ℝ) ^ ν) := by
  let f : ℕ → ℝ := fun n => auxiliary A B ε γ n / n
  have hf₁ : f 1 = 1 := by simp [f]
  have hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [f, auxiliary_mul γ hmn, Nat.cast_mul, mul_div_mul_comm]
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun ν : ℕ => ‖f (p ^ ν)‖) := by
    intro p hp
    have hfpos : ∀ ν : ℕ, 0 ≤ f (p ^ ν) := fun ν =>
      div_nonneg (auxiliary_nonneg hA (zero_le_one.trans hB) _ _) (Nat.cast_nonneg _)
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hfpos _)]
    simpa only [f, auxiliary_prime_pow A B ε γ hp, Nat.cast_pow] using
      auxiliaryLocal_summable hA hB hε γ hγε hp
  have heuler := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hf₁ hmul hsum s).2
  convert heuler using 1
  apply Finset.prod_congr rfl
  intro p hp
  apply tsum_congr
  intro ν
  simp only [f, auxiliary_prime_pow A B ε γ (Finset.mem_filter.mp hp).2, Nat.cast_pow]

end NairTenenbaum
