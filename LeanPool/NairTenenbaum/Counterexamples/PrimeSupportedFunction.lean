/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
import Mathlib.Tactic.Positivity

/-! # An arithmetic function supported on powers of two

This family supplies admissible test functions with arbitrarily small positive
growth exponents. Its multiplicativity is proved on all positive inputs.
-/

@[expose] public section

namespace NairTenenbaum

/-- The predicate that an integer is a power of two. -/
def TwoPower (n : ℕ) : Prop := ∃ ν : ℕ, n = 2 ^ ν

theorem twoPower_mul_iff (m n : ℕ) : TwoPower (m * n) ↔ TwoPower m ∧ TwoPower n := by
  constructor
  · rintro ⟨ν, hν⟩
    have hm : m ∣ 2 ^ ν := hν ▸ dvd_mul_right m n
    have hn : n ∣ 2 ^ ν := hν ▸ dvd_mul_left n m
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  · rintro ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    exact ⟨i + j, (pow_add _ _ _).symm⟩

/-- Value `a^ν` at `2^ν`, and zero elsewhere. -/
noncomputable def twoSupported (a : ℝ) (n : ℕ+) : ℝ := by
  classical
  exact if TwoPower n then a ^ (n : ℕ).factorization 2 else 0

theorem twoSupported_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ+) : 0 ≤ twoSupported a n := by
  unfold twoSupported
  split_ifs <;> positivity

@[simp] theorem twoSupported_pow (a : ℝ) (ν : ℕ) :
    twoSupported a ((2 : ℕ+) ^ ν) = a ^ ν := by
  classical
  change (if TwoPower (2 ^ ν) then a ^ (2 ^ ν).factorization 2 else 0) = _
  rw [ite_eq_left ⟨ν, rfl⟩, Nat.factorization_pow_self Nat.prime_two]

theorem twoSupported_mul (a : ℝ) (m n : ℕ+) :
    twoSupported a (m * n) = twoSupported a m * twoSupported a n := by
  classical
  unfold twoSupported
  change (if TwoPower ((m : ℕ) * (n : ℕ)) then a ^ ((m : ℕ) * (n : ℕ)).factorization 2 else 0) = _
  by_cases hm : TwoPower m <;> by_cases hn : TwoPower n
  · have hmn : TwoPower ((m : ℕ) * (n : ℕ)) := (twoPower_mul_iff m n).mpr ⟨hm, hn⟩
    simp only [ite_eq_left hm, ite_eq_left hn, ite_eq_left hmn,
      Nat.factorization_mul m.ne_zero n.ne_zero, Finsupp.add_apply, pow_add]
  · have hmn : ¬ TwoPower ((m : ℕ) * (n : ℕ)) := fun h => hn ((twoPower_mul_iff m n).mp h).2
    simp [hn, hmn]
  · have hmn : ¬ TwoPower ((m : ℕ) * (n : ℕ)) := fun h => hm ((twoPower_mul_iff m n).mp h).1
    simp [hm, hmn]
  · have hmn : ¬ TwoPower ((m : ℕ) * (n : ℕ)) := fun h => hm ((twoPower_mul_iff m n).mp h).1
    simp [hm, hmn]

theorem twoSupported_growth (η : ℝ) (n : ℕ+) :
    twoSupported ((2 : ℝ) ^ η) n ≤
      min (((2 : ℝ) ^ η) ^ bigOmega n) ((n : ℝ) ^ η) := by
  classical
  by_cases hn : TwoPower n
  · obtain ⟨ν, hν⟩ := hn
    have heq : n = (2 : ℕ+) ^ ν := PNat.coe_injective (by simpa using hν)
    rw [heq, twoSupported_pow]
    simp only [PNat.pow_coe, PNat.val_ofNat]
    have hΩ : bigOmega (2 ^ ν) = ν := by
      simp [bigOmega, Nat.prime_two.primeFactorsList_pow]
    rw [hΩ]
    change ((2 : ℝ) ^ η) ^ ν ≤ min (((2 : ℝ) ^ η) ^ ν) ((((2 : ℕ) ^ ν : ℕ) : ℝ) ^ η)
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), min_self]
  · rw [twoSupported, ite_eq_right hn]
    exact le_min (by positivity) (by positivity)

/-- The arithmetic map supported on powers of two in the counterexample. -/
noncomputable def twoSupportedMap (a : ℝ) : ArithmeticMap 1 := fun n => twoSupported a (n 0)

/-- Membership holds for every real exponent; applications use positive exponents. -/
theorem twoSupported_admissible (η : ℝ) :
    Admissible ((2 : ℝ) ^ η) 1 η (twoSupportedMap ((2 : ℝ) ^ η)) := by
  refine ⟨fun n => twoSupported_nonneg (by positivity) _, fun m n _ => ?_⟩
  change twoSupported ((2 : ℝ) ^ η) (m 0 * n 0) ≤ _
  rw [twoSupported_mul]
  apply mul_le_mul_of_nonneg_right _ (twoSupported_nonneg (by positivity) _)
  simpa only [growthBound, mass, Fin.prod_univ_one, one_mul] using twoSupported_growth η (m 0)

/-- A multiplicative twist depending only on the exponent of two. -/
noncomputable def twoTwist (a : ℝ) (n : ℕ) : ℝ := (2 / a) ^ n.factorization 2

theorem twoTwist_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < twoTwist a n := by
  unfold twoTwist
  positivity

@[simp] theorem twoTwist_one (a : ℝ) : twoTwist a 1 = 1 := by simp [twoTwist]

theorem twoTwist_mul (a : ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    twoTwist a (m * n) = twoTwist a m * twoTwist a n := by
  simp only [twoTwist, Nat.factorization_mul hm hn, Finsupp.add_apply, pow_add]

@[simp] theorem twoTwist_two_pow (a : ℝ) (ν : ℕ) : twoTwist a (2 ^ ν) = (2 / a) ^ ν := by
  rw [twoTwist, Nat.factorization_pow_self Nat.prime_two]

theorem twoTwist_other_prime_pow (a : ℝ) {p : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) (ν : ℕ) :
    twoTwist a (p ^ ν) = 1 := by
  simp [twoTwist, hp.factorization_pow, hp₂]

end NairTenenbaum
