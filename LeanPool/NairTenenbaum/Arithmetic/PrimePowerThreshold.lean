/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeThreshold
public import LeanPool.NairTenenbaum.Polynomials.PolynomialLocal
public import Mathlib.Algebra.Order.Star.Real

/-! # Least prime powers exceeding a real threshold -/

@[expose] public section

namespace NairTenenbaum

/-- The least exponent whose prime power exceeds the real threshold. -/
noncomputable def firstPowerAbove (p : ℕ) (T : ℝ) : ℕ :=
  if hp : 1 < p then Nat.find (pow_unbounded_of_one_lt T (by
    exact_mod_cast hp : (1 : ℝ) < p)) else 0

theorem firstPowerAbove_spec {p : ℕ} (hp : 1 < p) (T : ℝ) :
    T < (p : ℝ) ^ firstPowerAbove p T := by
  simp only [firstPowerAbove, dite_eq_left hp]
  exact Nat.find_spec (pow_unbounded_of_one_lt T (by exact_mod_cast hp : (1 : ℝ) < p))

theorem firstPowerAbove_le {p e : ℕ} (hp : 1 < p) {T : ℝ} (he : T < (p : ℝ) ^ e) :
    firstPowerAbove p T ≤ e := by
  simp only [firstPowerAbove, dite_eq_left hp]
  exact Nat.find_min' _ he

theorem firstPowerAbove_pos {p : ℕ} (hp : 1 < p) {T : ℝ} (hT : 1 ≤ T) :
    0 < firstPowerAbove p T := by
  have H := firstPowerAbove_spec hp T
  by_contra h
  have he : firstPowerAbove p T = 0 := by omega
  rw [he, pow_zero] at H
  linarith

theorem firstPowerAbove_upper {p : ℕ} (hp : 1 < p) {T : ℝ} (hT : 1 ≤ T) :
    (p : ℝ) ^ firstPowerAbove p T ≤ p * T := by
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (firstPowerAbove_pos hp hT).ne'
  have hprev : (p : ℝ) ^ e ≤ T := by
    by_contra! h
    have H := firstPowerAbove_le hp h
    omega
  rw [he, pow_succ, mul_comm]
  exact mul_le_mul_of_nonneg_left hprev (Nat.cast_nonneg _)

/-- Minimality preserves divisibility whenever an available prime power
already exceeds the threshold. -/
theorem firstPowerAbove_dvd {p e n : ℕ} (hp : 1 < p) {T : ℝ}
    (he : T < (p : ℝ) ^ e) (hd : p ^ e ∣ n) : p ^ firstPowerAbove p T ∣ n :=
  (pow_dvd_pow p (firstPowerAbove_le hp he)).trans hd

/-- The total multiplicities of the irreducible factors are bounded by degree. -/
theorem PolynomialSystem.sum_totalExponent_le_degree {k r : ℕ} (P : PolynomialSystem k r) :
    (∑ i, totalExponent P.exponent i) ≤ P.total.natDegree := by
  rw [P.total_degree]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right _ (P.factor_degree_pos i))

/-- A large weighted prime part forces a large prime power in one coordinate.
The exponent loss is the total degree, accounting for repeated factors. -/
theorem PolynomialSystem.exists_large_coordinate_primePower {k r : ℕ} (P : PolynomialSystem k r)
    (n : Tuple r) {p : ℕ} {T : ℝ} (hT : 1 ≤ T)
    (hlarge : T ^ P.total.natDegree <
      (p : ℝ) ^ (∑ i, totalExponent P.exponent i * (n i : ℕ).factorization p)) :
    ∃ i, T < (p : ℝ) ^ (n i : ℕ).factorization p := by
  by_contra! h
  have H : (p : ℝ) ^ (∑ i, totalExponent P.exponent i * (n i : ℕ).factorization p) ≤
      T ^ (∑ i, totalExponent P.exponent i) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
    intro i _
    rw [Nat.mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (h i) _
  exact (not_lt_of_ge (H.trans (pow_le_pow_right₀ hT P.sum_totalExponent_le_degree))) hlarge

/-- The gap between two prefix thresholds forces a large coordinate prime
power at the crossing prime. -/
theorem PolynomialSystem.exists_large_primePower_of_crossing {k r : ℕ} (P : PolynomialSystem k r)
    (n : Tuple r) {p : ℕ} (hp : p.Prime) {T : ℝ} (hT : 1 ≤ T)
    (hsmall : (weightedMass P.exponent (primeSelect n (Finset.range p)) : ℝ) ≤ T ^
        P.total.natDegree)
    (hcross : (T ^ P.total.natDegree) ^ 2 <
      (weightedMass P.exponent (primeSelect n (Finset.range (p + 1))) : ℝ)) :
    ∃ i, T < (p : ℝ) ^ (n i : ℕ).factorization p := by
  apply P.exists_large_coordinate_primePower n hT
  have hmass : weightedMass P.exponent (primePart n p) =
      p ^ (∑ i, totalExponent P.exponent i * (n i : ℕ).factorization p) := by
    simpa only [mass_substitute] using mass_substitute_primePart P.exponent n hp
  rw [primeSelect_range_succ, weightedMass_mul, hmass, Nat.cast_mul, Nat.cast_pow] at hcross
  by_contra! h
  have H := mul_le_mul hsmall h (by positivity) (pow_nonneg (zero_le_one.trans hT) _)
  nlinarith

end NairTenenbaum
