/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimePowerCounting
public import LeanPool.NairTenenbaum.Sieve.SmallDivisorSum
public import LeanPool.NairTenenbaum.Smooth.SmoothDivisorDensity

/-! # Counting polynomial values with a large smooth divisor -/

@[expose] public section

namespace NairTenenbaum

/-- Smooth divisors between the lower real cutoff and the upper integral cutoff. -/
noncomputable def smoothLargeDivisors (s : Finset ℕ) (N : ℕ+) (T : ℝ) : Finset ℕ+ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n : ℕ+ => (n : ℕ) ∈ Nat.factoredNumbers s ∧ T < (n : ℝ))

/-- Polynomial values divisible by one of the specified large smooth divisors. -/
noncomputable def smoothDivisorExceptionalSet (Q : Polynomial ℤ) (s : Finset ℕ)
    (N : ℕ+) (T : ℝ) (a b : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Ioc a b).filter (fun t => ∃ d ∈ smoothLargeDivisors s N T, (d : ℤ) ∣ Q.eval t)

/-- The uniform constant for counting values with a large smooth divisor. -/
noncomputable def smoothDivisorBound (g D : ℕ) (s : Finset ℕ) : ℝ :=
  ((max g (D ^ 3)) ^ (s.filter Nat.Prime).card : ℕ) *
    (1 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (s.filter Nat.Prime).card

theorem smoothDivisorBound_pos (g : ℕ) {D : ℕ} (hD : 0 < D) (s : Finset ℕ) :
    0 < smoothDivisorBound g D s := by
  have hM : 0 < max g (D ^ 3) := (pow_pos hD 3).trans_le (le_max_right _ _)
  have hden : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  unfold smoothDivisorBound
  positivity

/-- A union over the large smooth moduli uses their reciprocal-density tail. -/
theorem PolynomialSystem.smoothDivisorExceptionalSet_card_le {k r : ℕ} (P : PolynomialSystem k r)
    (s : Finset ℕ) (N : ℕ+) {T : ℝ} (hT : 0 < T) {a b : ℤ} (hab : a ≤ b)
    (hlevel : (N : ℝ) ≤ (b : ℝ) - a) :
    ((smoothDivisorExceptionalSet P.radical s N T a b).card : ℝ) ≤
      2 * ((b : ℝ) - a) * smoothDivisorBound P.total.natDegree P.badDiscriminant s *
        T ^ (-(1 / 2 : ℝ)) := by
  let S := smoothLargeDivisors s N T
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hdensity := smooth_root_density_tail_le P.radical s
    (max P.total.natDegree (P.badDiscriminant ^ 3))
    ((Nat.one_le_pow _ _ P.badDiscriminant_pos).trans (le_max_right _ _))
    (fun _ _ hp ν => P.radical_rootCount_prime_pow_uniform hp ν) S
    (fun d hd => (Finset.mem_filter.mp hd).2.1) hT (fun d hd => (Finset.mem_filter.mp hd).2.2.le)
  calc
    _ ≤ ∑ d ∈ S, (polynomialCongruenceCount P.radical d a b : ℝ) := by
      exact_mod_cast polynomialCongruenceUnion_card_le S (fun _ => P.radical) (fun d => (d : ℕ)) a b
    _ ≤ ∑ d ∈ S, 2 * ((b : ℝ) - a) * rootCount P.radical d / d := by
      apply Finset.sum_le_sum
      intro d hd
      exact polynomialCongruenceCount_le_twice d.pos hab
        ((by
          exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2 : (d : ℝ) ≤ N).trans
              hlevel)
    _ = 2 * ((b : ℝ) - a) * ∑ d ∈ S, (rootCount P.radical d : ℝ) / d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ 2 * ((b : ℝ) - a) *
        (smoothDivisorBound P.total.natDegree P.badDiscriminant s * T ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hdensity (by positivity)
    _ = _ := by ring

/-- The least common multiple of the coordinates controls their weighted
mass with exponent at most the total polynomial degree. -/
theorem PolynomialSystem.weightedMass_le_tupleLCM_pow {k r : ℕ} (P : PolynomialSystem k r)
    (m : Tuple r) : weightedMass P.exponent m ≤ tupleLCM m ^ P.total.natDegree := by
  calc
    _ ≤ ∏ i, tupleLCM m ^ totalExponent P.exponent i := by
      apply Finset.prod_le_prod
      intro i _
      exact Nat.pow_le_pow_left (Nat.le_of_dvd (tupleLCM_pos m) (coordinate_dvd_tupleLCM m i)) _
    _ = tupleLCM m ^ (∑ i, totalExponent P.exponent i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := Nat.pow_le_pow_right (tupleLCM_pos m) P.sum_totalExponent_le_degree

/-- A large smooth divisor tuple gives a single large smooth divisor of the
radical value, even when its coordinates have common prime factors. -/
theorem PolynomialSystem.mem_smoothDivisorExceptionalSet_of_tuple {k r : ℕ}
    (P : PolynomialSystem k r) (s : Finset ℕ) (N : ℕ+) {T : ℝ}
    {a b t : ℤ} (ht : t ∈ Finset.Ioc a b) (m : Tuple r)
    (hdiv : ∀ i, (m i : ℤ) ∣ (P.R i).eval t)
    (hsmooth : weightedMass P.exponent m ∈ Nat.factoredNumbers s)
    (hlarge : T ^ P.total.natDegree < (weightedMass P.exponent m : ℝ))
    (hsmall : weightedMass P.exponent m ≤ N) :
    t ∈ smoothDivisorExceptionalSet P.radical s N T a b := by
  have hdvd : tupleLCM m ∣ weightedMass P.exponent m :=
    (tupleLCM_dvd_mass m).trans (mass_dvd_weightedMass P.exponent P.exponent_pos m)
  have hbig : T < (tupleLCM m : ℝ) := by
    by_contra! h
    have H := pow_le_pow_left₀ (Nat.cast_nonneg _) h P.total.natDegree
    have H' : (weightedMass P.exponent m : ℝ) ≤ (tupleLCM m : ℝ) ^ P.total.natDegree := by
      exact_mod_cast P.weightedMass_le_tupleLCM_pow m
    linarith
  refine Finset.mem_filter.mpr ⟨ht, ⟨tupleLCM m, tupleLCM_pos m⟩, ?_, P.tupleLCM_dvd_radical_eval
      m t hdiv⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨one_le,
    (Nat.le_of_dvd (weightedMass_pos P.exponent m) hdvd).trans hsmall⟩,
      Nat.mem_factoredNumbers_of_dvd hsmooth hdvd, hbig⟩

end NairTenenbaum
