/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimePowerCounting
public import LeanPool.NairTenenbaum.Polynomials.PolynomialValueTuples

/-! # The second class lies in the large-prime-power exceptional set -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

theorem PolynomialSystem.mem_primePowerExceptionalSet_of_crossing {k r : ℕ}
    (P : PolynomialSystem k r) {a b t : ℤ} (ht : t ∈ Finset.Ioc a b)
    {n : Tuple r} (hn : ∀ i, (n i : ℕ) = ((P.R i).eval t).natAbs)
    {p : ℕ} (hp : p.Prime) {z T : ℝ} (hz : 0 ≤ z) (hpz : (p : ℝ) ≤ z) (hT : 1 ≤ T)
    (hsmall : (weightedMass P.exponent (primeSelect n (Finset.range p)) : ℝ) ≤ T ^
        P.total.natDegree)
    (hcross : (T ^ P.total.natDegree) ^ 2 <
      (weightedMass P.exponent (primeSelect n (Finset.range (p + 1))) : ℝ)) :
    t ∈ primePowerExceptionalSet P.R z T a b := by
  obtain ⟨i, hi⟩ := P.exists_large_primePower_of_crossing n hp hT hsmall hcross
  have hd : p ^ firstPowerAbove p T ∣ (n i : ℕ) :=
    firstPowerAbove_dvd hp.one_lt hi (Nat.ordProj_dvd _ _)
  apply Finset.mem_filter.mpr
  refine ⟨ht, p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (Nat.lt_succ_of_le ((Nat.le_floor_iff hz).mpr hpz)), hp⟩, i, ?_⟩
  rw [← Nat.cast_pow]
  exact Int.natCast_dvd.mpr (by simpa only [hn i] using hd)

/-- The root-count constant depends only on the total degree and restricted
bad discriminant. -/
theorem PolynomialSystem.primePowerExceptionalSet_card_le {k r : ℕ} (P : PolynomialSystem k r)
    {z T : ℝ} (hz : 1 ≤ z) (hT : 1 ≤ T) {a b : ℤ} (hab : a ≤ b)
    (hlevel : z * T ≤ (b : ℝ) - a) :
    ((primePowerExceptionalSet P.R z T a b).card : ℝ) ≤
      4 * ((b : ℝ) - a) * (P.total.natDegree : ℝ) *
        (max P.total.natDegree (P.badDiscriminant ^ 3) : ℕ) * z / T := by
  have H := NairTenenbaum.primePowerExceptionalSet_card_le P.R hz hT
    (Nat.cast_nonneg (max P.total.natDegree (P.badDiscriminant ^ 3)) : (0 : ℝ) ≤ _)
    (fun p hp i => by
      exact_mod_cast (P.factor_rootCount_prime_pow_uniform (Finset.mem_filter.mp hp).2 _ i).trans
        (max_le_max (Polynomial.natDegree_le_of_dvd (P.factor_dvd_total i) P.total_ne_zero)
            le_rfl)) hab hlevel
  apply H.trans
  apply div_le_div_of_nonneg_right _ (zero_le_one.trans hT)
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hz)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left (by exact_mod_cast P.factor_count_le_degree)
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  positivity

/-- The useful specialization `T=z³` produces a quadratic saving. -/
theorem PolynomialSystem.primePowerExceptionalSet_cube_card_le {k r : ℕ}
    (P : PolynomialSystem k r) {z : ℝ} (hz : 1 ≤ z) {a b : ℤ} (hab : a ≤ b)
    (hlevel : z ^ 4 ≤ (b : ℝ) - a) :
    ((primePowerExceptionalSet P.R z (z ^ 3) a b).card : ℝ) ≤
      4 * ((b : ℝ) - a) * (P.total.natDegree : ℝ) *
        (max P.total.natDegree (P.badDiscriminant ^ 3) : ℕ) / z ^ 2 := by
  have hz₀ : z ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hz)
  have H := P.primePowerExceptionalSet_card_le hz (one_le_pow₀ hz)
    hab (by nlinarith : z * z ^ 3 ≤ (b : ℝ) - a)
  convert H using 1
  field_simp

end NairTenenbaum
