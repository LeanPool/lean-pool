/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeThreshold
public import LeanPool.NairTenenbaum.Sieve.SmallDivisorSum

/-! # Growth of arithmetic weights on rough remaining factors -/

@[expose] public section

namespace NairTenenbaum

/-- A rough integer has at most `log n / log z` prime factors, counted with
multiplicity. The power form also covers `n=1`. -/
theorem rough_pow_bigOmega_le {n : ℕ} (hn : n ≠ 0) {z : ℝ} (hz : 0 ≤ z)
    (hrough : ∀ p ∈ n.primeFactors, z ≤ (p : ℝ)) : z ^ bigOmega n ≤ (n : ℝ) := by
  have H : ∀ l : List ℕ, (∀ p ∈ l, z ≤ (p : ℝ)) → z ^ l.length ≤ (l.prod : ℝ) := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      intro hl
      simpa only [List.length_cons, List.prod_cons, Nat.cast_mul, pow_succ, mul_comm] using
        mul_le_mul (hl p (by simp)) (ih (fun q hq => hl q (by simp [hq])))
          (pow_nonneg hz _) (Nat.cast_nonneg p)
  simpa only [bigOmega, Nat.prod_primeFactorsList hn] using
    H n.primeFactorsList (fun p hp => hrough p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr
        hp))

theorem rough_bigOmega_le {n : ℕ} (hn : n ≠ 0) {z : ℝ} (hz : 1 < z)
    (hrough : ∀ p ∈ n.primeFactors, z ≤ (p : ℝ)) :
    (bigOmega n : ℝ) ≤ Real.log n / Real.log z := by
  apply (le_div_iff₀ (Real.log_pos hz)).mpr
  have H := Real.log_le_log (pow_pos (by linarith : 0 < z) _)
    (rough_pow_bigOmega_le hn (by linarith) hrough)
  simpa only [Real.log_pow] using H

/-- With a power cutoff and a power bound on the integer, the number of
remaining prime factors is uniformly bounded. -/
theorem rough_bigOmega_le_of_power {n : ℕ} (hn : n ≠ 0) {x α c : ℝ}
    (hx : 1 < x) (hα : 0 < α) (hnx : (n : ℝ) ≤ x ^ c)
    (hrough : ∀ p ∈ n.primeFactors, x ^ α ≤ (p : ℝ)) :
    (bigOmega n : ℝ) ≤ c / α := by
  have hz : 1 < x ^ α := Real.one_lt_rpow hx hα
  have H := rough_bigOmega_le hn hz hrough
  have hlog := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ) < n) hnx
  rw [Real.log_rpow (by linarith : 0 < x)] at H hlog
  apply (le_div_iff₀ hα).mpr
  have H' := (le_div_iff₀ (mul_pos hα (Real.log_pos hx))).mp H
  exact (mul_le_mul_iff_right₀ (Real.log_pos hx)).mp (by nlinarith)

theorem prime_dvd_weightedMass_iff {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (n : Tuple r) {p : ℕ} (hp : p.Prime) :
    p ∣ weightedMass γ n ↔ p ∣ mass n := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff
      (fun i => (n i : ℕ) ^ totalExponent γ i)).mp h
    exact (hp.dvd_of_dvd_pow hi).trans (coordinate_dvd_mass n i)
  · exact fun h => h.trans (mass_dvd_weightedMass γ hγ n)

/-- Selecting all primes below `q` leaves a rough weighted mass. -/
theorem primeReject_weightedMass_rough {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (n : Tuple r) (q : ℕ) :
    ∀ p ∈ (weightedMass γ (primeReject n (Finset.range q))).primeFactors, q ≤ p := by
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hd := (prime_dvd_weightedMass_iff γ hγ _ hp').mp (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨i, _, hi⟩ := (hp'.prime.dvd_finsetProd_iff
    (fun i => (primeReject n (Finset.range q) i : ℕ))).mp hd
  exact primeReject_range_prime_ge n q i
    (Nat.mem_primeFactors.mpr ⟨hp', hi, (primeReject n (Finset.range q) i).ne_zero⟩)

/-- Equation (29) with the remaining rough factor bounded by a constant. -/
theorem Admissible.pullback_primeSplit_le_of_rough {k r : ℕ} {A B σ : ℝ}
    {F : ArithmeticMap k} (hF : Admissible A B σ F) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (n : Tuple r) (q : ℕ) {x α c : ℝ} (hx : 1 < x) (hα : 0 < α)
    (hq : x ^ α ≤ (q : ℝ)) (hnx : (weightedMass γ n : ℝ) ≤ x ^ c) :
    pullback γ F n ≤ A ^ (c / α) * pullback γ F (primeSelect n (Finset.range q)) := by
  let v := primeReject n (Finset.range q)
  have hv : weightedMass γ v ≤ weightedMass γ n := by
    have H := Nat.le_mul_of_pos_left (weightedMass γ v)
      (weightedMass_pos γ (primeSelect n (Finset.range q)))
    simpa only [v, ← weightedMass_mul, primeSelect_mul_primeReject] using H
  have hΩ := rough_bigOmega_le_of_power (weightedMass_pos γ v).ne' hx hα
    ((by exact_mod_cast hv : (weightedMass γ v : ℝ) ≤ weightedMass γ n).trans hnx)
    (fun p hp => hq.trans (by exact_mod_cast primeReject_weightedMass_rough γ hγ n q p hp))
  have hG := (hF.pullback_minimalMajorant_le_growth (zero_le_one.trans hA) hB γ v).trans
      (min_le_left _ _)
  have hpow : A ^ bigOmega (weightedMass γ v) ≤ A ^ (c / α) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hA hΩ
  have H := (hF.pullback_primeSplit_le (zero_le_one.trans hA) hB γ n (Finset.range q)).trans
    (mul_le_mul_of_nonneg_left (hG.trans hpow) (hF.nonneg _))
  simpa only [mul_comm] using H

end NairTenenbaum
