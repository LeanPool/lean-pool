/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.TotientProducts
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentEuler
public import LeanPool.NairTenenbaum.Sieve.SievePrimes

/-! # The conditional sieve for prime arguments

We sieve `Q(t) * t`, omitting primes dividing the congruence modulus or
`(g+1)!`. The latter omission removes every possible fixed prime of the
enlarged polynomial, at a cost depending only on the original degree bound.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- The sieve modulus for the total polynomial times `X`, omitting obstructed primes. -/
noncomputable def primeArgumentSieveModulus (Q : ℤ[X]) (g n : ℕ) (z : ℝ) : ℕ :=
  sieveModulus (Q * X) (n * (g + 1).factorial) z

theorem primeArgumentSieveModulus_squarefree (Q : ℤ[X]) (g n : ℕ) (z : ℝ) :
    Squarefree (primeArgumentSieveModulus Q g n z) :=
  sieveModulus_squarefree _ _ _

theorem primeArgumentSieveModulus_coprime (Q : ℤ[X]) (g n : ℕ) (z : ℝ) :
    (primeArgumentSieveModulus Q g n z).Coprime n :=
  (sieveModulus_coprime (Q * X) (n * (g + 1).factorial) z).of_dvd_right
    (dvd_mul_right _ _)

theorem primeArgumentSieveModulus_large_prime (Q : ℤ[X]) (g n : ℕ) (z : ℝ)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ primeArgumentSieveModulus Q g n z) :
    g + 1 < p := by
  have H := sieveModulus_coprime (Q * X) (n * (g + 1).factorial) z
  have hnot : ¬p ∣ n * (g + 1).factorial := hp.coprime_iff_not_dvd.mp (H.of_dvd_left hd)
  by_contra h
  exact hnot (dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos (by omega)) n)

/-- The small-prime exclusion makes the enlarged polynomial admissible at
every selected prime; it requires no global admissibility of `Q * X`. -/
theorem primeArgumentSieveModulus_root_lt {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {g : ℕ} (hdeg : Q.natDegree ≤ g) (n : ℕ) (z : ℝ)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ primeArgumentSieveModulus Q g n z) :
    rootCount (Q * X) p < p :=
  rootCount_mul_X_prime_lt hQ hp
    ((Nat.add_le_add_right hdeg 1).trans_lt (primeArgumentSieveModulus_large_prime Q g n z hp hd))

/-- Every prime argument above the sieve cutoff survives the sieve of `X`. -/
theorem primeArgumentSieveModulus_coprime_prime (Q : ℤ[X]) (g n : ℕ)
    {z : ℝ} (hz : 0 ≤ z) {t : ℕ} (ht : t.Prime) (hzt : z < t) :
    (primeArgumentSieveModulus Q g n z).Coprime t := by
  apply Nat.coprime_comm.mpr
  apply ht.coprime_iff_not_dvd.mpr
  intro hd
  have hmem := Nat.mem_primeFactors.mpr
    ⟨ht, hd, (primeArgumentSieveModulus_squarefree Q g n z).ne_zero⟩
  exact (not_le_of_gt hzt) (sieveModulus_prime_le (Q * X) (n * (g + 1).factorial) hz hmem)

/-- Passing from the original sieve to the enlarged sieve removes constraints
on `Q(t)` only. A prime with zero root count cannot divide a polynomial value. -/
theorem primeArgumentSieveModulus_coprime_value (Q : ℤ[X]) (g n : ℕ)
    {z : ℝ} (hz : 0 ≤ z) (t : ℤ)
    (hsift : (sieveModulus Q n z).Coprime (Q.eval t).natAbs) :
    (primeArgumentSieveModulus Q g n z).Coprime (Q.eval t).natAbs := by
  apply Nat.coprime_of_dvd
  intro p hp hpM hpQ
  have hmem := Nat.mem_primeFactors.mpr
    ⟨hp, hpM, (primeArgumentSieveModulus_squarefree Q g n z).ne_zero⟩
  have hple := sieveModulus_prime_le (Q * X) (n * (g + 1).factorial) hz hmem
  have hpn : ¬p ∣ n := hp.coprime_iff_not_dvd.mp
    ((primeArgumentSieveModulus_coprime Q g n z).of_dvd_left hpM)
  have hroot : 0 < rootCount Q p := by
    let : NeZero p := ⟨hp.ne_zero⟩
    rw [← residueRootSet_card]
    apply card_pos.mpr
    exact ⟨(t : ZMod p), (cast_mem_residueRootSet Q p t).mpr (Int.natCast_dvd.mpr hpQ)⟩
  have hmem' : p ∈ (sieveModulus Q n z).primeFactors := by
    rw [sieveModulus_primeFactors]
    exact mem_filter.mpr ⟨mem_filter.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hz).mpr hple)), hp⟩,
      hpn, hroot.ne'⟩
  exact hp.not_dvd_one (by
    simpa only [hsift.gcd_eq_one] using Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hmem') hpQ)

/-- The original roughness condition and primality together imply the
enlarged sieve condition used in the conditional estimate. -/
theorem primeArgumentSieveModulus_coprime_mul_X (Q : ℤ[X]) (g n : ℕ)
    {z : ℝ} (hz : 0 ≤ z) (t : ℤ) (ht : t.natAbs.Prime) (hzt : z < t.natAbs)
    (hsift : (sieveModulus Q n z).Coprime (Q.eval t).natAbs) :
    (primeArgumentSieveModulus Q g n z).Coprime ((Q * X).eval t).natAbs := by
  rw [Polynomial.eval_mul, Polynomial.eval_X, Int.natAbs_mul]
  exact (primeArgumentSieveModulus_coprime_value Q g n hz t hsift).mul_right
    (primeArgumentSieveModulus_coprime_prime Q g n hz ht hzt)

/-- The degree-dependent constant in the prime-argument Euler-product comparison. -/
noncomputable def primeArgumentEulerConstant (g : ℕ) : ℝ :=
  omittedEulerBound g * totientTwist (g + 1) (g + 1).factorial

theorem primeArgumentEulerConstant_pos (g : ℕ) : 0 < primeArgumentEulerConstant g := by
  apply mul_pos (omittedEulerBound_pos g)
  exact lt_of_lt_of_le zero_lt_one (totientTwist_one_le _ (Nat.factorial_ne_zero _))

/-- The conditional prime-argument sieve retains the original polynomial's
Euler product and costs one additional totient twist on the prefix modulus. -/
theorem primeArgumentSieveModulus_euler_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hzero : Q.eval 0 ≠ 0) {g n : ℕ} (hdeg : Q.natDegree ≤ g) (hn : n ≠ 0)
    {z : ℝ} (hz : 1 < z) :
    (∏ p ∈ (primeArgumentSieveModulus Q g n z).primeFactors,
      (1 - (rootCount (Q * X) p : ℝ) / p)) ≤
      primeArgumentEulerConstant g * sieveProduct Q z *
        totientTwist 1 (Q.eval 0).natAbs * totientTwist (g + 1) n / Real.log z := by
  let m := n * (g + 1).factorial
  have hm : m ≠ 0 := mul_ne_zero hn (Nat.factorial_ne_zero _)
  have hq : (Q.eval 0).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hzero
  have hlog : 0 < Real.log z := Real.log_pos hz
  have hQprod : progressionSieveProduct Q m z ≤
      omittedEulerBound g * sieveProduct Q z * totientTwist g m := by
    simpa only [sievePrimeSet_euler_eq, progressionSieveProduct] using
      sievePrimeSet_euler_le hQ hdeg hm z
  have hXprod : progressionSieveProduct X (m * (Q.eval 0).natAbs) z ≤
      (totientTwist 1 m * totientTwist 1 (Q.eval 0).natAbs) / Real.log z := by
    have H := progressionSieveProduct_X_le_inv_log (mul_ne_zero hm hq) hz
    have H' : progressionSieveProduct X (m * (Q.eval 0).natAbs) z ≤
        totientTwist 1 (m * (Q.eval 0).natAbs) / Real.log z := by
      simpa only [totientTwist, pow_one] using H
    exact H'.trans (div_le_div_of_nonneg_right (totientTwist_mul_le 1 hm hq) hlog.le)
  have hXnonneg : 0 ≤ progressionSieveProduct (X : ℤ[X]) (m * (Q.eval 0).natAbs) z := by
    unfold progressionSieveProduct
    apply prod_nonneg
    intro p hp
    have hp' := (mem_filter.mp (mem_filter.mp hp).1).2
    rw [rootCount_X, Nat.cast_one]
    exact sub_nonneg.mpr ((div_le_one (by exact_mod_cast hp'.pos)).mpr
      (by exact_mod_cast hp'.one_le))
  have hQnonneg : 0 ≤ omittedEulerBound g * sieveProduct Q z * totientTwist g m :=
    mul_nonneg (mul_nonneg (omittedEulerBound_pos g).le (sieveProduct_pos hQ z).le)
      (totientTwist_nonneg g m)
  have htwist : totientTwist g m * totientTwist 1 m = totientTwist (g + 1) m := by
    simp [totientTwist, pow_succ]
  calc
    _ = progressionSieveProduct (Q * X) m z := by
      rw [primeArgumentSieveModulus, sieveModulus_primeFactors, sievePrimeSet_euler_eq]
      rfl
    _ ≤ progressionSieveProduct Q m z *
        progressionSieveProduct X (m * (Q.eval 0).natAbs) z :=
      progressionSieveProduct_mul_X_le Q m z
    _ ≤ (omittedEulerBound g * sieveProduct Q z * totientTwist g m) *
        ((totientTwist 1 m * totientTwist 1 (Q.eval 0).natAbs) / Real.log z) :=
      mul_le_mul hQprod hXprod hXnonneg hQnonneg
    _ = (omittedEulerBound g * sieveProduct Q z * totientTwist 1 (Q.eval 0).natAbs /
        Real.log z) * totientTwist (g + 1) m := by rw [← htwist]; ring
    _ ≤ (omittedEulerBound g * sieveProduct Q z * totientTwist 1 (Q.eval 0).natAbs /
        Real.log z) * (totientTwist (g + 1) n * totientTwist (g + 1) (g + 1).factorial) :=
      mul_le_mul_of_nonneg_left (totientTwist_mul_le _ hn (Nat.factorial_ne_zero _))
        (div_nonneg (mul_nonneg (mul_nonneg (omittedEulerBound_pos g).le
          (sieveProduct_pos hQ z).le) (totientTwist_nonneg _ _)) hlog.le)
    _ = _ := by unfold primeArgumentEulerConstant; ring

/-- The restored conditional estimate for sieving prime arguments. The
constant depends only on the original degree bound and the sieve slack.
Congruence densities, the totient correction at `Q(0)`, and the logarithmic
saving all remain explicit. -/
theorem exists_primeArgument_conditional_sieve_bound (g : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → Q.eval 0 ≠ 0 →
      Q.natDegree ≤ g → ∀ (r : ℕ) (R : Fin r → ℤ[X]) (m : Tuple r),
      (Pairwise fun i j => Nat.Coprime (m i) (m j)) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      (conditionalPolynomialSiftedCount (Q * X)
        (primeArgumentSieveModulus Q g (mass m) z) R m a b : ℝ) ≤
        K * (((b : ℝ) - a) * sieveProduct Q z * totientTwist 1 (Q.eval 0).natAbs *
          totientTwist (g + 1) (mass m) / Real.log z *
          (∏ i, ((rootCount (R i) (m i) : ℝ) / m i)) +
          (∏ i, (rootCount (R i) (m i) : ℝ)) * z ^ (4 * ((g : ℝ) + 1) * (1 + η))) := by
  obtain ⟨K, hK, H⟩ := exists_local_conditional_polynomial_sieve_bound
    (g := (g : ℝ) + 1) (by have := (Nat.cast_nonneg g : (0 : ℝ) ≤ g); linarith) hη
  let C := 4 * primeArgumentEulerConstant g + K
  have hKC : K ≤ C := by dsimp [C]; linarith [primeArgumentEulerConstant_pos g]
  have hBC : 4 * primeArgumentEulerConstant g ≤ C := by dsimp [C]; linarith
  refine ⟨C, hK.trans hKC, ?_⟩
  intro Q hQ hzero hdeg r R m hpair a b z hab hz hzlog
  let P := primeArgumentSieveModulus Q g (mass m) z
  let D : ℝ := ∏ i, ((rootCount (R i) (m i) : ℝ) / m i)
  let E : ℝ := (∏ i, (rootCount (R i) (m i) : ℝ)) *
    z ^ (4 * ((g : ℝ) + 1) * (1 + η))
  let M : ℝ := ((b : ℝ) - a) * sieveProduct Q z * totientTwist 1 (Q.eval 0).natAbs *
    totientTwist (g + 1) (mass m) / Real.log z * D
  have hD : 0 ≤ D := prod_nonneg (fun _ _ => by positivity)
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hE : 0 ≤ E := mul_nonneg (prod_nonneg (fun _ _ => Nat.cast_nonneg _))
    (Real.rpow_nonneg (by linarith) _)
  have hM : 0 ≤ M := mul_nonneg (div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hL (sieveProduct_pos hQ z).le)
      (totientTwist_nonneg _ _)) (totientTwist_nonneg _ _)) (by linarith)) hD
  have Hcount := H (Q * X) P (primeArgumentSieveModulus_squarefree Q g (mass m) z)
    (fun p hp hd => primeArgumentSieveModulus_root_lt hQ hdeg (mass m) z hp hd)
    (fun p hp _ => by
      have Hr := (rootCount_mul_X_prime_le_degree_add_one hQ hp).trans
        (Nat.add_le_add_right hdeg 1)
      exact_mod_cast Hr)
    (fun p hp hd => sieveModulus_root_pos (Q * X) ((mass m) * (g + 1).factorial) z hp hd)
    r R m hpair (primeArgumentSieveModulus_coprime Q g (mass m) z) a b z hab hz hzlog
    (fun p hp => sieveModulus_prime_le (Q * X) ((mass m) * (g + 1).factorial)
      (by linarith) hp)
  have Heuler := primeArgumentSieveModulus_euler_le hQ hzero hdeg (mass_pos m).ne'
    (show 1 < z by linarith)
  have Hmain : 4 * ((b : ℝ) - a) * D *
      (∏ p ∈ P.primeFactors, (1 - (rootCount (Q * X) p : ℝ) / p)) ≤
      (4 * primeArgumentEulerConstant g) * M := by
    have H' := mul_le_mul_of_nonneg_left Heuler
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hL) hD)
    convert H' using 1
    dsimp [P, M]
    ring
  change (conditionalPolynomialSiftedCount (Q * X) P R m a b : ℝ) ≤ C * (M + E)
  calc
    _ ≤ 4 * ((b : ℝ) - a) * D *
        (∏ p ∈ P.primeFactors, (1 - (rootCount (Q * X) p : ℝ) / p)) + K * E := by
      simpa only [D, E, mul_assoc] using Hcount
    _ ≤ (4 * primeArgumentEulerConstant g) * M + K * E := add_le_add Hmain le_rfl
    _ ≤ C * M + C * E := add_le_add (mul_le_mul_of_nonneg_right hBC hM)
      (mul_le_mul_of_nonneg_right hKC hE)
    _ = _ := by ring

end NairTenenbaum
