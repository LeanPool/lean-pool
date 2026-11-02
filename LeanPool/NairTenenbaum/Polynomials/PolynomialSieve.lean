/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.CongruenceCount
public import LeanPool.NairTenenbaum.Sieve.SelbergRemainder

/-! # The Selberg upper bound for polynomial values in intervals -/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

/-- Polynomial congruence density as a multiplicative arithmetic function. -/
noncomputable def rootDensity (Q : ℤ[X]) : ArithmeticFunction ℝ :=
  ⟨fun d => (rootCount Q d : ℝ) / d, by simp⟩

theorem rootDensity_apply (Q : ℤ[X]) (d : ℕ) : rootDensity Q d = (rootCount Q d : ℝ) / d := rfl

theorem rootDensity_multiplicative (Q : ℤ[X]) : (rootDensity Q).IsMultiplicative := by
  refine ⟨by simp [rootDensity_apply], ?_⟩
  intro m n hmn
  simp only [rootDensity_apply, rootCount_mul Q hmn, Nat.cast_mul, mul_div_mul_comm]

theorem rootCount_squarefree {Q : ℤ[X]} {n : ℕ} (hn : Squarefree n) :
    rootCount Q n = ∏ p ∈ n.primeFactors, rootCount Q p := by
  rw [Nat.multiplicative_factorization (rootCount Q) (fun _ _ h => rootCount_mul Q h)
    (rootCount_one Q) hn.ne_zero]
  simp only [Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp), pow_one]

theorem rootCount_squarefree_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q) {g : ℝ}
    (hg : (Q.natDegree : ℝ) ≤ g) {n : ℕ} (hn : Squarefree n) :
    (rootCount Q n : ℝ) ≤ g ^ n.primeFactors.card := by
  rw [rootCount_squarefree hn, Nat.cast_prod, ← Finset.prod_const]
  apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
  intro p hp
  have H : (rootCount Q p : ℝ) ≤ Q.natDegree := by
    exact_mod_cast rootCount_le_degree hQ (Nat.prime_of_mem_primeFactors hp)
  exact H.trans hg

/-- Counting fibers transfers a finite set to natural-valued sieve support,
without assuming that the value map is injective. -/
theorem sum_fiber_card_filter {ι : Type*} (T : Finset ι) (f : ι → ℕ) (pred : ℕ → Prop)
    [DecidablePred pred] :
    (∑ d ∈ T.image f, if pred d then ((T.filter fun n => f n = d).card : ℝ) else 0) =
      ((T.filter fun n => pred (f n)).card : ℝ) := by
  classical
  rw [← Finset.sum_filter, ← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter]
  congr 2
  apply Finset.filter_congr
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_image_of_mem f hn, true_and]

/-- The Selberg bounding sieve attached to polynomial values on an interval. -/
noncomputable def polynomialBoundingSieve (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (a b : ℤ) : BoundingSieve where
  support := (Finset.Ioc a b).image (fun n => (Q.eval n).natAbs)
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun d => (((Finset.Ioc a b).filter fun n => (Q.eval n).natAbs = d).card : ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := (b : ℝ) - a
  nu := rootDensity Q
  nu_mult := rootDensity_multiplicative Q
  nu_pos_of_prime := fun p hp hd => div_pos (by
    exact_mod_cast hroot p hp hd) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := fun p hp _ => (div_lt_one (by
    exact_mod_cast hp.pos)).mpr (by exact_mod_cast hQ p hp)

theorem polynomialBoundingSieve_multSum (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (a b : ℤ) (d : ℕ) :
    (polynomialBoundingSieve Q hQ P hP hroot a b).multSum d = polynomialCongruenceCount Q d a b :=
        by
  change (∑ m ∈ (Finset.Ioc a b).image (fun n => (Q.eval n).natAbs),
    if d ∣ m then (((Finset.Ioc a b).filter fun n => (Q.eval n).natAbs = m).card : ℝ) else 0) = _
  rw [sum_fiber_card_filter]
  unfold polynomialCongruenceCount
  congr 2
  apply Finset.filter_congr
  intro n _
  exact Int.natCast_dvd.symm

theorem polynomialBoundingSieve_rem_le (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (a b : ℤ) (hab : a ≤ b) {d : ℕ} (hd : d ∣ P) :
    |(polynomialBoundingSieve Q hQ P hP hroot a b).rem d| ≤ rootCount Q d := by
  rw [BoundingSieve.rem, polynomialBoundingSieve_multSum]
  have H := polynomialCongruenceCount_error Q (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero
      hP.ne_zero hd)) a b hab
  convert H using 2
  change _ - ((rootCount Q d : ℝ) / d) * ((b : ℝ) - a) = _
  ring

/-- The number of polynomial values coprime to the sieve modulus. -/
noncomputable def polynomialSiftedCount (Q : ℤ[X]) (P : ℕ) (a b : ℤ) : ℕ :=
  ((Finset.Ioc a b).filter fun n => Nat.Coprime P (Q.eval n).natAbs).card

theorem polynomialBoundingSieve_siftedSum (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (a b : ℤ) :
    (polynomialBoundingSieve Q hQ P hP hroot a b).siftedSum = polynomialSiftedCount Q P a b := by
  exact sum_fiber_card_filter (Finset.Ioc a b) (fun n => (Q.eval n).natAbs) (Nat.Coprime P)

/-- A polynomial sieve bound with constants independent of the coefficients,
the interval, and the selected primes. Root-free primes can simply be omitted. -/
theorem exists_polynomial_sieve_bound {g η : ℝ} (hg : 1 ≤ g) (hη : 0 < η) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → (Q.natDegree : ℝ) ≤ g →
      ∀ (P : ℕ), Squarefree P → (∀ p, p.Prime → p ∣ P → 0 < rootCount Q p) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      (∀ p ∈ P.primeFactors, (p : ℝ) ≤ z) →
      (polynomialSiftedCount Q P a b : ℝ) ≤
        4 * ((b : ℝ) - a) * (∏ p ∈ P.primeFactors, (1 - (rootCount Q p : ℝ) / p)) +
          K * z ^ (4 * g * (1 + η)) := by
  obtain ⟨K, hK, H⟩ := exists_selberg_upper_bound hg hη
  refine ⟨K, hK, ?_⟩
  intro Q hQ hdeg P hP hroot a b z hab hz hzlog hprimes
  let s := polynomialBoundingSieve Q hQ P hP hroot a b
  have hdim (p : ℕ) (hp : p ∈ s.prodPrimes.primeFactors) : s.nu p ≤ g / p := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
    have H : (rootCount Q p : ℝ) ≤ Q.natDegree := by
      exact_mod_cast rootCount_le_degree hQ (Nat.prime_of_mem_primeFactors hp)
    exact H.trans hdeg
  have hgap (p : ℕ) (hp : p ∈ s.prodPrimes.primeFactors) : s.nu p ≤ 1 - 1 / (p : ℝ) := by
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have Hr : (rootCount Q p : ℝ) + 1 ≤ p := by
      exact_mod_cast hQ p (Nat.prime_of_mem_primeFactors hp)
    change (rootCount Q p : ℝ) / p ≤ _
    apply (div_le_iff₀ hp₀).mpr
    field_simp
    linarith
  have herr (d : ℕ) (hd : d ∣ s.prodPrimes) : |s.rem d| ≤ (1 : ℝ) * g ^ d.primeFactors.card := by
    rw [one_mul]
    exact (polynomialBoundingSieve_rem_le Q hQ P hP hroot a b hab hd).trans
      (rootCount_squarefree_le hQ hdeg (hP.squarefree_of_dvd hd))
  have HB := H s z 1 hz hzlog (by norm_num)
    (by change 0 ≤ (b : ℝ) - a; exact_mod_cast sub_nonneg.mpr hab)
    hprimes hdim hgap herr
  dsimp only [s] at HB
  rw [polynomialBoundingSieve_siftedSum] at HB
  simpa only [polynomialBoundingSieve, rootDensity_apply, one_mul] using HB

end NairTenenbaum
