/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.FractionalAuxiliary
public import LeanPool.NairTenenbaum.Polynomials.DiscriminantSplitting

/-! # Least common multiples and bad-prime mass

Coordinates supported at bad primes need not be coprime. Their simultaneous
congruence conditions have least common multiple as modulus. The product of
fractional auxiliary series bounds the associated mass uniformly.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The least common multiple of the coordinates of a positive integer tuple. -/
def tupleLCM {r : ℕ} (n : Tuple r) : ℕ := Finset.univ.lcm (fun i => (n i : ℕ))

theorem tupleLCM_pos {r : ℕ} (n : Tuple r) : 0 < tupleLCM n :=
  Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun i _ => (n i).ne_zero))

theorem coordinate_dvd_tupleLCM {r : ℕ} (n : Tuple r) (i : Fin r) : (n i : ℕ) ∣ tupleLCM n :=
  Finset.dvd_lcm (Finset.mem_univ i)

theorem tupleLCM_dvd_mass {r : ℕ} (n : Tuple r) : tupleLCM n ∣ mass n :=
  Finset.lcm_dvd (fun i _ => coordinate_dvd_mass n i)

theorem mass_le_tupleLCM_pow {r G : ℕ} (n : Tuple r) (hr : r ≤ G) : mass n ≤ tupleLCM n ^ G := by
  have hd : mass n ∣ tupleLCM n ^ r := by
    have H := Finset.prod_dvd_prod_of_dvd (fun i => (n i : ℕ)) (fun _ => tupleLCM n) (fun i (_ : i
        ∈ (Finset.univ : Finset (Fin r))) =>
      coordinate_dvd_tupleLCM n i)
    simpa only [mass, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using H
  exact (Nat.le_of_dvd (pow_pos (tupleLCM_pos n) _) hd).trans
    (Nat.pow_le_pow_right (Nat.succ_le_iff.mpr (tupleLCM_pos n)) hr)

theorem mass_rpow_le_tupleLCM {r G : ℕ} (n : Tuple r) (hG : 0 < G) (hr : r ≤ G) :
    (mass n : ℝ) ^ (1 / (G : ℝ)) ≤ tupleLCM n := by
  rw [one_div]
  apply (Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by exact_mod_cast hG)).mpr
  rw [Real.rpow_natCast]
  exact_mod_cast mass_le_tupleLCM_pow n hr

theorem tupleLCM_mem_factoredNumbers {r : ℕ} (n : Tuple r) (s : Finset ℕ)
    (hn : ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers s) : tupleLCM n ∈ Nat.factoredNumbers s := by
  have H := (weightedMass_mem_factoredNumbers_iff (identityExponents r) (by
    intro i; simp) n s).mpr hn
  rw [weightedMass_identity] at H
  exact Nat.mem_factoredNumbers_of_dvd H (tupleLCM_dvd_mass n)

/-- The least-common-multiple density is bounded by a product of fractional
coordinate densities. No pairwise coprimality is assumed. -/
theorem auxiliary_prod_div_tupleLCM_le {r G : ℕ} {A B ε : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (η : Fin r → ℕ) (n : Tuple r) (hG : 0 < G) (hr : r ≤ G) :
    (∏ i, auxiliary A B ε (η i) (n i)) / (tupleLCM n : ℝ) ≤
      ∏ i, fractionalAuxiliary A B ε (1 / (G : ℝ)) (η i) (n i) := by
  have hpow : 0 < (mass n : ℝ) ^ (1 / (G : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast mass_pos n) _
  calc
    _ ≤ (∏ i, auxiliary A B ε (η i) (n i)) / (mass n : ℝ) ^ (1 / (G : ℝ)) :=
      div_le_div_of_nonneg_left (Finset.prod_nonneg (fun _i _ => auxiliary_nonneg hA hB _ _))
        hpow (mass_rpow_le_tupleLCM n hG hr)
    _ = _ := by
      simp only [fractionalAuxiliary, Finset.prod_div_distrib, mass, Nat.cast_prod]
      rw [← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]

/-- A uniform local prime-power root bound gives a bound on every integer
supported by the same finite set of primes. -/
theorem rootCount_factored_le (Q : ℤ[X]) (s : Finset ℕ) (C : ℕ) (hC : 1 ≤ C)
    (hρ : ∀ p ∈ s, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) {n : ℕ}
    (hn : n ∈ Nat.factoredNumbers s) : rootCount Q n ≤ C ^ (s.filter Nat.Prime).card := by
  have heq := Nat.multiplicative_factorization (rootCount Q)
    (fun _ _ h => rootCount_mul Q h) (rootCount_one Q) hn.1
  rw [heq]
  simp only [Finsupp.prod, Nat.support_factorization]
  calc
    _ ≤ ∏ _p ∈ n.primeFactors, C := by
      apply Finset.prod_le_prod
      intro p hp
      exact hρ p (Nat.primeFactors_subset_of_mem_factoredNumbers hn hp)
        (Nat.prime_of_mem_primeFactors hp) _
    _ = C ^ n.primeFactors.card := by rw [Finset.prod_const]
    _ ≤ _ := Nat.pow_le_pow_right hC (Finset.card_le_card (fun p hp =>
      Finset.mem_filter.mpr ⟨Nat.primeFactors_subset_of_mem_factoredNumbers hn hp,
        Nat.prime_of_mem_primeFactors hp⟩))

/-- The radical's root count on a bad-prime-supported modulus is bounded
solely by the restricted discriminant. -/
theorem PolynomialSystem.radical_rootCount_bad_supported {k r : ℕ} (P : PolynomialSystem k r)
    {n : ℕ} (hn : n ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) :
    rootCount P.radical n ≤ (P.badDiscriminant ^ 3) ^ P.badDiscriminant.primeFactors.card := by
  have H := rootCount_factored_le P.radical P.badDiscriminant.primeFactors (P.badDiscriminant ^ 3)
    (Nat.succ_le_iff.mpr (pow_pos P.badDiscriminant_pos _))
    (fun p hp hprime ν => P.radical_rootCount_prime_pow_le_bad_cube hprime
      (Nat.dvd_of_mem_primeFactors hp) ν) hn
  simpa only [Finset.filter_eq_self.mpr (fun _ hp => Nat.prime_of_mem_primeFactors hp)] using H

/-- Sum a product of fractional auxiliary weights over any supported finite
set of tuples, using a common geometric exponent gap. -/
theorem sum_prod_fractionalAuxiliary_le {r G : ℕ} {A B ε σ : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hσ : σ < 0) (hr : r ≤ G)
    (η : Fin r → ℕ) (θ : Fin r → ℝ) (hη : ∀ i, (η i : ℝ) * ε - θ i ≤ σ)
    (s : Finset ℕ) (S : Finset (Tuple r)) (N : ℕ+)
    (hbox : ∀ n ∈ S, ∀ i, n i ≤ N) (hs : ∀ n ∈ S, ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers s) :
    (∑ n ∈ S, ∏ i, fractionalAuxiliary A B ε (θ i) (η i) (n i)) ≤
      (B / (1 - (2 : ℝ) ^ σ)) ^ (G * (s.filter Nat.Prime).card) := by
  classical
  let T := (Finset.Icc 1 N).filter (fun n : ℕ+ => (n : ℕ) ∈ Nat.factoredNumbers s)
  let U := fun i (n : ℕ+) => fractionalAuxiliary A B ε (θ i) (η i) n
  let K := B / (1 - (2 : ℝ) ^ σ)
  have hU : ∀ i n, 0 ≤ U i n := fun i n => fractionalAuxiliary_nonneg hA (zero_le_one.trans hB) _ _
  have hK : 1 ≤ K := by
    apply (le_div_iff₀ (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hσ))).mpr
    have : 0 ≤ (2 : ℝ) ^ σ := by positivity
    linarith
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin r => T) := by
    intro n hn
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨one_le, hbox n hn i⟩, hs n hn i⟩)
  calc
    _ ≤ ∑ n ∈ Fintype.piFinset (fun _ : Fin r => T), ∏ i, U i (n i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => Finset.prod_nonneg (fun i _ => hU i
          _))
    _ = ∏ i, ∑ n ∈ T, U i n := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : Fin r, K ^ (s.filter Nat.Prime).card := by
      apply Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun n _ => hU i n))
      intro i _
      exact fractionalAuxiliary_sum_le hA hB hε hσ (η i) (hη i) s T
        (fun n hn => (Finset.mem_filter.mp hn).2)
    _ = K ^ (r * (s.filter Nat.Prime).card) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm]
    _ ≤ _ := pow_le_pow_right₀ hK (Nat.mul_le_mul_right _ hr)


/-- A finite sum over arbitrary bad-prime tuples is bounded independently of
its coordinate cutoff. -/
theorem auxiliary_tupleLCM_sum_le {r G : ℕ} {A B ε σ : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hσ : σ < 0) (hG : 0 < G) (hr : r ≤ G)
    (η : Fin r → ℕ) (hη : ∀ i, (η i : ℝ) * ε - 1 / (G : ℝ) ≤ σ)
    (s : Finset ℕ) (S : Finset (Tuple r)) (N : ℕ+)
    (hbox : ∀ n ∈ S, ∀ i, n i ≤ N) (hs : ∀ n ∈ S, ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers s) :
    (∑ n ∈ S, (∏ i, auxiliary A B ε (η i) (n i)) / (tupleLCM n : ℝ)) ≤
      (B / (1 - (2 : ℝ) ^ σ)) ^ (G * (s.filter Nat.Prime).card) := by
  exact (Finset.sum_le_sum (fun n _ =>
    auxiliary_prod_div_tupleLCM_le hA (zero_le_one.trans hB) η n hG hr)).trans
      (sum_prod_fractionalAuxiliary_le hA hB hε hσ hr η (fun _ => 1 / (G : ℝ))
        hη s S N hbox hs)

/-- The cost of a bad-prime tuple, retaining a congruence density for its
least common multiple instead of discarding the removed congruences. -/
noncomputable def badPrimeTupleKernel {r : ℕ} (A B ε : ℝ) (η : Fin r → ℕ)
    (Q : ℤ[X]) (n : Tuple r) : ℝ :=
  (∏ i, auxiliary A B ε (η i) (n i)) * rootCount Q (tupleLCM n) / (tupleLCM n : ℝ)

theorem badPrimeTupleKernel_nonneg {r : ℕ} {A B ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (η : Fin r → ℕ) (Q : ℤ[X]) (n : Tuple r) : 0 ≤ badPrimeTupleKernel A B ε η Q n :=
  div_nonneg (mul_nonneg (Finset.prod_nonneg (fun _i _ => auxiliary_nonneg hA hB _ _))
    (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- Uniform bound for the total mass of the bad-prime kernel. -/
noncomputable def badPrimeMassBound (B : ℝ) (g D : ℕ) : ℝ :=
  ((D ^ 3) ^ D.primeFactors.card : ℕ) *
    (B / (1 - (2 : ℝ) ^ (-7 / (8 * (g : ℝ))))) ^ (g * D.primeFactors.card)

theorem badPrimeMassBound_pos {B : ℝ} (hB : 0 < B) {g D : ℕ} (hg : 0 < g) (hD : 0 < D) :
    0 < badPrimeMassBound B g D := by
  have hσ : -7 / (8 * (g : ℝ)) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hd : 0 < 1 - (2 : ℝ) ^ (-7 / (8 * (g : ℝ))) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hσ)
  exact mul_pos (by exact_mod_cast pow_pos (pow_pos hD 3) D.primeFactors.card)
    (pow_pos (div_pos hB hd) _)

/-- The growth condition of Theorem 1 leaves a fixed geometric gap in the
bad-prime series, even when all coordinates have large valuations together. -/
theorem badPrime_exponent_gap {g η : ℕ} (hg : 0 < g) (hη : η ≤ g) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) :
    (η : ℝ) * ε - 1 / (g : ℝ) ≤ -7 / (8 * (g : ℝ)) := by
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have hge : (g : ℝ) * ε ≤ (1 / 8) / (g : ℝ) :=
    (le_div_iff₀ hg₀).mpr (by nlinarith)
  calc
    _ ≤ ((1 / 8) / (g : ℝ)) - 1 / (g : ℝ) :=
      sub_le_sub_right ((mul_le_mul_of_nonneg_right (by exact_mod_cast hη) hε).trans hge) _
    _ = _ := by ring

/-- All bad-prime valuations can be summed at a cost depending only on the
total degree, the growth constant `B`, and the restricted discriminant. -/
theorem PolynomialSystem.badPrimeTupleKernel_sum_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hg : 0 < P.total.natDegree)
    (hsmall : (P.total.natDegree : ℝ) ^ 2 * ε ≤ 1 / 8)
    (S : Finset (Tuple r)) (N : ℕ+) (hbox : ∀ n ∈ S, ∀ i, n i ≤ N)
    (hs : ∀ n ∈ S, ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) :
    (∑ n ∈ S, badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical n) ≤
      badPrimeMassBound B P.total.natDegree P.badDiscriminant := by
  let K : ℝ := ((P.badDiscriminant ^ 3) ^ P.badDiscriminant.primeFactors.card : ℕ)
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hσ : -7 / (8 * (P.total.natDegree : ℝ)) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have haux := auxiliary_tupleLCM_sum_le hA hB hε hσ hg P.factor_count_le_degree
    (totalExponent P.exponent)
    (fun i => badPrime_exponent_gap hg (P.totalExponent_le_degree i) hε.le hsmall)
    P.badDiscriminant.primeFactors S N hbox hs
  have hfilt : P.badDiscriminant.primeFactors.filter Nat.Prime = P.badDiscriminant.primeFactors :=
    Finset.filter_eq_self.mpr (fun _ hp => Nat.prime_of_mem_primeFactors hp)
  rw [hfilt] at haux
  calc
    _ ≤ ∑ n ∈ S, K * ((∏ i, auxiliary A B ε (totalExponent P.exponent i) (n i)) / (tupleLCM n :
        ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hρ : (rootCount P.radical (tupleLCM n) : ℝ) ≤ K := by
        dsimp only [K]
        exact_mod_cast P.radical_rootCount_bad_supported (tupleLCM_mem_factoredNumbers n _ (hs n
            hn))
      have H := mul_le_mul_of_nonneg_left hρ
        (div_nonneg (Finset.prod_nonneg (s := Finset.univ) (fun i _ => auxiliary_nonneg (ε := ε)
            hA (zero_le_one.trans hB) (totalExponent P.exponent i) (n i)))
          (Nat.cast_nonneg (tupleLCM n)))
      simpa only [badPrimeTupleKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using H
    _ = K * ∑ n ∈ S, (∏ i, auxiliary A B ε (totalExponent P.exponent i) (n i)) / (tupleLCM n : ℝ)
        := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left haux hK

end NairTenenbaum
