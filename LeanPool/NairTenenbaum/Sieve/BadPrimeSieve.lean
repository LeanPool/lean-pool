/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.TotientProducts
public import LeanPool.NairTenenbaum.Sieve.BadPrimeCongruence
public import LeanPool.NairTenenbaum.Sieve.SieveLevel

/-! # The sieve estimate after full bad-prime removal

The removed coordinates are replaced by a radical congruence at their least
common multiple. Its full prime-power density is retained during summation.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

/-- The pairwise coprime moduli used after grouping the bad-prime tuple by its least common
multiple. -/
def badSieveModuli {r : ℕ} (u v : Tuple r) : Tuple (r + 1) :=
  Fin.cons ⟨tupleLCM u, tupleLCM_pos u⟩ v

@[simp] theorem badSieveModuli_zero {r : ℕ} (u v : Tuple r) :
    badSieveModuli u v 0 = ⟨tupleLCM u, tupleLCM_pos u⟩ := rfl

@[simp] theorem badSieveModuli_succ {r : ℕ} (u v : Tuple r) (i : Fin r) :
    badSieveModuli u v i.succ = v i := rfl

theorem mass_badSieveModuli {r : ℕ} (u v : Tuple r) :
    mass (badSieveModuli u v) = tupleLCM u * mass v := by
  simp only [mass, Fin.prod_univ_succ, badSieveModuli_zero, badSieveModuli_succ, PNat.mk_coe]

theorem badSieveModuli_pairwise {r D : ℕ} (u v : Tuple r) (hv : Dagger D v)
    (hu : ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers D.primeFactors) :
    Pairwise fun i j => Nat.Coprime (badSieveModuli u v i) (badSieveModuli u v j) := by
  have hcross (i : Fin r) : Nat.Coprime (tupleLCM u) (v i) :=
    factoredNumbers_coprime_of_coprime (tupleLCM_mem_factoredNumbers u _ hu) (hv.2 i).symm
  intro i j hij
  revert hij
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · exact fun h => (h rfl).elim
  · exact fun _ => hcross j
  · exact fun _ => (hcross i).symm
  · exact fun h => hv.1 i j (fun e => h (congrArg Fin.succ e))

theorem totientTwist_badSieveModuli_le {r D : ℕ} (g : ℕ) (u v : Tuple r) (hD : D ≠ 0)
    (hu : ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers D.primeFactors) :
    totientTwist g (mass (badSieveModuli u v)) ≤ totientTwist g D * ∏ i, totientTwist g (v i) := by
  rw [mass_badSieveModuli]
  have H := totientTwist_le_of_primeFactors_subset g (tupleLCM_pos u).ne' hD
    (Nat.primeFactors_subset_of_mem_factoredNumbers (tupleLCM_mem_factoredNumbers u _ hu))
  exact (totientTwist_mul_le g (tupleLCM_pos u).ne' (mass_pos v).ne').trans
    (mul_le_mul H (totientTwist_mass_le g v) (totientTwist_nonneg g (mass v)) (totientTwist_nonneg
        g D))

theorem PolynomialSystem.congruenceSet_subset_badSieve {k r : ℕ} (P : PolynomialSystem k r)
    (u v : Tuple r) (a b : ℤ) :
    polynomialCongruenceSet P.R (u * v) a b ⊆
      polynomialCongruenceSet (Fin.cons P.radical P.R) (badSieveModuli u v) a b := by
  intro n hn
  simp only [polynomialCongruenceSet, Finset.mem_filter] at hn ⊢
  obtain ⟨hn, hdiv⟩ := hn
  refine ⟨hn, ?_⟩
  have hu : ∀ i, (u i : ℤ) ∣ (P.R i).eval n := by
    intro i
    exact (dvd_mul_right (u i : ℤ) (v i : ℤ)).trans (by simpa using hdiv i)
  have hv : ∀ i, (v i : ℤ) ∣ (P.R i).eval n := by
    intro i
    exact (dvd_mul_left (v i : ℤ) (u i : ℤ)).trans (by simpa using hdiv i)
  intro i
  exact Fin.cases (P.tupleLCM_dvd_radical_eval u n hu) hv i

/-- The conditional sifted count for a bad part and a good divisor tuple. -/
noncomputable def PolynomialSystem.badPrimeSiftedCount {k r : ℕ} (P : PolynomialSystem k r)
    (u v : Tuple r) (a b : ℤ) (z : ℝ) : ℕ :=
  conditionalPolynomialSiftedCount P.total (sieveModulus P.total (mass (badSieveModuli u v)) z)
    P.R (u * v) a b

theorem PolynomialSystem.badPrimeSiftedCount_le {k r : ℕ} (P : PolynomialSystem k r)
    (u v : Tuple r) (a b : ℤ) (z : ℝ) :
    P.badPrimeSiftedCount u v a b z ≤
      conditionalPolynomialSiftedCount P.total (sieveModulus P.total (mass (badSieveModuli u v)) z)
        (Fin.cons P.radical P.R) (badSieveModuli u v) a b := by
  unfold badPrimeSiftedCount conditionalPolynomialSiftedCount
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (P.congruenceSet_subset_badSieve u v a b)

theorem PolynomialSystem.badSieveMainTerm_le {k r : ℕ} (P : PolynomialSystem k r)
    (g : ℕ) (u v : Tuple r) (hu : ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers
        P.badDiscriminant.primeFactors)
    (a b : ℤ) (hab : a ≤ b) (z : ℝ) :
    conditionalSieveMainTerm P.total g (Fin.cons P.radical P.R) (badSieveModuli u v) a b z ≤
      ((b : ℝ) - a) * sieveProduct P.total z * totientTwist g P.badDiscriminant *
        (∏ i, totientTwist g (v i)) * ((rootCount P.radical (tupleLCM u) : ℝ) / tupleLCM u) *
          ∏ i, ((rootCount (P.R i) (v i) : ℝ) / v i) := by
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hdensity : 0 ≤ (rootCount P.radical (tupleLCM u) : ℝ) / tupleLCM u *
      ∏ i, ((rootCount (P.R i) (v i) : ℝ) / v i) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Finset.prod_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have H := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (totientTwist_badSieveModuli_le g u v P.badDiscriminant_pos.ne' hu)
      (mul_nonneg hL (sieveProduct_pos P.noFixedPrime z).le)) hdensity
  simpa only [conditionalSieveMainTerm, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, badSieveModuli_zero, badSieveModuli_succ, PNat.mk_coe, mul_assoc,
        PolynomialSystem.total] using H

/-- Pointwise sieve bound with all bad-prime valuations retained in the radical
LCM density. The two constants depend only on the degree and chosen exponents. -/
theorem exists_badPrime_sieve_bound {g : ℕ} (hg : 0 < g) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ K L : ℝ, 1 ≤ K ∧ 1 ≤ L ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree ≤ g →
      ∀ (u v : Tuple r), Dagger P.badDiscriminant v →
      (∀ i, (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      L * (tupleLCM u : ℝ) * mass v * z ^ (4 * (g : ℝ) * (1 + η) + δ) ≤ (b : ℝ) - a →
      (P.badPrimeSiftedCount u v a b z : ℝ) ≤
        K * ((b : ℝ) - a) * sieveProduct P.total z * totientTwist g P.badDiscriminant *
          (∏ i, totientTwist g (v i)) * ((rootCount P.radical (tupleLCM u) : ℝ) / tupleLCM u) *
            ∏ i, ((rootCount (P.R i) (v i) : ℝ) / v i) := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_conditional_sieve_level_bound hg hη hδ
  refine ⟨K, L, hK, hL, ?_⟩
  intro k r P hdeg u v hv hu a b z hab hz hzlog hsize
  have Hcount := H P.total P.noFixedPrime hdeg (r + 1) (Fin.cons P.radical P.R) (badSieveModuli u v)
    (badSieveModuli_pairwise u v hv hu) a b z hab hz hzlog
    (by simpa only [mass_badSieveModuli, Nat.cast_mul, mul_assoc] using hsize)
  have Hle := (Nat.cast_le (α := ℝ)).mpr (P.badPrimeSiftedCount_le u v a b z)
  have Hmain := mul_le_mul_of_nonneg_left (P.badSieveMainTerm_le g u v hu a b hab z)
      (zero_le_one.trans hK)
  exact (Hle.trans Hcount).trans (by simpa only [mul_assoc] using Hmain)

/-- The uniform cost of the full bad-prime sieve summation. -/
noncomputable def badPrimeSieveCost (B : ℝ) (g D : ℕ) : ℝ :=
  totientTwist g D * badPrimeMassBound B g D

/-- Transfer a count bound through the auxiliary weight of the bad-prime part.
The coefficient includes any sieve correction specific to the argument set. -/
theorem PolynomialSystem.weighted_count_le_badPrimeKernel {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (u v : Tuple r)
    (hcross : ∀ i j, Nat.Coprime (u i) (v j)) {C count : ℝ} (hcount : 0 ≤ count)
    (hbound : count ≤ C * ((rootCount P.radical (tupleLCM u) : ℝ) / tupleLCM u) *
      ∏ i, ((rootCount (P.R i) (v i) : ℝ) / v i)) :
    pullback P.exponent F (u * v) * count ≤
      C * badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u *
        rootTupleWeight P.exponent F P.R v := by
  have haux : 0 ≤ ∏ i, auxiliary A B ε (totalExponent P.exponent i) (u i) :=
    Finset.prod_nonneg (fun i _ => auxiliary_nonneg hA (zero_le_one.trans hB) _ _)
  have Hf := mul_le_mul_of_nonneg_right
    (hF.pullback_mul_le_auxiliary hA hB P.exponent u v hcross) hcount
  have H := Hf.trans (mul_le_mul_of_nonneg_left hbound (mul_nonneg haux (hF.nonneg _)))
  convert H using 1
  dsimp only [badPrimeTupleKernel, rootTupleWeight]
  ring

/-- Summing the entire bad-prime part costs only a degree/discriminant constant.
The good tuple retains the totient-modified root weight required in the main proof. -/
theorem exists_badPrime_sieve_sum_bound {g : ℕ} (hg : 0 < g) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ K L : ℝ, 1 ≤ K ∧ 1 ≤ L ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (A B ε : ℝ) (F : ArithmeticMap k), Admissible A B ε F → 0 ≤ A → 1 ≤ B → 0 < ε →
      (g : ℝ) ^ 2 * ε ≤ 1 / 8 →
      ∀ (S : Finset (Tuple r)) (v : Tuple r), Dagger P.badDiscriminant v →
      (∀ u ∈ S, ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      (∀ u ∈ S, L * (tupleLCM u : ℝ) * mass v * z ^ (4 * (g : ℝ) * (1 + η) + δ) ≤ (b : ℝ) - a) →
      (∑ u ∈ S, pullback P.exponent F (u * v) * P.badPrimeSiftedCount u v a b z) ≤
        K * badPrimeSieveCost B g P.badDiscriminant * ((b : ℝ) - a) * sieveProduct P.total z *
          rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist g (v i) := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_badPrime_sieve_bound hg hη hδ
  refine ⟨K, L, hK, hL, ?_⟩
  intro k r P hdeg A B ε F hF hA hB hε hsmall S v hv hs a b z hab hz hzlog hsize
  let C : ℝ := K * ((b : ℝ) - a) * sieveProduct P.total z * totientTwist g P.badDiscriminant *
    rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist g (v i)
  have hW := rootTupleWeight_nonneg P.exponent hF.nonneg P.R v
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (mul_nonneg (zero_le_one.trans hK) (by exact_mod_cast sub_nonneg.mpr hab))
      (sieveProduct_pos P.noFixedPrime z).le) (totientTwist_nonneg g P.badDiscriminant)) hW)
    (Finset.prod_nonneg (fun _ _ => totientTwist_nonneg _ _))
  have Hsum : (∑ u ∈ S, pullback P.exponent F (u * v) * P.badPrimeSiftedCount u v a b z) ≤
      C * ∑ u ∈ S, badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have hcross (i j : Fin r) : Nat.Coprime (u i) (v j) :=
      factoredNumbers_coprime_of_coprime (hs u hu i) (hv.2 j).symm
    have Hcount := H k r P hdeg.le u v hv (hs u hu) a b z hab hz hzlog (hsize u hu)
    have H' := P.weighted_count_le_badPrimeKernel hF hA hB u v hcross
      (C := K * ((b : ℝ) - a) * sieveProduct P.total z * totientTwist g P.badDiscriminant * (∏ i,
        totientTwist g (v i)))
      (Nat.cast_nonneg (P.badPrimeSiftedCount u v a b z)) (by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using Hcount)
    convert H' using 1
    dsimp only [C]
    ring
  have Hmass := P.badPrimeTupleKernel_sum_le_of_support hA hB hε
    (by simpa only [hdeg] using hg) (by simpa only [hdeg] using hsmall) S hs
  rw [hdeg] at Hmass
  calc
    _ ≤ _ := Hsum
    _ ≤ C * badPrimeMassBound B g P.badDiscriminant := mul_le_mul_of_nonneg_left Hmass hC
    _ = _ := by dsimp [C, badPrimeSieveCost]; ring

end NairTenenbaum
