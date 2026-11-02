/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Sieve.JointCongruence

/-! # Summing bad-prime congruence contributions

The complete bad-prime valuations have a uniform total cost when their joint
congruence density is retained. This is the counting input for the corrected
full-prime-power discriminant split.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

theorem factoredNumbers_coprime_of_coprime {D n m : ℕ}
    (hn : n ∈ Nat.factoredNumbers D.primeFactors) (hm : Nat.Coprime D m) : Nat.Coprime n m := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hpm
  have hpD := Nat.dvd_of_mem_primeFactors
    (Nat.primeFactors_subset_of_mem_factoredNumbers hn
      (Nat.mem_primeFactors.mpr ⟨hp, hpn, Nat.ne_zero_of_mem_factoredNumbers hn⟩))
  exact hp.not_dvd_one (by simpa only [hm.gcd_eq_one] using Nat.dvd_gcd hpD hpm)

theorem PolynomialSystem.badPrimeTupleKernel_sum_le_of_support {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hg : 0 < P.total.natDegree)
    (hsmall : (P.total.natDegree : ℝ) ^ 2 * ε ≤ 1 / 8)
    (S : Finset (Tuple r))
    (hs : ∀ n ∈ S, ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) :
    (∑ n ∈ S, badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical n) ≤
      badPrimeMassBound B P.total.natDegree P.badDiscriminant := by
  let N : ℕ+ := ⟨(∑ n ∈ S, mass n) + 1, by omega⟩
  apply P.badPrimeTupleKernel_sum_le hA hB hε hg hsmall S N _ hs
  intro n hn i
  have H := Finset.single_le_sum (fun n _ => Nat.zero_le (mass n)) hn
  exact (Nat.le_of_dvd (mass_pos n) (coordinate_dvd_mass n i)).trans (H.trans (Nat.le_succ _))

/-- A uniform sum over bad-prime valuations, with the good-coordinate density
left intact. The size hypothesis is on the actual combined congruence modulus. -/
theorem PolynomialSystem.badPrime_congruence_sum_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hg : 0 < P.total.natDegree)
    (hsmall : (P.total.natDegree : ℝ) ^ 2 * ε ≤ 1 / 8)
    (S : Finset (Tuple r)) (v : Tuple r) (hv : Dagger P.badDiscriminant v)
    (hs : ∀ u ∈ S, ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors)
    (a b : ℤ) (hab : a ≤ b)
    (hsize : ∀ u ∈ S, (tupleLCM u : ℝ) * mass v ≤ (b : ℝ) - a) :
    (∑ u ∈ S, (∏ i, auxiliary A B ε (totalExponent P.exponent i) (u i)) *
      jointCongruenceCount P.R (fun i => ((u * v) i : ℕ)) a b) ≤
      2 * ((b : ℝ) - a) * badPrimeMassBound B P.total.natDegree P.badDiscriminant *
        ∏ i, ((rootCount (P.R i) (v i) : ℝ) / v i) := by
  let C : ℝ := 2 * ((b : ℝ) - a) * ∏ i, ((rootCount (P.R i) (v i) : ℝ) / v i)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) (by exact_mod_cast sub_nonneg.mpr hab))
    (Finset.prod_nonneg (fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have H : (∑ u ∈ S, (∏ i, auxiliary A B ε (totalExponent P.exponent i) (u i)) *
      jointCongruenceCount P.R (fun i => ((u * v) i : ℕ)) a b) ≤
      C * ∑ u ∈ S, badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have hcop (i : Fin r) : Nat.Coprime (tupleLCM u) (v i) :=
      factoredNumbers_coprime_of_coprime (tupleLCM_mem_factoredNumbers u _ (hs u hu)) (hv.2 i).symm
    have hcount := (Nat.cast_le (α := ℝ)).mpr (P.jointCongruenceCount_le_mixed u v a b)
    have Hcount := hcount.trans (mixedCongruenceCount_le P.radical P.R (tupleLCM_pos u) v hv.1
        hcop a b hab (hsize u hu))
    have haux : 0 ≤ ∏ i, auxiliary A B ε (totalExponent P.exponent i) (u i) :=
      Finset.prod_nonneg (fun i _ => auxiliary_nonneg hA (zero_le_one.trans hB) _ _)
    calc
      _ ≤ (∏ i, auxiliary A B ε (totalExponent P.exponent i) (u i)) *
          (2 * ((b : ℝ) - a) * ((rootCount P.radical (tupleLCM u) : ℝ) / tupleLCM u) *
            ∏ i, ((rootCount (P.R i) (v i) : ℝ) / v i)) := mul_le_mul_of_nonneg_left Hcount haux
      _ = _ := by dsimp [C, badPrimeTupleKernel]; ring
  calc
    _ ≤ _ := H
    _ ≤ C * badPrimeMassBound B P.total.natDegree P.badDiscriminant :=
      mul_le_mul_of_nonneg_left (P.badPrimeTupleKernel_sum_le_of_support hA hB hε hg hsmall S hs) hC
    _ = _ := by dsimp [C]; ring

/-- The same estimate with the original admissible arithmetic function. -/
theorem PolynomialSystem.badPrime_weighted_congruence_sum_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hg : 0 < P.total.natDegree)
    (hsmall : (P.total.natDegree : ℝ) ^ 2 * ε ≤ 1 / 8)
    (S : Finset (Tuple r)) (v : Tuple r) (hv : Dagger P.badDiscriminant v)
    (hs : ∀ u ∈ S, ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors)
    (a b : ℤ) (hab : a ≤ b)
    (hsize : ∀ u ∈ S, (tupleLCM u : ℝ) * mass v ≤ (b : ℝ) - a) :
    (∑ u ∈ S, pullback P.exponent F (u * v) *
      jointCongruenceCount P.R (fun i => ((u * v) i : ℕ)) a b) ≤
      2 * ((b : ℝ) - a) * badPrimeMassBound B P.total.natDegree P.badDiscriminant *
        rootTupleWeight P.exponent F P.R v := by
  have hFv : 0 ≤ pullback P.exponent F v := hF.nonneg _
  have H : (∑ u ∈ S, pullback P.exponent F (u * v) *
      jointCongruenceCount P.R (fun i => ((u * v) i : ℕ)) a b) ≤
      pullback P.exponent F v * ∑ u ∈ S,
        (∏ i, auxiliary A B ε (totalExponent P.exponent i) (u i)) *
          jointCongruenceCount P.R (fun i => ((u * v) i : ℕ)) a b := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have hcross (i j : Fin r) : Nat.Coprime (u i) (v j) :=
      factoredNumbers_coprime_of_coprime (hs u hu i) (hv.2 j).symm
    have H := mul_le_mul_of_nonneg_right
      (hF.pullback_mul_le_auxiliary hA hB P.exponent u v hcross)
      (Nat.cast_nonneg (jointCongruenceCount P.R (fun i => ((u * v) i : ℕ)) a b))
    simpa only [mul_comm, mul_left_comm, mul_assoc] using H
  calc
    _ ≤ _ := H
    _ ≤ pullback P.exponent F v *
        (2 * ((b : ℝ) - a) * badPrimeMassBound B P.total.natDegree P.badDiscriminant *
          ∏ i, ((rootCount (P.R i) (v i) : ℝ) / v i)) :=
      mul_le_mul_of_nonneg_left
        (P.badPrime_congruence_sum_le hA hB hε hg hsmall S v hv hs a b hab hsize) hFv
    _ = _ := by dsimp [rootTupleWeight]; ring

end NairTenenbaum
