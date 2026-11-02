/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.IrreducibleSystem
public import Mathlib.Algebra.AffineMonoid.Basic

/-! # Constructing the polynomial factorization data

The union of the normalized integral factors of the original polynomials
provides a finite common factor family. Primitivity follows from the
no-fixed-prime condition; Gauss's lemma therefore supplies the rational
irreducibility and nonassociation required by `PolynomialSystem`.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial UniqueFactorizationMonoid

/-- Factoring a nonzero integral polynomial leaves only a unit sign. -/
theorem exists_sign_mul_normalizedFactors (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    ∃ s : ℤ, s.natAbs = 1 ∧ Q = Polynomial.C s * (normalizedFactors Q).prod := by
  obtain ⟨u, hu⟩ := prod_normalizedFactors hQ
  obtain ⟨s, hs, hsu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  refine ⟨s, Int.isUnit_iff_natAbs_eq.mp hs, ?_⟩
  calc
    Q = (normalizedFactors Q).prod * ↑u := hu.symm
    _ = Polynomial.C s * (normalizedFactors Q).prod := by rw [← hsu, mul_comm]

/-- Distinct normalized primitive integral polynomials cannot become
associated after extension of scalars to the rationals. -/
theorem not_associated_map_of_normalized {P Q : Polynomial ℤ}
    (hP : P.IsPrimitive) (hQ : Q.IsPrimitive)
    (hnP : normalize P = P) (hnQ : normalize Q = Q) (hne : P ≠ Q) :
    ¬Associated (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)) := by
  intro H
  have hPQ := (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast P Q hP).mpr H.dvd
  have hQP := (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast Q P hQ).mpr H.symm.dvd
  have heq := normalize_eq_normalize_iff.mpr ⟨hPQ, hQP⟩
  exact hne (by simpa only [hnP, hnQ] using heq)

/-- Every admissible polynomial family has all the data required by the
analytic theorems. Constant unit polynomials and empty families are included. -/
theorem exists_polynomialSystem {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hfixed : NoFixedPrimeDivisor (∏ j, Q j)) :
    ∃ r : ℕ, ∃ P : PolynomialSystem k r, P.Q = Q := by
  classical
  have hQfixed (j : Fin k) : NoFixedPrimeDivisor (Q j) :=
    hfixed.of_dvd (Finset.dvd_prod_of_mem Q (Finset.mem_univ j))
  have hQne (j : Fin k) : Q j ≠ 0 := (hQfixed j).isPrimitive.ne_zero
  let S : Finset (Polynomial ℤ) := Finset.univ.biUnion (fun j => (normalizedFactors (Q j)).toFinset)
  have hmem (p : Polynomial ℤ) : p ∈ S ↔ ∃ j, p ∈ normalizedFactors (Q j) := by
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, Multiset.mem_toFinset, true_and]
  have hsub (j : Fin k) : (normalizedFactors (Q j)).toFinset ⊆ S := by
    intro p hp
    exact (hmem p).mpr ⟨j, Multiset.mem_toFinset.mp hp⟩
  let r := Fintype.card S
  let e : Fin r ≃ S := (Fintype.equivFin S).symm
  let R : Fin r → Polynomial ℤ := fun i => (e i).val
  let γ : Fin k → Fin r → ℕ := fun j i => (normalizedFactors (Q j)).count (R i)
  have hRmem (i : Fin r) : ∃ j, R i ∈ normalizedFactors (Q j) := (hmem (R i)).mp (e i).property
  have hRfixed (i : Fin r) : NoFixedPrimeDivisor (R i) := by
    obtain ⟨j, hj⟩ := hRmem i
    exact (hQfixed j).of_dvd (dvd_of_mem_normalizedFactors hj)
  have hRirr (i : Fin r) : Irreducible ((R i).map (Int.castRingHom ℚ)) := by
    obtain ⟨j, hj⟩ := hRmem i
    exact (hRfixed i).irreducible_map (irreducible_of_normalized_factor _ hj)
  have hRnorm (i : Fin r) : normalize (R i) = R i := by
    obtain ⟨j, hj⟩ := hRmem i
    exact normalize_normalized_factor _ hj
  have hRinj : Function.Injective R := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hnonassoc (i j : Fin r) (hij : i ≠ j) :
      ¬Associated ((R i).map (Int.castRingHom ℚ)) ((R j).map (Int.castRingHom ℚ)) :=
    not_associated_map_of_normalized (hRfixed i).isPrimitive (hRfixed j).isPrimitive
      (hRnorm i) (hRnorm j) (fun H => hij (hRinj H))
  have hγpos (i : Fin r) : 0 < totalExponent γ i := by
    obtain ⟨j, hj⟩ := hRmem i
    exact Finset.sum_pos_iff.mpr ⟨j, Finset.mem_univ _, Multiset.count_pos.mpr hj⟩
  have hprod (j : Fin k) : (∏ i, R i ^ γ j i) = (normalizedFactors (Q j)).prod := by
    calc
      _ = ∏ p : S, (p : Polynomial ℤ) ^ (normalizedFactors (Q j)).count (p : Polynomial ℤ) :=
        Fintype.prod_equiv e _ _ (fun _ => rfl)
      _ = ∏ p ∈ S, p ^ (normalizedFactors (Q j)).count p :=
        (Finset.prod_subtype S (fun _ => Iff.rfl) (fun p : Polynomial ℤ => p ^ (normalizedFactors
            (Q j)).count p)).symm
      _ = _ := (Finset.prod_multiset_count_of_subset _ S (hsub j)).symm
  choose s hs hfactor using fun j => exists_sign_mul_normalizedFactors (Q j) (hQne j)
  refine ⟨r, {
    Q := Q
    R := R
    exponent := γ
    sign := s
    sign_abs := hs
    factorization := fun j => by rw [hprod j]; exact hfactor j
    irreducible := hRirr
    nonassociated := hnonassoc
    exponent_pos := hγpos
    noFixedPrime := hfixed }, rfl⟩

/-- A selected common factorization of the original polynomial family. -/
noncomputable def familySystem {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hfixed : NoFixedPrimeDivisor (∏ j, Q j)) : Σ r : ℕ, PolynomialSystem k r :=
  ⟨Classical.choose (exists_polynomialSystem Q hfixed),
    Classical.choose (Classical.choose_spec (exists_polynomialSystem Q hfixed))⟩

@[simp] theorem familySystem_Q {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hfixed : NoFixedPrimeDivisor (∏ j, Q j)) : (familySystem Q hfixed).2.Q = Q :=
  Classical.choose_spec (Classical.choose_spec (exists_polynomialSystem Q hfixed))

@[simp] theorem familySystem_total {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hfixed : NoFixedPrimeDivisor (∏ j, Q j)) : (familySystem Q hfixed).2.total = ∏ j, Q j := by
  unfold PolynomialSystem.total
  rw [familySystem_Q]

end NairTenenbaum
