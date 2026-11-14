/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem
public import Mathlib.FieldTheory.Separable

/-! # Degrees and separability of the polynomial family

The degree identities and the nonvanishing of `D*` asserted in §2 are consequences
of the factorization data, rather than additional assumptions on that data.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- Separability over the rationals forces the integral discriminant to be nonzero. -/
theorem discr_ne_zero_of_separable_map {Q : ℤ[X]}
    (hQ : (Q.map (Int.castRingHom ℚ)).Separable) : Q.discr ≠ 0 := by
  by_cases hdeg : Q.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg, discr_C]
    norm_num
  have hres := resultant_ne_zero _ _ hQ
  have hmap : (Q.map (Int.castRingHom ℚ)).resultant
      (Q.map (Int.castRingHom ℚ)).derivative =
      (Int.castRingHom ℚ) (Q.resultant Q.derivative Q.natDegree (Q.natDegree - 1)) := by
    rw [derivative_map]
    simp only [natDegree_map_eq_of_injective (f := Int.castRingHom ℚ)
      Int.cast_injective, natDegree_derivative]
    exact resultant_map_map _ _ _ _ _
  rw [hmap, resultant_deriv (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg))] at hres
  intro hz
  simp [hz] at hres

namespace PolynomialSystem

variable {k r : ℕ} (P : PolynomialSystem k r)

theorem factor_ne_zero (h : Fin r) : P.R h ≠ 0 := by
  intro hz
  have := (P.irreducible h).ne_zero
  simp [hz] at this

theorem sign_ne_zero (j : Fin k) : P.sign j ≠ 0 := by
  intro hz
  have := P.sign_abs j
  simp [hz] at this

theorem polynomial_ne_zero (j : Fin k) : P.Q j ≠ 0 := by
  rw [P.factorization j]
  exact mul_ne_zero (by simpa using P.sign_ne_zero j)
    (Finset.prod_ne_zero_iff.mpr fun h _ => pow_ne_zero _ (P.factor_ne_zero h))

theorem total_ne_zero : P.total ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => P.polynomial_ne_zero j

theorem radical_ne_zero : P.radical ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun h _ => P.factor_ne_zero h

/-- Collecting the exponents in the factorization of the total polynomial. -/
theorem total_factorization :
    P.total = C (∏ j, P.sign j) * ∏ h, P.R h ^ totalExponent P.exponent h := by
  unfold total
  simp_rw [P.factorization]
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro h _
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem total_sign_unit : IsUnit (∏ j, P.sign j) := by
  apply IsUnit.prod_iff.mpr
  intro j _
  exact Int.isUnit_iff_natAbs_eq.mpr (P.sign_abs j)

theorem factor_dvd_total (h : Fin r) : P.R h ∣ P.total := by
  rw [P.total_factorization]
  apply dvd_mul_of_dvd_right
  exact (dvd_pow_self _ (P.exponent_pos h).ne').trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ h))

theorem factor_noFixedPrime (h : Fin r) : NoFixedPrimeDivisor (P.R h) :=
  P.noFixedPrime.of_dvd (P.factor_dvd_total h)

theorem rootCount_total_eq_radical {p : ℕ} (hp : p.Prime) :
    rootCount P.total p = rootCount P.radical p := by
  rw [P.total_factorization, rootCount_C_mul_unit _ P.total_sign_unit]
  exact rootCount_prod_pow_prime P.R _ P.exponent_pos hp

theorem radical_noFixedPrime : NoFixedPrimeDivisor P.radical := by
  intro p hp
  rw [← P.rootCount_total_eq_radical hp]
  exact P.noFixedPrime p hp

theorem factor_degree_pos (h : Fin r) : 0 < (P.R h).natDegree := by
  have := (P.irreducible h).natDegree_pos
  rwa [natDegree_map_eq_of_injective
    (Int.cast_injective : Function.Injective (Int.castRingHom ℚ))] at this

theorem polynomial_degree (j : Fin k) :
    (P.Q j).natDegree = ∑ h, P.exponent j h * (P.R h).natDegree := by
  rw [P.factorization j, natDegree_C_mul (P.sign_ne_zero j),
    natDegree_prod _ _ (fun h _ => pow_ne_zero _ (P.factor_ne_zero h))]
  simp only [natDegree_pow]

theorem total_degree_eq_sum : P.total.natDegree = ∑ j, (P.Q j).natDegree :=
  natDegree_prod _ _ (fun j _ => P.polynomial_ne_zero j)

/-- The degree identity `g = ∑ γ_h r_h` in §2. -/
theorem total_degree :
    P.total.natDegree = ∑ h, totalExponent P.exponent h * (P.R h).natDegree := by
  rw [P.total_degree_eq_sum]
  simp_rw [P.polynomial_degree, totalExponent, Finset.sum_mul]
  exact Finset.sum_comm

theorem totalExponent_le_degree (h : Fin r) :
    totalExponent P.exponent h ≤ P.total.natDegree := by
  rw [P.total_degree]
  exact (Nat.le_mul_of_pos_right _ (P.factor_degree_pos h)).trans
    (Finset.single_le_sum (f := fun i => totalExponent P.exponent i * (P.R i).natDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ h))

theorem radical_degree : P.radical.natDegree = ∑ h, (P.R h).natDegree :=
  natDegree_prod _ _ (fun h _ => P.factor_ne_zero h)

theorem radical_degree_le_total : P.radical.natDegree ≤ P.total.natDegree := by
  rw [P.radical_degree, P.total_degree]
  exact Finset.sum_le_sum fun h _ => Nat.le_mul_of_pos_left _ (P.exponent_pos h)

theorem factor_count_le_degree : r ≤ P.total.natDegree := by
  calc
    r = ∑ _h : Fin r, 1 := by simp
    _ ≤ P.radical.natDegree := by
      rw [P.radical_degree]
      exact Finset.sum_le_sum fun h _ => P.factor_degree_pos h
    _ ≤ P.total.natDegree := P.radical_degree_le_total

theorem factors_coprime {i j : Fin r} (hij : i ≠ j) :
    IsCoprime ((P.R i).map (Int.castRingHom ℚ)) ((P.R j).map (Int.castRingHom ℚ)) := by
  rcases (P.irreducible i).isCoprime_or_dvd ((P.R j).map (Int.castRingHom ℚ)) with h | h
  · exact h
  · exact False.elim (P.nonassociated i j hij
      ((P.irreducible i).associated_of_dvd (P.irreducible j) h))

theorem radical_separable : (P.radical.map (Int.castRingHom ℚ)).Separable := by
  rw [radical, Polynomial.map_prod]
  exact separable_prod (fun _ _ hij => P.factors_coprime hij)
    (fun h => (P.irreducible h).separable)

theorem discriminant_pos : 0 < P.discriminant :=
  Int.natAbs_pos.mpr (discr_ne_zero_of_separable_map P.radical_separable)

end PolynomialSystem

end NairTenenbaum
