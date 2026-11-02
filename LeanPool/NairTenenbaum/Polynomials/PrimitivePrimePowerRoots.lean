/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PrimitiveResidueRoots
public import LeanPool.NairTenenbaum.Sieve.BadPrimeRoots

/-! # Uniform prime-power roots for primitive polynomials

Fixed prime divisors are allowed. The discriminant separates the primes
with simple reduction from the finite set requiring a larger bound.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial

theorem simple_roots_of_discr_primitive {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    {p : ℕ} (hp : p.Prime) (hD : (Q.discr : ZMod p) ≠ 0) (a : ResidueRoots Q p) :
    Q.derivative.eval₂ (Int.castRingHom (ZMod p)) (a : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hdeg : 2 ≤ Q.natDegree
  · obtain ⟨U, V, hbez⟩ := exists_mul_add_mul_eq_C_discr Q hdeg
    intro hz
    have h := congrArg (fun f : ℤ[X] => f.eval₂ (Int.castRingHom (ZMod p)) (a : ZMod p)) hbez
    simp only [eval₂_add, eval₂_mul, a.property, hz, zero_mul, zero_add, eval₂_C] at h
    exact hD h.symm
  · have hdeg' : (Q.map (Int.castRingHom (ZMod p))).natDegree ≤ 1 :=
      natDegree_map_le.trans (by omega)
    have h := eval_derivative_ne_zero_of_degree_le_one (primitive_map_zmod_ne_zero hQ hp) hdeg'
      (a := (a : ZMod p)) (by simpa only [Polynomial.eval_map] using a.property)
    simpa only [derivative_map, Polynomial.eval_map] using h

/-- The uniform prime-power bound away from the discriminant, including primes
dividing the leading coefficient. -/
theorem rootCount_prime_pow_le_of_discr_primitive {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    {p ν : ℕ} (hp : p.Prime) (hν : ν ≠ 0) (hD : (Q.discr : ZMod p) ≠ 0) :
    rootCount Q (p ^ ν) ≤ rootCount Q p :=
  rootCount_prime_pow_le_of_simple hp hν (simple_roots_of_discr_primitive hQ hp hD)

theorem rootCount_prime_pow_le_discr_cube {Q : ℤ[X]} (hD : Q.discr ≠ 0)
    {p : ℕ} (hp : p.Prime) (hpD : p ∣ Q.discr.natAbs) (ν : ℕ) :
    rootCount Q (p ^ ν) ≤ Q.discr.natAbs ^ 3 := by
  have hdeg : 2 ≤ Q.natDegree := by
    by_contra! h
    have HE := discr_eq_one_of_natDegree_le_one (Q := Q) (by omega)
    rw [HE, Int.natAbs_one] at hpD
    exact hp.not_dvd_one hpD
  have hDpos := Int.natAbs_pos.mpr hD
  have H := rootCount_prime_pow_le_factorization_bound hdeg hD hp ν
  have hpow : p ^ Q.discr.natAbs.factorization p ≤ Q.discr.natAbs :=
    Nat.le_of_dvd hDpos (Nat.ordProj_dvd _ _)
  have hple : p ≤ Q.discr.natAbs := Nat.le_of_dvd hDpos hpD
  calc
    _ ≤ p ^ (2 * Q.discr.natAbs.factorization p + 1) := H
    _ = (p ^ Q.discr.natAbs.factorization p) ^ 2 * p := by
      rw [pow_add, pow_one, Nat.mul_comm 2, pow_mul]
    _ ≤ Q.discr.natAbs ^ 2 * Q.discr.natAbs := Nat.mul_le_mul (Nat.pow_le_pow_left hpow 2) hple
    _ = _ := by ring

theorem primitive_rootCount_prime_pow_uniform {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    (hD : Q.discr ≠ 0) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    rootCount Q (p ^ ν) ≤ max Q.natDegree (Q.discr.natAbs ^ 3) := by
  by_cases hν : ν = 0
  · subst ν
    simp only [pow_zero, rootCount_one]
    exact (one_le_pow₀ (Int.natAbs_pos.mpr hD)).trans (le_max_right _ _)
  · by_cases hpD : p ∣ Q.discr.natAbs
    · exact (rootCount_prime_pow_le_discr_cube hD hp hpD ν).trans (le_max_right _ _)
    · have hDp : (Q.discr : ZMod p) ≠ 0 := by
        simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd] using hpD
      exact ((rootCount_prime_pow_le_of_discr_primitive hQ hp hν hDp).trans
        (primitive_rootCount_le_degree hQ hp)).trans (le_max_left _ _)

end NairTenenbaum
