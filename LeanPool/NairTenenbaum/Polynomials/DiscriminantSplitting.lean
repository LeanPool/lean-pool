/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.CongruenceCount
public import LeanPool.NairTenenbaum.Arithmetic.MultivariableComparison

/-! # Removing the full discriminant-supported part

For divisors of distinct polynomial values, all common prime divisors belong
to the radical discriminant. Removing their full prime powers produces a
dagger tuple and a cross-coprime factorization. A single division by the gcd
with the discriminant does not in general have these properties.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

theorem primeSelect_coordinate_dvd {r : ℕ} (n : Tuple r) (s : Finset ℕ) (i : Fin r) :
    (primeSelect n s i : ℕ) ∣ n i := by
  use (primeReject n s i : ℕ)
  exact congrArg (fun a : ℕ+ => (a : ℕ)) (congrFun (primeSelect_mul_primeReject n s) i).symm

theorem primeReject_coordinate_dvd {r : ℕ} (n : Tuple r) (s : Finset ℕ) (i : Fin r) :
    (primeReject n s i : ℕ) ∣ n i := by
  use (primeSelect n s i : ℕ)
  simpa only [Pi.mul_apply, PNat.mul_coe, mul_comm] using
    congrArg (fun a : ℕ+ => (a : ℕ)) (congrFun (primeSelect_mul_primeReject n s) i).symm

/-- Every coordinate remaining after full prime-power removal is coprime to
`D`, even when the original valuation exceeds the valuation of `D`. -/
theorem primeReject_coprime {r : ℕ} (n : Tuple r) {D : ℕ} (hD : D ≠ 0) (i : Fin r) :
    Nat.Coprime (primeReject n D.primeFactors i) D := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hpD
  have hm := Nat.mem_primeFactors.mpr ⟨hp, hpn, (primeReject n D.primeFactors i).ne_zero⟩
  rw [primeFactors_primeReject] at hm
  exact (Finset.mem_sdiff.mp hm).2 (Nat.mem_primeFactors.mpr ⟨hp, hpD, hD⟩)

/-- Common-divisor control suffices to make the remaining tuple dagger. -/
theorem primeReject_dagger {r : ℕ} (n : Tuple r) {D : ℕ} (hD : D ≠ 0)
    (hcommon : ∀ i j, i ≠ j → Nat.gcd (n i) (n j) ∣ D) :
    Dagger D (primeReject n D.primeFactors) := by
  refine ⟨?_, primeReject_coprime n hD⟩
  intro i j hij
  apply Nat.coprime_of_dvd
  intro p hp hpi hpj
  have hpD := (Nat.dvd_gcd (hpi.trans (primeReject_coordinate_dvd n _ i))
    (hpj.trans (primeReject_coordinate_dvd n _ j))).trans (hcommon i j hij)
  have H := Nat.dvd_gcd hpi hpD
  rw [(primeReject_coprime n hD i).gcd_eq_one] at H
  exact hp.not_dvd_one H

/-- An actual integral zero modulo a positive modulus witnesses a nonzero
root count. -/
theorem rootCount_pos_of_dvd_eval (Q : ℤ[X]) {q : ℕ} (hq : q ≠ 0) (a : ℤ)
    (ha : (q : ℤ) ∣ Q.eval a) : 0 < rootCount Q q := by
  let : NeZero q := ⟨hq⟩
  rw [← residueRootSet_card Q q]
  exact Finset.card_pos.mpr ⟨(a : ZMod q), (cast_mem_residueRootSet Q q a).mpr ha⟩

/-- Removing all discriminant primes from divisors of the irreducible values
produces exactly the coprimality restrictions required by (16). -/
theorem PolynomialSystem.divisor_primeReject_dagger {k r : ℕ} (P : PolynomialSystem k r)
    (a : ℤ) (m : Tuple r) (hm : ∀ i, (m i : ℕ) ∣ ((P.R i).eval a).natAbs) :
    Dagger P.discriminant (primeReject m P.discriminant.primeFactors) := by
  apply primeReject_dagger m P.discriminant_pos.ne'
  intro i j hij
  exact (Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (hm i)) ((Nat.gcd_dvd_right _ _).trans (hm
      j))).trans (P.common_value_gcd_dvd_discriminant hij a)

/-- For tuples dividing polynomial values, the removed part is supported only
on the restricted bad discriminant, rather than all discriminant primes. -/
theorem PolynomialSystem.divisor_primeSelect_bad_support {k r : ℕ} (P : PolynomialSystem k r)
    (a : ℤ) (m : Tuple r) (hm : ∀ i, (m i : ℕ) ∣ ((P.R i).eval a).natAbs) (i : Fin r) :
    (primeSelect m P.discriminant.primeFactors i : ℕ) ∈
      Nat.factoredNumbers P.badDiscriminant.primeFactors := by
  apply Nat.mem_factoredNumbers_of_primeFactors_subset (primeSelect m _ i).ne_zero
  intro p hp
  rw [primeFactors_primeSelect] at hp
  obtain ⟨hpm, hpD⟩ := Finset.mem_inter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hpm
  have hpQ : (p : ℤ) ∣ P.total.eval a :=
    (Int.natCast_dvd.mpr ((Nat.dvd_of_mem_primeFactors hpm).trans (hm i))).trans
      (Polynomial.eval_dvd (P.factor_dvd_total i))
  have hbad := (P.prime_dvd_badDiscriminant_iff hprime).mpr
    ⟨Nat.dvd_of_mem_primeFactors hpD, (rootCount_pos_of_dvd_eval P.total hprime.ne_zero a hpQ).ne'⟩
  exact Nat.mem_primeFactors.mpr ⟨hprime, hbad, P.badDiscriminant_pos.ne'⟩

/-- Dividing by one gcd can leave a discriminant prime in both factors. Thus
that division cannot replace the full prime-power removal above. -/
theorem gcd_removal_not_coprime :
    ¬ Nat.Coprime (8 / Nat.gcd 8 4) 4 ∧
      ¬ Nat.Coprime (8 / Nat.gcd 8 4) (Nat.gcd 8 4) := by decide

end NairTenenbaum
