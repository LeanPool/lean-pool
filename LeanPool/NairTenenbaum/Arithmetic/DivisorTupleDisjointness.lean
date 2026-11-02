/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialLocal

/-! # Uniqueness of divisor tuples at a fixed substituted mass

Outside the radical discriminant, a prime cannot divide the values of two
distinct irreducible factors at the same integer. This makes the congruence
sets for distinct tuples of the same weighted mass disjoint.
-/

@[expose] public section

namespace NairTenenbaum

/-- Cross-coprimality removes every other coordinate from a weighted product. -/
theorem coordinate_dvd_of_weightedMass_dvd {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (n m : Tuple r)
    (hcross : ∀ i j, i ≠ j → Nat.Coprime (n i) (m j))
    (hmass : weightedMass γ n ∣ weightedMass γ m) (i : Fin r) : (n i : ℕ) ∣ m i := by
  classical
  have hd : (n i : ℕ) ^ totalExponent γ i ∣ ∏ j, (m j : ℕ) ^ totalExponent γ j :=
    (Finset.dvd_prod_of_mem (fun j => (n j : ℕ) ^ totalExponent γ j) (Finset.mem_univ i)).trans
        hmass
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at hd
  have hc : Nat.Coprime ((n i : ℕ) ^ totalExponent γ i)
      (∏ j ∈ Finset.univ.erase i, (m j : ℕ) ^ totalExponent γ j) := by
    rw [Nat.coprime_prod_right_iff]
    intro j hj
    exact ((hcross i j (Finset.mem_erase.mp hj).1.symm).pow_left _).pow_right _
  exact (Nat.pow_dvd_pow_iff (hγ i).ne').mp (hc.dvd_of_dvd_mul_left hd)

/-- Equality of weighted masses determines cross-coprime tuples uniquely. -/
theorem weightedMass_injective_of_cross_coprime {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (n m : Tuple r)
    (hcross : ∀ i j, i ≠ j → Nat.Coprime (n i) (m j))
    (hmass : weightedMass γ n = weightedMass γ m) : n = m := by
  funext i
  apply Subtype.ext
  apply Nat.dvd_antisymm
  · exact coordinate_dvd_of_weightedMass_dvd γ hγ n m hcross (hmass ▸ dvd_refl _) i
  · exact coordinate_dvd_of_weightedMass_dvd γ hγ m n
      (fun i j hij => (hcross j i hij.symm).symm) (hmass ▸ dvd_refl _) i

/-- Actual value divisors avoiding the discriminant are coprime across
unequal irreducible-factor coordinates. -/
theorem PolynomialSystem.divisor_tuple_cross_coprime {k r : ℕ} (P : PolynomialSystem k r)
    (t : ℤ) (n m : Tuple r) (hn : ∀ i, (n i : ℤ) ∣ (P.R i).eval t)
    (hm : ∀ i, (m i : ℤ) ∣ (P.R i).eval t)
    (hD : ∀ i, Nat.Coprime (n i) P.discriminant) :
    ∀ i j, i ≠ j → Nat.Coprime (n i) (m j) := by
  intro i j hij
  apply Nat.coprime_of_dvd
  intro p hp hpn hpm
  have hpD := (Nat.dvd_gcd (hpn.trans (Int.natCast_dvd.mp (hn i)))
    (hpm.trans (Int.natCast_dvd.mp (hm j)))).trans (P.common_value_gcd_dvd_discriminant hij t)
  have H := Nat.dvd_gcd hpn hpD
  rw [(hD i).gcd_eq_one] at H
  exact hp.not_dvd_one H

/-- Distinct dagger tuples of the same weighted mass cannot hold at the same
integer. This is the disjointness needed before summing their root densities. -/
theorem PolynomialSystem.divisor_tuple_eq_of_weightedMass_eq {k r : ℕ} (P : PolynomialSystem k r)
    (t : ℤ) (n m : Tuple r) (hn : ∀ i, (n i : ℤ) ∣ (P.R i).eval t)
    (hm : ∀ i, (m i : ℤ) ∣ (P.R i).eval t) (hD : Dagger P.discriminant n)
    (hmass : weightedMass P.exponent n = weightedMass P.exponent m) : n = m :=
  weightedMass_injective_of_cross_coprime P.exponent P.exponent_pos n m
    (P.divisor_tuple_cross_coprime t n m hn hm hD.2) hmass

end NairTenenbaum
