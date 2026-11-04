/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-! # The factorization data for irreducible pairwise coprime families -/

@[expose] public section

namespace NairTenenbaum

/-- For an irreducible pairwise coprime family, the original polynomials
already provide all factorization data, with the identity exponent matrix. -/
noncomputable def PolynomialSystem.ofIrreducible {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hQ : ∀ j, Irreducible ((Q j).map (Int.castRingHom ℚ)))
    (hcoprime : ∀ i j, i ≠ j → IsCoprime ((Q i).map (Int.castRingHom ℚ)) ((Q j).map
        (Int.castRingHom ℚ)))
    (hfixed : NoFixedPrimeDivisor (∏ j, Q j)) : PolynomialSystem k k where
  Q := Q
  R := Q
  exponent := identityExponents k
  sign := fun _ => 1
  sign_abs := fun _ => rfl
  factorization := by intro j; simp [identityExponents]
  irreducible := hQ
  nonassociated := fun i j hij hassoc => (hQ i).not_isUnit ((hcoprime i j
      hij).isUnit_of_associated hassoc).1
  exponent_pos := by intro j; simp
  noFixedPrime := hfixed

@[simp] theorem PolynomialSystem.ofIrreducible_total {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hQ : ∀ j, Irreducible ((Q j).map (Int.castRingHom ℚ)))
    (hcoprime : ∀ i j, i ≠ j → IsCoprime ((Q i).map (Int.castRingHom ℚ)) ((Q j).map
        (Int.castRingHom ℚ)))
    (hfixed : NoFixedPrimeDivisor (∏ j, Q j)) :
    (PolynomialSystem.ofIrreducible Q hQ hcoprime hfixed).total = ∏ j, Q j := rfl

/-- A fixed content prime would make the polynomial identically zero modulo
that prime. Thus the no-fixed-prime condition supplies primitivity. -/
theorem NoFixedPrimeDivisor.isPrimitive {Q : Polynomial ℤ} (hQ : NoFixedPrimeDivisor Q) :
    Q.IsPrimitive := by
  intro a ha
  apply Int.isUnit_iff_natAbs_eq.mpr
  by_contra hunit
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd hunit
  have ha₀ : (a : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr (Int.natCast_dvd.mpr
      hpa)
  obtain ⟨T, hT⟩ := ha
  apply hQ.map_ne_zero hp
  rw [hT, Polynomial.map_mul, Polynomial.map_C]
  change Polynomial.C (a : ZMod p) * _ = 0
  rw [ha₀, Polynomial.C_0, zero_mul]

/-- Gauss's lemma transfers the paper's integral irreducibility hypothesis to
the rational factorization interface. -/
theorem NoFixedPrimeDivisor.irreducible_map {Q : Polynomial ℤ}
    (hQ : NoFixedPrimeDivisor Q) (hI : Irreducible Q) :
    Irreducible (Q.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hQ.isPrimitive).mp hI

/-- Restricted discriminant of an irreducible family, expressed directly in
terms of the product polynomial. -/
noncomputable def irreducibleBadDiscriminant {k : ℕ} (Q : Fin k → Polynomial ℤ) : ℕ :=
  let T := ∏ j, Q j
  let D := T.discr.natAbs
  ∏ p ∈ D.primeFactors.filter (fun p => rootCount T p ≠ 0), p ^ D.factorization p

@[simp] theorem PolynomialSystem.ofIrreducible_badDiscriminant {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hQ : ∀ j, Irreducible ((Q j).map (Int.castRingHom ℚ)))
    (hcoprime : ∀ i j, i ≠ j → IsCoprime ((Q i).map (Int.castRingHom ℚ)) ((Q j).map
        (Int.castRingHom ℚ)))
    (hfixed : NoFixedPrimeDivisor (∏ j, Q j)) :
    (PolynomialSystem.ofIrreducible Q hQ hcoprime hfixed).badDiscriminant =
        irreducibleBadDiscriminant Q := rfl

end NairTenenbaum
