/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimePowerRoots

/-! # Root counts under arithmetic-progression substitution

The affine map is a permutation modulo every modulus coprime to its slope.
At a prime dividing the slope, the transformed polynomial is constant. These
facts supply the root-count identities in the proof of Corollary 1.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial

/-- The integral substitution used to parametrize a residue class. -/
noncomputable def affinePolynomial (q : ℕ) (a : ℤ) : ℤ[X] := C (q : ℤ) * X + C a

@[simp] theorem eval_affinePolynomial (q : ℕ) (a t : ℤ) :
    (affinePolynomial q a).eval t = (q : ℤ) * t + a := by
  simp [affinePolynomial]

@[simp] theorem eval₂_affinePolynomial {R : Type*} [CommRing R]
    (q : ℕ) (a : ℤ) (t : R) :
    (affinePolynomial q a).eval₂ (Int.castRingHom R) t = (q : R) * t + a := by
  simp only [affinePolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  change ((q : ℤ) : R) * t + (a : R) = (q : R) * t + (a : R)
  rw [Int.cast_natCast]

/-- The residue-root equivalence induced by an invertible affine substitution. -/
noncomputable def rootsAffine (Q : ℤ[X]) (q : ℕ) (a : ℤ) (n : ℕ) (hqn : q.Coprime n) :
    ResidueRoots (Q.comp (affinePolynomial q a)) n ≃ ResidueRoots Q n := by
  let u := ((ZMod.isUnit_iff_coprime q n).mpr hqn).unit
  have hu : (u : ZMod n) = q := IsUnit.unit_spec _
  let e : ZMod n ≃ ZMod n := u.mulLeft.trans (Equiv.addRight (a : ZMod n))
  apply Equiv.subtypeEquiv e
  intro t
  simp [e, Polynomial.eval₂_comp, hu]

/-- Equation (37)'s substitution preserves root counts at coprime moduli. -/
theorem rootCount_comp_affine_of_coprime (Q : ℤ[X]) (q : ℕ) (a : ℤ) (n : ℕ)
    (hqn : q.Coprime n) : rootCount (Q.comp (affinePolynomial q a)) n = rootCount Q n :=
  Nat.card_congr (rootsAffine Q q a n hqn)

/-- At a prime dividing the slope, the value at the residue representative
controls every root of the transformed polynomial. -/
theorem rootCount_comp_affine_prime_eq_zero (Q : ℤ[X]) {q p : ℕ} (a : ℤ)
    (hpq : p ∣ q) (hpa : ¬p ∣ (Q.eval a).natAbs) :
    rootCount (Q.comp (affinePolynomial q a)) p = 0 := by
  have hq : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).mpr hpq
  have hval : ((Q.eval a : ℤ) : ZMod p) ≠ 0 := by
    intro h
    exact hpa (Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h))
  let : IsEmpty (ResidueRoots (Q.comp (affinePolynomial q a)) p) := ⟨by
    intro t
    have H := t.property
    rw [Polynomial.eval₂_comp, eval₂_affinePolynomial, hq, zero_mul, zero_add] at H
    change Q.eval₂ (Int.castRingHom (ZMod p)) ((Int.castRingHom (ZMod p)) a) = 0 at H
    rw [Polynomial.eval₂_at_apply] at H
    exact hval H⟩
  exact Nat.card_of_isEmpty

/-- Under the progression's coprimality hypothesis, every modulus sharing a
prime with the slope has no roots. -/
theorem rootCount_comp_affine_eq_zero (Q : ℤ[X]) (q : ℕ) (a : ℤ) (n : ℕ)
    (hqa : q.Coprime (Q.eval a).natAbs) (hqn : ¬q.Coprime n) :
    rootCount (Q.comp (affinePolynomial q a)) n = 0 := by
  obtain ⟨p, hp, hpq, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hqn
  have hpa : ¬p ∣ (Q.eval a).natAbs := by
    intro h
    have H : p ∣ 1 := by simpa only [hqa.gcd_eq_one] using Nat.dvd_gcd hpq h
    exact hp.not_dvd_one H
  exact rootCount_eq_zero_of_dvd hp.ne_zero hpn (rootCount_comp_affine_prime_eq_zero Q a hpq hpa)

/-- The full root-count formula, including all prime powers and composite
moduli. -/
theorem rootCount_comp_affine (Q : ℤ[X]) (q : ℕ) (a : ℤ) (n : ℕ)
    (hqa : q.Coprime (Q.eval a).natAbs) :
    rootCount (Q.comp (affinePolynomial q a)) n = if q.Coprime n then rootCount Q n else 0 := by
  by_cases hqn : q.Coprime n
  · rw [ite_eq_left hqn, rootCount_comp_affine_of_coprime Q q a n hqn]
  · rw [ite_eq_right hqn, rootCount_comp_affine_eq_zero Q q a n hqa hqn]

/-- A permitted arithmetic progression preserves absence of fixed prime
divisors, as required when applying Theorem 1 to the substituted family. -/
theorem NoFixedPrimeDivisor.comp_affine {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (q : ℕ) (a : ℤ) (hqa : q.Coprime (Q.eval a).natAbs) :
    NoFixedPrimeDivisor (Q.comp (affinePolynomial q a)) := by
  intro p hp
  rw [rootCount_comp_affine Q q a p hqa]
  split_ifs
  · exact hQ p hp
  · exact hp.pos

/-- The Euler product in the arithmetic-progression corollaries omits primes
that divide the progression modulus. -/
noncomputable def progressionSieveProduct (Q : ℤ[X]) (q : ℕ) (x : ℝ) : ℝ :=
  ∏ p ∈ ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).filter (fun p => ¬p ∣ q),
    (1 - (rootCount Q p : ℝ) / p)

/-- The sieve product for the substituted polynomial is exactly the original
product with primes dividing the progression modulus omitted. -/
theorem sieveProduct_comp_affine (Q : ℤ[X]) (q : ℕ) (a : ℤ) (x : ℝ)
    (hqa : q.Coprime (Q.eval a).natAbs) :
    sieveProduct (Q.comp (affinePolynomial q a)) x = progressionSieveProduct Q q x := by
  classical
  unfold sieveProduct progressionSieveProduct
  conv_rhs => rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  have H : q.Coprime p ↔ ¬p ∣ q := Nat.coprime_comm.trans
    (Finset.mem_filter.mp hp).2.coprime_iff_not_dvd
  rw [rootCount_comp_affine Q q a p hqa]
  by_cases h : q.Coprime p
  · simp only [ite_eq_left h, ite_eq_left (H.mp h)]
  · have h' : ¬¬p ∣ q := fun h' => h (H.mpr h')
    simp only [ite_eq_right h, ite_eq_right h', Nat.cast_zero, zero_div, sub_zero]

end NairTenenbaum
