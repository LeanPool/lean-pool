/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Stepanov.Defect
public import Mathlib.FieldTheory.Finite.GaloisField


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# The Artin–Schreier Kloosterman curve

Specializes the point-count argument to `y² = (x^p-x)²-4c` over finite extensions,
following Harcos (2015), equation (3).
-/

@[expose] public section

open Polynomial

namespace KloostermanWeil.Stepanov

/-- The additive Artin–Schreier polynomial `X^p-X`. -/
noncomputable def kloostermanArtinSchreier (p n : ℕ) [Fact p.Prime] :
    (GaloisField p n)[X] := X ^ p - X

/-- The affine curve polynomial occurring in Harcos equation (3). -/
noncomputable def kloostermanCurvePolynomial (p n : ℕ) [Fact p.Prime]
    (c : ZMod p) : (GaloisField p n)[X] :=
  (kloostermanArtinSchreier p n) ^ 2 -
    C (algebraMap (ZMod p) (GaloisField p n) (4 * c))

/-- The Artin–Schreier polynomial has derivative `-1`. -/
theorem derivative_kloostermanArtinSchreier (p n : ℕ) [Fact p.Prime] :
    derivative (kloostermanArtinSchreier p n) = -1 := by
  unfold kloostermanArtinSchreier
  rw [derivative_sub, derivative_X_pow, derivative_X]
  have hpzero : (p : GaloisField p n) = 0 := CharP.cast_eq_zero _ p
  rw [hpzero]
  simp

/-- The exact degree of `X^p-X`. -/
theorem natDegree_kloostermanArtinSchreier (p n : ℕ) [Fact p.Prime] :
    (kloostermanArtinSchreier p n).natDegree = p := by
  unfold kloostermanArtinSchreier
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow p
  · rw [natDegree_X_pow, natDegree_X]
    exact (show p.Prime from Fact.out).one_lt

/-- Harcos's curve polynomial has degree exactly `2p`. -/
theorem natDegree_kloostermanCurvePolynomial
    (p n : ℕ) [Fact p.Prime] (c : ZMod p) :
    (kloostermanCurvePolynomial p n c).natDegree = 2 * p := by
  unfold kloostermanCurvePolynomial
  rw [natDegree_sub_C, natDegree_pow,
    natDegree_kloostermanArtinSchreier]

/-- In odd prime characteristic, the scalar `4c` stays nonzero in every
finite extension whenever `c` is nonzero. -/
theorem map_four_mul_ne_zero
    (p n : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) :
    algebraMap (ZMod p) (GaloisField p n) (4 * c) ≠ 0 := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
  have hpne2 : p ≠ 2 := by omega
  have h4p : ¬ p ∣ 4 := by
    intro hd
    have hp2 : p ∣ 2 := by
      have hpow : p ∣ 2 ^ 2 := by
        simpa [pow_two] using hd
      exact hp.dvd_of_dvd_pow hpow
    have hpeq : p = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left hp.ne_one
    exact hpne2 hpeq
  have h4z : (4 : ZMod p) ≠ 0 := by
    exact fun h => h4p ((CharP.cast_eq_zero_iff (ZMod p) p 4).mp h)
  have h4c : (4 : ZMod p) * c ≠ 0 := mul_ne_zero h4z hc
  intro hz
  apply h4c
  apply FaithfulSMul.algebraMap_injective (ZMod p) (GaloisField p n)
  simpa using hz

/-- The constant coefficient needed by the Stepanov construction is
nonzero. -/
theorem coeff_zero_kloostermanCurvePolynomial_ne_zero
    (p n : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) :
    (kloostermanCurvePolynomial p n c).coeff 0 ≠ 0 := by
  have hmap := map_four_mul_ne_zero p n hpodd c hc
  have hp0 : p ≠ 0 := (show p.Prime from Fact.out).ne_zero
  simpa [kloostermanCurvePolynomial, kloostermanArtinSchreier,
    coeff_zero_eq_eval_zero, hp0] using neg_ne_zero.mpr hmap

/-- The curve polynomial is separable. -/
theorem separable_kloostermanCurvePolynomial
    (p n : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) :
    (kloostermanCurvePolynomial p n c).Separable := by
  apply separable_sq_sub_C_of_derivative_eq_neg_one
  · exact derivative_kloostermanArtinSchreier p n
  · exact map_four_mul_ne_zero p n hpodd c hc
  · intro htwo
    have hpdiv : p ∣ 2 :=
      (CharP.cast_eq_zero_iff (GaloisField p n) p 2).mp htwo
    have hp : p.Prime := Fact.out
    have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
    have hpne2 : p ≠ 2 := by omega
    have hpeq : p = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp hpdiv |>.resolve_left hp.ne_one
    exact hpne2 hpeq

/-- The separable positive-degree curve polynomial is not a scalar square,
which is the exact nondegeneracy hypothesis in Stepanov's theorem. -/
theorem not_isScalarSquare_kloostermanCurvePolynomial
    (p n : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) :
    ¬ IsScalarSquare (kloostermanCurvePolynomial p n c) := by
  apply not_isScalarSquare_of_separable _
    (separable_kloostermanCurvePolynomial p n hpodd c hc)
  rw [natDegree_kloostermanCurvePolynomial]
  have hp : 0 < p := (show p.Prime from Fact.out).pos
  omega

/-- Uniform high-extension estimate for the exact curve in Harcos equation
(3).  The constant depends on `p` but not on the extension degree `n`. -/
theorem kloostermanCurve_defect_high_extension
    (p n : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) (hn : n ≠ 0)
    (hlarge : 100 * (2 * p + 1) * (Nat.sqrt (p ^ n) + 1) < p ^ n) :
    letI := Fintype.ofFinite (GaloisField p n)
    |((hyperellipticAffinePointFinset
        (kloostermanCurvePolynomial p n c)).card : ℤ) - (p ^ n : ℕ)| <
      (80 * (2 * p + 1) * (Nat.sqrt (p ^ n) + 1) + 1 : ℕ) := by
  classical
  let := Fintype.ofFinite (GaloisField p n)
  have hcard : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p n hn
  let f := kloostermanCurvePolynomial p n c
  have hdeg : f.natDegree = 2 * p :=
    natDegree_kloostermanCurvePolynomial p n c
  have hf : f ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hdeg
    have hp : 0 < p := (show p.Prime from Fact.out).pos
    omega
  have hm : 3 < f.natDegree := by
    rw [hdeg]
    have hp : 2 ≤ p := (show p.Prime from Fact.out).two_le
    omega
  have h := stepanov_hyperelliptic_defect_high_field hcard hpodd f hf hm
    (by simpa [hdeg] using hlarge)
    (coeff_zero_kloostermanCurvePolynomial_ne_zero p n hpodd c hc)
    (not_isScalarSquare_kloostermanCurvePolynomial p n hpodd c hc)
  simpa [f, hdeg] using h

end KloostermanWeil.Stepanov
