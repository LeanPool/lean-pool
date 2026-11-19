/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.Squarefree.Basic

import Mathlib.Algebra.MvPolynomial.Division
import LeanPool.Ratpoints.Mathlib.Algebra.Squarefree.Basic
import LeanPool.Ratpoints.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Squarefree homogenizations and the reflection

Candidates for `Mathlib.Algebra.Polynomial.Homogenize`: when the homogenization of a polynomial is
squarefree, and the homogenization of its reflection.

## Main statements

* `Polynomial.homogenize_eq_homogenize_natDegree_mul`: the homogenizations of `p` of degree
  `n ≥ p.natDegree` are that of degree `p.natDegree` times powers of the second variable.
* `Polynomial.squarefree_of_squarefree_homogenize`: over a commutative semiring without zero
  divisors, a polynomial with a squarefree homogenization is squarefree.
* `Polynomial.squarefree_homogenize_iff`: for a polynomial `p` over a domain and
  `n ≥ p.natDegree`, the homogenization of degree `n` is squarefree if and only if `p` is
  squarefree and `n ≤ p.natDegree + 1`.
* `Polynomial.homogenize_reflect`: the homogenization of degree `n` of the reflection of `p` in
  degree `n` is that of `p` with the two variables exchanged, for every `p` and `n`.
* `Polynomial.squarefree_homogenize_reflect_iff`: so the reflection does not change whether the
  homogenization is squarefree.
* `Polynomial.squarefree_homogenize_iff_squarefree_reflect`: for `n ≥ p.natDegree`, the
  homogenization of degree `n` of a polynomial over a domain is squarefree exactly when the
  reflection of `p` in degree `n` is, if `n` exceeds the degree of the reflection by at most one.

## Proof

For `n ≥ p.natDegree + 2`, `X 1 ^ 2` divides the homogenization
(`Polynomial.homogenize_eq_homogenize_natDegree_mul`), and if `a * a` divides `p`, the square of the
homogenization of `a` divides it (`Polynomial.squarefree_of_squarefree_homogenize`). Conversely, let
`A * A` divide the homogenization for `n ≤ p.natDegree + 1`: then `A` is homogeneous
(`MvPolynomial.IsHomogeneous.of_mul_left`), `X 1` does not divide it, since
`X 1 ^ (n - p.natDegree)` is the largest power of `X 1` that divides the homogenization
(`Polynomial.not_X_one_dvd_homogenize_natDegree`), and the square of its value at `(X, 1)` divides
`p`, so that this value is a unit; hence `A` is a unit. The reflection compares the coefficients of
the two homogenizations, and the exchange of the variables is a ring automorphism, which preserves
squarefreeness (`MulEquiv.squarefree_iff`). Mathlib's file does not import squarefreeness.
-/

@[expose] public section

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R] {p : R[X]} {n : ℕ}

/-- For `n ≥ p.natDegree`, the homogenization of degree `n` of `p` is that of degree `p.natDegree`
times the power `n - p.natDegree` of the second variable. -/
theorem homogenize_eq_homogenize_natDegree_mul (hn : p.natDegree ≤ n) :
    p.homogenize n = p.homogenize p.natDegree * MvPolynomial.X 1 ^ (n - p.natDegree) := by
  simpa [Nat.add_sub_cancel' hn] using
    homogenize_mul p 1 le_rfl (natDegree_one.trans_le (n - p.natDegree).zero_le)

/-- The second variable does not divide the homogenization of degree `p.natDegree` of a polynomial
`p ≠ 0`: the coefficient of `X 0 ^ p.natDegree` there is the leading coefficient of `p`, while every
multiple of `X 1` has the coefficient `0` there. -/
theorem not_X_one_dvd_homogenize_natDegree (hp : p ≠ 0) :
    ¬ MvPolynomial.X 1 ∣ p.homogenize p.natDegree := fun ⟨q, hq⟩ ↦ by
  have := congr(($hq).coeff (Finsupp.single 0 p.natDegree))
  simp [coeff_homogenize, MvPolynomial.coeff_X_mul', hp] at this

/-- A polynomial over a commutative semiring without zero divisors is squarefree if some
homogenization of it is, of degree `n ≥ p.natDegree`. -/
theorem squarefree_of_squarefree_homogenize [NoZeroDivisors R] (hn : p.natDegree ≤ n)
    (h : Squarefree (p.homogenize n)) : Squarefree p := fun a ha ↦ by
  have hd : (a * a).natDegree = a.natDegree + a.natDegree := by rw [← sq, natDegree_pow, two_mul]
  have := (homogenize_dvd ha).trans ⟨_, homogenize_eq_homogenize_natDegree_mul hn⟩
  rw [hd, homogenize_mul _ _ le_rfl le_rfl] at this
  simpa using (h _ this).map (MvPolynomial.aeval ![(X : R[X]), 1])

variable (p n) in
/-- The homogenization of degree `n` of the reflection of `p` in degree `n` is that of `p` with
the two variables exchanged, for every `p` and `n`: both see only the coefficients of `p` up to
`n`. -/
theorem homogenize_reflect :
    (p.reflect n).homogenize n = MvPolynomial.rename (Equiv.swap 0 1) (p.homogenize n) := by
  ext m
  obtain ⟨m, rfl⟩ := Finsupp.mapDomain_surjective (Equiv.swap (0 : Fin 2) 1).surjective m
  rw [MvPolynomial.coeff_rename_mapDomain _ (Equiv.injective _), coeff_homogenize,
    coeff_homogenize, coeff_reflect]
  simp [Finsupp.mapDomain_equiv_apply]
  grind [revAt_le]

variable (p n) in
theorem squarefree_homogenize_reflect_iff :
    Squarefree ((p.reflect n).homogenize n) ↔ Squarefree (p.homogenize n) := by
  rw [homogenize_reflect, ← MvPolynomial.renameEquiv_apply R]
  exact MulEquiv.squarefree_iff _

end CommSemiring

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R] {p : R[X]} {n : ℕ}

-- For `n ≥ p.natDegree + 2`, `X 1 ^ 2` divides `p.homogenize n`.
private theorem le_natDegree_add_one_of_squarefree_homogenize (hn : p.natDegree ≤ n)
    (h : Squarefree (p.homogenize n)) : n ≤ p.natDegree + 1 := by
  by_contra! hlt
  refine MvPolynomial.X_prime.not_isUnit (h (MvPolynomial.X 1) ?_)
  rw [homogenize_eq_homogenize_natDegree_mul hn, ← sq]
  exact (pow_dvd_pow _ (by lia)).mul_left _

-- For `n ≤ p.natDegree + 1`, `X 1` divides no `A` with `A * A ∣ p.homogenize n`.
private theorem not_X_one_dvd_of_mul_self_dvd_homogenize (hp : p ≠ 0) (hn : p.natDegree ≤ n)
    (h : n ≤ p.natDegree + 1) {A : MvPolynomial (Fin 2) R} (hA : A * A ∣ p.homogenize n) :
    ¬ MvPolynomial.X 1 ∣ A := fun hX ↦ by
  rw [homogenize_eq_homogenize_natDegree_mul hn, ← sq] at hA
  have := MvPolynomial.X_prime.pow_dvd_of_dvd_mul_left 2 (not_X_one_dvd_homogenize_natDegree hp)
    ((pow_dvd_pow_of_dvd hX 2).trans hA)
  rw [pow_dvd_pow_iff (MvPolynomial.X_ne_zero 1) MvPolynomial.X_prime.not_isUnit] at this
  lia

-- A homogeneous `A` that `X 1` does not divide is a unit if its value at `(X, 1)` is one.
private theorem isUnit_of_isHomogeneous {A : MvPolynomial (Fin 2) R}
    (hA : A.IsHomogeneous A.totalDegree) (hX : ¬ MvPolynomial.X 1 ∣ A)
    (h : IsUnit (MvPolynomial.aeval ![(X : R[X]), 1] A)) : IsUnit A := by
  obtain ⟨u, hu, hua⟩ := Polynomial.isUnit_iff.mp h
  have hAC := homogenize_eq_of_isHomogeneous hA hua.symm
  rw [homogenize_C] at hAC
  obtain h0 | h0 := eq_or_ne A.totalDegree 0
  · rw [← hAC, h0, pow_zero, mul_one]
    exact hu.map _
  · exact absurd (hAC ▸ (dvd_pow_self _ h0).mul_left _) hX

-- A squarefree polynomial has a squarefree homogenization of degree `n ≤ p.natDegree + 1`.
private theorem squarefree_homogenize (hp : Squarefree p) (hn : p.natDegree ≤ n)
    (h : n ≤ p.natDegree + 1) : Squarefree (p.homogenize n) := fun A ⟨B, hB⟩ ↦ by
  have hF : A * (A * B) ≠ 0 :=
    mul_assoc A A B ▸ hB ▸ (homogenize_eq_zero_iff hn).not.mpr hp.ne_zero
  refine isUnit_of_isHomogeneous ((mul_assoc A A B ▸ hB ▸ isHomogeneous_homogenize p).of_mul_left
    (right_ne_zero_of_mul hF)) (not_X_one_dvd_of_mul_self_dvd_homogenize hp.ne_zero hn h ⟨B, hB⟩)
    (hp _ ⟨MvPolynomial.aeval ![(X : R[X]), 1] B, ?_⟩)
  rw [← map_mul, ← map_mul, ← hB, aeval_homogenize_X_one p hn]

/-- The homogenization of degree `n ≥ p.natDegree` of a polynomial `p` over a domain is squarefree
if and only if `p` is squarefree and `n` exceeds the degree of `p` by at most one; for larger `n`,
`X 1 ^ 2` divides it. -/
theorem squarefree_homogenize_iff (hn : p.natDegree ≤ n) :
    Squarefree (p.homogenize n) ↔ Squarefree p ∧ n ≤ p.natDegree + 1 :=
  ⟨fun h ↦ ⟨squarefree_of_squarefree_homogenize hn h,
    le_natDegree_add_one_of_squarefree_homogenize hn h⟩, fun h ↦ squarefree_homogenize h.1 hn h.2⟩

/-- For `n ≥ p.natDegree`, the homogenization of degree `n` of a polynomial `p` over a domain is
squarefree exactly when the reflection of `p` in degree `n` is, if `n` exceeds the degree of the
reflection by at most one: the homogenization of degree `n` of the reflection is that of `p` with
the variables exchanged (`Polynomial.homogenize_reflect`). -/
theorem squarefree_homogenize_iff_squarefree_reflect (hn : p.natDegree ≤ n)
    (h : n ≤ (p.reflect n).natDegree + 1) :
    Squarefree (p.homogenize n) ↔ Squarefree (p.reflect n) := by
  rw [← squarefree_homogenize_reflect_iff,
    squarefree_homogenize_iff (natDegree_reflect_le.trans (by lia)), and_iff_left h]

end IsDomain

end Polynomial

end
