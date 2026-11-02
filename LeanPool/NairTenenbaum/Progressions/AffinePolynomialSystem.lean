/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialStructure
public import LeanPool.NairTenenbaum.Progressions.AffineRootCounts

/-! # Polynomial systems after arithmetic-progression substitution -/

@[expose] public section

namespace NairTenenbaum

open Polynomial

/-- Over the rationals an affine substitution with nonzero slope is an algebra
automorphism, so it preserves irreducible factors and their nonassociation. -/
noncomputable def rationalAffineEquiv (q : ℕ) (a : ℤ) (hq : q ≠ 0) : ℚ[X] ≃ₐ[ℚ] ℚ[X] := by
  letI : Invertible (q : ℚ) := invertibleOfNonzero (by exact_mod_cast hq)
  exact Polynomial.algEquivCMulXAddC (q : ℚ) (a : ℚ)

theorem rationalAffineEquiv_map (q : ℕ) (a : ℤ) (hq : q ≠ 0) (Q : ℤ[X]) :
    rationalAffineEquiv q a hq (Q.map (Int.castRingHom ℚ)) =
      (Q.comp (affinePolynomial q a)).map (Int.castRingHom ℚ) := by
  simp only [rationalAffineEquiv, Polynomial.algEquivCMulXAddC_apply, ← Polynomial.comp_eq_aeval,
    Polynomial.map_comp, affinePolynomial, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X]
  congr 2

@[simp] theorem natDegree_affinePolynomial {q : ℕ} (hq : q ≠ 0) (a : ℤ) :
    (affinePolynomial q a).natDegree = 1 := by
  rw [affinePolynomial, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X]
  exact_mod_cast hq

/-- The substituted polynomial family, with all factorization hypotheses proved
from the original family and the progression's coprimality condition. -/
noncomputable def PolynomialSystem.affine {k r : ℕ} (P : PolynomialSystem k r)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) (hqa : q.Coprime (P.total.eval a).natAbs) : PolynomialSystem k r
        where
  Q := fun j => (P.Q j).comp (affinePolynomial q a)
  R := fun i => (P.R i).comp (affinePolynomial q a)
  exponent := P.exponent
  sign := P.sign
  sign_abs := P.sign_abs
  factorization := by
    intro j
    rw [P.factorization j, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.prod_comp]
    simp only [Polynomial.pow_comp]
  irreducible := by
    intro i
    rw [← rationalAffineEquiv_map q a hq]
    exact (MulEquiv.irreducible_iff (f := rationalAffineEquiv q a hq)).mpr (P.irreducible i)
  nonassociated := by
    intro i j hij h
    rw [← rationalAffineEquiv_map q a hq, ← rationalAffineEquiv_map q a hq] at h
    apply P.nonassociated i j hij
    have H := h.map (rationalAffineEquiv q a hq).symm.toMonoidHom
    change Associated ((rationalAffineEquiv q a hq).symm
      ((rationalAffineEquiv q a hq) ((P.R i).map (Int.castRingHom ℚ))))
      ((rationalAffineEquiv q a hq).symm
      ((rationalAffineEquiv q a hq) ((P.R j).map (Int.castRingHom ℚ)))) at H
    simpa only [AlgEquiv.symm_apply_apply] using H
  exponent_pos := P.exponent_pos
  noFixedPrime := by
    rw [← Polynomial.prod_comp]
    exact P.noFixedPrime.comp_affine q a hqa

@[simp] theorem PolynomialSystem.affine_total {k r : ℕ} (P : PolynomialSystem k r)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) (hqa : q.Coprime (P.total.eval a).natAbs) :
    (P.affine q a hq hqa).total = P.total.comp (affinePolynomial q a) := by
  simp only [PolynomialSystem.total, PolynomialSystem.affine, Polynomial.prod_comp]

@[simp] theorem PolynomialSystem.affine_radical {k r : ℕ} (P : PolynomialSystem k r)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) (hqa : q.Coprime (P.total.eval a).natAbs) :
    (P.affine q a hq hqa).radical = P.radical.comp (affinePolynomial q a) := by
  simp only [PolynomialSystem.radical, PolynomialSystem.affine, Polynomial.prod_comp]

theorem PolynomialSystem.affine_degree {k r : ℕ} (P : PolynomialSystem k r)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) (hqa : q.Coprime (P.total.eval a).natAbs) :
    (P.affine q a hq hqa).total.natDegree = P.total.natDegree := by
  rw [P.affine_total, Polynomial.natDegree_comp, natDegree_affinePolynomial hq, mul_one]

/-- The transformed irreducible root counts vanish precisely on the moduli
excluded by the progression; on coprime moduli they are unchanged. -/
theorem PolynomialSystem.affine_factor_rootCount {k r : ℕ} (P : PolynomialSystem k r)
    (q : ℕ) (a : ℤ) (hq : q ≠ 0) (hqa : q.Coprime (P.total.eval a).natAbs) (i : Fin r) (n : ℕ) :
    rootCount ((P.affine q a hq hqa).R i) n = if q.Coprime n then rootCount (P.R i) n else 0 := by
  apply rootCount_comp_affine
  exact hqa.of_dvd_right (Int.natAbs_dvd_natAbs.mpr (Polynomial.eval_dvd (P.factor_dvd_total i)))

end NairTenenbaum
