/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Radial scaling `X j ↦ X j * T` of a multivariate polynomial; the coefficient of
`T ^ n` is the homogeneous component of degree `n`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Replace every coordinate by itself times the same scalar parameter. -/
def radialMap {K σ : Type*} [CommRing K] :
    MvPolynomial σ K →+* Polynomial (MvPolynomial σ K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun j => Polynomial.C (MvPolynomial.X j) * Polynomial.X)

/-- The radial map sends a constant `C c` to the constant polynomial `C (C c)`. -/
@[simp] lemma radialMap_C {K σ : Type*} [CommRing K] (c : K) :
    radialMap (MvPolynomial.C c : MvPolynomial σ K) = Polynomial.C (MvPolynomial.C c) := by
  simp [radialMap]

/-- The radial map sends the variable `X j` to `X j * T`. -/
@[simp] lemma radialMap_X {K σ : Type*} [CommRing K] (j : σ) :
    radialMap (MvPolynomial.X j : MvPolynomial σ K) =
      Polynomial.C (MvPolynomial.X j) * Polynomial.X := by simp [radialMap]

private lemma radialMap_monomial {K σ : Type*} [CommRing K] (e : σ →₀ ℕ) (c : K) :
    radialMap (monomial e c) = Polynomial.C (monomial e c) * Polynomial.X ^ e.degree := by
  classical
  rw [monomial_eq, map_mul, radialMap_C, map_finsuppProd]
  simp only [map_pow, radialMap_X, mul_pow]
  rw [Finsupp.prod_mul]
  simp only [← map_pow, Finsupp.prod]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum]
  rw [← mul_assoc, ← Polynomial.C_mul]
  rfl

/-- The coefficient of `T ^ n` in the radial image of `f` is the homogeneous component of
`f` of degree `n`. -/
lemma radialMap_coeff {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) (n : ℕ) :
    (radialMap f).coeff n = homogeneousComponent n f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, Polynomial.coeff_add, hf, hg]
  | monomial e c =>
    rw [radialMap_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
    split_ifs <;> simp_all

/-- The radial map is injective, since evaluating at `T = 1` recovers the polynomial. -/
lemma radialMap_injective {K σ : Type*} [CommRing K] :
    Function.Injective (radialMap : MvPolynomial σ K →+* Polynomial (MvPolynomial σ K)) := by
  have he : (Polynomial.evalRingHom 1).comp
      (radialMap : MvPolynomial σ K →+* Polynomial (MvPolynomial σ K)) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp
  exact Function.LeftInverse.injective (fun p => RingHom.congr_fun he p)

/-- The constant coefficient of the radial image of `f` is the constant `f(0)`. -/
lemma constantCoeff_comp_radialMap {K σ : Type*} [CommRing K] :
    Polynomial.constantCoeff.comp
      (radialMap : MvPolynomial σ K →+* Polynomial (MvPolynomial σ K)) =
      C.comp (eval (fun _ => (0 : K))) := by
  apply MvPolynomial.ringHom_ext <;> intro <;> simp

end
end CCDN
