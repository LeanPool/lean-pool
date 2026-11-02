/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Equiv
import LeanPool.CCDN.Algebra.PolynomialPrimeLocalization
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.Monic

/-! Ordinary irreducibility of the generic stretching substitution
f(x,z) -> f(x,y*z). The fresh variable y is first made invertible; scaling
then becomes a polynomial automorphism. Monicity in x descends irreducibility
back to the polynomial coefficient ring. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma optionEquivLeft_map_coefficients {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : MvPolynomial (Option σ) R) :
    optionEquivLeft S σ (MvPolynomial.map φ f) =
      Polynomial.map (MvPolynomial.map φ) (optionEquivLeft R σ f) := by
  have he : (optionEquivLeft S σ).toRingHom.comp (MvPolynomial.map φ) =
      (Polynomial.mapRingHom (MvPolynomial.map φ)).comp (optionEquivLeft R σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      cases i <;> simp [optionEquivLeft_apply]
  exact RingHom.congr_fun he f

/-- Simultaneously multiply all polynomial variables by a nonzero scalar. -/
def variableScaleEquiv (K σ : Type*) [Field K] (a : K) (ha : a ≠ 0) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (aeval (fun i => C a * X i))
    (aeval (fun i => C a⁻¹ * X i))
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
      simp only [map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
      simp only [map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul])

/-- The scaling automorphism by `a` sends each variable `X i` to `a * X i`. -/
@[simp] lemma variableScaleEquiv_X {K σ : Type*} [Field K]
    (a : K) (ha : a ≠ 0) (i : σ) :
    variableScaleEquiv K σ a ha (X i) = C a * X i := by
  simp [variableScaleEquiv]

/-- Introduce a fresh polynomial parameter and scale each transverse variable
by that parameter, keeping the distinguished outer variable fixed. -/
def genericStretchCoefficients (K σ : Type*) [Field K] :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ (MvPolynomial Unit K) :=
  aeval (fun i => C (X ()) * X i)

/-- The generic stretch `f(x, z) ↦ f(x, y * z)` of `f`, viewed as a polynomial in the distinguished
outer variable `x` whose coefficients involve the transverse variables `z` and the fresh
parameter `y`. -/
def genericPlaneStretch {K σ : Type*} [Field K]
    (f : MvPolynomial (Option σ) K) :
    Polynomial (MvPolynomial σ (MvPolynomial Unit K)) :=
  Polynomial.map (genericStretchCoefficients K σ).toRingHom (optionEquivLeft K σ f)

private lemma genericPlaneStretch_monic {K σ : Type*} [Field K]
    (f : MvPolynomial (Option σ) K) (hf : (optionEquivLeft K σ f).Monic) :
    (genericPlaneStretch f).Monic := hf.map _

/-- The generic stretch is ordinarily irreducible before any slope parameters
are specialized or localized. -/
theorem genericPlaneStretch_irreducible {K σ : Type*} [Field K]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : 0 < f.totalDegree) (hm : (optionEquivLeft K σ f).Monic) :
    Irreducible (genericPlaneStretch f) := by
  let R := MvPolynomial Unit K
  let F := FractionRing R
  let ι : R →+* F := algebraMap R F
  let κ : K →+* F := ι.comp C
  let y : F := ι (X ())
  have hy : y ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (X_ne_zero ())
  let e := Polynomial.mapAlgEquiv (variableScaleEquiv F σ y hy)
  have hbase : Irreducible (optionEquivLeft F σ (MvPolynomial.map κ f)) :=
    (MulEquiv.irreducible_iff (f := optionEquivLeft F σ)).mpr
      (irreducible_mvPolynomial_map_fraction_parameters f hf hd)
  have hi : Irreducible (e (optionEquivLeft F σ (MvPolynomial.map κ f))) :=
    (MulEquiv.irreducible_iff (f := e)).mpr hbase
  apply Polynomial.Monic.irreducible_of_irreducible_map
    (MvPolynomial.map ι) (genericPlaneStretch f) (genericPlaneStretch_monic f hm)
  have he : (MvPolynomial.map ι).comp (genericStretchCoefficients K σ).toRingHom =
      (variableScaleEquiv F σ y hy).toRingHom.comp (MvPolynomial.map κ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [genericStretchCoefficients, κ, ι, variableScaleEquiv]
    · intro i
      simp [genericStretchCoefficients, y, variableScaleEquiv]
  change Irreducible (Polynomial.map (variableScaleEquiv F σ y hy).toRingHom
    (optionEquivLeft F σ (MvPolynomial.map κ f))) at hi
  rw [optionEquivLeft_map_coefficients, Polynomial.map_map] at hi
  simpa only [genericPlaneStretch, Polynomial.map_map, he] using hi

end
end CCDN
