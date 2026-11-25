/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.StandardHermitianTwoForm
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.StandardKahlerTopPower

/-!
# The exterior-power/determinant density identity in every dimension

`actualTopPowerDensity A` is the genuine top exterior power of a real two-form
evaluated on the standard interleaved real frame, and `normalizedTopPowerDensity A`
is the determinant of the complex coefficient matrix recovered from `A`.  The two
were previously known to agree only in complex dimensions `0`, `1` and `2`
(`CoordinateDensityLowDim`, `CoordinateDensityTwo`), and in every dimension for a
form with diagonal real-frame blocks (`StandardKahlerTopPower`).

This file proves the identity in every dimension for a real `(1,1)`-form with
semipositive coefficients — the case in which the restricted-mass densities of
this project are evaluated.  The argument avoids the general Pfaffian shuffle
computation entirely:

* a semipositive real `(1,1)`-form on `ℂⁿ` is literally the pullback
  `ω(S ·, S ·)` of the standard Hermitian form by a `ℂ`-linear map `S`
  (`exists_linearMap_eq_standard_compContinuousLinearMap`);
* the top power of a pullback multiplies by the real determinant
  (`actualTopPowerDensity_compContinuousLinearMap`), and on the standard form it
  is `n!` (`actualTopPowerDensity_eq_factorial_of_apply_eq_im`), so the actual
  density is `|det_ℂ S|² n!` by `normSq_det_eq_realDet`;
* the coefficient matrix of that pullback is `π` times the conjugate of the Gram
  matrix `⟪S eⱼ, S e_k⟫`, whose determinant is `|det_ℂ S|²`, so the normalized
  density is the same number.

Consequently the coordinate density used by `acTopMass` is the Bedford--Taylor
determinant density in every dimension, not only for `dim ≤ 2`.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder Matrix

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

section Gram

private theorem conj_eq_re_sub_I_mul_im (z : ℂ) :
    (starRingEnd ℂ) z = (z.re : ℂ) - Complex.I * (z.im : ℂ) := by
  apply Complex.ext <;> simp

/-- The matrix of a `ℂ`-linear endomorphism of `ℂⁿ` in the standard basis. -/
def standardMatrix (S : ComplexModel n →ₗ[ℂ] ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis S

theorem standardMatrix_apply (S : ComplexModel n →ₗ[ℂ] ComplexModel n) (p j : Fin n) :
    standardMatrix S p j = S (coordinateVector j) p := by
  simp [standardMatrix, LinearMap.toMatrix_apply, coordinateVector]

theorem det_standardMatrix (S : ComplexModel n →ₗ[ℂ] ComplexModel n) :
    (standardMatrix S).det = LinearMap.det S :=
  LinearMap.det_toMatrix _ S

/-- The Gram matrix `⟪S eⱼ, S e_k⟫` of the images of the standard basis. -/
def gramMatrix (S : ComplexModel n →ₗ[ℂ] ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => inner ℂ (S (coordinateVector j)) (S (coordinateVector k))

theorem gramMatrix_eq (S : ComplexModel n →ₗ[ℂ] ComplexModel n) :
    gramMatrix S = (standardMatrix S)ᴴ * standardMatrix S := by
  ext j k
  simp only [gramMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    standardMatrix_apply, PiLp.inner_apply, RCLike.inner_apply]
  exact Finset.sum_congr rfl fun x _ => by rw [Complex.star_def]; ring

/-- The Gram determinant of a `ℂ`-linear endomorphism is the squared modulus of
its complex determinant. -/
theorem det_gramMatrix (S : ComplexModel n →ₗ[ℂ] ComplexModel n) :
    (gramMatrix S).det = (Complex.normSq (LinearMap.det S) : ℝ) := by
  rw [gramMatrix_eq, Matrix.det_mul, Matrix.det_conjTranspose, det_standardMatrix,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]

end Gram

section Pullback

variable (S : ComplexModel n →ₗ[ℂ] ComplexModel n)

/-- The pullback of the standard Hermitian form along a `ℂ`-linear map. -/
def standardPullback (S : ComplexModel n →ₗ[ℂ] ComplexModel n) :
    CoordinateRealTwoForm n :=
  (standardHermitianTwoForm n).compContinuousLinearMap
    (LinearMap.toContinuousLinearMap (S.restrictScalars ℝ))

@[simp] theorem standardPullback_apply (v w : ComplexModel n) :
    standardPullback S ![v, w] = (inner ℂ (S v) (S w)).im :=
  standardHermitianTwoForm_compContinuousLinearMap_apply S v w

/-- The genuine top exterior-power density of a pullback of the standard form. -/
theorem actualTopPowerDensity_standardPullback :
    actualTopPowerDensity (standardPullback S) =
      Complex.normSq (LinearMap.det S) * (n.factorial : ℝ) := by
  rw [standardPullback, actualTopPowerDensity_compContinuousLinearMap,
    actualTopPowerDensity_eq_factorial_of_apply_eq_im _ standardHermitianTwoForm_apply]
  congr 1
  rw [← normSq_det_eq_realDet]
  rfl

/-- The complex coefficient matrix of a pullback of the standard form is `π`
times the conjugate Gram matrix. -/
theorem normalizedHermitianMatrix_standardPullback :
    normalizedHermitianMatrix (standardPullback S) =
      (Real.pi : ℂ) • (gramMatrix S).map (starRingEnd ℂ) := by
  ext j k
  have h1 : standardPullback S ![coordinateVector j, Complex.I • coordinateVector k] =
      (inner ℂ (S (coordinateVector j)) (S (coordinateVector k)) : ℂ).re := by
    rw [standardPullback_apply, map_smul, inner_smul_right]
    simp [Complex.mul_im]
  have h2 : standardPullback S ![coordinateVector j, coordinateVector k] =
      (inner ℂ (S (coordinateVector j)) (S (coordinateVector k)) : ℂ).im :=
    standardPullback_apply S _ _
  rw [normalizedHermitianMatrix, h1, h2]
  simp only [Matrix.smul_apply, Matrix.map_apply, gramMatrix, Matrix.of_apply, smul_eq_mul,
    conj_eq_re_sub_I_mul_im]

/-- The determinant normalization of a pullback of the standard form. -/
theorem normalizedTopPowerDensity_standardPullback :
    normalizedTopPowerDensity (standardPullback S) =
      Complex.normSq (LinearMap.det S) * (n.factorial : ℝ) := by
  have hpi : (Real.pi : ℝ) ^ n ≠ 0 := by positivity
  have hconj : ((gramMatrix S).map (starRingEnd ℂ)).det =
      starRingEnd ℂ ((gramMatrix S).det) :=
    (RingHom.map_det (starRingEnd ℂ) (gramMatrix S)).symm
  have hdet : (normalizedHermitianMatrix (standardPullback S)).det =
      ((Real.pi ^ n * Complex.normSq (LinearMap.det S) : ℝ) : ℂ) := by
    rw [normalizedHermitianMatrix_standardPullback, Matrix.det_smul, hconj, det_gramMatrix,
      Complex.conj_ofReal, Fintype.card_fin]
    push_cast
    ring
  rw [normalizedTopPowerDensity, complexTopCoefficient_eq, hdet, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  field_simp

end Pullback

/-- **The exterior-power/determinant density identity in every dimension**, for a
semipositive real `(1,1)`-form.  This removes the `dim ≤ 2` restriction from the
coordinate densities used by the restricted masses. -/
theorem actualTopPowerDensity_eq_normalizedTopPowerDensity_of_semipositive
    (A : CoordinateRealTwoForm n) (hA : IsOneOne A)
    (hpos : PositiveClasses.CoefficientSemipositive A) :
    actualTopPowerDensity A = normalizedTopPowerDensity A := by
  obtain ⟨S, hS⟩ := exists_linearMap_eq_standard_compContinuousLinearMap hA hpos
  have hAS : A = standardPullback S := hS
  rw [hAS, actualTopPowerDensity_standardPullback, normalizedTopPowerDensity_standardPullback]

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
