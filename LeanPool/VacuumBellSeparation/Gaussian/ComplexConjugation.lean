/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SourceGram

/-!
# Real conjugation and the conjugate source Gram operator

Conjugation is the actual antilinear isometric involution `(x,y) ↦ (x,-y)`.
The conjugate of an operator is `C A C`. For the physical source Gram
operator this proves the second expression `1-(i/2)J_C`.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap HilbertComplexification
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HilbertComplexification

/-- The canonical conjugation associated with the original real space. -/
noncomputable def conjugation : HilbertComplexification E ≃ₗᵢ⋆[ℂ] HilbertComplexification E where
  toFun z := mk z.re (-z.im)
  invFun z := mk z.re (-z.im)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by
    apply HilbertComplexification.ext
    · rfl
    · change -(z.im + w.im) = -z.im + -w.im
      abel
  map_smul' c z := by
    apply HilbertComplexification.ext
    · change c.re • z.re - c.im • z.im =
        (conj c).re • z.re - (conj c).im • (-z.im)
      simp only [Complex.conj_re, Complex.conj_im, neg_smul, smul_neg, neg_neg]
    · change -(c.im • z.re + c.re • z.im) =
        (conj c).im • z.re + (conj c).re • (-z.im)
      simp only [Complex.conj_re, Complex.conj_im, neg_smul, smul_neg]
      abel
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq, norm_sq]
    simp

@[simp] theorem conjugation_re (z : HilbertComplexification E) :
    (conjugation z).re = z.re := rfl

@[simp] theorem conjugation_im (z : HilbertComplexification E) :
    (conjugation z).im = -z.im := rfl

@[simp] theorem conjugation_conjugation (z : HilbertComplexification E) :
    conjugation (conjugation z) = z := by ext <;> simp

@[simp] theorem conjugation_ofReal (x : E) : conjugation (ofReal x) = ofReal x := by
  ext <;> simp

end HilbertComplexification

/-- Actual conjugation of a bounded complex-linear operator by the real
antilinear involution, giving another bounded complex-linear operator. -/
noncomputable def conjugateOperator
    (A : HilbertComplexification E →L[ℂ] HilbertComplexification E) :
    HilbertComplexification E →L[ℂ] HilbertComplexification E :=
  conjugation.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp conjugation.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem conjugateOperator_apply
    (A : HilbertComplexification E →L[ℂ] HilbertComplexification E)
    (z : HilbertComplexification E) :
    conjugateOperator A z = conjugation (A (conjugation z)) := rfl

@[simp]
theorem conjugateOperator_one : conjugateOperator (1 :
    HilbertComplexification E →L[ℂ] HilbertComplexification E) = 1 := by
  apply ContinuousLinearMap.ext
  intro z
  simp [one_apply_eq_self]

@[simp]
theorem conjugateOperator_add
    (A B : HilbertComplexification E →L[ℂ] HilbertComplexification E) :
    conjugateOperator (A + B) = conjugateOperator A + conjugateOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  simp

@[simp]
theorem conjugateOperator_smul (c : ℂ)
    (A : HilbertComplexification E →L[ℂ] HilbertComplexification E) :
    conjugateOperator (c • A) = conj c • conjugateOperator A := by
  apply ContinuousLinearMap.ext
  intro z
  change conjugation (c • A (conjugation z)) = conj c • conjugation (A (conjugation z))
  exact conjugation.map_smulₛₗ c (A (conjugation z))

@[simp]
theorem conjugateOperator_complexify (A : E →L[ℝ] E) :
    conjugateOperator (complexify A) = complexify A := by
  apply ContinuousLinearMap.ext
  intro z
  apply HilbertComplexification.ext <;> simp

/-- The conjugate Gram is computed from the actual physical Gram operator;
it is not a separately stipulated covariance expression. -/
theorem conjugate_sourceMap_gram
    {H : Type*} [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : E →ₗᵢ[ℝ] H) :
    conjugateOperator ((sourceMap K).adjoint.comp (sourceMap K)) =
      1 - (Complex.I / 2) • complexCommutation K := by
  rw [sourceMap_adjoint_mul_self, conjugateOperator_add, conjugateOperator_one,
    conjugateOperator_smul]
  have hc : conj (Complex.I / 2) = -(Complex.I / 2) := by
    simp only [map_div₀, Complex.conj_I, map_ofNat, neg_div]
  simp only [complexCommutation, conjugateOperator_complexify, hc, neg_smul, sub_eq_add_neg]

end VacuumBellSeparation.Gaussian
