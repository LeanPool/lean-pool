/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HilbertComplexification
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Complex extensions of real Hilbert-space operators

Real bounded operators extend componentwise, with exactly the same operator
norm. This extension preserves adjoints, skew-adjointness, and real
isometries. All maps use the concrete Hilbert complexification.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap HilbertComplexification

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Complexify linear map obtained from `mk`. -/
noncomputable def complexifyLinearMap (A : E →L[ℝ] F) :
    HilbertComplexification E →ₗ[ℂ] HilbertComplexification F where
  toFun z := mk (A z.re) (A z.im)
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp

@[simp]
theorem complexifyLinearMap_re (A : E →L[ℝ] F) (z : HilbertComplexification E) :
    (complexifyLinearMap A z).re = A z.re := rfl

@[simp]
theorem complexifyLinearMap_im (A : E →L[ℝ] F) (z : HilbertComplexification E) :
    (complexifyLinearMap A z).im = A z.im := rfl

theorem norm_complexifyLinearMap_le (A : E →L[ℝ] F) (z : HilbertComplexification E) :
    ‖complexifyLinearMap A z‖ ≤ ‖A‖ * ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg z))).mp
  rw [HilbertComplexification.norm_sq, mul_pow, HilbertComplexification.norm_sq]
  simp only [complexifyLinearMap_re, complexifyLinearMap_im]
  calc
    ‖A z.re‖ ^ 2 + ‖A z.im‖ ^ 2 ≤
        (‖A‖ * ‖z.re‖) ^ 2 + (‖A‖ * ‖z.im‖) ^ 2 := by
      gcongr <;> exact A.le_opNorm _
    _ = ‖A‖ ^ 2 * (‖z.re‖ ^ 2 + ‖z.im‖ ^ 2) := by ring

/-- The genuine bounded complex-linear extension of a real bounded map. -/
noncomputable def complexify (A : E →L[ℝ] F) :
    HilbertComplexification E →L[ℂ] HilbertComplexification F :=
  (complexifyLinearMap A).mkContinuous ‖A‖ (norm_complexifyLinearMap_le A)

@[simp]
theorem complexify_re (A : E →L[ℝ] F) (z : HilbertComplexification E) :
    (complexify A z).re = A z.re := rfl

@[simp]
theorem complexify_im (A : E →L[ℝ] F) (z : HilbertComplexification E) :
    (complexify A z).im = A z.im := rfl

@[simp]
theorem complexify_ofReal (A : E →L[ℝ] F) (x : E) :
    complexify A (ofReal x) = ofReal (A x) := by ext <;> simp

theorem norm_complexify_le (A : E →L[ℝ] F) : ‖complexify A‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_complexifyLinearMap_le A)

theorem norm_complexify (A : E →L[ℝ] F) : ‖complexify A‖ = ‖A‖ := by
  apply le_antisymm (norm_complexify_le A)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖A x‖ = ‖ofReal (A x)‖ := (ofReal.norm_map (A x)).symm
    _ = ‖complexify A (ofReal x)‖ := by rw [complexify_ofReal]
    _ ≤ ‖complexify A‖ * ‖ofReal x‖ := (complexify A).le_opNorm _
    _ = ‖complexify A‖ * ‖x‖ := by rw [ofReal.norm_map]

@[simp]
theorem complexify_zero : complexify (0 : E →L[ℝ] F) = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  apply HilbertComplexification.ext <;> simp

@[simp]
theorem complexify_add (A B : E →L[ℝ] F) :
    complexify (A + B) = complexify A + complexify B := by
  apply ContinuousLinearMap.ext
  intro z
  apply HilbertComplexification.ext <;> simp

@[simp]
theorem complexify_neg (A : E →L[ℝ] F) : complexify (-A) = -complexify A := by
  apply ContinuousLinearMap.ext
  intro z
  apply HilbertComplexification.ext <;> simp

@[simp]
theorem complexify_real_smul (r : ℝ) (A : E →L[ℝ] F) :
    complexify (r • A) = r • complexify A := by
  apply ContinuousLinearMap.ext
  intro z
  apply HilbertComplexification.ext <;> simp

@[simp]
theorem complexify_one : complexify (1 : E →L[ℝ] E) = 1 := by
  apply ContinuousLinearMap.ext
  intro z
  apply HilbertComplexification.ext <;> simp [one_apply_eq_self]

@[simp]
theorem complexify_mul (A B : E →L[ℝ] E) :
    complexify (A * B) = complexify A * complexify B := by
  apply ContinuousLinearMap.ext
  intro z
  apply HilbertComplexification.ext <;> simp [mul_apply_eq_comp]

section Adjoint

variable [CompleteSpace E] [CompleteSpace F]

theorem complexify_adjoint (A : E →L[ℝ] F) :
    (complexify A).adjoint = complexify A.adjoint := by
  have hinner (z : HilbertComplexification E) (w : HilbertComplexification F) :
      inner ℂ (complexify A z) w = inner ℂ z (complexify A.adjoint w) := by
    apply Complex.ext <;>
      simp only [HilbertComplexification.inner_eq, complexify_re, complexify_im,
        A.adjoint_inner_right]
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact hinner z w

theorem complexify_mem_skewAdjoint {J : E →L[ℝ] E}
    (hJ : J ∈ skewAdjoint (E →L[ℝ] E)) :
    complexify J ∈ skewAdjoint (HilbertComplexification E →L[ℂ] HilbertComplexification E) := by
  change (complexify J).adjoint = -complexify J
  change J.adjoint = -J at hJ
  rw [complexify_adjoint, hJ, complexify_neg]

end Adjoint

/-- Isometric real source inclusions extend to actual complex isometries. -/
noncomputable def complexifyIsometry (i : E →ₗᵢ[ℝ] F) :
    HilbertComplexification E →ₗᵢ[ℂ] HilbertComplexification F where
  toLinearMap := complexifyLinearMap i.toContinuousLinearMap
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [HilbertComplexification.norm_sq, HilbertComplexification.norm_sq]
    simp

@[simp]
theorem complexifyIsometry_re (i : E →ₗᵢ[ℝ] F) (z : HilbertComplexification E) :
    (complexifyIsometry i z).re = i z.re := rfl

@[simp]
theorem complexifyIsometry_im (i : E →ₗᵢ[ℝ] F) (z : HilbertComplexification E) :
    (complexifyIsometry i z).im = i z.im := rfl

end VacuumBellSeparation.Gaussian
