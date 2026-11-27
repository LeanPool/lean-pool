/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompressionPower

/-!
# Actual isometric corners and positive functional calculus

An isometric embedding defines a genuine nonunital star-algebra map
A ↦ i A i†. Positive real powers commute with this map because they vanish
at zero. This keeps the complementary zero block, including infinite
Hilbert spaces, rather than replacing a corner by a unital map.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped NNReal

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Isometric corner obtained from `ι.toContinuousLinearMap`. -/
def isometricCorner (ι : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) : F →L[ℂ] F :=
  ι.toContinuousLinearMap ∘L A ∘L ι.toContinuousLinearMap.adjoint

@[simp] theorem isometricCorner_apply (ι : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) (x : F) :
    isometricCorner ι A x = ι (A (ι.toContinuousLinearMap.adjoint x)) := rfl

/-- Continuous linear map for the isometric corner hom, of type `(E →L[ℂ] E) →⋆ₙₐ[ℂ] (F →L[ℂ] F)
where toFun`. -/
def isometricCornerHom (ι : E →ₗᵢ[ℂ] F) :
    (E →L[ℂ] E) →⋆ₙₐ[ℂ] (F →L[ℂ] F) where
  toFun := isometricCorner ι
  map_zero' := by ext x; simp
  map_add' A B := by ext x; simp
  map_mul' A B := by
    ext x
    simp only [isometricCorner_apply, mul_apply_eq_comp, adjoint_embedding_apply]
  map_smul' c A := by ext x; simp
  map_star' A := by
    change isometricCorner ι A.adjoint = (isometricCorner ι A).adjoint
    simp only [isometricCorner, adjoint_comp, adjoint_adjoint, comp_assoc]

theorem isometricCorner_nonneg (ι : E →ₗᵢ[ℂ] F) {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    0 ≤ isometricCorner ι A :=
  nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hA).conj_adjoint
    ι.toContinuousLinearMap)

theorem isometricCorner_continuous (ι : E →ₗᵢ[ℂ] F) : Continuous (isometricCorner ι) := by
  unfold isometricCorner
  fun_prop

theorem isometricCorner_rpow (ι : E →ₗᵢ[ℂ] F) {A : E →L[ℂ] E}
    (hA : 0 ≤ A) {p : ℝ} (hp : 0 < p) :
    isometricCorner ι (A ^ p) = isometricCorner ι A ^ p := by
  let f : ℝ≥0 → ℝ≥0 := fun t => t ^ p
  have hf : Continuous f := NNReal.continuous_rpow_const hp.le
  have hf₀ : f 0 = 0 := NNReal.zero_rpow hp.ne'
  have hh := (isometricCornerHom ι).map_cfcₙ f A
    (hf := hf.continuousOn) (hf₀ := hf₀) (hφ := isometricCorner_continuous ι)
    (ha := hA) (hφa := isometricCorner_nonneg ι hA)
  rw [cfcₙ_eq_cfc hf.continuousOn hf₀, cfcₙ_eq_cfc hf.continuousOn hf₀] at hh
  exact hh

end VacuumBellSeparation.Gaussian
