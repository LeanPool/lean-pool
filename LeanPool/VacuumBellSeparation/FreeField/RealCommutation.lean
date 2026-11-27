/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.StandardSubspace
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The real source commutation operator

For a real Hilbert space isometrically embedded in the physical complex
one-particle space, the symplectic form is twice the imaginary part of the
physical inner product. Its representing operator is constructed here as
`J = -2 K* i K`. The minus sign follows from the conjugate-linear-first
inner-product convention. Neither standardness nor complex injectivity is
assumed. Complexification and the complex Gram operator are separate steps.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open ClosedSubmodule

namespace VacuumBellSeparation

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real-linear operator representing twice the imaginary physical inner product. -/
noncomputable def realCommutation (K : E →ₗᵢ[ℝ] H) : E →L[ℝ] E :=
  (-2 : ℝ) • (K.toContinuousLinearMap.adjoint.comp
    ((scalarSMulCLE H Complex.UnitI).toContinuousLinearMap.comp K.toContinuousLinearMap))

theorem realCommutation_apply (K : E →ₗᵢ[ℝ] H) (x : E) :
    realCommutation K x = (-2 : ℝ) • K.toContinuousLinearMap.adjoint (Complex.I • K x) := by
  simp [realCommutation, scalarSMulCLE, Complex.UnitI]

/-- The Riesz representation identity, with the manuscript's normalization. -/
theorem inner_realCommutation (K : E →ₗᵢ[ℝ] H) (x y : E) :
    ⟪x, realCommutation K y⟫_ℝ = 2 * (⟪K x, K y⟫_ℂ).im := by
  rw [realCommutation_apply, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right]
  rw [ClosedSubmodule.inner_real_eq_re_inner, inner_smul_right]
  simp [Complex.mul_re]

theorem realCommutation_skew_inner (K : E →ₗᵢ[ℝ] H) (x y : E) :
    ⟪realCommutation K x, y⟫_ℝ = -⟪x, realCommutation K y⟫_ℝ := by
  rw [real_inner_comm, inner_realCommutation, inner_realCommutation]
  have h : (⟪K y, K x⟫_ℂ).im = -(⟪K x, K y⟫_ℂ).im := by
    rw [← inner_conj_symm (K y) (K x)]
    rfl
  rw [h]
  ring

theorem realCommutation_mem_skewAdjoint (K : E →ₗᵢ[ℝ] H) :
    realCommutation K ∈ skewAdjoint (E →L[ℝ] E) := by
  change (realCommutation K).adjoint = -(realCommutation K)
  ext x
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, neg_apply,
    inner_neg_right]
  exact realCommutation_skew_inner K y x

/-- The commutation bound follows from the isometry, with no spectral hypothesis. -/
theorem norm_realCommutation_le_two (K : E →ₗᵢ[ℝ] H) : ‖realCommutation K‖ ≤ 2 := by
  have hK : ‖K.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa using K.norm_toContinuousLinearMap_le
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [realCommutation_apply, norm_smul]
  norm_num only [norm_neg, Real.norm_ofNat]
  calc
    2 * ‖K.toContinuousLinearMap.adjoint (Complex.I • K x)‖ ≤
        2 * (‖K.toContinuousLinearMap.adjoint‖ * ‖Complex.I • K x‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by norm_num)
    _ ≤ 2 * (1 * ‖Complex.I • K x‖) := by gcongr
    _ = 2 * ‖x‖ := by simp [norm_smul]

/-- The physical Gram identity for the real embedding and its constructed operator. -/
theorem inner_realEmbedding_gram (K : E →ₗᵢ[ℝ] H) (x y : E) :
    ⟪K x, K y⟫_ℂ = (⟪x, y⟫_ℝ : ℂ) +
      (Complex.I / 2) * (⟪x, realCommutation K y⟫_ℝ : ℂ) := by
  have hre : (⟪K x, K y⟫_ℂ).re = ⟪x, y⟫_ℝ := K.inner_map_map x y
  rw [inner_realCommutation]
  apply Complex.ext
  · simp [Complex.mul_re, hre]
  · simp [Complex.mul_im]

end VacuumBellSeparation
