/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ProductGaussianIntegrability
public import LeanPool.VacuumBellSeparation.Gaussian.ComplexMatrixGaussianIntegral
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Exact integrability criterion for a real symmetric matrix Gaussian

Actual Hermitian diagonalization changes Lebesgue measure by a finite
nonzero determinant. Scalar slice integrability excludes zero and negative
eigenvalues. The criterion also holds for the extended nonnegative integral,
which is essential before a positive inverse sandwich has any extension.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixGaussian_eigenvector_coordinates {P : Matrix ι ι ℝ}
    (hP : P.IsHermitian) (x : ι → ℝ) :
    matrixGaussian P ((hP.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ x) =
      ∏ i, Real.exp (-(hP.eigenvalues i / 2) * (x i) ^ 2) := by
  let U : Matrix ι ι ℝ := hP.eigenvectorUnitary
  have hd : Uᵀ * P * U = Matrix.diagonal hP.eigenvalues := by
    have h := hP.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, Function.id_comp] using h
  have hq := dotProduct_congruence Uᵀ P x x
  rw [Matrix.transpose_transpose, hd] at hq
  rw [matrixGaussian, hq, ← Real.exp_sum]
  congr 1
  simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq ι] in
/-- Symmetry is essential: a quadratic form otherwise sees only the
symmetric part, so it cannot detect positive definiteness of P itself. -/
theorem integrable_matrixGaussian_iff {P : Matrix ι ι ℝ} (hP : P.IsHermitian) :
    Integrable (matrixGaussian P) ↔ P.PosDef := by
  classical
  constructor
  · intro h
    let U : Matrix ι ι ℝ := hP.eigenvectorUnitary
    have hU : IsUnit U := Unitary.isUnit_coe
    have hd : U.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det U).mp hU)
    have hmap : Measurable (Matrix.toLin' U) := (LinearMap.continuous_on_pi _).measurable
    have hi : Integrable (matrixGaussian P) (Measure.map (Matrix.toLin' U) volume) := by
      rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hd]
      exact h.smul_measure ENNReal.ofReal_ne_top
    have hc := hi.comp_measurable hmap
    have heq : matrixGaussian P ∘ Matrix.toLin' U =
        fun x : ι → ℝ => ∏ i, Real.exp (-(hP.eigenvalues i / 2) * (x i) ^ 2) := by
      funext x
      exact matrixGaussian_eigenvector_coordinates hP x
    rw [heq] at hc
    have he := (integrable_productGaussian_iff (fun i => hP.eigenvalues i / 2)).mp hc
    apply hP.posDef_iff_eigenvalues_pos.mpr
    intro i
    linarith [he i]
  · exact integrable_matrixGaussian

theorem integrable_coherentMatrixGaussian_iff {m : ℕ}
    {P : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hP : P.IsHermitian) :
    Integrable (coherentMatrixGaussian P) ↔ P.PosDef := by
  constructor
  · intro h
    have heq : matrixGaussian ((2 : ℝ) • P) ∘ complexRealCoordinates m =
        coherentMatrixGaussian P := by
      funext z
      exact (coherentMatrixGaussian_eq P z).symm
    have hc : Integrable (matrixGaussian ((2 : ℝ) • P) ∘ complexRealCoordinates m) := by
      rwa [heq]
    have hi := ((complexRealCoordinates_measurePreserving m).integrable_comp_emb
      (complexRealCoordinates m).measurableEmbedding).mp hc
    have hp := (integrable_matrixGaussian_iff (hP.smul (by simp : IsSelfAdjoint (2 : ℝ)))).mp hi
    have hh := hp.smul (by norm_num : (0 : ℝ) < 1 / 2)
    simpa only [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] using hh
  · exact integrable_coherentMatrixGaussian

theorem continuous_coherentMatrixGaussian {m : ℕ}
    (P : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Continuous (coherentMatrixGaussian P) := by
  have hc : Continuous (complexRealCoordinates m) := by
    apply continuous_pi
    rintro ⟨j, a⟩
    fin_cases a
    · change Continuous (fun z : Fin m → ℂ => (z j).re)
      fun_prop
    · change Continuous (fun z : Fin m → ℂ => (z j).im)
      fun_prop
  unfold coherentMatrixGaussian
  fun_prop

theorem lintegral_coherentMatrixGaussian_lt_top_iff {m : ℕ}
    {P : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hP : P.IsHermitian) :
    (∫⁻ z : Fin m → ℂ, ENNReal.ofReal (coherentMatrixGaussian P z)) < ⊤ ↔ P.PosDef := by
  have hi : Integrable (coherentMatrixGaussian P) ↔
      (∫⁻ z : Fin m → ℂ, ENNReal.ofReal (coherentMatrixGaussian P z)) < ⊤ := by
    have hn : 0 ≤ᵐ[volume] coherentMatrixGaussian P :=
      Filter.Eventually.of_forall fun z => (Real.exp_pos _).le
    constructor
    · intro h
      exact (hasFiniteIntegral_iff_ofReal hn).mp h.2
    · intro h
      exact ⟨(continuous_coherentMatrixGaussian P).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal hn).mpr h⟩
  exact hi.symm.trans (integrable_coherentMatrixGaussian_iff hP)

end VacuumBellSeparation.Gaussian
