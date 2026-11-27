/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixGaussianIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Complex coherent-coordinate Gaussian measure and normalization

The coordinate map z↦(Re z_j, Im z_j) is a proved measurable,
volume-preserving equivalence. Consequently the coherent Gaussian
exp(-u(z)ᵀ P u(z)) has complex-plane integral π^m / sqrt(det P).
Equivalently its exponent is -r(z)ᵀ P r(z)/2 for r=√2 u.
All measures are actual product Lebesgue measures, including m=0.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem volume_preserving_real_uncurry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ).symm := by
  refine ⟨(MeasurableEquiv.curry ι κ ℝ).symm.measurable, ?_⟩
  change Measure.map (MeasurableEquiv.curry ι κ ℝ).symm volume =
    Measure.pi (fun _ : ι × κ => (volume : Measure ℝ))
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (MeasurableEquiv.curry ι κ ℝ).symm.measurable
    (MeasurableSet.pi Set.countable_univ fun i _ => hs i)]
  have heq : (MeasurableEquiv.curry ι κ ℝ).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s (i, j))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      MeasurableEquiv.coe_curry_symm, Function.uncurry_apply_pair, Prod.forall]
  rw [heq, volume_pi_pi]
  simp_rw [volume_pi_pi]
  exact (Fintype.prod_prod_type (fun i : ι × κ => volume (s i))).symm

/-- Complex real coordinates. -/
def complexRealCoordinates (m : ℕ) : (Fin m → ℂ) ≃ᵐ (Fin m × Fin 2 → ℝ) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin m => Complex.measurableEquivPi)).trans
    (MeasurableEquiv.curry (Fin m) (Fin 2) ℝ).symm

@[simp] theorem complexRealCoordinates_apply (m : ℕ) (z : Fin m → ℂ) (i : Fin m) :
    complexRealCoordinates m z (i, 0) = (z i).re := rfl

@[simp] theorem complexRealCoordinates_apply_one (m : ℕ) (z : Fin m → ℂ) (i : Fin m) :
    complexRealCoordinates m z (i, 1) = (z i).im := rfl

theorem complexRealCoordinates_measurePreserving (m : ℕ) :
    MeasurePreserving (complexRealCoordinates m) :=
  (volume_preserving_real_uncurry (Fin m) (Fin 2)).comp
    (volume_preserving_pi (fun _ : Fin m => Complex.volume_preserving_equiv_pi))

/-- Coherent matrix Gaussian given by `Real.exp (-(complexRealCoordinates m z ⬝ᵥ (P *ᵥ
complexRealCoordinates m z)))`. -/
def coherentMatrixGaussian {m : ℕ} (P : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (z : Fin m → ℂ) : ℝ :=
  Real.exp (-(complexRealCoordinates m z ⬝ᵥ (P *ᵥ complexRealCoordinates m z)))

theorem coherentMatrixGaussian_eq {m : ℕ}
    (P : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (z : Fin m → ℂ) :
    coherentMatrixGaussian P z = matrixGaussian ((2 : ℝ) • P) (complexRealCoordinates m z) := by
  simp only [coherentMatrixGaussian, matrixGaussian, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]
  congr 1
  ring

theorem integrable_coherentMatrixGaussian {m : ℕ}
    {P : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hP : P.PosDef) :
    Integrable (coherentMatrixGaussian P) := by
  have h := (complexRealCoordinates_measurePreserving m).integrable_comp_of_integrable
    (integrable_matrixGaussian (hP.smul (by norm_num : (0 : ℝ) < 2)))
  simpa only [Function.comp_def, ← coherentMatrixGaussian_eq] using h

/-- The literal π^m normalization used with normalized coherent vectors. -/
theorem integral_coherentMatrixGaussian {m : ℕ}
    {P : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hP : P.PosDef) :
    (∫ z : Fin m → ℂ, coherentMatrixGaussian P z) = Real.pi ^ m / Real.sqrt P.det := by
  have h := (complexRealCoordinates_measurePreserving m).integral_comp
    (complexRealCoordinates m).measurableEmbedding (matrixGaussian ((2 : ℝ) • P))
  simp only [← coherentMatrixGaussian_eq] at h
  rw [h, integral_matrixGaussian (hP.smul (by norm_num : (0 : ℝ) < 2)),
    Matrix.det_smul, Fintype.card_prod]
  simp only [Fintype.card_fin]
  have hn : Real.sqrt (2 * Real.pi) ^ (m * 2) = (2 * Real.pi) ^ m := by
    rw [Nat.mul_comm m 2, pow_mul, Real.sq_sqrt (by positivity)]
  have hd : Real.sqrt (2 ^ (m * 2) * P.det) = (2 : ℝ) ^ m * Real.sqrt P.det := by
    rw [Real.sqrt_mul (by positivity), pow_mul, Real.sqrt_sq (by positivity)]
  rw [hn, hd, mul_pow]
  field_simp [show (2 : ℝ) ^ m ≠ 0 by positivity,
    ne_of_gt (Real.sqrt_pos.mpr hP.det_pos)]

end VacuumBellSeparation.Gaussian
