/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SymplecticWeylImplementer
public import LeanPool.VacuumBellSeparation.Gaussian.QuadratureMatrices
public import LeanPool.VacuumBellSeparation.Gaussian.ComplexMatrixGaussianIntegral

/-!
# Actual real matrix coordinates for the constructed Weyl implementer

The coordinate equivalence sends a complex mode vector to its interleaved
real and imaginary parts. Conjugating literal real matrix multiplication
by this equivalence gives a genuine bounded real linear label map. The
matrix identity Sᵀ Ω S = Ω proves preservation of the actual Weyl form.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

/-- Complex real linear equivalence of type `MultiModePhaseSpace m ≃ₗ[ℝ] (Fin m × Fin 2 → ℝ) where
toEquiv`. -/
def complexRealLinearEquiv (m : ℕ) :
    MultiModePhaseSpace m ≃ₗ[ℝ] (Fin m × Fin 2 → ℝ) where
  toEquiv := (WithLp.equiv 2 (Fin m → ℂ)).trans (complexRealCoordinates m).toEquiv
  map_add' z w := by
    ext ⟨j, k⟩
    fin_cases k <;>
      simp [complexRealCoordinates_apply, complexRealCoordinates_apply_one]
  map_smul' c z := by
    ext ⟨j, k⟩
    fin_cases k <;>
      simp [complexRealCoordinates_apply, complexRealCoordinates_apply_one]

@[simp] theorem complexRealLinearEquiv_apply (m : ℕ) (z : MultiModePhaseSpace m) :
    complexRealLinearEquiv m z = complexRealCoordinates m (fun j => z j) := rfl

theorem inner_im_eq_real_symplectic {m : ℕ} (z w : MultiModePhaseSpace m) :
    (inner ℂ z w).im = complexRealLinearEquiv m z ⬝ᵥ
      (modeSymplecticForm *ᵥ complexRealLinearEquiv m w) := by
  rw [dotProduct_modeSymplecticForm]
  simp only [PiLp.inner_apply, RCLike.inner_apply', Complex.im_sum, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, complexRealLinearEquiv_apply,
    modeQuadratureTuple, complexRealCoordinates_apply, complexRealCoordinates_apply_one,
    quadratureSymplectic]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Matrix Weyl label map of type `MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m`. -/
def matrixWeylLabelMap {m : ℕ}
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m :=
  ((complexRealLinearEquiv m).symm.toLinearMap.comp
    (S.mulVecLin.comp (complexRealLinearEquiv m).toLinearMap)).toContinuousLinearMap

theorem complexRealLinearEquiv_matrixWeylLabelMap {m : ℕ}
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (z : MultiModePhaseSpace m) :
    complexRealLinearEquiv m (matrixWeylLabelMap S z) = S *ᵥ complexRealLinearEquiv m z := by
  change complexRealLinearEquiv m
    ((complexRealLinearEquiv m).symm (S *ᵥ complexRealLinearEquiv m z)) = _
  exact (complexRealLinearEquiv m).apply_symm_apply _

theorem matrixWeylLabelMap_preservesWeylForm {m : ℕ}
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : Sᵀ * modeSymplecticForm * S = modeSymplecticForm) :
    PreservesWeylForm (matrixWeylLabelMap S) := by
  intro z w
  rw [inner_im_eq_real_symplectic, inner_im_eq_real_symplectic,
    complexRealLinearEquiv_matrixWeylLabelMap, complexRealLinearEquiv_matrixWeylLabelMap]
  have h := dotProduct_congruence Sᵀ modeSymplecticForm
    (complexRealLinearEquiv m z) (complexRealLinearEquiv m w)
  simpa only [Matrix.transpose_transpose, hS] using h

/-- A real symplectic matrix has an actual constructed oscillator unitary
implementer on the fixed representation. -/
theorem exists_matrix_weyl_implementer {m : ℕ}
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : Sᵀ * modeSymplecticForm * S = modeSymplecticForm) :
    ∃ U : MultiModeOscillatorSpace m ≃ₗᵢ[ℂ] MultiModeOscillatorSpace m,
      ∀ z, U.conjStarAlgEquiv (multiOscillatorWeyl z) = multiOscillatorWeyl
        (matrixWeylLabelMap S z) :=
  ⟨symplecticWeylImplementer (matrixWeylLabelMap_preservesWeylForm S hS),
    symplecticWeylImplementer_conj_weyl (matrixWeylLabelMap_preservesWeylForm S hS)⟩

end VacuumBellSeparation.Gaussian
