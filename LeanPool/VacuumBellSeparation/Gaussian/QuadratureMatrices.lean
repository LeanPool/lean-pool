/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeThermalCharacteristic
public import LeanPool.VacuumBellSeparation.Gaussian.SymplecticBlocks

/-!
# Matrix coordinates for the actual finite-mode Weyl representation

Mode/quadrature vectors are rearranged into real pairs without changing
their values. The literal block symplectic form and mode diagonal give
the exact Weyl phase and covariance quadratic form. A final rectangular
matrix identity transports these forms through actual coordinates.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexConjugate

/-- Mode quadrature tuple given by `fun j => (r (j, 0), r (j, 1))`. -/
def modeQuadratureTuple {ι : Type*} (r : ι × Fin 2 → ℝ) : ι → ℝ × ℝ :=
  fun j => (r (j, 0), r (j, 1))

@[simp] theorem modeQuadratureTuple_add {ι : Type*} (r s : ι × Fin 2 → ℝ) :
    modeQuadratureTuple (r + s) = modeQuadratureTuple r + modeQuadratureTuple s := rfl

theorem modeSymplecticForm_mulVec_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι × Fin 2 → ℝ) (i : ι) :
    (modeSymplecticForm *ᵥ r) (i, 0) = r (i, 1) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    modeSymplecticForm, oneModeSymplecticForm, Matrix.one_apply]

theorem modeSymplecticForm_mulVec_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι × Fin 2 → ℝ) (i : ι) :
    (modeSymplecticForm *ᵥ r) (i, 1) = -r (i, 0) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    modeSymplecticForm, oneModeSymplecticForm, Matrix.one_apply]

theorem dotProduct_modeSymplecticForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r s : ι × Fin 2 → ℝ) :
    r ⬝ᵥ (modeSymplecticForm *ᵥ s) =
      ∑ j, quadratureSymplectic (modeQuadratureTuple r j) (modeQuadratureTuple s j) := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    modeSymplecticForm_mulVec_zero, modeSymplecticForm_mulVec_one,
    modeQuadratureTuple, quadratureSymplectic, mul_neg, sub_eq_add_neg]

theorem dotProduct_modeDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : ι → ℝ) (r : ι × Fin 2 → ℝ) :
    r ⬝ᵥ (modeDiagonal ν *ᵥ r) =
      ∑ j, ν j * ((r (j, 0)) ^ 2 + (r (j, 1)) ^ 2) := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    modeDiagonal, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dotProduct_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℝ) (A : Matrix κ κ ℝ) (x y : ι → ℝ) :
    (Sᵀ *ᵥ x) ⬝ᵥ (A *ᵥ (Sᵀ *ᵥ y)) = x ⬝ᵥ ((S * A * Sᵀ) *ᵥ y) := by
  calc
    (Sᵀ *ᵥ x) ⬝ᵥ (A *ᵥ (Sᵀ *ᵥ y)) =
        (A *ᵥ (Sᵀ *ᵥ y)) ⬝ᵥ (Sᵀ *ᵥ x) := dotProduct_comm _ _
    _ = x ⬝ᵥ (S *ᵥ (A *ᵥ (Sᵀ *ᵥ y))) :=
      Matrix.dotProduct_transpose_mulVec S _ x
    _ = x ⬝ᵥ ((S * A * Sᵀ) *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem multiQuadratureLabel_add {m : ℕ} (v w : Fin m → ℝ × ℝ) :
    multiQuadratureLabel (v + w) = multiQuadratureLabel v + multiQuadratureLabel w := by
  ext j
  exact quadratureLabel_add (v j) (w j)

theorem multiQuadratureLabel_symplectic {m : ℕ} (v w : Fin m → ℝ × ℝ) :
    (inner ℂ (multiQuadratureLabel v) (multiQuadratureLabel w)).im =
      (∑ j, quadratureSymplectic (v j) (w j)) / 2 := by
  simp only [PiLp.inner_apply, multiQuadratureLabel,
    RCLike.inner_apply', Complex.im_sum, quadratureLabel_symplectic, Finset.sum_div]

theorem multiQuadratureWeyl_mem_unitary {m : ℕ} (v : Fin m → ℝ × ℝ) :
    multiQuadratureWeyl v ∈
      unitary (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :=
  multiOscillatorWeyl_mem_unitary _

theorem multiQuadratureWeyl_mul {m : ℕ} (v w : Fin m → ℝ × ℝ) :
    multiQuadratureWeyl v * multiQuadratureWeyl w =
      Complex.exp (-(Complex.I * (((∑ j, quadratureSymplectic (v j) (w j)) / 2 : ℝ) : ℂ))) •
        multiQuadratureWeyl (v + w) := by
  rw [multiQuadratureWeyl, multiQuadratureWeyl, multiOscillatorWeyl_mul, weylPhase]
  simp only [id_eq, multiQuadratureLabel_symplectic,
    multiQuadratureWeyl, multiQuadratureLabel_add]

end VacuumBellSeparation.Gaussian
