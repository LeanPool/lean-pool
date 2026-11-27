/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityWeylInversion
public import LeanPool.VacuumBellSeparation.Gaussian.CoherentMatrixFourier

/-!
# Actual Gaussian characteristic implies the coherent Gaussian diagonal

Gaussianity is defined by the actual complex density expectation of the
constructed Weyl operators. Weak inversion and the genuine matrix Fourier
integral derive its Husimi diagonal. The displacement-label covariance
and the physical position/momentum covariance differ by the explicit
symplectic rotation, which is retained in this theorem.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory
open scoped ComplexConjugate MatrixOrder Matrix.Norms.L2Operator

/-- Condition that the data have Gaussian displacement characteristic. -/
def HasGaussianDisplacementCharacteristic {m : ℕ}
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) : Prop :=
  ∀ z : Fin m → ℂ,
    densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl (WithLp.toLp 2 z)) =
      Complex.exp ((-(complexRealCoordinates m z ⬝ᵥ
        (V *ᵥ complexRealCoordinates m z)) : ℝ) : ℂ)

theorem complexRealCoordinates_dot_self {m : ℕ} (z : Fin m → ℂ) :
    complexRealCoordinates m z ⬝ᵥ complexRealCoordinates m z =
      ‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    complexRealCoordinates_apply, complexRealCoordinates_apply_one,
    EuclideanSpace.norm_sq_eq, Complex.sq_norm, Complex.normSq_apply]

theorem symplectic_rotated_dot_complexRealCoordinates {m : ℕ}
    (w : MultiModePhaseSpace m) (z : Fin m → ℂ) :
    (modeSymplecticForm *ᵥ complexRealCoordinates m (fun j => w j)) ⬝ᵥ
      complexRealCoordinates m z = -(inner ℂ w (WithLp.toLp 2 z)).im := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    modeSymplecticForm_mulVec_zero, modeSymplecticForm_mulVec_one,
    complexRealCoordinates_apply, complexRealCoordinates_apply_one,
    PiLp.inner_apply, RCLike.inner_apply', Complex.im_sum,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gaussianDensity_convolution_integrand {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianDisplacementCharacteristic A V) (w : MultiModePhaseSpace m)
    (z : Fin m → ℂ) :
    weylVacuumWeight m z * coherentFourierPhase w (WithLp.toLp 2 z) *
      densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl (WithLp.toLp 2 z)) =
        coherentMatrixFourier (V + (1 / 2 : ℝ) • 1)
          (modeSymplecticForm *ᵥ complexRealCoordinates m (fun j => w j)) z := by
  rw [hG z, weylVacuumWeight, coherentFourierPhase, coherentMatrixFourier,
    ← Complex.exp_add, ← Complex.exp_add,
    symplectic_rotated_dot_complexRealCoordinates]
  congr 1
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, complexRealCoordinates_dot_self]
  push_cast
  ring

/-- The actual Husimi diagonal. V is explicitly the covariance in
displacement labels, hence the two symplectic rotations in its inverse
quadratic form. No Bargmann-kernel or coherent-diagonal hypothesis is used. -/
theorem gaussianDensity_coherent_diagonal {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianDisplacementCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) (w : MultiModePhaseSpace m) :
    inner ℂ (multiCoherentVector w) (A (multiCoherentVector w)) =
      ((Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹ : ℂ) *
        Complex.exp ((-((modeSymplecticForm *ᵥ complexRealCoordinates m (fun j => w j)) ⬝ᵥ
          ((V + (1 / 2 : ℝ) • 1)⁻¹ *ᵥ
            (modeSymplecticForm *ᵥ complexRealCoordinates m (fun j => w j)))) : ℝ) : ℂ) := by
  have h := integral_densityWeyl_convolution hA w
  simp_rw [gaussianDensity_convolution_integrand hG] at h
  rw [integral_coherentMatrixFourier hC] at h
  have hp : (Real.pi : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.pi_pos.ne')
  apply (mul_left_cancel₀ hp)
  exact h.symm.trans (by push_cast; ring)

end VacuumBellSeparation.Gaussian
