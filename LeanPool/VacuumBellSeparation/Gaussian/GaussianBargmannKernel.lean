/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianBargmannMatrixDefs
public import LeanPool.VacuumBellSeparation.Gaussian.BargmannBlockCoordinates

/-!
# The manuscript's literal Bargmann matrix kernel

The actual Gaussian characteristic and actual exponential vectors give
the independent-label kernel in the manuscript's grouped quadrature
coordinates. The matrix is literally S_B - D_Bᵀ (V + I/2)⁻¹ D_B.
The covariance hypothesis concerns the actual state, and positivity of
V + I/2 justifies the Gaussian integral used upstream.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexConjugate MatrixOrder Matrix.Norms.L2Operator

theorem groupedPhysicalCovariance_add_scalar {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (c : ℝ) :
    groupedPhysicalCovariance (V + c • 1) = groupedPhysicalCovariance V + c • 1 := by
  simp only [groupedPhysicalCovariance, Matrix.submatrix_add, Matrix.submatrix_smul,
    Pi.add_apply, Pi.smul_apply, Matrix.submatrix_one_equiv]

theorem groupedPhysicalCovariance_det {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    (groupedPhysicalCovariance V).det = V.det :=
  Matrix.det_submatrix_equiv_self (groupedToMode m) V

theorem groupedPhysicalCovariance_inv {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    (groupedPhysicalCovariance V)⁻¹ = groupedPhysicalCovariance V⁻¹ :=
  Matrix.inv_submatrix_equiv V (groupedToMode m) (groupedToMode m)

theorem bargmannPair_swap_quadratic {m : ℕ} (a b : MultiModePhaseSpace m) :
    bargmannPair a b ⬝ᵥ (bargmannSwap *ᵥ bargmannPair a b) = 2 * inner ℂ a b := by
  simp only [bargmannSwap, bargmannPair, Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec, Matrix.one_mulVec,
    zero_add, add_zero, sumElim_dotProduct_sumElim]
  change (fun j => conj (a j)) ⬝ᵥ (fun j => b j) +
    (fun j => b j) ⬝ᵥ (fun j => conj (a j)) = 2 * inner ℂ a b
  rw [dotProduct_comm (fun j => b j) (fun j => conj (a j))]
  have hi : (fun j => conj (a j)) ⬝ᵥ (fun j => b j) = inner ℂ a b := by
    simp only [dotProduct, PiLp.inner_apply, RCLike.inner_apply']
  rw [hi]
  ring

theorem interleavedBargmannQuadratures_inverse_quadratic {m : ℕ}
    (C : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (a b : MultiModePhaseSpace m) :
    interleavedBargmannQuadratures a b ⬝ᵥ
        (complexifyMatrix C⁻¹ *ᵥ interleavedBargmannQuadratures a b) =
      bargmannPair a b ⬝ᵥ
        ((bargmannDᵀ * complexifyMatrix (groupedPhysicalCovariance C)⁻¹ * bargmannD) *ᵥ
          bargmannPair a b) := by
  have hr := reindexed_complex_quadratic (groupedToMode m) (complexifyMatrix C⁻¹)
    (bargmannD *ᵥ bargmannPair a b)
  have hc : complexifyMatrix (groupedPhysicalCovariance C)⁻¹ =
      (complexifyMatrix C⁻¹).submatrix (groupedToMode m) (groupedToMode m) := by
    rw [groupedPhysicalCovariance_inv]
    rfl
  have hd := complex_dotProduct_congruence bargmannDᵀ
    (complexifyMatrix (groupedPhysicalCovariance C)⁻¹) (bargmannPair a b) (bargmannPair a b)
  rw [Matrix.transpose_transpose, hc] at hd
  rw [hc]
  exact hr.symm.trans hd

theorem bargmannGaussianMatrix_quadratic {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (a b : MultiModePhaseSpace m) :
    inner ℂ a b + (1 / 4 : ℂ) * (bargmannFourierCoefficient a b ⬝ᵥ
        (complexifyMatrix (physicalDisplacementCovariance (V + (1 / 2 : ℝ) • 1)⁻¹) *ᵥ
          bargmannFourierCoefficient a b)) =
      (1 / 2 : ℂ) * (bargmannPair a b ⬝ᵥ
        (bargmannGaussianMatrix V *ᵥ bargmannPair a b)) := by
  rw [bargmannFourierCoefficient_quadratic,
    interleavedBargmannQuadratures_inverse_quadratic, groupedPhysicalCovariance_add_scalar]
  simp only [bargmannGaussianMatrix, Matrix.sub_mulVec, dotProduct_sub,
    bargmannPair_swap_quadratic]
  ring

/-- The exact Appendix A Bargmann formula for actual exponential vectors
and an actual positive trace-class density with Gaussian physical
characteristic. The labels are independent, not just equal-label values. -/
theorem gaussianPhysical_bargmannKernel {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) (a b : MultiModePhaseSpace m) :
    multiBargmannKernel A (fun j => a j) (fun j => b j) =
      ((Real.sqrt (groupedPhysicalCovariance V + (1 / 2 : ℝ) • 1).det)⁻¹ : ℂ) *
        Complex.exp ((1 / 2 : ℂ) * (bargmannPair a b ⬝ᵥ
          (bargmannGaussianMatrix V *ᵥ bargmannPair a b))) := by
  rw [gaussianPhysical_bargmannKernel_fourier hA hG hC,
    bargmannGaussianMatrix_quadratic,
    ← groupedPhysicalCovariance_add_scalar, groupedPhysicalCovariance_det]

end VacuumBellSeparation.Gaussian
