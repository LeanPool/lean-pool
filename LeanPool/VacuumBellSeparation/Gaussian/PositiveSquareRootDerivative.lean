/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveSylvesterInverse
public import LeanPool.VacuumBellSeparation.Gaussian.CovarianceResolventPerturbation
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The actual positive matrix square root is strictly differentiable

The inverse function theorem is applied to squaring on the genuine real
self-adjoint subspace. The proved positive Sylvester equivalence supplies
the derivative inverse. Local positivity and sqrt(X²)=X identify the
local inverse with the actual CFC square root, without assuming prior
square-root continuity or differentiable spectral branches.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Filter
open scoped MatrixOrder Matrix.Norms.L2Operator Topology RightActions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Symmetric matrix square. -/
def symmetricMatrixSquare (X : RealSymmetricMatrixSpace ι) : RealSymmetricMatrixSpace ι :=
  ⟨(X : Matrix ι ι ℝ) * (X : Matrix ι ι ℝ), by
    change IsSelfAdjoint ((X : Matrix ι ι ℝ) * (X : Matrix ι ι ℝ))
    simpa only [pow_two] using (realSymmetricMatrix_isHermitian X).isSelfAdjoint.pow 2⟩

/-- Symmetric matrix sqrt. -/
def symmetricMatrixSqrt (X : RealSymmetricMatrixSpace ι) : RealSymmetricMatrixSpace ι :=
  ⟨CFC.sqrt (X : Matrix ι ι ℝ), (CFC.sqrt_nonneg _).isSelfAdjoint⟩

theorem hasStrictFDerivAt_symmetricMatrixSquare
    (R : RealSymmetricMatrixSpace ι) (hR : (R : Matrix ι ι ℝ).PosDef) :
    HasStrictFDerivAt symmetricMatrixSquare
      (positiveSylvesterSelfAdjointContinuousEquiv hR :
        RealSymmetricMatrixSpace ι →L[ℝ] RealSymmetricMatrixSpace ι) R := by
  let e : RealSymmetricMatrixSpace ι →L[ℝ] Matrix ι ι ℝ :=
    (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)).subtypeL
  let p : Matrix ι ι ℝ →L[ℝ] RealSymmetricMatrixSpace ι := selfAdjointPartL ℝ (Matrix ι ι ℝ)
  have he := e.hasStrictFDerivAt (x := R)
  have h := p.hasStrictFDerivAt.comp R (he.mul' he)
  convert h using 1
  · funext X
    apply Subtype.ext
    change (X : Matrix ι ι ℝ) * (X : Matrix ι ι ℝ) =
      (selfAdjointPart ℝ ((X : Matrix ι ι ℝ) * X) : Matrix ι ι ℝ)
    exact ((show IsSelfAdjoint ((X : Matrix ι ι ℝ) * X) by
      simpa only [pow_two] using (realSymmetricMatrix_isHermitian X).isSelfAdjoint.pow
        2).coe_selfAdjointPart_apply ℝ).symm
  · apply ContinuousLinearMap.ext
    intro X
    apply Subtype.ext
    change ((positiveSylvesterSelfAdjointContinuousEquiv hR X :
      RealSymmetricMatrixSpace ι) : Matrix ι ι ℝ) = _
    rw [positiveSylvesterSelfAdjointContinuousEquiv_apply]
    change (R : Matrix ι ι ℝ) * (X : Matrix ι ι ℝ) + (X : Matrix ι ι ℝ) * R =
      (selfAdjointPart ℝ ((R : Matrix ι ι ℝ) * X + (X : Matrix ι ι ℝ) * R) : Matrix ι ι ℝ)
    have hs : IsSelfAdjoint ((R : Matrix ι ι ℝ) * X + (X : Matrix ι ι ℝ) * R) := by
      rw [← positiveSylvesterEquiv_apply hR]
      exact positiveSylvesterEquiv_preserves_selfAdjoint hR X.property
    exact (hs.coe_selfAdjointPart_apply ℝ).symm

omit [DecidableEq ι] [Fintype ι] in
theorem eventually_posDef_at_positive_symmetric [Finite ι]
    (R : RealSymmetricMatrixSpace ι) (hR : (R : Matrix ι ι ℝ).PosDef) :
    ∀ᶠ X : RealSymmetricMatrixSpace ι in 𝓝 R, (X : Matrix ι ι ℝ).PosDef := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hc : Continuous (fun X : RealSymmetricMatrixSpace ι =>
      ‖relativeCovariancePerturbation (R : Matrix ι ι ℝ) ((R : Matrix ι ι ℝ) - X)‖) := by
    unfold relativeCovariancePerturbation
    fun_prop
  have he := (hc.tendsto R).eventually_lt_const (show
      ‖relativeCovariancePerturbation (R : Matrix ι ι ℝ) ((R : Matrix ι ι ℝ) - R)‖ < 1 by
    simp [relativeCovariancePerturbation])
  filter_upwards [he] with X hX
  have hp := covariance_gap_posDef_of_relative_norm hR
    (hR.isHermitian.sub (realSymmetricMatrix_isHermitian X)) hX
  simpa only [sub_sub_cancel] using hp

theorem symmetricMatrixSqrt_square_eventually
    (R : RealSymmetricMatrixSpace ι) (hR : (R : Matrix ι ι ℝ).PosDef) :
    ∀ᶠ X : RealSymmetricMatrixSpace ι in 𝓝 R,
      symmetricMatrixSqrt (symmetricMatrixSquare X) = X := by
  filter_upwards [eventually_posDef_at_positive_symmetric R hR] with X hX
  apply Subtype.ext
  exact CFC.sqrt_mul_self (X : Matrix ι ι ℝ) hX.posSemidef.nonneg

/-- The actual derivative of the actual CFC square root at a positive
matrix is the inverse positive Sylvester operator at its actual root. -/
theorem hasStrictFDerivAt_symmetricMatrixSqrt
    (V : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef) :
    HasStrictFDerivAt symmetricMatrixSqrt
      ((positiveSylvesterSelfAdjointContinuousEquiv (matrix_sqrt_posDef hV)).symm :
        RealSymmetricMatrixSpace ι →L[ℝ] RealSymmetricMatrixSpace ι) V := by
  let R := symmetricMatrixSqrt V
  have hR : (R : Matrix ι ι ℝ).PosDef := matrix_sqrt_posDef hV
  have h := (hasStrictFDerivAt_symmetricMatrixSquare R hR).to_local_left_inverse
    (symmetricMatrixSqrt_square_eventually R hR)
  have hs : symmetricMatrixSquare R = V := by
    apply Subtype.ext
    exact CFC.sqrt_mul_sqrt_self (V : Matrix ι ι ℝ) hV.posSemidef.nonneg
  rwa [hs] at h

theorem hasFDerivAt_symmetricMatrixSqrt
    (V : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef) :
    HasFDerivAt symmetricMatrixSqrt
      ((positiveSylvesterSelfAdjointContinuousEquiv (matrix_sqrt_posDef hV)).symm :
        RealSymmetricMatrixSpace ι →L[ℝ] RealSymmetricMatrixSpace ι) V :=
  (hasStrictFDerivAt_symmetricMatrixSqrt V hV).hasFDerivAt

end VacuumBellSeparation.Gaussian
