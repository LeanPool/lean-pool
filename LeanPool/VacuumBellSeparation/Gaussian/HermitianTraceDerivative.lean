/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HermitianTraceTaylorBound
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Star

/-!
# Actual Fréchet differentiation of finite Hermitian spectral traces

On the genuine real self-adjoint subspace, a local scalar second-order
remainder gives the actual Fréchet derivative H ↦ Re Tr(f'(A) H).
The hypothesis is an explicit scalar bound at spectral pairs, not an
assumption that eigenbranches or the matrix trace are differentiable.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Filter Asymptotics
open scoped Matrix.Norms.L2Operator Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hermitian matrix space with underlying type `selfAdjoint.submodule ℝ (Matrix ι ι ℂ)`. -/
abbrev HermitianMatrixSpace (ι : Type*) :=
  selfAdjoint.submodule ℝ (Matrix ι ι ℂ)

omit [DecidableEq ι] [Fintype ι] in
theorem hermitianMatrix_isHermitian (A : HermitianMatrixSpace ι) :
    (A : Matrix ι ι ℂ).IsHermitian := A.property

/-- Real part of the trace of the continuous functional calculus on a Hermitian matrix. -/
def hermitianSpectralTrace (f : ℝ → ℝ) (A : HermitianMatrixSpace ι) : ℝ :=
  (cfc f (A : Matrix ι ι ℂ)).trace.re

/-- The continuous linear directional derivative of a Hermitian spectral trace. -/
def hermitianTraceDerivative (A : HermitianMatrixSpace ι) (d : ℝ → ℝ) :
    HermitianMatrixSpace ι →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H => (cfc d (A : Matrix ι ι ℂ) * (H : Matrix ι ι ℂ)).trace.re
      map_add' := by
        intro H K
        change (cfc d (A : Matrix ι ι ℂ) * ((H : Matrix ι ι ℂ) + K)).trace.re = _
        simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := by
        intro c H
        change (cfc d (A : Matrix ι ι ℂ) * (c • (H : Matrix ι ι ℂ))).trace.re = _
        simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
          RingHom.id_apply] }

@[simp] theorem hermitianTraceDerivative_apply
    (A H : HermitianMatrixSpace ι) (d : ℝ → ℝ) :
    hermitianTraceDerivative A d H =
      (cfc d (A : Matrix ι ι ℂ) * (H : Matrix ι ι ℂ)).trace.re := rfl

/-- A proved scalar Taylor bound near the actual finite spectra yields
the true derivative of the actual continuous-functional-calculus trace. -/
theorem hasFDerivAt_hermitianSpectralTrace_of_scalar_remainder
    (A : HermitianMatrixSpace ι) (f d : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hrem : ∀ᶠ B : HermitianMatrixSpace ι in 𝓝 A, ∀ i j,
      |f ((hermitianMatrix_isHermitian B).eigenvalues j) -
        f ((hermitianMatrix_isHermitian A).eigenvalues i) -
        d ((hermitianMatrix_isHermitian A).eigenvalues i) *
          ((hermitianMatrix_isHermitian B).eigenvalues j -
            (hermitianMatrix_isHermitian A).eigenvalues i)| ≤
        C * ((hermitianMatrix_isHermitian B).eigenvalues j -
          (hermitianMatrix_isHermitian A).eigenvalues i) ^ 2) :
    HasFDerivAt (hermitianSpectralTrace f) (hermitianTraceDerivative A d) A := by
  apply HasFDerivAt.of_isLittleO
  have hb : (fun B : HermitianMatrixSpace ι => hermitianSpectralTrace f B -
      hermitianSpectralTrace f A - hermitianTraceDerivative A d (B - A)) =O[𝓝 A]
        (fun B => ‖B - A‖ ^ 2) := by
    apply isBigO_iff.mpr
    refine ⟨C * Fintype.card ι, ?_⟩
    filter_upwards [hrem] with B hB
    have h := abs_real_trace_cfc_remainder_le_norm_sq
      (hermitianMatrix_isHermitian A) (hermitianMatrix_isHermitian B) f d hC hB
    change |(cfc f (B : Matrix ι ι ℂ)).trace.re -
      (cfc f (A : Matrix ι ι ℂ)).trace.re -
      (cfc d (A : Matrix ι ι ℂ) * ((B - A : HermitianMatrixSpace ι) : Matrix ι ι ℂ)).trace.re| ≤
        (C * Fintype.card ι) * |‖B - A‖ ^ 2|
    rw [abs_of_nonneg (sq_nonneg (‖B - A‖ : ℝ))]
    have hn : ‖(B : Matrix ι ι ℂ) - (A : Matrix ι ι ℂ)‖ =
        ‖B - A‖ := rfl
    rw [hn] at h
    simpa only [Matrix.trace_sub, Complex.sub_re, Submodule.coe_sub] using h
  exact hb.trans_isLittleO (isLittleO_pow_sub_sub A (by norm_num : 1 < (2 : ℕ)))

/-- An unconditional example at arbitrary, possibly degenerate, Hermitian
matrices: the actual trace-square derivative is H ↦ Re Tr(2 A H). -/
theorem hasFDerivAt_hermitianSpectralTrace_square (A : HermitianMatrixSpace ι) :
    HasFDerivAt (hermitianSpectralTrace (fun x => x ^ 2))
      (hermitianTraceDerivative A (fun x => 2 * x)) A := by
  apply hasFDerivAt_hermitianSpectralTrace_of_scalar_remainder A _ _ (C := 1) zero_le_one
  exact Filter.Eventually.of_forall fun B i j => by
    have he :
        (hermitianMatrix_isHermitian B).eigenvalues j ^ 2 -
          (hermitianMatrix_isHermitian A).eigenvalues i ^ 2 -
          (2 * (hermitianMatrix_isHermitian A).eigenvalues i) *
            ((hermitianMatrix_isHermitian B).eigenvalues j -
              (hermitianMatrix_isHermitian A).eigenvalues i) =
        ((hermitianMatrix_isHermitian B).eigenvalues j -
          (hermitianMatrix_isHermitian A).eigenvalues i) ^ 2 := by ring
    rw [he, abs_of_nonneg (sq_nonneg _), one_mul]

end VacuumBellSeparation.Gaussian
