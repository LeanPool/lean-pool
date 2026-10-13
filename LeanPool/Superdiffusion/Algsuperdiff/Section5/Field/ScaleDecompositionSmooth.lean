/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.ScaleDecomposition
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# ScaleDecompositionSmooth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Differentiability of the high-frequency stream field

The nonnegative shell series has locally summable first derivatives.  Uniform
convergence on every origin cube gives a continuous derivative, so its sum is
genuinely `C¹` rather than merely pointwise differentiable.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Stream
open HCPolySupport
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ} {gamma : ℝ}

/-- The termwise derivative of the nonnegative-shell part. -/
def streamFieldLargeDeriv (omega : FullSample d gamma) (x : Vec d) :
    Vec d →L[ℝ] Mat d :=
  ∑' r : ℕ, ShellField.deriv (omega.1.1 (r : ℤ)) x

private theorem hasFDerivAt_streamFieldLarge (omega : FullSample d gamma)
    (x : Vec d) :
    HasFDerivAt (streamFieldLarge omega) (streamFieldLargeDeriv omega x) x := by
  obtain ⟨ell, hx⟩ := exists_nat_mem_openOriginCube x
  let u : ℕ → ℝ := fun r =>
    (d : ℝ) * localCubeDerivNorm (ell : ℤ) (omega.1.1 (r : ℤ))
  have hu : Summable u := by
    simpa only [u, zero_add] using
      (summable_localCubeDerivNorm_ascending omega ell 0).mul_left (d : ℝ)
  have hbound : ∀ r : ℕ, ∀ z ∈ openCubeSet (originCube d (ell : ℤ)),
      ‖ShellField.deriv (omega.1.1 (r : ℤ)) z‖ ≤ u r := by
    intro r z hz
    have hmatrix := matrixDerivativeNorm_deriv_le_localCubeDerivNorm
      (ell : ℤ) (omega.1.1 (r : ℤ)) hz
    exact (Section5.Support.norm_le_dim_mul_matrixDerivativeNorm
        (ShellField.deriv (omega.1.1 (r : ℤ)) z)).trans
      (mul_le_mul_of_nonneg_left hmatrix (Nat.cast_nonneg d))
  have hzero : Summable fun r : ℕ =>
      omega.1.1 (r : ℤ) (0 : Vec d) - omega.1.1 (r : ℤ) 0 := by
    simpa only [sub_self] using (summable_zero : Summable fun _r : ℕ => (0 : Mat d))
  unfold streamFieldLarge streamFieldLargeDeriv
  exact hasFDerivAt_tsum_of_isPreconnected hu
    (isOpen_openCubeSet (originCube d (ell : ℤ)))
    (convex_openCubeSet (originCube d (ell : ℤ))).isPreconnected
    (fun r z _ => (ShellField.hasFDerivAt (omega.1.1 (r : ℤ)) z).sub_const
      (omega.1.1 (r : ℤ) 0))
    hbound (zero_mem_openOriginCube d (ell : ℤ)) hzero hx

private theorem continuous_streamFieldLargeDeriv (omega : FullSample d gamma) :
    Continuous (streamFieldLargeDeriv omega) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨ell, hx⟩ := exists_nat_mem_openOriginCube x
  let u : ℕ → ℝ := fun r =>
    (d : ℝ) * localCubeDerivNorm (ell : ℤ) (omega.1.1 (r : ℤ))
  have hu : Summable u := by
    simpa only [u, zero_add] using
      (summable_localCubeDerivNorm_ascending omega ell 0).mul_left (d : ℝ)
  have hbound : ∀ r : ℕ, ∀ z ∈ openCubeSet (originCube d (ell : ℤ)),
      ‖ShellField.deriv (omega.1.1 (r : ℤ)) z‖ ≤ u r := by
    intro r z hz
    have hmatrix := matrixDerivativeNorm_deriv_le_localCubeDerivNorm
      (ell : ℤ) (omega.1.1 (r : ℤ)) hz
    exact (Section5.Support.norm_le_dim_mul_matrixDerivativeNorm
        (ShellField.deriv (omega.1.1 (r : ℤ)) z)).trans
      (mul_le_mul_of_nonneg_left hmatrix (Nat.cast_nonneg d))
  have hcont : ContinuousOn (streamFieldLargeDeriv omega)
      (openCubeSet (originCube d (ell : ℤ))) := by
    unfold streamFieldLargeDeriv
    -- The operator-norm uniformity on `Vec d →L[ℝ] Mat d` reached through the
    -- ambient `NormedAddCommGroup` is only defeq (not instance-reducibly equal)
    -- to `ContinuousLinearMap.uniformSpace`, so bridge the two by hand.
    have : @CompleteSpace (Vec d →L[ℝ] Mat d) PseudoMetricSpace.toUniformSpace :=
      inferInstanceAs (CompleteSpace (Vec d →L[ℝ] Mat d))
    exact continuousOn_tsum
      (fun r => (ShellField.deriv (omega.1.1 (r : ℤ))).continuous.continuousOn)
      hu hbound
  exact (hcont x hx).continuousAt
    ((isOpen_openCubeSet (originCube d (ell : ℤ))).mem_nhds hx)

/-- The nonnegative-shell part of the stream field is continuously
differentiable, with derivative `streamFieldLargeDeriv`. -/
theorem streamFieldLarge_contDiff_one (omega : FullSample d gamma) :
    ContDiff ℝ 1 (streamFieldLarge omega) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨streamFieldLargeDeriv omega, continuous_streamFieldLargeDeriv omega,
      hasFDerivAt_streamFieldLarge omega⟩

/-- The Fréchet derivative of the nonnegative-shell part is its termwise
derivative series. -/
theorem fderiv_streamFieldLarge (omega : FullSample d gamma) (x : Vec d) :
    fderiv ℝ (streamFieldLarge omega) x = streamFieldLargeDeriv omega x :=
  (hasFDerivAt_streamFieldLarge omega x).fderiv

end

end Algsuperdiff.Section5.Field
