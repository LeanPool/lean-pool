/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.HighContrast.Coupled.LocalEnergy.Cutoff
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientIterationGeometry
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.InnerCubeAndHessian
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1

/-!
# High-contrast homogenization: Provider.Regularity.HarmonicCaccioppoli

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace CubeCalderonZygmund

open MeasureTheory

noncomputable section

/-- The direct squared-cutoff Caccioppoli estimate needed before the harmonic
gradient-gain iteration.  Its right side is the parent value energy, with the
exact cutoff-gradient coefficient left visible. -/
theorem harmonic_centralChild_gradient_energy_le
    {d : ℕ} (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (hu : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0)) :
    ∫ x in openCubeSet (centralChild Q), vecNormSq (u.grad x) ∂volume ≤
      4 * ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((3 / 4 : ℝ) - 1 / 2) * cubeRadius Q)) ^ 2) *
        ∫ x in openCubeSet Q, u.toFun x ^ 2 ∂volume := by
  let eta : QuantitativeCubeCutoff Q (1 / 2 : ℝ) (3 / 4 : ℝ) :=
    QuantitativeCubeCutoff.canonical Q (1 / 2 : ℝ) (3 / 4 : ℝ)
      (by norm_num) (by norm_num)
  have heta_tsupport : tsupport (eta : Vec d → ℝ) ⊆ openCubeSet Q :=
    (QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledClosedCubeSet
      (Q := Q) (ρ₁ := (1 / 2 : ℝ)) (ρ₂ := (3 / 4 : ℝ))
      (by norm_num) (by norm_num)).trans
      (scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q
        (by norm_num) (by norm_num))
  have heta_sq_tsupport : tsupport (sqCutoff (eta : Vec d → ℝ)) ⊆ openCubeSet Q :=
    (tsupport_sq_subset (eta : Vec d → ℝ)).trans heta_tsupport
  have hzero : MemScalarL2 (openCubeSet Q) (fun _ : Vec d => (0 : ℝ)) := by
    exact MeasureTheory.MemLp.zero
  have htest := hu.test_mulContDiffHasCompactSupport_expanded
    (isOpenBoundedConvexDomain_openCubeSet Q) hzero
    (sqCutoff_contDiff eta.smooth) (hasCompactSupport_sq eta.hasCompactSupport)
    heta_sq_tsupport
  have henergy :
      ∫ x in openCubeSet Q,
        (eta x ^ 2 * vecNormSq (u.grad x) +
          u.toFun x * vecDot (u.grad x)
            (fun j => 2 * eta x * euclideanGradient (eta : Vec d → ℝ) x j))
          ∂volume = 0 := by
    simpa only [sqCutoff_apply, fderiv_sqCutoff eta.smooth,
      euclideanGradient, euclideanCoordDeriv, zero_mul, integral_zero,
      vecNormSq, WeakPoissonEquationOn.vecDot_cutoff_energy_integrand] using htest
  have hmain : IntegrableOn
      (fun x => eta x ^ 2 * vecNormSq (u.grad x)) (openCubeSet Q) :=
    WeakPoissonEquationOn.integrableOn_sq_cutoff_vecNormSq_of_memVectorL2
      u.grad_memVectorL2 eta.smooth eta.hasCompactSupport
  have hcross : IntegrableOn
      (fun x => u.toFun x * vecDot (u.grad x)
        (fun j => 2 * eta x * euclideanGradient (eta : Vec d → ℝ) x j))
      (openCubeSet Q) :=
    WeakPoissonEquationOn.integrableOn_sq_cutoff_cross_of_memScalarL2_memVectorL2
      u.memL2 u.grad_memVectorL2 eta.smooth eta.hasCompactSupport
  have herr_int : IntegrableOn
      (fun x => 2 * u.toFun x ^ 2 *
        vecNormSq (euclideanGradient (eta : Vec d → ℝ) x)) (openCubeSet Q) :=
    WeakPoissonEquationOn.integrableOn_two_mul_sq_mul_vecNormSq_euclideanGradient_of_memScalarL2
      u.memL2 eta.smooth eta.hasCompactSupport
  have hhalf :
      (1 / 2 : ℝ) * ∫ x in openCubeSet Q,
          eta x ^ 2 * vecNormSq (u.grad x) ∂volume ≤
        ∫ x in openCubeSet Q, 2 * u.toFun x ^ 2 *
          vecNormSq (euclideanGradient (eta : Vec d → ℝ) x) ∂volume := by
    have hpoint :
        (fun x => -(u.toFun x * vecDot (u.grad x)
          (fun j => 2 * eta x * euclideanGradient (eta : Vec d → ℝ) x j)))
            ≤ᵐ[volume.restrict (openCubeSet Q)]
          fun x => eta x ^ 2 * vecNormSq (u.grad x) / 2 +
            2 * u.toFun x ^ 2 *
              vecNormSq (euclideanGradient (eta : Vec d → ℝ) x) :=
      Filter.Eventually.of_forall fun x =>
        by
          simpa only [neg_mul] using
            (WeakPoissonEquationOn.neg_sq_cutoff_error_integrand_le
              (eta x) (u.toFun x) (u.grad x)
              (euclideanGradient (eta : Vec d → ℝ) x))
    have h :=
      WeakPoissonEquationOn.integral_half_main_le_scalar_rhs_add_error_of_add_energy_identity
      (V := openCubeSet Q)
      (m := fun x => eta x ^ 2 * vecNormSq (u.grad x))
      (c := fun x => u.toFun x * vecDot (u.grad x)
        (fun j => 2 * eta x * euclideanGradient (eta : Vec d → ℝ) x j))
      (e := fun x => 2 * u.toFun x ^ 2 *
        vecNormSq (euclideanGradient (eta : Vec d → ℝ) x))
      (R := 0) henergy
      hpoint
      hmain hcross herr_int
    simpa using h
  have hinner_subset : openCubeSet (centralChild Q) ⊆ openCubeSet Q :=
    centralDescendant_openCubeSet_subset Q 1
  have hinner_one : ∀ x ∈ openCubeSet (centralChild Q), eta x = 1 := by
    intro x hx
    have hx_open : x ∈ scaledOpenCubeSet Q (1 / 2 : ℝ) :=
      centralChild_cubeSet_subset_scaledOpenInnerHalf Q
        (openCubeSet_subset_cubeSet (centralChild Q) hx)
    have hx_closed : x ∈ scaledClosedCubeSet Q (1 / 2 : ℝ) :=
      scaledOpenCubeSet_subset_scaledClosedCubeSet Q (1 / 2 : ℝ) hx_open
    exact eta.eq_one_on_inner x hx_closed
  have hinner :=
    WeakPoissonEquationOn.integral_vecNormSq_le_integral_sqCutoff_vecNormSq_of_subset_eq_one
    (S := openCubeSet (centralChild Q)) (V := openCubeSet Q)
    (G := u.grad) (η := (eta : Vec d → ℝ))
    (measurableSet_openCubeSet (centralChild Q)) hinner_subset hinner_one
    u.grad_memVectorL2 eta.smooth eta.hasCompactSupport
  have herror :=
    WeakPoissonEquationOn.integral_sq_mul_vecNormSq_euclideanGradient_quantitativeCubeCutoff_le
      (η := eta) (V := openCubeSet Q) (w := u.toFun) u.memL2
  have herror_twice :
      ∫ x in openCubeSet Q, 2 * u.toFun x ^ 2 *
          vecNormSq (euclideanGradient (eta : Vec d → ℝ) x) ∂volume =
        2 * ∫ x in openCubeSet Q, u.toFun x ^ 2 *
          vecNormSq (euclideanGradient (eta : Vec d → ℝ) x) ∂volume := by
    calc
      ∫ x in openCubeSet Q, 2 * u.toFun x ^ 2 *
          vecNormSq (euclideanGradient (eta : Vec d → ℝ) x) ∂volume =
          ∫ x in openCubeSet Q, 2 * (u.toFun x ^ 2 *
            vecNormSq (euclideanGradient (eta : Vec d → ℝ) x)) ∂volume := by
              congr with x
              ring
      _ = 2 * ∫ x in openCubeSet Q, u.toFun x ^ 2 *
          vecNormSq (euclideanGradient (eta : Vec d → ℝ) x) ∂volume := by
            rw [MeasureTheory.integral_const_mul]
  calc
    ∫ x in openCubeSet (centralChild Q), vecNormSq (u.grad x) ∂volume ≤
        ∫ x in openCubeSet Q, eta x ^ 2 * vecNormSq (u.grad x) ∂volume := hinner
    _ ≤ 4 * ∫ x in openCubeSet Q, u.toFun x ^ 2 *
          vecNormSq (euclideanGradient (eta : Vec d → ℝ) x) ∂volume := by
      rw [herror_twice] at hhalf
      linarith only [hhalf]
    _ ≤ 4 * (((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            (((3 / 4 : ℝ) - 1 / 2) * cubeRadius Q)) ^ 2) *
          ∫ x in openCubeSet Q, u.toFun x ^ 2 ∂volume) := by
      exact mul_le_mul_of_nonneg_left herror (by norm_num)
    _ = 4 * ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((3 / 4 : ℝ) - 1 / 2) * cubeRadius Q)) ^ 2) *
        ∫ x in openCubeSet Q, u.toFun x ^ 2 ∂volume := by ring

end

end CubeCalderonZygmund
end HCPolySupport
