/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsWeakDerivative
public import LeanPool.CutoffRigidity.GibbsConstants
public import LeanPool.CutoffRigidity.DistributionalConstantsC3

/-! # Constants in the genuine closed Gibbs gradient kernel

Actual locally integrable functions with vanishing ordinary distributional
coordinate derivatives have constant smooth mollifications. Genuine a.e.
approximation by normalized bumps then identifies the original function with
a constant a.e. This is applied to the actual closed weighted H¹ gradient.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory Filter Topology ContinuousLinearMap
open scoped ENNReal Convolution

variable {d : ℕ}

/-- Every actual Gibbs L² class is locally Lebesgue integrable. The proof
uses compact cutoffs equal to one on a neighborhood, not a smooth class
representative. -/
theorem gibbsLp_locallyIntegrable_volume
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : Continuous V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] ℝ) :
    LocallyIntegrable (u : EuclideanSpace ℝ (Fin d) → ℝ) volume := by
  intro x
  let φ : ContDiffBump x := ⟨1, 2, by norm_num, by norm_num⟩
  have hi := integrable_compact_test_mul_gibbsLp_volume hV hprob φ.continuous φ.hasCompactSupport u
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
  apply hi.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_mul]

/-- A zero distributional coordinate derivative makes every compact smooth
mollification have zero ordinary derivative in that coordinate. -/
theorem coordinateDerivative_bumpMollification_eq_zero_of_weak
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LocallyIntegrable f volume)
    (hweak : ∀ (ψ : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      ∀ i : Fin d, (∫ y, coordinateDerivative i ψ y * f y ∂volume) = 0)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    coordinateDerivative i (bumpMollification φ f) x = 0 :=
  coordinateDerivative_bumpMollification_eq_zero_of_weak_c3 hf
    (fun ψ hψ hψc i => hweak ψ (hψ.of_le (by norm_num)) hψc i) φ x i

/-- A locally integrable distribution with zero coordinate derivatives has
constant actual smooth mollifications on connected Euclidean space. -/
theorem bumpMollification_eq_const_of_weak_zero
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LocallyIntegrable f volume)
    (hweak : ∀ (ψ : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      ∀ i : Fin d, (∫ y, coordinateDerivative i ψ y * f y ∂volume) = 0)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    bumpMollification φ f x = bumpMollification φ f 0 :=
  bumpMollification_eq_const_of_weak_zero_c3 hf
    (fun ψ hψ hψc i => hweak ψ (hψ.of_le (by norm_num)) hψc i) φ x

/-- Actual locally integrable zero-gradient distributions are a.e. constants.
Normalized compact bumps approximate the original function a.e. by the
Lebesgue differentiation theorem already proved in Mathlib. -/
theorem ae_eq_const_of_locallyIntegrable_weak_derivative_zero
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LocallyIntegrable f volume)
    (hweak : ∀ (ψ : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      ∀ i : Fin d, (∫ y, coordinateDerivative i ψ y * f y ∂volume) = 0) :
    ∃ c : ℝ, f =ᵐ[volume] fun _ => c :=
  ae_eq_const_of_locallyIntegrable_weak_derivative_zero_c3 hf
    (fun ψ hψ hψc i => hweak ψ (hψ.of_le (by norm_num)) hψc i)

/-- A genuine closed Gibbs H¹ function whose actual weak gradient vanishes
is an actual constant Gibbs L² class. No classical representative or
Poincaré inequality is assumed. -/
theorem gibbsSobolev_eq_constant_of_derivative_eq_zero
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hprob) (hzero : gibbsSobolevDerivative hV hprob u = 0) :
    ∃ c : ℝ, gibbsSobolevInclusion hV hprob u = gibbsConstantLp hprob c := by
  let μ := gibbsMeasure volume V
  let U := gibbsSobolevInclusion hV hprob u
  have hGzero : (fun x => gibbsSobolevDerivative hV hprob u x) =ᵐ[μ]
      (fun _ => (0 : EuclideanSpace ℝ (Fin d))) := by
    rw [hzero]
    exact Lp.coeFn_zero _ _ _
  have hGvol := (gibbsMeasure_ae_eq_iff volume hV.continuous.measurable).mp hGzero
  have hweak : ∀ (ψ : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      ∀ i : Fin d, (∫ y, coordinateDerivative i ψ y * U y ∂volume) = 0 := by
    intro ψ hψ hψc i
    have h := gibbsSobolev_coordinate_weak_derivative_volume hV hprob hψ hψc i u
    have hi : (∫ x, ψ x * (gibbsSobolevDerivative hV hprob u x) i ∂volume) = 0 := by
      calc
        _ = ∫ _ : EuclideanSpace ℝ (Fin d), (0 : ℝ) ∂volume := by
          apply integral_congr_ae
          filter_upwards [hGvol] with x hx
          simp only [hx, PiLp.zero_apply, mul_zero]
        _ = 0 := integral_zero _ _
    rw [hi] at h
    exact neg_eq_zero.mp h.symm
  obtain ⟨c, hc⟩ := ae_eq_const_of_locallyIntegrable_weak_derivative_zero
    (gibbsLp_locallyIntegrable_volume hV.continuous hprob U) hweak
  refine ⟨c, ?_⟩
  let := hprob
  have hconst : (gibbsConstantLp hprob c : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[μ] fun _ => c := by
    exact (memLp_const c).coeFn_toLp
  apply Lp.ext
  filter_upwards [(gibbsMeasure_absolutelyContinuous volume V).ae_eq hc, hconst] with x hx hcx
  exact hx.trans hcx.symm

end CutoffRigidity
