/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointNormalizedKernels
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Actual analytic neighborhoods of the normalized Bessel kernels

One-variable Cauchy analyticity applies to the Bessel functions and the
principal square root on the right half-plane. Their compositions with
the literal polynomial squared radius give several-variable analyticity.
No general unproved several-variable holomorphy principle is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian Set

private theorem analyticAt_positive_halfPlane {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ f z) {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ f z := by
  have hd : DifferentiableOn ℂ f {w : ℂ | 0 < w.re} :=
    fun w hw => (hf w hw).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re) z hz

theorem analyticAt_spatialSquaredRadius (s : ℝ) (d : EuclideanSpace ℂ (Fin 3)) :
    AnalyticAt ℂ (spatialSquaredRadius s) d := by
  unfold spatialSquaredRadius
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (analyticAt_const.add
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) j :
      EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ).analyticAt d)).pow 2

theorem analyticAt_spatialComplexRadius (s : ℝ) (d : EuclideanSpace ℂ (Fin 3))
    (hd : 0 < (spatialSquaredRadius s d).re) :
    AnalyticAt ℂ (spatialComplexRadius s) d := by
  exact (analyticAt_positive_halfPlane
    (fun _ h => Complex.differentiableAt_sqrt (Or.inl h)) hd).comp
      (analyticAt_spatialSquaredRadius s d)

theorem analyticAt_besselFieldKernel {μ : ℝ} (hμ : 0 < μ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    AnalyticAt ℂ (besselFieldKernel μ) ρ :=
  analyticAt_positive_halfPlane (fun _ h => differentiableAt_besselFieldKernel hμ h) hρ

theorem analyticAt_besselMomentumKernel {μ : ℝ} (hμ : 0 < μ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    AnalyticAt ℂ (besselMomentumKernel μ) ρ :=
  analyticAt_positive_halfPlane (fun _ h => differentiableAt_besselMomentumKernel hμ h) hρ

theorem analyticAt_spatialSixPair (z : Fin 6 → ℂ) : AnalyticAt ℂ spatialSixPair z := by
  have hl : AnalyticAt ℂ (fun w : Fin 6 → ℂ => fun j : Fin 3 => w (Fin.castAdd 3 j)) z :=
    AnalyticAt.pi (fun j => (ContinuousLinearMap.proj (Fin.castAdd 3 j) : (Fin 6
      → ℂ) →L[ℂ] ℂ).analyticAt z)
  have hr : AnalyticAt ℂ (fun w : Fin 6 → ℂ => fun j : Fin 3 => w (Fin.natAdd 3 j)) z :=
    AnalyticAt.pi (fun j => (ContinuousLinearMap.proj (Fin.natAdd 3 j) : (Fin 6
      → ℂ) →L[ℂ] ℂ).analyticAt z)
  exact ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.analyticAt _ |>.comp hl).prod
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.analyticAt _ |>.comp hr)

theorem analyticAt_spatialPairFieldKernel {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 ≤ R)
    (hsep : 8 * Real.sqrt 3 * R ≤ s) {xy : SpatialComplexPair}
    (hxy : xy ∈ spatialClosedPolydisc R) :
    AnalyticAt ℂ (spatialPairFieldKernel μ s) xy := by
  have hq := spatialSquaredRadius_re_pos hs (show 0 ≤ 2 * Real.sqrt 3 * R by positivity)
    (show 4 * (2 * Real.sqrt 3 * R) ≤ s by nlinarith) (xy.2 - xy.1)
    (spatial_polydisc_difference_norm_le hR hxy)
  have hsub : AnalyticAt ℂ (fun p : SpatialComplexPair => p.2 - p.1) xy :=
    analyticAt_snd.sub analyticAt_fst
  have h := ((analyticAt_besselFieldKernel hμ
    (spatialComplexRadius_re_pos_of_squared s _ hq)).comp
      (analyticAt_spatialComplexRadius s _ hq)).comp
        (f := fun p : SpatialComplexPair => p.2 - p.1) hsub
  simpa only [spatialPairFieldKernel, Function.comp_def] using! h

theorem analyticAt_spatialPairMomentumKernel {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 ≤ R)
    (hsep : 8 * Real.sqrt 3 * R ≤ s) {xy : SpatialComplexPair}
    (hxy : xy ∈ spatialClosedPolydisc R) :
    AnalyticAt ℂ (spatialPairMomentumKernel μ s) xy := by
  have hq := spatialSquaredRadius_re_pos hs (show 0 ≤ 2 * Real.sqrt 3 * R by positivity)
    (show 4 * (2 * Real.sqrt 3 * R) ≤ s by nlinarith) (xy.2 - xy.1)
    (spatial_polydisc_difference_norm_le hR hxy)
  have hsub : AnalyticAt ℂ (fun p : SpatialComplexPair => p.2 - p.1) xy :=
    analyticAt_snd.sub analyticAt_fst
  have h := ((analyticAt_besselMomentumKernel hμ
    (spatialComplexRadius_re_pos_of_squared s _ hq)).comp
      (analyticAt_spatialComplexRadius s _ hq)).comp
        (f := fun p : SpatialComplexPair => p.2 - p.1) hsub
  simpa only [spatialPairMomentumKernel, Function.comp_def] using! h

theorem jointNormalizedFieldKernel_analyticAt {μ s : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (z : Fin 6 → ℂ)
    (hz : z ∈ coordinateClosedPolydisc 6 (1 / 100)) :
    AnalyticAt ℂ (jointNormalizedFieldKernel μ s) z := by
  have hp := spatialSixPair_mem_polydisc (joint_scaled_coordinate_mem hs hz)
  have ha := (analyticAt_spatialPairFieldKernel hμ hs (by positivity)
    (joint_fixed_polydisc_separation hs) hp).comp
      (analyticAt_spatialSixPair (fun j => (s : ℂ) * z j))
  exact ha.comp (AnalyticAt.pi (fun j => analyticAt_const.mul
    ((ContinuousLinearMap.proj j : (Fin 6 → ℂ) →L[ℂ] ℂ).analyticAt z)))

theorem jointNormalizedMomentumKernel_analyticAt {μ s : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (z : Fin 6 → ℂ)
    (hz : z ∈ coordinateClosedPolydisc 6 (1 / 100)) :
    AnalyticAt ℂ (jointNormalizedMomentumKernel μ s) z := by
  have hp := spatialSixPair_mem_polydisc (joint_scaled_coordinate_mem hs hz)
  have ha := (analyticAt_spatialPairMomentumKernel hμ hs (by positivity)
    (joint_fixed_polydisc_separation hs) hp).comp
      (analyticAt_spatialSixPair (fun j => (s : ℂ) * z j))
  exact ha.comp (AnalyticAt.pi (fun j => analyticAt_const.mul
    ((ContinuousLinearMap.proj j : (Fin 6 → ℂ) →L[ℂ] ℂ).analyticAt z)))

end VacuumBellSeparation
