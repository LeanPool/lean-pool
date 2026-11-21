/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorHessianRows
public import LeanPool.CutoffRigidity.GibbsVolumeGraphLimit

/-! # Actual closed-domain membership of localized eigenfunction gradients

The distributional Hessian constructed from the eigenfunction equation
provides strong graph approximation by actual smooth compact mollifications.
Thus localized gradient coordinates belong to the genuine closed Gibbs
Sobolev domain, without any assumed classical representative.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Genuine weighted H¹ membership of each compactly localized weak-gradient
coordinate of an actual operator eigenvector. Both actual L² components
are identified, rather than supplied as a domain hypothesis. -/
theorem exists_gibbsSobolev_localizedOperatorEigenGradient {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hprob rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (i : Fin d) :
    ∃ v : gibbsSobolevGraph hV hprob,
      gibbsSobolevInclusion hV hprob v = volumeToGibbsL2 hV ρ hρ hHess
        ((localizedOperatorEigenGradient_memLp hV hprob rate u hχ hχc i).toLp
          (localizedOperatorEigenGradient hV hprob rate u χ i)) ∧
      gibbsSobolevDerivative hV hprob v = volumeToGibbsL2Vector hV ρ hρ hHess
        (gibbsOperatorLocalizedHessianRow hV hprob rate u hχ hχc i) := by
  let g := localizedOperatorEigenGradient hV hprob rate u χ i
  have hgm := localizedOperatorEigenGradient_memLp hV hprob rate u hχ hχc i
  have hgl := hgm.locallyIntegrable (by norm_num)
  have hgc := localizedOperatorEigenGradient_hasCompactSupport hV hprob rate u hχc i
  let φ (n : ℕ) : ContDiffBump (0 : E) :=
    euclideanMollifierBump (differenceStep n) (differenceStep_pos n)
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := differenceStep_tendsto_zero
  let f (n : ℕ) := bumpMollification (φ n) g
  have hf (n : ℕ) : ContDiff ℝ 2 (f n) :=
    (bumpMollification_contDiff (φ n) hgl).of_le (by norm_num)
  have hfc (n : ℕ) : HasCompactSupport (f n) :=
    bumpMollification_hasCompactSupport (φ n) hgc
  apply exists_gibbsSobolev_of_volume_L2_graph_limit hV hprob ρ hρ hHess f hf hfc
  · exact localizedOperatorEigenGradient_mollified_tendsto hV hprob rate u hχ hχc i φ hφ
  · exact gibbsOperatorLocalizedHessianRow_mollified_gradient_tendsto
      hV hprob rate u hχ hχc i φ hφ

/-- A genuine closed-domain lift, chosen from the proved strong graph limit. -/
@[expose] noncomputable def gibbsOperatorLocalizedGradientSobolevLift {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hprob rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (i : Fin d) :
    gibbsSobolevGraph hV hprob :=
  (exists_gibbsSobolev_localizedOperatorEigenGradient hV hprob ρ hρ hHess rate u hχ hχc i).choose

theorem gibbsOperatorLocalizedGradientSobolevLift_inclusion_ae {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hprob rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (i : Fin d) :
    (gibbsSobolevInclusion hV hprob
      (gibbsOperatorLocalizedGradientSobolevLift hV hprob ρ hρ hHess rate u hχ hχc i) : E → ℝ)
      =ᵐ[gibbsMeasure volume V] localizedOperatorEigenGradient hV hprob rate u χ i := by
  have hs := (exists_gibbsSobolev_localizedOperatorEigenGradient hV hprob ρ hρ hHess
    rate u hχ hχc i).choose_spec.1
  change gibbsSobolevInclusion hV hprob
    (gibbsOperatorLocalizedGradientSobolevLift hV hprob ρ hρ hHess rate u hχ hχc i) = _ at hs
  rw [hs]
  exact (volumeToGibbsL2_coeFn hV ρ hρ hHess _).trans
    ((gibbsMeasure_absolutelyContinuous volume V).ae_eq
      (localizedOperatorEigenGradient_memLp hV hprob rate u hχ hχc i).coeFn_toLp)

/-- Every coordinate of the actual closed derivative is the actual selected
distributional Hessian, almost everywhere for the Gibbs measure. -/
theorem gibbsOperatorLocalizedGradientSobolevLift_derivative_coordinate_ae {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hprob rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (i j : Fin d) :
    (fun x => (gibbsSobolevDerivative hV hprob
      (gibbsOperatorLocalizedGradientSobolevLift hV hprob ρ hρ hHess rate u hχ hχc i) x) j)
      =ᵐ[gibbsMeasure volume V] gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i j := by
  have hs := (exists_gibbsSobolev_localizedOperatorEigenGradient hV hprob ρ hρ hHess
    rate u hχ hχc i).choose_spec.2
  change gibbsSobolevDerivative hV hprob
    (gibbsOperatorLocalizedGradientSobolevLift hV hprob ρ hρ hHess rate u hχ hχc i) = _ at hs
  rw [hs]
  have he := (EuclideanSpace.proj j : E →L[ℝ] ℝ).coeFn_compLp
    (gibbsOperatorLocalizedHessianRow hV hprob rate u hχ hχc i)
  have hproj := euclideanL2_project_assemble
    (fun k => gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i k) j
  change (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp
    (gibbsOperatorLocalizedHessianRow hV hprob rate u hχ hχc i) = _ at hproj
  rw [hproj] at he
  filter_upwards [volumeToGibbsL2Vector_coeFn hV ρ hρ hHess
    (gibbsOperatorLocalizedHessianRow hV hprob rate u hχ hχc i),
    (gibbsMeasure_absolutelyContinuous volume V).ae_eq he] with x hx hp
  rw [hx]
  exact hp.symm

/-- Genuine weighted integration by parts for the actual weak Hessian.
This follows from proved closed-domain membership, with no classical
regularity assumption on the operator eigenvector. -/
theorem gibbsOperatorLocalizedHessian_weighted_ibp {V χ ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hprob rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i j : Fin d) :
    (∫ x, ψ x * gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i j x
      ∂gibbsMeasure volume V) =
    -(∫ x, (coordinateDerivative j ψ x - ψ x * coordinateDerivative j V x) *
      localizedOperatorEigenGradient hV hprob rate u χ i x ∂gibbsMeasure volume V) := by
  have he := gibbsSobolev_coordinate_weak_derivative hV hprob hψ hψc j
    (gibbsOperatorLocalizedGradientSobolevLift hV hprob ρ hρ hHess rate u hχ hχc i)
  have hleft := integral_congr_ae
    ((gibbsOperatorLocalizedGradientSobolevLift_derivative_coordinate_ae
      hV hprob ρ hρ hHess rate u hχ hχc i j).fun_mul (Filter.EventuallyEq.rfl : ψ =ᵐ[gibbsMeasure
        volume V] ψ))
  have hright := integral_congr_ae
    ((gibbsOperatorLocalizedGradientSobolevLift_inclusion_ae
      hV hprob ρ hρ hHess rate u hχ hχc i).fun_mul
        (Filter.EventuallyEq.rfl : (fun x => coordinateDerivative j ψ x - ψ x *
          coordinateDerivative j V x) =ᵐ[gibbsMeasure volume V] _))
  simp_rw [mul_comm] at hleft hright
  rw [hleft, hright] at he
  simpa only [mul_comm] using he

end CutoffRigidity
