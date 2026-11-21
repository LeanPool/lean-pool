/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsVolumeGraphLimit
public import LeanPool.CutoffRigidity.WeakH1Mollification
public import LeanPool.CutoffRigidity.GibbsOperatorWeakEigenfunction

/-!
# Actual compact weak H¹ and C¹ test functions

Compact raw L² functions with actual L² weak derivatives are lifted into the
closed Gibbs gradient graph by genuine normalized smooth approximation.
This also makes compact C¹ functions legitimate variational tests.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Genuine compact weak derivatives, not a stipulated domain premise,
supply an actual Gibbs Sobolev lift through proved mollifier limits. -/
theorem exists_gibbsSobolev_of_compact_weak_derivatives {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgm : Measurable g) (hg : MemLp g 2 volume) (hgc : HasCompactSupport g)
    (H : Fin d → E →₂[volume] ℝ)
    (hweak : ∀ j : Fin d, ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ y, g y * coordinateDerivative j ψ y) = -(∫ y, H j y * ψ y)) :
    ∃ v : gibbsSobolevGraph hV hprob,
      gibbsSobolevInclusion hV hprob v = volumeToGibbsL2 hV ρ hρ hHess (hg.toLp g) ∧
      gibbsSobolevDerivative hV hprob v =
        volumeToGibbsL2Vector hV ρ hρ hHess (euclideanL2Assemble H) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let φ (n : ℕ) : ContDiffBump (0 : E) := euclideanMollifierBump (ε n) (hε n)
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let f (n : ℕ) := bumpMollification (φ n) g
  have hf (n : ℕ) : ContDiff ℝ 2 (f n) :=
    (bumpMollification_contDiff (φ n) (hg.locallyIntegrable (by norm_num))).of_le (by norm_num)
  have hfc (n : ℕ) : HasCompactSupport (f n) := bumpMollification_hasCompactSupport (φ n) hgc
  have hlimf : Tendsto (fun n => compactC2VolumeLp (f n) (hf n) (hfc n)) atTop (𝓝 (hg.toLp g)) := by
    exact bumpMollificationLp_tendsto φ hφ g hgm hg
  have hlimG : Tendsto (fun n => compactC2VolumeGradientLp (f n) (hf n) (hfc n))
      atTop (𝓝 (euclideanL2Assemble H)) := by
    exact mollifiedGradientLp_tendsto_of_weak_derivatives φ hφ (hg.locallyIntegrable
      (by norm_num)) hgc H hweak
  exact exists_gibbsSobolev_of_volume_L2_graph_limit hV hprob ρ hρ hHess f hf hfc
    (hg.toLp g) (euclideanL2Assemble H) hlimf hlimG

/-- Classical compact C¹ functions satisfy the ordinary weak derivative
identity needed by the actual mollifier/domain theorem. -/
theorem compact_c1_volume_weak_derivative {g : E → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (j : Fin d)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ) :
    (∫ y, g y * coordinateDerivative j ψ y) =
      -(∫ y, gradient g y j * ψ y) := by
  let v := EuclideanSpace.single j (1 : ℝ)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hDg : Continuous (fun x => fderiv ℝ g x v) := by
    change Continuous (fun x => fderiv ℝ g x (EuclideanSpace.single j 1))
    simp_rw [fderiv_single_eq_gradient_coordinate]
    exact (EuclideanSpace.proj j).continuous.comp (continuous_gradient_of_c1 hg)
  have hDψ : Continuous (fun x => fderiv ℝ ψ x v) := by
    change Continuous (fun x => fderiv ℝ ψ x (EuclideanSpace.single j 1))
    simp_rw [fderiv_single_eq_gradient_coordinate]
    exact (EuclideanSpace.proj j).continuous.comp (continuous_gradient_of_c1 (hψ.of_le
      (by norm_num)))
  have h1 : Integrable (fun x => fderiv ℝ g x v * ψ x) volume :=
    (hDg.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have h2 : Integrable (fun x => g x * fderiv ℝ ψ x v) volume :=
    (hg.continuous.mul hDψ).integrable_of_hasCompactSupport hgc.mul_right
  have h3 : Integrable (fun x => g x * ψ x) volume :=
    (hg.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hgc.mul_right
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => hgd x) (fun x _ => hψd x)
  simpa only [coordinateDerivative, v, fderiv_single_eq_gradient_coordinate] using hi

/-- Actual compact C¹ functions belong to the genuine Gibbs H¹ domain,
with the actual classical gradient as their derivative representative. -/
theorem exists_gibbsSobolev_of_compact_c1 {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∃ v : gibbsSobolevGraph hV hprob,
      (gibbsSobolevInclusion hV hprob v : E → ℝ) =ᵐ[gibbsMeasure volume V] g ∧
      (gibbsSobolevDerivative hV hprob v : E → E) =ᵐ[gibbsMeasure volume V] gradient g := by
  have hgLp : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
  have hGLp := c1_compact_gradient_memLp hg hgc
  let G := hGLp.toLp (gradient g)
  let H (j : Fin d) := (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp G
  have hweak : ∀ j : Fin d, ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ y, g y * coordinateDerivative j ψ y) = -(∫ y, H j y * ψ y) := by
    intro j ψ hψ hψc
    rw [compact_c1_volume_weak_derivative hg hgc j ψ hψ hψc]
    congr 1
    apply integral_congr_ae
    filter_upwards [(EuclideanSpace.proj j : E →L[ℝ] ℝ).coeFn_compLp G,
      hGLp.coeFn_toLp] with x hp hx
    change gradient g x j * ψ x = (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp G x * ψ x
    rw [hp, hx]
    rfl
  obtain ⟨v, hv, hD⟩ := exists_gibbsSobolev_of_compact_weak_derivatives hV hprob ρ hρ hHess
    hg.continuous.measurable hgLp hgc H hweak
  refine ⟨v, ?_, ?_⟩
  · rw [hv]
    exact (volumeToGibbsL2_coeFn hV ρ hρ hHess _).trans
      ((gibbsMeasure_absolutelyContinuous volume V).ae_eq hgLp.coeFn_toLp)
  · have hass : euclideanL2Assemble H = G := euclideanL2_assemble_projections G
    rw [hD, hass]
    exact (volumeToGibbsL2Vector_coeFn hV ρ hρ hHess _).trans
      ((gibbsMeasure_absolutelyContinuous volume V).ae_eq hGLp.coeFn_toLp)

/-- Actual operator eigenfunctions may be tested against compact C¹
functions. This is needed for the differentiated weak equation when the
potential has exactly the C² regularity assumed in the paper. -/
theorem gibbsOperatorEigen_compact_c1_test_equation {V φ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hprob rate)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ x, inner ℝ
      (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x)
      (gradient φ x) ∂gibbsMeasure volume V) =
      rate * (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * φ x ∂gibbsMeasure volume V) := by
  obtain ⟨v, hv, hDv⟩ := exists_gibbsSobolev_of_compact_c1 hV hprob ρ hρ hHess hφ hφc
  have he := gibbsOperatorEigenSobolevLift_weak_eigenfunction hV hprob rate u v
  have hl : gibbsDirichletEnergy hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) v =
      ∫ x, inner ℝ
        (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x)
        (gradient φ x) ∂gibbsMeasure volume V := by
    rw [gibbsDirichletEnergy, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hDv] with x hx
    rw [hx]
  have hr : inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (gibbsSobolevInclusion hV hprob v) =
      ∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * φ x ∂gibbsMeasure volume V := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx, Real.inner_apply]
  rwa [hl, hr] at he

end CutoffRigidity
