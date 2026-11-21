/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.OperatorEigenDistributionRigidity
public import LeanPool.CutoffRigidity.GibbsSobolevConstants
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Genuine affine representatives of curvature-rate operator eigenvectors -/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ContDiff

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Every coordinate of the actual weak gradient is an actual constant
distribution, and hence the full weak gradient is a constant vector a.e. -/
theorem gibbsOperatorEigen_equalRate_gradient_constant {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsOperatorEigenspace hV hp ρ) :
    ∃ a : E, (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u) : E → E)
      =ᵐ[volume] fun _ => a := by
  let G := gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u)
  have hcoord (i : Fin d) : ∃ c : ℝ, (fun x => (G x) i) =ᵐ[volume] fun _ => c := by
    apply ae_eq_const_of_locallyIntegrable_weak_derivative_zero_c3
      (gibbsVector_coordinate_locallyIntegrable_volume hV.continuous hp G i)
    intro ψ hψ hψc j
    simpa only [mul_comm] using
      gibbsOperatorEigen_equalRate_gradient_distribution_zero hV hp ρ hρ hHess u i j ψ hψ hψc
  choose c hc using hcoord
  refine ⟨WithLp.toLp 2 c, ?_⟩
  have hall := ae_all_iff.mpr hc
  filter_upwards [hall] with x hx
  apply PiLp.ext
  intro i
  exact hx i

/-- A genuine affine representative of each actual curvature-rate
operator eigenclass, recovered directly from its weak gradient. -/
theorem gibbsOperatorEigen_equalRate_affine_representative {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsOperatorEigenspace hV hp ρ) :
    ∃ (a : E) (b : ℝ),
      (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u) : E → E)
        =ᵐ[volume] (fun _ => a) ∧
      (u : E →₂[gibbsMeasure volume V] ℝ) =ᵐ[volume] fun x => inner ℝ a x + b := by
  let G := gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u)
  let U : E → ℝ := (u : E →₂[gibbsMeasure volume V] ℝ)
  obtain ⟨a, ha⟩ := gibbsOperatorEigen_equalRate_gradient_constant hV hp ρ hρ hHess u
  have hlin : ContDiff ℝ 3 (fun x : E => inner ℝ a x) := by
    have he : (fun x : E => inner ℝ a x) = (innerSL ℝ a : E → ℝ) := by
      funext x
      exact (innerSL_apply_apply (𝕜 := ℝ) a x).symm
    rw [he]
    exact (innerSL ℝ a).contDiff
  have hLoc : LocallyIntegrable (fun x => U x - inner ℝ a x) volume :=
    (gibbsLp_locallyIntegrable_volume hV.continuous hp (u : E →₂[gibbsMeasure volume V] ℝ)).sub
      hlin.continuous.locallyIntegrable
  have hweak (ψ : E → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ) (i : Fin d) :
      (∫ x, coordinateDerivative i ψ x * (U x - inner ℝ a x)) = 0 := by
    have hDψ := (c1_coordinateDerivative_of_c2 (hψ.of_le (by norm_num)) i).continuous
    have hDψc : HasCompactSupport (coordinateDerivative i ψ) :=
      hψc.fderiv_apply ℝ (EuclideanSpace.single i 1)
    have hDU := integrable_compact_test_mul_gibbsLp_volume hV.continuous hp hDψ hDψc
      (u : E →₂[gibbsMeasure volume V] ℝ)
    have hDL : Integrable (fun x => coordinateDerivative i ψ x * inner ℝ a x) volume :=
      (hDψ.mul hlin.continuous).integrable_of_hasCompactSupport
        (by simpa only [Pi.mul_def] using hDψc.mul_right (f' := fun x => inner ℝ a x))
    have he := gibbsSobolev_coordinate_weak_derivative_volume hV hp (hψ.of_le (by norm_num)) hψc i
      (gibbsOperatorEigenSobolevLift hV hp ρ u)
    rw [gibbsOperatorEigenSobolevLift_inclusion] at he
    have hGi : (∫ x, ψ x * (G x) i) = ∫ x, ψ x * a i := by
      apply integral_congr_ae
      filter_upwards [ha] with x hx
      rw [hx]
    change (∫ x, ψ x * (G x) i) = -(∫ x, coordinateDerivative i ψ x * U x) at he
    rw [hGi] at he
    have hDl (x : E) : coordinateDerivative i (fun y : E => inner ℝ a y) x = a i := by
      have hg : gradient (fun y : E => inner ℝ a y) x = a := by
        simpa only [add_zero] using gradient_inner_add_const a 0 x
      rw [coordinateDerivative, fderiv_single_eq_gradient_coordinate, hg]
    have hl := compact_directional_gibbs_ibp (V := fun _ : E => 0) contDiff_const
      (hψ.of_le (by norm_num)) (hlin.of_le (by norm_num)) hψc i
    have hμ0 : gibbsMeasure (volume : Measure E) (fun _ => 0) = volume := by simp [gibbsMeasure]
    rw [hμ0] at hl
    have hz (x : E) : coordinateDerivative i (fun _ : E => (0 : ℝ)) x = 0 := by
      simp [coordinateDerivative]
    change (∫ x, ψ x * coordinateDerivative i (fun y : E => inner ℝ a y) x) =
      -(∫ x, (coordinateDerivative i ψ x - ψ x * coordinateDerivative i (fun _ : E => 0) x) *
        inner ℝ a x) at hl
    simp_rw [hDl, hz] at hl
    simp only [mul_zero, sub_zero] at hl
    simp_rw [mul_sub]
    rw [integral_sub hDU hDL]
    dsimp only [U] at *
    linarith only [he, hl]
  obtain ⟨b, hb⟩ := ae_eq_const_of_locallyIntegrable_weak_derivative_zero_c3 hLoc hweak
  refine ⟨a, b, ha, ?_⟩
  filter_upwards [hb] with x hx
  change U x - inner ℝ a x = b at hx
  change U x = inner ℝ a x + b
  linarith

/-- The actual weak operator equation identifies the genuine affine
representative as a pointwise classical eigenfunction. This uses continuous
residual uniqueness for actual compact tests, without elliptic regularity. -/
theorem gibbsOperatorEigen_affine_pointwise_equation {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate) (a : E) (b : ℝ)
    (ha : (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) : E → E)
      =ᵐ[volume] fun _ => a)
    (hu : (u : E →₂[gibbsMeasure volume V] ℝ) =ᵐ[volume] fun x => inner ℝ a x + b) :
    ∀ x, langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
      -rate * (inner ℝ a x + b) := by
  let := hp
  let f (x : E) := inner ℝ a x + b
  have hf : ContDiff ℝ 2 f := by
    have he : f = fun x => (innerSL ℝ a : E → ℝ) x + b := by
      funext x
      rw [innerSL_apply_apply]
    rw [he]
    exact (innerSL ℝ a).contDiff.add contDiff_const
  have hgrad (x : E) : gradient f x = a := gradient_inner_add_const a b x
  have hLf := continuous_langevinDifferentialOperator hV hf
  have hres : Continuous (fun x => langevinDifferentialOperator V f x + rate * f x) :=
    hLf.add (continuous_const.mul hf.continuous)
  have hweak (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
      (∫ x, ψ x • (langevinDifferentialOperator V f x + rate * f x) ∂gibbsMeasure volume V) = 0
        := by
    have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
    have he := gibbsOperatorEigen_compact_test_equation hV hp rate u hψ2 hψc
    have haμ := (gibbsMeasure_absolutelyContinuous volume V).ae_eq ha
    have huμ := (gibbsMeasure_absolutelyContinuous volume V).ae_eq hu
    have hleft : (∫ x, inner ℝ
        (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x)
        (gradient ψ x) ∂gibbsMeasure volume V) =
        ∫ x, inner ℝ a (gradient ψ x) ∂gibbsMeasure volume V := by
      apply integral_congr_ae
      filter_upwards [haμ] with x hx
      rw [hx]
    have hright : (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * ψ x ∂gibbsMeasure volume V) =
        ∫ x, ψ x * f x ∂gibbsMeasure volume V := by
      apply integral_congr_ae
      filter_upwards [huμ] with x hx
      rw [hx]
      exact mul_comm _ _
    rw [hleft, hright] at he
    have hibp := compact_test_gibbs_energy hV (hψ2.of_le (by norm_num)) hf hψc
    simp_rw [hgrad] at hibp
    have hswap : (∫ x, inner ℝ (gradient ψ x) a ∂gibbsMeasure volume V) =
        ∫ x, inner ℝ a (gradient ψ x) ∂gibbsMeasure volume V := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => real_inner_comm _ _)
    rw [hswap] at hibp
    have hLI := integrable_cutoff_mul_continuous hV.continuous hψ.continuous hψc hLf
    have hFI := integrable_cutoff_mul_continuous hV.continuous hψ.continuous hψc hf.continuous
    have hpnt (x : E) : ψ x • (langevinDifferentialOperator V f x + rate * f x) =
        ψ x * langevinDifferentialOperator V f x + rate * (ψ x * f x) := by
      rw [smul_eq_mul]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpnt),
      integral_add hLI (hFI.const_mul rate), integral_const_mul]
    linarith only [he, hibp]
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hres.locallyIntegrable hweak
  have hz := gibbsMeasure_eq_of_ae_eq volume hV.continuous.measurable hres continuous_const hae
  intro x
  have hx := congrFun hz x
  change langevinDifferentialOperator V f x = -rate * f x
  linarith

/-- The actual curvature-rate operator eigenspace consists of genuine C²
eigenfunctions, as proved by weak Bochner rigidity rather than a definition. -/
theorem gibbsOperatorEigenspace_le_classicalL2Eigenspace {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    gibbsOperatorEigenspace hV hp ρ ≤ classicalL2Eigenspace V ρ := by
  intro u hu
  let v : gibbsOperatorEigenspace hV hp ρ := ⟨u, hu⟩
  obtain ⟨a, b, ha, hb⟩ := gibbsOperatorEigen_equalRate_affine_representative hV hp ρ hρ hHess v
  refine ⟨fun x => inner ℝ a x + b, ?_,
    gibbsOperatorEigen_affine_pointwise_equation hV hp ρ v a b ha hb,
    ((gibbsMeasure_absolutelyContinuous volume V).ae_eq hb).symm⟩
  have he : (fun x : E => inner ℝ a x + b) = fun x => (innerSL ℝ a : E → ℝ) x + b := by
    funext x
    rw [innerSL_apply_apply]
  rw [he]
  exact (innerSL ℝ a).contDiff.add contDiff_const

/-- Equality of the actual operator and classical curvature-rate
eigenspaces, derived in both directions. -/
theorem gibbsOperatorEigenspace_eq_classicalL2Eigenspace {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    gibbsOperatorEigenspace hV hp ρ = classicalL2Eigenspace V ρ :=
  le_antisymm (gibbsOperatorEigenspace_le_classicalL2Eigenspace hV hp ρ hρ hHess)
    (classicalL2Eigenspace_le_gibbsOperatorEigenspace hV hp ρ hρ.le)

end CutoffRigidity
