/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorLocalBochner

/-! # Integrability and actual localizers for weak operator Bochner estimates -/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A compact continuous coefficient times two actual Gibbs L² functions
is integrable; no smoothness of either L² function is required. -/
theorem integrable_compact_coefficient_L2_product {V a f g : E → ℝ}
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ha : Continuous a) (hac : HasCompactSupport a)
    (hf : MemLp f 2 (gibbsMeasure volume V)) (hg : MemLp g 2 (gibbsMeasure volume V)) :
    Integrable (fun x => a x * f x * g x) (gibbsMeasure volume V) := by
  let := hp
  have ham : MemLp a ⊤ (gibbsMeasure volume V) := ha.memLp_of_hasCompactSupport hac
  have haf : MemLp (fun x => a x * f x) 2 (gibbsMeasure volume V) := ham.fun_mul hf
  simpa only [Pi.mul_def] using haf.integrable_mul hg

theorem gibbsOperatorLocalizedHessian_memLp_gibbs {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (i j : Fin d) :
    MemLp (gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j) 2 (gibbsMeasure volume V) :=
  (memLp_congr_ae (volumeToGibbsL2_coeFn hV ρ hρ hHess _)).mp
    (Lp.memLp (volumeToGibbsL2 hV ρ hρ hHess
      (gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j)))

/-- Every compact set has an actual smooth compact cutoff equal to one
on an open neighborhood, hence with zero actual coordinate derivatives. -/
theorem exists_compact_C3_cutoff_one_jet (K : Set E) (hK : IsCompact K) :
    ∃ χ : E → ℝ, ContDiff ℝ 3 χ ∧ HasCompactSupport χ ∧
      ∀ x ∈ K, χ x = 1 ∧ ∀ i : Fin d, coordinateDerivative i χ x = 0 := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : E)
  let φ : ContDiffBump (0 : E) := ⟨R, 2 * R, hR, by linarith⟩
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_⟩
  intro x hx
  have he : (φ : E → ℝ) =ᶠ[𝓝 x] (fun _ => 1) := φ.eventuallyEq_one_of_mem_ball (hKR hx)
  refine ⟨he.eq_of_nhds, ?_⟩
  intro i
  unfold coordinateDerivative
  rw [he.fderiv_eq]
  simp

/-- The actual compact weak Hessian energy appearing in each coordinate
of the localized Bochner identity is integrable. -/
theorem operatorEigen_local_hessian_energy_integrable {V χ η : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hη : Continuous η) (hηc : HasCompactSupport η) (i j : Fin d) :
    Integrable (fun x => η x ^ 2 *
      (gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x) ^ 2) (gibbsMeasure volume V) := by
  have hs : HasCompactSupport (fun x => η x ^ 2) := by
    simpa only [Pi.mul_def, pow_two] using hηc.mul_right (f' := η)
  have hc : Continuous (fun x => η x ^ 2) := by
    simpa only [Pi.mul_def, pow_two] using hη.mul hη
  have hH := gibbsOperatorLocalizedHessian_memLp_gibbs hV hp ρ hρ hHess rate u hχ hχc i j
  simpa only [pow_two, mul_assoc] using integrable_compact_coefficient_L2_product hp hc hs hH hH

theorem gibbsOperatorEigen_gradient_coordinate_memLp {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate) (i : Fin d) :
    MemLp (fun x =>
      (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i)
      2 (gibbsMeasure volume V) :=
  (EuclideanSpace.proj i : E →L[ℝ] ℝ).comp_memLp
    (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u))

theorem operatorEigen_local_bochner_cross_integrable {V χ η : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (i j : Fin d) :
    Integrable (fun x => 2 * η x * coordinateDerivative j η x *
      (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i *
      gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x) (gibbsMeasure volume V) := by
  have hD := (c1_coordinateDerivative_of_c2 hη j).continuous
  have hc : Continuous (fun x => 2 * η x * coordinateDerivative j η x) := by fun_prop
  have hs : HasCompactSupport (fun x => 2 * η x * coordinateDerivative j η x) := by
    have hh : HasCompactSupport (fun x => 2 * η x) := by
      simpa only [Function.comp_def] using hηc.comp_left (g := fun r : ℝ => 2 * r) (by simp)
    simpa only [Pi.mul_def] using hh.mul_right (f' := coordinateDerivative j η)
  exact integrable_compact_coefficient_L2_product hp hc hs
    (gibbsOperatorEigen_gradient_coordinate_memLp hV hp rate u i)
    (gibbsOperatorLocalizedHessian_memLp_gibbs hV hp ρ hρ hHess rate u hχ hχc i j)

theorem operatorEigen_local_gradient_potential_integrable {V η : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate)
    (hη : Continuous η) (hηc : HasCompactSupport η) (i j : Fin d) :
    Integrable (fun x => η x ^ 2 *
      (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i *
      (coordinateDerivative i (coordinateDerivative j V) x *
        (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) j))
      (gibbsMeasure volume V) := by
  have hc : Continuous (fun x => η x ^ 2 * coordinateDerivative i (coordinateDerivative j V) x) :=
    (hη.pow 2).mul (continuous_coordinateDerivative_of_c1 (c1_coordinateDerivative_of_c2 hV j) i)
  have hsc : HasCompactSupport (fun x => η x ^ 2) := by
    simpa only [Pi.mul_def, pow_two] using hηc.mul_right (f' := η)
  have hs : HasCompactSupport
      (fun x => η x ^ 2 * coordinateDerivative i (coordinateDerivative j V) x) := by
    simpa only [Pi.mul_def] using
      hsc.mul_right (f' := coordinateDerivative i (coordinateDerivative j V))
  convert integrable_compact_coefficient_L2_product hp hc hs
    (gibbsOperatorEigen_gradient_coordinate_memLp hV hp rate u i)
    (gibbsOperatorEigen_gradient_coordinate_memLp hV hp rate u j) using 1
  funext x
  ring

theorem operatorEigen_local_gradient_energy_integrable {V η : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate)
    (hη : Continuous η) (hηc : HasCompactSupport η) (i : Fin d) :
    Integrable (fun x => η x ^ 2 *
      ((gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i) ^ 2)
      (gibbsMeasure volume V) := by
  have hc : Continuous (fun x => η x ^ 2) := by
    simpa only [Pi.mul_def, pow_two] using hη.mul hη
  have hs : HasCompactSupport (fun x => η x ^ 2) := by
    simpa only [Pi.mul_def, pow_two] using hηc.mul_right (f' := η)
  have hGi := gibbsOperatorEigen_gradient_coordinate_memLp hV hp rate u i
  simpa only [pow_two, mul_assoc] using integrable_compact_coefficient_L2_product hp hc hs hGi hGi

end CutoffRigidity
