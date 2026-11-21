/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorWeakDifferentiation
public import LeanPool.CutoffRigidity.WeakGradientEnergyTest

/-! # Genuine local Bochner energy testing for actual operator eigenvectors

The weighted differentiated equation is tested against localized weak
gradient coordinates using their proved strong H¹ mollifications.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A localized Hessian entry multiplied by the cutoff and the Gibbs density. -/
@[expose] noncomputable def gibbsOperatorWeightedLocalHessian {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hp rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i j : Fin d) (x : E) : ℝ :=
  (χ x * Real.exp (-V x)) * gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x

/-- The gradient row of the differentiated eigen-equation, weighted by the cutoff and Gibbs
density. -/
@[expose] noncomputable def gibbsOperatorWeightedLocalGradientRhs {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hp rate) (χ : E → ℝ) (i : Fin d) (x : E) : ℝ :=
  (χ x * Real.exp (-V x)) *
    (rate * (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i -
      ∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x *
        (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) j)

theorem gibbsOperatorWeightedLocalHessian_memLp {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hp rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i j : Fin d) : MemLp (gibbsOperatorWeightedLocalHessian hV hp rate u hχ hχc i j) 2 volume := by
  have hc : Continuous (fun x => χ x * Real.exp (-V x)) := by fun_prop
  have hs : HasCompactSupport (fun x => χ x * Real.exp (-V x)) := by
    simpa only [Pi.mul_def] using hχc.mul_right (f' := fun x => Real.exp (-V x))
  exact (hc.memLp_of_hasCompactSupport hs : MemLp _ ⊤ volume).fun_mul
    (Lp.memLp (gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j))

theorem gibbsOperatorWeightedLocalGradientRhs_memLp {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hp rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i : Fin d) : MemLp (gibbsOperatorWeightedLocalGradientRhs hV hp rate u χ i) 2 volume := by
  let G := gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u)
  have hc : Continuous (fun x => χ x * Real.exp (-V x)) := by fun_prop
  have hs : HasCompactSupport (fun x => χ x * Real.exp (-V x)) := by
    simpa only [Pi.mul_def] using hχc.mul_right (f' := fun x => Real.exp (-V x))
  have hfirst := (compact_cutoff_gibbsVector_coordinate_memLp_volume hV.continuous hc hs G
    i).const_mul rate
  have hterm (j : Fin d) : MemLp (fun x =>
      ((χ x * Real.exp (-V x)) * coordinateDerivative i (coordinateDerivative j V) x) * (G x) j)
      2 volume := by
    have hcj := hc.mul (continuous_coordinateDerivative_of_c1 (c1_coordinateDerivative_of_c2 hV j)
      i)
    have hsj : HasCompactSupport (fun x =>
        (χ x * Real.exp (-V x)) * coordinateDerivative i (coordinateDerivative j V) x) := by
      simpa only [Pi.mul_def] using hs.mul_right (f' := coordinateDerivative i
        (coordinateDerivative j V))
    exact compact_cutoff_gibbsVector_coordinate_memLp_volume hV.continuous hcj hsj G j
  have hsum := memLp_finsetSum' Finset.univ (fun j _ => hterm j)
  convert hfirst.sub hsum using 1
  funext x
  simp only [gibbsOperatorWeightedLocalGradientRhs, Pi.sub_apply, Finset.sum_apply, G]
  simp_rw [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

/-- The actual local differentiated equation, written as a genuine
Lebesgue weak divergence identity with actual L² coefficients. -/
theorem gibbsOperatorEigen_weighted_local_divergence {V χ η : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hlocal : ∀ x ∈ tsupport η, χ x = 1 ∧ ∀ k, coordinateDerivative k χ x = 0)
    (i : Fin d) (ψ : E → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ tsupport η) :
    (∑ j : Fin d, ∫ x, coordinateDerivative j ψ x *
      gibbsOperatorWeightedLocalHessian hV hp rate u hχ hχc i j x) =
    ∫ x, ψ x * gibbsOperatorWeightedLocalGradientRhs hV hp rate u χ i x := by
  let G := gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u)
  have he := gibbsOperatorEigen_differentiated_weak_equation hV hp ρ hρ hHess rate u
    hχ hχc hψ hψc (fun x hx => hlocal x (hψs hx)) i
  have hL (j : Fin d) : (∫ x, coordinateDerivative j ψ x *
      gibbsOperatorWeightedLocalHessian hV hp rate u hχ hχc i j x) =
      ∫ x, coordinateDerivative j ψ x *
        gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x ∂gibbsMeasure volume V := by
    rw [integral_gibbsMeasure volume hV.continuous.measurable]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport η
    · simp only [gibbsOperatorWeightedLocalHessian, (hlocal x hx).1, one_mul, smul_eq_mul]
      ring
    · have hz := coordinateDerivative_eq_zero_of_notMem_tsupport j (fun h => hx (hψs h))
      simp [hz]
  have hR : (∫ x, ψ x * gibbsOperatorWeightedLocalGradientRhs hV hp rate u χ i x) =
      ∫ x, rate * (ψ x * (G x) i) -
        ψ x * (∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x * (G x) j)
        ∂gibbsMeasure volume V := by
    rw [integral_gibbsMeasure volume hV.continuous.measurable]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport η
    · simp only [gibbsOperatorWeightedLocalGradientRhs, (hlocal x hx).1, one_mul, smul_eq_mul]
      dsimp only [G]
      ring
    · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hψs h))
      simp [hz]
  have hGi := integrable_compact_gibbsVector_coordinate hp hψ.continuous hψc G i
  have hVterm := integrable_gibbsTest_potentialHessian_coordinate hV hp hψ.continuous hψc G i
  have hVsum : Integrable (fun x => ψ x *
      (∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x * (G x) j))
      (gibbsMeasure volume V) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ (fun j _ => hVterm j)
  rw [hR, integral_sub (hGi.const_mul rate) hVsum, integral_const_mul]
  simp_rw [hL]
  have hGradInt := integrable_gibbsTest_localizedHessian hV hp ρ hρ hHess rate u
    hχ hχc (hψ.of_le (by norm_num)) hψc i
  rw [integral_finsetSum _ (fun j _ => hGradInt j)] at he
  dsimp only [G] at *
  linarith only [he]

/-- The actual row-wise localized Bochner energy identity, justified by
strong H¹ approximation of the weak gradient coordinate. Every coefficient
is an actual Gibbs density times a proved actual weak derivative. -/
theorem gibbsOperatorEigen_localized_row_energy {V χ η : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hη : ContDiff ℝ 3 η) (hηc : HasCompactSupport η)
    (hlocal : ∀ x ∈ tsupport η, χ x = 1 ∧ ∀ k, coordinateDerivative k χ x = 0)
    (i : Fin d) :
    (∑ j : Fin d, ∫ x, gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x *
      (η x ^ 2 * gibbsOperatorWeightedLocalHessian hV hp rate u hχ hχc i j x)) +
    (∑ j : Fin d, ∫ x, localizedOperatorEigenGradient hV hp rate u χ i x *
      (2 * η x * coordinateDerivative j η x *
        gibbsOperatorWeightedLocalHessian hV hp rate u hχ hχc i j x)) =
    ∫ x, localizedOperatorEigenGradient hV hp rate u χ i x *
      (η x ^ 2 * gibbsOperatorWeightedLocalGradientRhs hV hp rate u χ i x) := by
  apply weak_divergence_localized_energy_test_raw
    (localizedOperatorEigenGradient_measurable hV hp rate u hχ i)
    (localizedOperatorEigenGradient_memLp hV hp rate u hχ hχc i)
    (fun j => gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j)
    (fun j => gibbsOperatorWeightedLocalHessian hV hp rate u hχ hχc i j)
    (fun j => gibbsOperatorWeightedLocalHessian_memLp hV hp rate u hχ hχc i j)
    (gibbsOperatorWeightedLocalGradientRhs_memLp hV hp rate u hχ hχc i)
    (fun j ψ hψ hψc => gibbsOperatorLocalizedHessian_weak_derivative
      hV hp rate u hχ hχc i j ψ hψ hψc) hη hηc
  intro ψ hψ hψc hψs
  exact gibbsOperatorEigen_weighted_local_divergence hV hp ρ hρ hHess rate u
    hχ hχc hlocal i ψ hψ hψc hψs

/-- The local row energy identity expressed as integrals against the Gibbs
measure, after removing the auxiliary density and localization factors. -/
theorem gibbsOperatorEigen_localized_row_bochner {V χ η : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hη : ContDiff ℝ 3 η) (hηc : HasCompactSupport η)
    (hlocal : ∀ x ∈ tsupport η, χ x = 1 ∧ ∀ k, coordinateDerivative k χ x = 0)
    (i : Fin d) :
    (∑ j : Fin d, ∫ x, η x ^ 2 *
      (gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x) ^ 2 ∂gibbsMeasure volume V) +
    (∑ j : Fin d, ∫ x, 2 * η x * coordinateDerivative j η x *
      (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i *
      gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x ∂gibbsMeasure volume V) =
    ∫ x, η x ^ 2 *
      (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i *
      (rate * (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i -
        ∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x *
          (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) j)
      ∂gibbsMeasure volume V := by
  have he := gibbsOperatorEigen_localized_row_energy hV hp ρ hρ hHess rate u hχ hχc hη hηc hlocal i
  have hA (j : Fin d) :
      (∫ x, gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x *
        (η x ^ 2 * gibbsOperatorWeightedLocalHessian hV hp rate u hχ hχc i j x)) =
      ∫ x, η x ^ 2 * (gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x) ^ 2
        ∂gibbsMeasure volume V := by
    rw [integral_gibbsMeasure volume hV.continuous.measurable]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport η
    · simp only [gibbsOperatorWeightedLocalHessian, (hlocal x hx).1, one_mul, smul_eq_mul]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hB (j : Fin d) :
      (∫ x, localizedOperatorEigenGradient hV hp rate u χ i x *
        (2 * η x * coordinateDerivative j η x *
          gibbsOperatorWeightedLocalHessian hV hp rate u hχ hχc i j x)) =
      ∫ x, 2 * η x * coordinateDerivative j η x *
        (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i *
          gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x ∂gibbsMeasure volume V := by
    rw [integral_gibbsMeasure volume hV.continuous.measurable]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport η
    · rw [localizedOperatorEigenGradient_eq_of_cutoff_jet hV hp rate u i x
        (hlocal x hx).1 ((hlocal x hx).2 i)]
      simp only [gibbsOperatorWeightedLocalHessian, (hlocal x hx).1, one_mul, smul_eq_mul]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hC :
      (∫ x, localizedOperatorEigenGradient hV hp rate u χ i x *
        (η x ^ 2 * gibbsOperatorWeightedLocalGradientRhs hV hp rate u χ i x)) =
      ∫ x, η x ^ 2 *
        (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i *
        (rate * (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i -
          ∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x *
            (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) j)
        ∂gibbsMeasure volume V := by
    rw [integral_gibbsMeasure volume hV.continuous.measurable]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport η
    · rw [localizedOperatorEigenGradient_eq_of_cutoff_jet hV hp rate u i x
        (hlocal x hx).1 ((hlocal x hx).2 i)]
      simp only [gibbsOperatorWeightedLocalGradientRhs, (hlocal x hx).1, one_mul, smul_eq_mul]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  simp_rw [hA, hB, hC] at he
  exact he

end CutoffRigidity
