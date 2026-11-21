/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorWeakGradientDomain
public import LeanPool.CutoffRigidity.GibbsCompactWeakH1

/-! # Differentiating the genuine operator eigenfunction equation

Compact weighted integration by parts applies to the actual weak Hessian.
These identities implement the coordinate calculation without a classical
representative or a third derivative of the potential.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integrable_compact_gibbsVector_coordinate {V a : E → ℝ}
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ha : Continuous a) (hac : HasCompactSupport a)
    (G : E →₂[gibbsMeasure volume V] E) (j : Fin d) :
    Integrable (fun x => a x * (G x) j) (gibbsMeasure volume V) := by
  let := hprob
  have ham : MemLp a 2 (gibbsMeasure volume V) := ha.memLp_of_hasCompactSupport hac
  exact ham.integrable_mul
    ((EuclideanSpace.proj j : E →L[ℝ] ℝ).comp_memLp G)

theorem coordinateDerivative_eq_zero_of_notMem_tsupport {ψ : E → ℝ}
    (i : Fin d) {x : E} (hx : x ∉ tsupport ψ) : coordinateDerivative i ψ x = 0 := by
  unfold coordinateDerivative
  rw [fderiv_of_notMem_tsupport ℝ hx]
  rfl

theorem coordinateDerivative_tsupport_subset (ψ : E → ℝ) (i : Fin d) :
    tsupport (coordinateDerivative i ψ) ⊆ tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)

/-- A genuine localization equals the original weak gradient wherever the
cutoff has value one and zero first derivatives. -/
theorem localizedOperatorEigenGradient_eq_of_cutoff_jet {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hprob rate) (i : Fin d) (x : E)
    (hχ : χ x = 1) (hDχ : coordinateDerivative i χ x = 0) :
    localizedOperatorEigenGradient hV hprob rate u χ i x =
      (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) i := by
  simp [localizedOperatorEigenGradient, hχ, hDχ]

/-- The weighted-adjoint derivative test only sees the original gradient
inside the region where the actual cutoff is identically one. -/
theorem weightedAdjoint_mul_localizedOperatorEigenGradient {V χ ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hprob rate)
    (hlocal : ∀ x ∈ tsupport ψ, χ x = 1 ∧ ∀ k, coordinateDerivative k χ x = 0)
    (i j : Fin d) (x : E) :
    coordinateWeightedAdjoint i V (coordinateDerivative j ψ) x *
        localizedOperatorEigenGradient hV hprob rate u χ j x =
      coordinateWeightedAdjoint i V (coordinateDerivative j ψ) x *
        (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) j := by
  by_cases hx : x ∈ tsupport ψ
  · rw [localizedOperatorEigenGradient_eq_of_cutoff_jet hV hprob rate u j x
      (hlocal x hx).1 ((hlocal x hx).2 j)]
  · have hj := coordinateDerivative_eq_zero_of_notMem_tsupport j hx
    have hij := coordinateDerivative_eq_zero_of_notMem_tsupport i
      (fun h => hx (coordinateDerivative_tsupport_subset ψ j h))
    simp [coordinateWeightedAdjoint, hj, hij]

/-- The actual coordinate commutator calculation for an operator
eigenvector. All Hessian terms are genuine L² weak derivatives already
constructed from the equation. -/
theorem gibbsOperatorEigen_weightedAdjoint_gradient_row {V χ ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hprob rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ)
    (hlocal : ∀ x ∈ tsupport ψ, χ x = 1 ∧ ∀ k, coordinateDerivative k χ x = 0)
    (i j : Fin d) :
    (∫ x, coordinateDerivative j (coordinateWeightedAdjoint i V ψ) x *
      (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) j
      ∂gibbsMeasure volume V) =
    -(∫ x, coordinateDerivative j ψ x *
      gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i j x ∂gibbsMeasure volume V) -
    (∫ x, ψ x * (coordinateDerivative i (coordinateDerivative j V) x *
      (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) j)
      ∂gibbsMeasure volume V) := by
  let G := gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u)
  let b := coordinateWeightedAdjoint i V (coordinateDerivative j ψ)
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have hDψ : ContDiff ℝ 2 (coordinateDerivative j ψ) := by
    apply contDiff_coordinateDerivative
    convert hψ using 1
    norm_num
  have hDψc : HasCompactSupport (coordinateDerivative j ψ) :=
    hψc.fderiv_apply ℝ (EuclideanSpace.single j 1)
  have hb : Continuous b := continuous_coordinateWeightedAdjoint hV
    (hDψ.of_le (by norm_num)) i
  have hbc : HasCompactSupport b := hasCompactSupport_coordinateWeightedAdjoint hDψc i
  have hIntb := integrable_compact_gibbsVector_coordinate hprob hb hbc G j
  have hVij := continuous_coordinateDerivative_of_c1 (c1_coordinateDerivative_of_c2 hV j) i
  have hCoeff : Continuous (fun x => ψ x * coordinateDerivative i (coordinateDerivative j V) x) :=
    hψ.continuous.mul hVij
  have hCoeffc : HasCompactSupport (fun x => ψ x * coordinateDerivative i (coordinateDerivative j
    V) x) := by
    simpa only [Pi.mul_def] using hψc.mul_right
      (f' := coordinateDerivative i (coordinateDerivative j V))
  have hIntV : Integrable (fun x => ψ x *
      (coordinateDerivative i (coordinateDerivative j V) x * (G x) j)) (gibbsMeasure volume V) := by
    simpa only [mul_assoc] using integrable_compact_gibbsVector_coordinate hprob hCoeff hCoeffc G j
  have hpoint (x : E) :
      coordinateDerivative j (coordinateWeightedAdjoint i V ψ) x * (G x) j =
      b x * (G x) j - ψ x * (coordinateDerivative i (coordinateDerivative j V) x * (G x) j) := by
    rw [coordinateDerivative_weightedAdjoint hV hψ2,
      coordinateDerivative_commute hψ2 j i, coordinateDerivative_commute hV j i]
    dsimp only [b, coordinateWeightedAdjoint]
    ring
  have ht := integral_congr_ae (μ := gibbsMeasure volume V)
    (Filter.Eventually.of_forall hpoint)
  rw [integral_sub hIntb hIntV] at ht
  have hi := gibbsOperatorLocalizedHessian_weighted_ibp hV hprob ρ hρ hHess rate u
    hχ hχc hDψ hDψc j i
  have heq := integral_congr_ae (μ := gibbsMeasure volume V)
    (Filter.Eventually.of_forall
      (weightedAdjoint_mul_localizedOperatorEigenGradient hV hprob rate u hlocal i j))
  change (∫ x, b x * localizedOperatorEigenGradient hV hprob rate u χ j x ∂gibbsMeasure volume V) =
    ∫ x, b x * (G x) j ∂gibbsMeasure volume V at heq
  change (∫ x, coordinateDerivative j ψ x *
    gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc j i x ∂gibbsMeasure volume V) =
    -(∫ x, b x * localizedOperatorEigenGradient hV hprob rate u χ j x ∂gibbsMeasure volume V) at hi
  rw [heq, gibbsOperatorLocalizedHessian_symmetric hV hprob rate u hχ hχc j i] at hi
  change _ = -_ - _
  linarith

/-- A compact test derivative times a coordinate of the localized weak Hessian is integrable. -/
theorem integrable_gibbsTest_localizedHessian {V χ ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hprob rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i j : Fin d) :
    Integrable (fun x => coordinateDerivative j ψ x *
      gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i j x) (gibbsMeasure volume V) := by
  let := hprob
  have hH : MemLp (gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i j) 2
      (gibbsMeasure volume V) :=
    (memLp_congr_ae (gibbsOperatorLocalizedGradientSobolevLift_derivative_coordinate_ae
      hV hprob ρ hρ hHess rate u hχ hχc i j)).mp
      ((EuclideanSpace.proj j : E →L[ℝ] ℝ).comp_memLp
        (gibbsSobolevDerivative hV hprob
          (gibbsOperatorLocalizedGradientSobolevLift hV hprob ρ hρ hHess rate u hχ hχc i)))
  have hD : MemLp (coordinateDerivative j ψ) 2 (gibbsMeasure volume V) :=
    (c1_coordinateDerivative_of_c2 hψ j).continuous.memLp_of_hasCompactSupport
      (hψc.fderiv_apply ℝ (EuclideanSpace.single j 1))
  exact hD.integrable_mul hH

/-- A compact scalar test times a potential Hessian coefficient and an L² gradient
coordinate is Gibbs integrable. -/
theorem integrable_gibbsTest_potentialHessian_coordinate {V ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (G : E →₂[gibbsMeasure volume V] E) (i j : Fin d) :
    Integrable (fun x => ψ x * (coordinateDerivative i (coordinateDerivative j V) x * (G x) j))
      (gibbsMeasure volume V) := by
  have hc := hψ.mul
    (continuous_coordinateDerivative_of_c1 (c1_coordinateDerivative_of_c2 hV j) i)
  have hs : HasCompactSupport (fun x => ψ x * coordinateDerivative i (coordinateDerivative j V)
    x) := by
    simpa only [Pi.mul_def] using hψc.mul_right
      (f' := coordinateDerivative i (coordinateDerivative j V))
  simpa only [Pi.mul_apply, mul_assoc] using integrable_compact_gibbsVector_coordinate hprob hc
    hs G j

/-- The differentiated eigenfunction equation for compact tests. This weak
Euclidean form of the coordinate calculation in Chafaï–Fathi, arXiv:2412.15969v5,
Section 1.5, uses an L² operator eigenclass and its locally constructed weak Hessian. -/
theorem gibbsOperatorEigen_differentiated_weak_equation {V χ ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hprob rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ)
    (hlocal : ∀ x ∈ tsupport ψ, χ x = 1 ∧ ∀ k, coordinateDerivative k χ x = 0)
    (i : Fin d) :
    (∫ x, ∑ j : Fin d, coordinateDerivative j ψ x *
      gibbsOperatorLocalizedHessian hV hprob rate u hχ hχc i j x ∂gibbsMeasure volume V) +
    (∫ x, ψ x * (∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x *
      (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) j)
      ∂gibbsMeasure volume V) =
    rate * (∫ x, ψ x *
      (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) i
      ∂gibbsMeasure volume V) := by
  let := hprob
  let G := gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u)
  let a := coordinateWeightedAdjoint i V ψ
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have ha := c1_coordinateWeightedAdjoint hV hψ2 i
  have hac : HasCompactSupport a := hasCompactSupport_coordinateWeightedAdjoint hψc i
  have hGradInt := integrable_gibbsTest_localizedHessian hV hprob ρ hρ hHess rate u
    hχ hχc hψ2 hψc i
  have hHessInt := integrable_gibbsTest_potentialHessian_coordinate hV hprob
    hψ.continuous hψc G i
  have hDerInt (j : Fin d) : Integrable (fun x => coordinateDerivative j a x * (G x) j)
      (gibbsMeasure volume V) :=
    integrable_compact_gibbsVector_coordinate hprob (continuous_coordinateDerivative_of_c1 ha j)
      (hac.fderiv_apply ℝ (EuclideanSpace.single j 1)) G j
  have henergy := gibbsOperatorEigen_compact_c1_test_equation hV hprob ρ hρ hHess rate u ha hac
  have hpoint (x : E) : inner ℝ (G x) (gradient a x) =
      ∑ j : Fin d, coordinateDerivative j a x * (G x) j := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.inner_apply, ← fderiv_single_eq_gradient_coordinate]
    exact mul_comm _ _
  have henergy' : (∫ x, ∑ j : Fin d, coordinateDerivative j a x * (G x) j ∂gibbsMeasure volume V) =
      rate * (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * a x ∂gibbsMeasure volume V) := by
    change (∫ x, inner ℝ (G x) (gradient a x) ∂gibbsMeasure volume V) =
      rate * (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * a x ∂gibbsMeasure volume V) at henergy
    simpa only [hpoint] using henergy
  have hi := gibbsSobolev_coordinate_weak_derivative hV hprob hψ2 hψc i
    (gibbsOperatorEigenSobolevLift hV hprob rate u)
  rw [gibbsOperatorEigenSobolevLift_inclusion] at hi
  change (∫ x, ψ x * (G x) i ∂gibbsMeasure volume V) =
    -(∫ x, a x * (u : E →₂[gibbsMeasure volume V] ℝ) x ∂gibbsMeasure volume V) at hi
  have hUa : (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * a x ∂gibbsMeasure volume V) =
    ∫ x, a x * (u : E →₂[gibbsMeasure volume V] ℝ) x ∂gibbsMeasure volume V := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
  rw [hUa, integral_finsetSum _ (fun j _ => hDerInt j)] at henergy'
  have hrow := gibbsOperatorEigen_weightedAdjoint_gradient_row hV hprob ρ hρ hHess
    rate u hχ hχc hψ hψc hlocal i
  dsimp only [a, G] at henergy'
  simp_rw [hrow] at henergy'
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at henergy'
  rw [integral_finsetSum _ (fun j _ => hGradInt j)]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => hHessInt j)]
  dsimp only [a, G] at hi ⊢
  rw [hi]
  nlinarith only [henergy']

end CutoffRigidity
