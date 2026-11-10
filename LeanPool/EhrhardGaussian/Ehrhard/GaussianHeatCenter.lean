/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott N. Armstrong
-/

/-
Ported from ASDExplicitGamma-dev/Gaussian/ConcentrationSemigroup.lean,
commit 2c9673f0bcca8062b441989bdc56f87b38715bb8.
Modified for EhrhardGaussian, 2026.
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianHeat
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Derivatives in the center of Gaussian heat averages -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard

/-- An affine Gaussian argument has a product bound in the norms of its location, scale and noise.
-/
lemma concentration_norm_add_smul_le {n : ℕ} (x ξ : Fin n → ℝ) (u : ℝ) :
    1 + ‖x + u • ξ‖ ≤ (1 + ‖x‖) * (1 + |u|) * (1 + ‖ξ‖) :=
  one_add_norm_add_smul_le x ξ u

/-- A Fréchet derivative evaluates as the sum of its coordinate derivatives times the direction
coordinates. -/
theorem concentration_fderiv_apply_eq_sum {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (z v : Fin n → ℝ) :
    fderiv ℝ F z v = ∑ i, v i * coordinateDerivative F i z :=
  fderiv_apply_eq_sum_coordinateDerivative z v

/-- A common bound on coordinate derivatives bounds every directional derivative by dimension times
the direction norm. -/
theorem concentration_abs_fderiv_apply_le {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (z v : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i, |coordinateDerivative F i z| ≤ B) :
    |fderiv ℝ F z v| ≤ (Fintype.card (Fin n) : ℝ) * ‖v‖ * B :=
  abs_fderiv_apply_le_of_coordinate_bound z v hB hcoord

/-- The scale derivative of a Gaussian average of a polynomially bounded C¹ function is the averaged
derivative in the Gaussian direction. -/
theorem hasDerivAt_shiftAverage_zero {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) (u : ℝ) :
    HasDerivAt (shiftAverage F 0)
      (∫ ξ, fderiv ℝ F (u • ξ) ξ ∂(standardGaussianMeasure n)) u := by
  simpa only [zero_add] using hasDerivAt_shiftAverage hF (0 : Fin n → ℝ) u

/-- Differentiating a polynomially bounded Gaussian shift in its centre. -/
theorem hasFDerivAt_shiftAverage_center {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (x : Fin n → ℝ) (c : ℝ) :
    Integrable (fun ξ => fderiv ℝ F (x + c • ξ)) (standardGaussianMeasure n) ∧
    HasFDerivAt (fun y => shiftAverage F y c)
      (∫ ξ, fderiv ℝ F (x + c • ξ) ∂(standardGaussianMeasure n)) x ∧
    ContinuousAt (fun y => ∫ ξ, fderiv ℝ F (y + c • ξ)
      ∂(standardGaussianMeasure n)) x := by
  rcases hF.2 with ⟨C, hC, d, hfunctionBound, hcoordinateBound⟩
  let Ψ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun y ξ => F (y + c • ξ)
  let Ψ' : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ :=
    fun y ξ => fderiv ℝ F (y + c • ξ)
  let B : ℝ := (2 + ‖x‖) * (1 + |c|)
  let K : ℝ := (Fintype.card (Fin n) : ℝ) * C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcontArg (y : Fin n → ℝ) : Continuous (fun ξ : Fin n → ℝ => y + c • ξ) := by
    exact continuous_const.add (continuous_id.const_smul c)
  have hFmeas : ∀ᶠ y in nhds x, AEStronglyMeasurable (Ψ y) (standardGaussianMeasure n) := by
    filter_upwards with y
    exact ((hF.1.continuous.comp (hcontArg y)).measurable).aestronglyMeasurable
  have hFint : Integrable (Ψ x) (standardGaussianMeasure n) := by
    let C' : ℝ := C * ((1 + ‖x‖) * (1 + |c|)) ^ d
    have hC' : 0 ≤ C' := by dsimp [C']; positivity
    apply integrable_of_pi_polynomial_bound
      ((hF.1.continuous.comp (hcontArg x)).measurable) hC' (d := d)
    intro ξ
    have hnorm : 1 + ‖x + c • ξ‖ ≤ (1 + ‖x‖) * (1 + |c|) * (1 + ‖ξ‖) :=
      concentration_norm_add_smul_le x ξ c
    calc
      |F (x + c • ξ)| ≤ C * (1 + ‖x + c • ξ‖) ^ d := hfunctionBound _
      _ ≤ C * ((1 + ‖x‖) * (1 + |c|) * (1 + ‖ξ‖)) ^ d := by gcongr
      _ = C' * (1 + ‖ξ‖) ^ d := by dsimp [C']; rw [mul_pow]; ring
  have hF'meas : AEStronglyMeasurable (Ψ' x) (standardGaussianMeasure n) := by
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact ((hfd.comp (hcontArg x)).measurable).aestronglyMeasurable
  have hpoly : Integrable (fun ξ : Fin n → ℝ => (1 + ‖ξ‖) ^ d)
      (standardGaussianMeasure n) := by
    apply integrable_of_pi_polynomial_bound (by fun_prop) (C := 1) (by norm_num) (d := d)
    intro ξ
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖ξ‖) ^ d)]
    simp
  have hboundInt : Integrable (fun ξ : Fin n → ℝ => K * (1 + ‖ξ‖) ^ d)
      (standardGaussianMeasure n) := by simpa using hpoly.const_mul K
  have hbound : ∀ᵐ ξ ∂(standardGaussianMeasure n), ∀ y ∈ Metric.ball x 1,
      ‖Ψ' y ξ‖ ≤ K * (1 + ‖ξ‖) ^ d := by
    apply ae_of_all
    intro ξ y hy
    have hyx : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy
    have hyNorm : ‖y‖ ≤ ‖x‖ + 1 := by
      calc
        ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
          calc
            ‖y‖ = ‖x + (y - x)‖ := by congr 1; abel
            _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + 1 := by linarith
    have hargNorm : 1 + ‖y + c • ξ‖ ≤ B * (1 + ‖ξ‖) := by
      calc
        1 + ‖y + c • ξ‖ ≤ (1 + ‖y‖) * (1 + |c|) * (1 + ‖ξ‖) :=
          concentration_norm_add_smul_le y ξ c
        _ ≤ B * (1 + ‖ξ‖) := by
          calc
            (1 + ‖y‖) * (1 + |c|) * (1 + ‖ξ‖) ≤
                (2 + ‖x‖) * (1 + |c|) * (1 + ‖ξ‖) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  linarith [hyNorm]
            _ = B * (1 + ‖ξ‖) := rfl
    have hcoord : ∀ i, |coordinateDerivative F i (y + c • ξ)| ≤
        C * (1 + ‖y + c • ξ‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (y + c • ξ)| ≤
            |F (y + c • ξ)| + |coordinateDerivative F i (y + c • ξ)| :=
              le_add_of_nonneg_left (abs_nonneg _)
        _ ≤ C * (1 + ‖y + c • ξ‖) ^ d := hcoordinateBound i _
    have hcoord' : ∀ i, |coordinateDerivative F i (y + c • ξ)| ≤
        C * B ^ d * (1 + ‖ξ‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (y + c • ξ)| ≤
            C * (1 + ‖y + c • ξ‖) ^ d := hcoord i
        _ ≤ C * (B * (1 + ‖ξ‖)) ^ d := by gcongr
        _ = C * B ^ d * (1 + ‖ξ‖) ^ d := by rw [mul_pow]; ring
    have hop : ‖fderiv ℝ F (y + c • ξ)‖ ≤ K * (1 + ‖ξ‖) ^ d := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      have hv := concentration_abs_fderiv_apply_le (y + c • ξ) v
        (by positivity : 0 ≤ C * B ^ d * (1 + ‖ξ‖) ^ d) hcoord'
      calc
        ‖fderiv ℝ F (y + c • ξ) v‖ = |fderiv ℝ F (y + c • ξ) v| := Real.norm_eq_abs _
        _ ≤ (Fintype.card (Fin n) : ℝ) * ‖v‖ *
            (C * B ^ d * (1 + ‖ξ‖) ^ d) := hv
        _ = (K * (1 + ‖ξ‖) ^ d) * ‖v‖ := by dsimp [K]; ring
    exact hop
  have hdiff : ∀ᵐ ξ ∂(standardGaussianMeasure n), ∀ y ∈ Metric.ball x 1,
      HasFDerivAt (Ψ · ξ) (Ψ' y ξ) y := by
    apply ae_of_all
    intro ξ y hy
    have harg : HasFDerivAt (fun z : Fin n → ℝ => z + c • ξ)
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) y := by
      have hbase : HasFDerivAt (fun z : Fin n → ℝ => z)
          (ContinuousLinearMap.id ℝ (Fin n → ℝ)) y := hasFDerivAt_id y
      exact (hasFDerivAt_add_const_iff (c := c • ξ)).2 hbase
    exact (hF.1.differentiable_one (y + c • ξ)).hasFDerivAt.comp y harg
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := Ψ) (x₀ := x) (s := Metric.ball x 1) (F' := Ψ')
    (bound := fun ξ => K * (1 + ‖ξ‖) ^ d)
    (Metric.ball_mem_nhds _ zero_lt_one) hFmeas hFint hF'meas hbound hboundInt hdiff
  have hderiv' : HasFDerivAt (fun y => ∫ ξ, F (y + c • ξ) ∂(standardGaussianMeasure n))
      (∫ ξ, fderiv ℝ F (x + c • ξ) ∂(standardGaussianMeasure n)) x := by
    simpa [Ψ, Ψ'] using hderiv
  have hF'derivInt : Integrable (Ψ' x) (standardGaussianMeasure n) := by
    have hboundAt : ∀ᵐ ξ ∂(standardGaussianMeasure n),
        ‖Ψ' x ξ‖ ≤ K * (1 + ‖ξ‖) ^ d :=
      hbound.mono fun ξ hξ => hξ x (Metric.mem_ball_self zero_lt_one)
    exact Integrable.mono' hboundInt hF'meas hboundAt
  have hF'measNhd : ∀ᶠ y in nhds x,
      AEStronglyMeasurable (Ψ' y) (standardGaussianMeasure n) := by
    filter_upwards with y
    exact (((hF.1.continuous_fderiv (by norm_num)).comp (hcontArg
      y)).measurable).aestronglyMeasurable
  have hF'boundNhd : ∀ᶠ y in nhds x, ∀ᵐ ξ ∂(standardGaussianMeasure n),
      ‖Ψ' y ξ‖ ≤ K * (1 + ‖ξ‖) ^ d := by
    filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    exact hbound.mono fun ξ hξ => hξ y hy
  have hF'cont : ∀ᵐ ξ ∂(standardGaussianMeasure n), ContinuousAt (Ψ' · ξ) x := by
    apply ae_of_all
    intro ξ
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact (hfd.comp (continuous_id.add
      (continuous_const : Continuous fun _ : Fin n → ℝ => c • ξ))).continuousAt
  have hF'continuousAt := continuousAt_of_dominated (F := Ψ') (x₀ := x)
    (bound := fun ξ => K * (1 + ‖ξ‖) ^ d)
    hF'measNhd hF'boundNhd hboundInt hF'cont
  constructor
  · constructor
    · exact hF'derivInt.aestronglyMeasurable
    · exact hF'derivInt.hasFiniteIntegral
  · constructor
    · simpa only [shiftAverage] using hderiv'
    · simpa [Ψ'] using hF'continuousAt


end EhrhardGaussian.Ehrhard
