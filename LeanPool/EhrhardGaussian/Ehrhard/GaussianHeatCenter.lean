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
    1 + ‖x + u • ξ‖ ≤ (1 + ‖x‖) * (1 + |u|) * (1 + ‖ξ‖) := by
  have htri : ‖x + u • ξ‖ ≤ ‖x‖ + |u| * ‖ξ‖ := by
    calc
      ‖x + u • ξ‖ ≤ ‖x‖ + ‖u • ξ‖ := norm_add_le _ _
      _ = ‖x‖ + |u| * ‖ξ‖ := by simp [norm_smul]
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have hu : 0 ≤ |u| := abs_nonneg _
  have hξ : 0 ≤ ‖ξ‖ := norm_nonneg _
  nlinarith [mul_nonneg hx hu, mul_nonneg hx hξ, mul_nonneg hu hξ]

/-- A Fréchet derivative evaluates as the sum of its coordinate derivatives times the direction
coordinates. -/
theorem concentration_fderiv_apply_eq_sum {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (z v : Fin n → ℝ) :
    fderiv ℝ F z v = ∑ i, v i * coordinateDerivative F i z := by
  have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hv, map_sum]
  simp [coordinateDerivative, smul_eq_mul, Pi.single_apply]

/-- A common bound on coordinate derivatives bounds every directional derivative by dimension times
the direction norm. -/
theorem concentration_abs_fderiv_apply_le {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (z v : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i, |coordinateDerivative F i z| ≤ B) :
    |fderiv ℝ F z v| ≤ (Fintype.card (Fin n) : ℝ) * ‖v‖ * B := by
  rw [concentration_fderiv_apply_eq_sum]
  calc
    |∑ i, v i * coordinateDerivative F i z| ≤
        ∑ i, |v i * coordinateDerivative F i z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ * B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hv : |v i| ≤ ‖v‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
      calc
        |v i| * |coordinateDerivative F i z| ≤ |v i| * B :=
          mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
        _ ≤ ‖v‖ * B := mul_le_mul_of_nonneg_right hv hB
    _ = (Fintype.card (Fin n) : ℝ) * ‖v‖ * B := by
      simp [Finset.sum_const, mul_assoc]

/-- The scale derivative of a Gaussian average of a polynomially bounded C¹ function is the averaged
derivative in the Gaussian direction. -/
theorem hasDerivAt_shiftAverage_zero {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) (u : ℝ) :
    HasDerivAt (shiftAverage F 0)
      (∫ ξ, fderiv ℝ F (u • ξ) ξ ∂(standardGaussianMeasure n)) u := by
  rcases hF.2 with ⟨C, hC, d, hfunctionBound, hcoordinateBound⟩
  let Φ : ℝ → (Fin n → ℝ) → ℝ := fun s ξ => F (s • ξ)
  let Φ' : ℝ → (Fin n → ℝ) → ℝ := fun s ξ => fderiv ℝ F (s • ξ) ξ
  let B : ℝ := 2 + |u|
  let K : ℝ := (Fintype.card (Fin n) : ℝ) * (|u| + 1) * C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hshiftCont (s : ℝ) : Continuous (fun ξ : Fin n → ℝ => s • ξ) :=
    continuous_id.const_smul s
  have hFmeas : ∀ᶠ s in nhds u, AEStronglyMeasurable (Φ s) (standardGaussianMeasure n) := by
    filter_upwards with s
    exact ((hF.1.continuous.comp (hshiftCont s)).measurable).aestronglyMeasurable
  have hFint : Integrable (Φ u) (standardGaussianMeasure n) := by
    let C' : ℝ := C * (1 + |u|) ^ d
    have hC' : 0 ≤ C' := by dsimp [C']; positivity
    apply integrable_of_pi_polynomial_bound
      ((hF.1.continuous.comp (continuous_id.const_smul u)).measurable)
      hC' (d := d)
    intro ξ
    have hnorm : 1 + ‖u • ξ‖ ≤ (1 + |u|) * (1 + ‖ξ‖) := by
      calc
        1 + ‖u • ξ‖ ≤ (1 + ‖(0 : Fin n → ℝ)‖) * (1 + |u|) * (1 + ‖ξ‖) :=
          by simpa using concentration_norm_add_smul_le (0 : Fin n → ℝ) ξ u
        _ = (1 + |u|) * (1 + ‖ξ‖) := by simp
    calc
      |F (u • ξ)| ≤ C * (1 + ‖u • ξ‖) ^ d := hfunctionBound _
      _ ≤ C * ((1 + |u|) * (1 + ‖ξ‖)) ^ d := by gcongr
      _ = C' * (1 + ‖ξ‖) ^ d := by
        dsimp [C']
        rw [mul_pow]
        ring
  have hderivCont : Continuous (fun ξ : Fin n → ℝ => fderiv ℝ F (u • ξ) ξ) := by
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact (hfd.comp (hshiftCont u)).clm_apply continuous_id
  have hF'meas : AEStronglyMeasurable (Φ' u) (standardGaussianMeasure n) :=
    hderivCont.measurable.aestronglyMeasurable
  have hpoly : Integrable (fun ξ : Fin n → ℝ => (1 + ‖ξ‖) ^ (d + 1))
      (standardGaussianMeasure n) := by
    apply integrable_of_pi_polynomial_bound (by fun_prop) (C := 1) (by norm_num)
      (d := d + 1)
    intro ξ
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖ξ‖) ^ (d + 1))]
    simp
  have hboundInt : Integrable (fun ξ : Fin n → ℝ => K * (1 + ‖ξ‖) ^ (d + 1))
      (standardGaussianMeasure n) := by
    simpa using hpoly.const_mul K
  have hbound : ∀ᵐ ξ ∂(standardGaussianMeasure n), ∀ s ∈ Metric.ball u 1,
      ‖Φ' s ξ‖ ≤ K * (1 + ‖ξ‖) ^ (d + 1) := by
    apply ae_of_all
    intro ξ s hs
    have hsabs : |s| ≤ |u| + 1 := by
      have hdist : |s - u| < 1 := by simpa [Real.dist_eq] using Metric.mem_ball.mp hs
      calc
        |s| = |(s - u) + u| := by congr 1; ring
        _ ≤ |s - u| + |u| := abs_add_le _ _
        _ ≤ 1 + |u| := by linarith
        _ = |u| + 1 := by ring
    have hcoord : ∀ i, |coordinateDerivative F i (s • ξ)| ≤
        C * (1 + ‖s • ξ‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (s • ξ)| ≤
            |F (s • ξ)| + |coordinateDerivative F i (s • ξ)| :=
              le_add_of_nonneg_left (abs_nonneg _)
        _ ≤ C * (1 + ‖s • ξ‖) ^ d := hcoordinateBound i (s • ξ)
    have hnorm : 1 + ‖s • ξ‖ ≤ B * (1 + ‖ξ‖) := by
      calc
        1 + ‖s • ξ‖ ≤ (1 + |s|) * (1 + ‖ξ‖) := by
          simpa using concentration_norm_add_smul_le (0 : Fin n → ℝ) ξ s
        _ ≤ B * (1 + ‖ξ‖) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [B]
          linarith [hsabs]
    have hcoord' : ∀ i, |coordinateDerivative F i (s • ξ)| ≤
        C * B ^ d * (1 + ‖ξ‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (s • ξ)| ≤ C * (1 + ‖s • ξ‖) ^ d := hcoord i
        _ ≤ C * (B * (1 + ‖ξ‖)) ^ d := by gcongr
        _ = C * B ^ d * (1 + ‖ξ‖) ^ d := by rw [mul_pow]; ring
    have hfd := concentration_abs_fderiv_apply_le (s • ξ) ξ
      (by positivity : 0 ≤ C * B ^ d * (1 + ‖ξ‖) ^ d) hcoord'
    have hξnorm : ‖ξ‖ ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    calc
      ‖Φ' s ξ‖ = |fderiv ℝ F (s • ξ) ξ| := Real.norm_eq_abs _
      _ ≤ (Fintype.card (Fin n) : ℝ) * ‖ξ‖ *
          (C * B ^ d * (1 + ‖ξ‖) ^ d) := hfd
      _ ≤ K * (1 + ‖ξ‖) ^ (d + 1) := by
        dsimp [K]
        have hfactor : 0 ≤ (Fintype.card (Fin n) : ℝ) * C * B ^ d := by positivity
        have hpow : 0 ≤ (1 + ‖ξ‖) ^ d := by positivity
        rw [pow_succ]
        calc
          (Fintype.card (Fin n) : ℝ) * ‖ξ‖ * (C * B ^ d * (1 + ‖ξ‖) ^ d) ≤
              (Fintype.card (Fin n) : ℝ) * (1 + ‖ξ‖) *
                (C * B ^ d * (1 + ‖ξ‖) ^ d) := by
                  gcongr
          _ ≤ (Fintype.card (Fin n) : ℝ) * (|u| + 1) *
                (1 + ‖ξ‖) * (C * B ^ d * (1 + ‖ξ‖) ^ d) := by
                  have hscale : 1 + ‖ξ‖ ≤ (|u| + 1) * (1 + ‖ξ‖) := by
                    have hnonneg : 0 ≤ |u| * (1 + ‖ξ‖) := by positivity
                    nlinarith
                  have hfactorGrow :
                      (Fintype.card (Fin n) : ℝ) * (1 + ‖ξ‖) ≤
                        (Fintype.card (Fin n) : ℝ) * (|u| + 1) * (1 + ‖ξ‖) := by
                    calc
                      (Fintype.card (Fin n) : ℝ) * (1 + ‖ξ‖) ≤
                          (Fintype.card (Fin n) : ℝ) * ((|u| + 1) * (1 + ‖ξ‖)) :=
                        mul_le_mul_of_nonneg_left hscale (by positivity)
                      _ = (Fintype.card (Fin n) : ℝ) * (|u| + 1) *
                          (1 + ‖ξ‖) := by ring
                  exact mul_le_mul_of_nonneg_right hfactorGrow (by positivity)
          _ = (Fintype.card (Fin n) : ℝ) * (|u| + 1) * C * B ^ d *
                ((1 + ‖ξ‖) ^ d * (1 + ‖ξ‖)) := by ring
  have hdiff : ∀ᵐ ξ ∂(standardGaussianMeasure n), ∀ s ∈ Metric.ball u 1,
      HasDerivAt (Φ · ξ) (Φ' s ξ) s := by
    apply ae_of_all
    intro ξ s hs
    have harg : HasDerivAt (fun r : ℝ => r • ξ) ξ s := by
      simpa using (hasDerivAt_id s).smul_const ξ
    have houter := (hF.1.differentiable_one (s • ξ)).hasFDerivAt
    have hcomp := houter.comp_hasDerivAt s harg
    simpa [Φ, Φ', Function.comp_def] using hcomp
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := Φ) (x₀ := u) (s := Metric.ball u 1) (F' := Φ')
    (bound := fun ξ => K * (1 + ‖ξ‖) ^ (d + 1))
    (Metric.ball_mem_nhds _ zero_lt_one) hFmeas hFint hF'meas hbound hboundInt hdiff
  change HasDerivAt (fun s => ∫ ξ, F (0 + s • ξ) ∂(standardGaussianMeasure n))
    (∫ ξ, fderiv ℝ F (u • ξ) ξ ∂(standardGaussianMeasure n)) u
  simpa only [zero_add] using hderiv.2

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
