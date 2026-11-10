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

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianHeatRegularity
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Differentiation along the Gaussian interpolation bridge -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard

/-- The Gaussian bridge argument has the explicit derivative of its two square-root coefficients. -/
theorem hasDerivAt_gaussian_bridge_argument {n : ℕ}
    (ξ η : Fin n → ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun r : ℝ => Real.sqrt r • ξ + Real.sqrt (1 - r) • η)
      ((1 / (2 * Real.sqrt t)) • ξ - (1 / (2 * Real.sqrt (1 - t))) • η) t := by
  have hleft : HasDerivAt (fun r : ℝ => Real.sqrt r • ξ)
      ((1 / (2 * Real.sqrt t)) • ξ) t := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt ht)).smul_const ξ using 1
  have hsub : HasDerivAt (fun r : ℝ => 1 - r) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have hroot : HasDerivAt (fun r : ℝ => Real.sqrt (1 - r))
      (-(1 / (2 * Real.sqrt (1 - t)))) t := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt (by linarith : 0 < 1 - t))).comp t hsub using 1
    · ext r
      rfl
    · ring_nf
  have hright := hroot.smul_const η
  convert hleft.add hright using 1
  · rw [sub_eq_add_neg, ← neg_smul]

private theorem integrable_gaussian_bridge {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (ξ : Fin n → ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Integrable (fun η => F (Real.sqrt t • ξ + Real.sqrt (1 - t) • η))
      (standardGaussianMeasure n) := by
  rcases hF.2 with ⟨C, hC, d, hvalue, _⟩
  let A : ℝ → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun r η => Real.sqrt r • ξ + Real.sqrt (1 - r) • η
  let Bξ : ℝ := 1 + ‖ξ‖
  have hAcont (r : ℝ) : Continuous (A r) := by
    dsimp [A]
    fun_prop
  have hpoint (η : Fin n → ℝ) :
      1 + ‖A t η‖ ≤ Bξ * (1 + ‖η‖) := by
    have hsqt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
    have hsqt1 : Real.sqrt t ≤ 1 := by
      rw [Real.sqrt_le_one]
      linarith
    have hsq1t : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
    have hsq1t1 : Real.sqrt (1 - t) ≤ 1 := by
      rw [Real.sqrt_le_one]
      linarith
    have hsum : ‖A t η‖ ≤ ‖ξ‖ + ‖η‖ := by
      dsimp [A]
      calc
        ‖Real.sqrt t • ξ + Real.sqrt (1 - t) • η‖ ≤
            ‖Real.sqrt t • ξ‖ + ‖Real.sqrt (1 - t) • η‖ := norm_add_le _ _
        _ = Real.sqrt t * ‖ξ‖ + Real.sqrt (1 - t) * ‖η‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqt,
            norm_smul, Real.norm_eq_abs, abs_of_nonneg hsq1t]
        _ ≤ ‖ξ‖ + ‖η‖ := by
          simpa only [one_mul] using add_le_add
            (mul_le_mul_of_nonneg_right hsqt1 (norm_nonneg ξ))
            (mul_le_mul_of_nonneg_right hsq1t1 (norm_nonneg η))
    dsimp [Bξ]
    nlinarith [norm_nonneg η, norm_nonneg ξ]
  have hmeas := (hF.1.continuous.comp (hAcont t)).measurable
  apply integrable_of_pi_polynomial_bound hmeas (C := C * Bξ ^ d)
    (by positivity) (d := d)
  intro η
  calc
    |F (A t η)| ≤ C * (1 + ‖A t η‖) ^ d := hvalue _
    _ ≤ C * (Bξ * (1 + ‖η‖)) ^ d := by gcongr; exact hpoint η
    _ = C * Bξ ^ d * (1 + ‖η‖) ^ d := by rw [mul_pow]; ring

/-- The derivative of a Gaussian bridge average is the average of its directional derivative. -/
theorem hasDerivAt_gaussian_bridge_integral {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (ξ : Fin n → ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Integrable (fun η => fderiv ℝ F (Real.sqrt t • ξ + Real.sqrt (1 - t) • η)
        ((1 / (2 * Real.sqrt t)) • ξ - (1 / (2 * Real.sqrt (1 - t))) • η))
        (standardGaussianMeasure n) ∧
    HasDerivAt
      (fun r => ∫ η, F (Real.sqrt r • ξ + Real.sqrt (1 - r) • η)
        ∂(standardGaussianMeasure n))
      (∫ η, fderiv ℝ F (Real.sqrt t • ξ + Real.sqrt (1 - t) • η)
        ((1 / (2 * Real.sqrt t)) • ξ - (1 / (2 * Real.sqrt (1 - t))) • η)
        ∂(standardGaussianMeasure n)) t := by
  rcases hF.2 with ⟨C, hC, d, hvalue, hcoordinate⟩
  let A : ℝ → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun r η => Real.sqrt r • ξ + Real.sqrt (1 - r) • η
  let A' : ℝ → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun r η => (1 / (2 * Real.sqrt r)) • ξ - (1 / (2 * Real.sqrt (1 - r))) • η
  let Bξ : ℝ := 1 + ‖ξ‖
  let Vξ : ℝ := ‖ξ‖ / (2 * Real.sqrt (t / 2)) + 1 / (2 * Real.sqrt ((1 - t) / 2))
  let K : ℝ := (Fintype.card (Fin n) : ℝ) * C * Bξ ^ d * Vξ
  let δ : ℝ := min (t / 2) ((1 - t) / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hBξ : 0 ≤ Bξ := by dsimp [Bξ]; positivity
  have hVξ : 0 ≤ Vξ := by dsimp [Vξ]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hAcont (r : ℝ) : Continuous (A r) := by
    dsimp [A]
    fun_prop
  have hFmeas : ∀ᶠ r in nhds t,
      AEStronglyMeasurable (fun η => F (A r η)) (standardGaussianMeasure n) := by
    filter_upwards with r
    exact ((hF.1.continuous.comp (hAcont r)).measurable).aestronglyMeasurable
  have hFint : Integrable (fun η => F (A t η)) (standardGaussianMeasure n) :=
    integrable_gaussian_bridge hF ξ ht ht1
  have hderivCont : Continuous (fun η =>
      fderiv ℝ F (A t η) (A' t η)) := by
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact (hfd.comp (hAcont t)).clm_apply (by fun_prop)
  have hF'meas : AEStronglyMeasurable (fun η =>
      fderiv ℝ F (A t η) (A' t η)) (standardGaussianMeasure n) :=
    hderivCont.measurable.aestronglyMeasurable
  have hpoly : Integrable (fun η : Fin n → ℝ => (1 + ‖η‖) ^ (d + 1))
      (standardGaussianMeasure n) := by
    apply integrable_of_pi_polynomial_bound (by fun_prop) (C := 1) (by norm_num)
      (d := d + 1)
    intro η
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖η‖) ^ (d + 1))]
    simp
  have hboundInt : Integrable (fun η : Fin n → ℝ => K * (1 + ‖η‖) ^ (d + 1))
      (standardGaussianMeasure n) := by simpa using hpoly.const_mul K
  have hbound : ∀ᵐ η ∂(standardGaussianMeasure n), ∀ r ∈ Metric.ball t δ,
      ‖fderiv ℝ F (A r η) (A' r η)‖ ≤ K * (1 + ‖η‖) ^ (d + 1) := by
    apply ae_of_all
    intro η r hr
    have hdist : |r - t| < δ := by simpa [Real.dist_eq] using Metric.mem_ball.mp hr
    have hlow : t / 2 < r := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hsmall : δ ≤ t / 2 := min_le_left _ _
      linarith
    have hupp : r < (1 + t) / 2 := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hsmall : δ ≤ (1 - t) / 2 := min_le_right _ _
      linarith
    have hlow1 : (1 - t) / 2 < 1 - r := by linarith
    have hrootr : Real.sqrt (t / 2) ≤ Real.sqrt r := Real.sqrt_le_sqrt hlow.le
    have hroot1r : Real.sqrt ((1 - t) / 2) ≤ Real.sqrt (1 - r) :=
      Real.sqrt_le_sqrt hlow1.le
    have hroot0 : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.2 (by linarith)
    have hroot10 : 0 < Real.sqrt ((1 - t) / 2) := Real.sqrt_pos.2 (by linarith)
    have hcoeff : ‖A' r η‖ ≤ Vξ * (1 + ‖η‖) := by
      have hnorm : ‖A' r η‖ ≤ ‖ξ‖ / (2 * Real.sqrt r) +
          ‖η‖ / (2 * Real.sqrt (1 - r)) := by
        dsimp [A']
        calc
          ‖(1 / (2 * Real.sqrt r)) • ξ -
              (1 / (2 * Real.sqrt (1 - r))) • η‖ ≤
              ‖(1 / (2 * Real.sqrt r)) • ξ‖ +
                ‖(1 / (2 * Real.sqrt (1 - r))) • η‖ := norm_sub_le _ _
          _ = ‖ξ‖ / (2 * Real.sqrt r) + ‖η‖ / (2 * Real.sqrt (1 - r)) := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
              Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            ring
      have hfirst : ‖ξ‖ / (2 * Real.sqrt r) ≤ ‖ξ‖ / (2 * Real.sqrt (t / 2)) := by
        have hden : 2 * Real.sqrt (t / 2) ≤ 2 * Real.sqrt r := by nlinarith
        have hrecip : 1 / (2 * Real.sqrt r) ≤ 1 / (2 * Real.sqrt (t / 2)) :=
          one_div_le_one_div_of_le (by positivity) hden
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hrecip)
          (norm_nonneg _)
      have hsecond : ‖η‖ / (2 * Real.sqrt (1 - r)) ≤
          ‖η‖ / (2 * Real.sqrt ((1 - t) / 2)) := by
        have hden : 2 * Real.sqrt ((1 - t) / 2) ≤ 2 * Real.sqrt (1 - r) := by nlinarith
        have hrecip : 1 / (2 * Real.sqrt (1 - r)) ≤
            1 / (2 * Real.sqrt ((1 - t) / 2)) :=
          one_div_le_one_div_of_le (by positivity) hden
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hrecip)
          (norm_nonneg _)
      dsimp [Vξ]
      calc
        ‖A' r η‖ ≤ ‖ξ‖ / (2 * Real.sqrt r) +
            ‖η‖ / (2 * Real.sqrt (1 - r)) := hnorm
        _ ≤ ‖ξ‖ / (2 * Real.sqrt (t / 2)) +
            ‖η‖ / (2 * Real.sqrt ((1 - t) / 2)) := add_le_add hfirst hsecond
        _ ≤ ‖ξ‖ / (2 * Real.sqrt (t / 2)) * (1 + ‖η‖) +
            1 / (2 * Real.sqrt ((1 - t) / 2)) * (1 + ‖η‖) := by
          have hnonneg₁ : 0 ≤ ‖ξ‖ / (2 * Real.sqrt (t / 2)) := by positivity
          have hnonneg₂ : 0 ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by positivity
          have hη : 0 ≤ ‖η‖ := norm_nonneg _
          have h₁ : ‖ξ‖ / (2 * Real.sqrt (t / 2)) ≤
              ‖ξ‖ / (2 * Real.sqrt (t / 2)) * (1 + ‖η‖) := by
            calc
              _ = (‖ξ‖ / (2 * Real.sqrt (t / 2))) * 1 := by ring
              _ ≤ (‖ξ‖ / (2 * Real.sqrt (t / 2))) * (1 + ‖η‖) :=
                mul_le_mul_of_nonneg_left (by linarith) hnonneg₁
          have h₂ : ‖η‖ / (2 * Real.sqrt ((1 - t) / 2)) ≤
              1 / (2 * Real.sqrt ((1 - t) / 2)) * (1 + ‖η‖) := by
            calc
              _ = (1 / (2 * Real.sqrt ((1 - t) / 2))) * ‖η‖ := by ring
              _ ≤ (1 / (2 * Real.sqrt ((1 - t) / 2))) * (1 + ‖η‖) :=
                mul_le_mul_of_nonneg_left (by linarith) hnonneg₂
          exact add_le_add h₁ h₂
        _ = Vξ * (1 + ‖η‖) := by dsimp [Vξ]; ring
    have hpoint : 1 + ‖A r η‖ ≤ Bξ * (1 + ‖η‖) := by
      have hsqr : 0 ≤ r := by linarith
      have hsq1 : 0 ≤ 1 - r := by linarith
      have hsqr1 : Real.sqrt r ≤ 1 := by rw [Real.sqrt_le_one]; linarith
      have hsq11 : Real.sqrt (1 - r) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
      have hsum : ‖A r η‖ ≤ ‖ξ‖ + ‖η‖ := by
        dsimp [A]
        calc
          ‖Real.sqrt r • ξ + Real.sqrt (1 - r) • η‖ ≤
              ‖Real.sqrt r • ξ‖ + ‖Real.sqrt (1 - r) • η‖ := norm_add_le _ _
          _ = Real.sqrt r * ‖ξ‖ + Real.sqrt (1 - r) * ‖η‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
              norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          _ ≤ ‖ξ‖ + ‖η‖ := by
            simpa only [one_mul] using add_le_add
              (mul_le_mul_of_nonneg_right hsqr1 (norm_nonneg ξ))
              (mul_le_mul_of_nonneg_right hsq11 (norm_nonneg η))
      dsimp [Bξ]
      nlinarith [norm_nonneg η, norm_nonneg ξ]
    have hcoord : ∀ i, |coordinateDerivative F i (A r η)| ≤
        C * (1 + ‖A r η‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (A r η)| ≤
            |F (A r η)| + |coordinateDerivative F i (A r η)| :=
              le_add_of_nonneg_left (abs_nonneg _)
        _ ≤ C * (1 + ‖A r η‖) ^ d := hcoordinate i _
    have hcoord' : ∀ i, |coordinateDerivative F i (A r η)| ≤
        C * Bξ ^ d * (1 + ‖η‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (A r η)| ≤ C * (1 + ‖A r η‖) ^ d := hcoord i
        _ ≤ C * (Bξ * (1 + ‖η‖)) ^ d := by gcongr
        _ = C * Bξ ^ d * (1 + ‖η‖) ^ d := by rw [mul_pow]; ring
    have hfd := concentration_abs_fderiv_apply_le (A r η) (A' r η)
      (by positivity : 0 ≤ C * Bξ ^ d * (1 + ‖η‖) ^ d) hcoord'
    have hη : ‖η‖ ≤ 1 + ‖η‖ := by linarith [norm_nonneg η]
    calc
      ‖fderiv ℝ F (A r η) (A' r η)‖ ≤
          (Fintype.card (Fin n) : ℝ) * ‖A' r η‖ *
            (C * Bξ ^ d * (1 + ‖η‖) ^ d) := hfd
      _ ≤ (Fintype.card (Fin n) : ℝ) * (Vξ * (1 + ‖η‖)) *
            (C * Bξ ^ d * (1 + ‖η‖) ^ d) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcoeff (by positivity)) (by positivity)
      _ = K * (1 + ‖η‖) ^ (d + 1) := by
        dsimp [K]
        rw [pow_succ]
        ring
  have hdiff : ∀ᵐ η ∂(standardGaussianMeasure n), ∀ r ∈ Metric.ball t δ,
      HasDerivAt (fun q => F (A q η)) (fderiv ℝ F (A r η) (A' r η)) r := by
    apply ae_of_all
    intro η r hr
    have hdist : |r - t| < δ := by simpa [Real.dist_eq] using Metric.mem_ball.mp hr
    have hlt : 0 < r := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hh := min_le_left (t / 2) ((1 - t) / 2)
      linarith
    have hlt1 : r < 1 := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hh := min_le_right (t / 2) ((1 - t) / 2)
      linarith
    have hA := hasDerivAt_gaussian_bridge_argument ξ η hlt hlt1
    have houter := (hF.1.differentiable_one (A r η)).hasFDerivAt
    have hcomp := houter.comp_hasDerivAt r hA
    simpa [A, A', Function.comp_def] using hcomp
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r η => F (A r η)) (x₀ := t) (s := Metric.ball t δ)
    (F' := fun r η => fderiv ℝ F (A r η) (A' r η))
    (bound := fun η => K * (1 + ‖η‖) ^ (d + 1))
    (Metric.ball_mem_nhds _ hδ) hFmeas hFint hF'meas hbound hboundInt hdiff
  simpa only [A, A'] using hderiv

/-- The proved heat identity gives the scaled Gaussian integration-by-parts identity. -/
theorem integral_fderiv_scaled_eq_sqrt_mul_laplacian {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₁ : HasPolynomiallyBoundedCoordinateDerivatives F)
    (hF₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    {t : ℝ} (ht : 0 < t) :
    ∫ ξ, fderiv ℝ F (Real.sqrt t • ξ) ξ ∂(standardGaussianMeasure n) =
      Real.sqrt t * ∫ ξ, ∑ i, coordinateDerivative (coordinateDerivative F i) i
        (Real.sqrt t • ξ) ∂(standardGaussianMeasure n) := by
  let s : ℝ := Real.sqrt t
  have hs : 0 < s := Real.sqrt_pos.2 ht
  have hsderiv : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t :=
    Real.hasDerivAt_sqrt (ne_of_gt ht)
  have hscale := hasDerivAt_shiftAverage_zero hF₁ s
  have hpath := hscale.comp t hsderiv
  have hheat := hasDerivAt_heatAverage hF₂ (0 : Fin n → ℝ) ht
  have hpath' : HasDerivAt (heatAverage F 0)
      ((1 / (2 * s)) * ∫ ξ, fderiv ℝ F (s • ξ) ξ ∂(standardGaussianMeasure n)) t := by
    convert hpath using 1
    · rfl
    · dsimp [s]
      rw [mul_comm]
  have hheat' : HasDerivAt (heatAverage F 0)
      ((1 / 2 : ℝ) * ∫ ξ, ∑ i,
        coordinateDerivative (coordinateDerivative F i) i (s • ξ)
        ∂(standardGaussianMeasure n)) t := by
    simpa [heatLaplacianAverage, s] using hheat
  have hEq := hpath'.unique hheat'
  have htwo : (1 / (2 * s)) *
      ∫ ξ, fderiv ℝ F (s • ξ) ξ ∂(standardGaussianMeasure n) =
      (1 / 2 : ℝ) * ∫ ξ, ∑ i,
        coordinateDerivative (coordinateDerivative F i) i (s • ξ)
        ∂(standardGaussianMeasure n) := hEq
  have hsne : s ≠ 0 := ne_of_gt hs
  calc
    ∫ ξ, fderiv ℝ F (s • ξ) ξ ∂(standardGaussianMeasure n) =
        (2 * s) * ((1 / (2 * s)) *
          ∫ ξ, fderiv ℝ F (s • ξ) ξ ∂(standardGaussianMeasure n)) := by
            field_simp [hsne]
    _ = (2 * s) * ((1 / 2 : ℝ) *
          ∫ ξ, ∑ i, coordinateDerivative (coordinateDerivative F i) i
            (s • ξ) ∂(standardGaussianMeasure n)) := congrArg (fun z : ℝ => (2 * s) * z) htwo
    _ = s * ∫ ξ, ∑ i, coordinateDerivative (coordinateDerivative F i) i
          (s • ξ) ∂(standardGaussianMeasure n) := by ring

/-- The scaled Gaussian derivative/Laplacian identity also holds for a Gaussian shift centered
at an arbitrary point. -/
theorem integral_fderiv_shift_scaled_eq_sqrt_mul_laplacian {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₁ : HasPolynomiallyBoundedCoordinateDerivatives F)
    (hF₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ ξ, fderiv ℝ F (x + Real.sqrt t • ξ) ξ ∂(standardGaussianMeasure n) =
      Real.sqrt t * ∫ ξ, ∑ i,
        coordinateDerivative (coordinateDerivative F i) i (x + Real.sqrt t • ξ)
        ∂(standardGaussianMeasure n) := by
  let T : (Fin n → ℝ) → ℝ := fun z => F (x + z)
  have hT₂ := hasPolynomiallyBoundedSecond_of_translate hF₂ x
  have hT₁ : HasPolynomiallyBoundedCoordinateDerivatives T :=
    hasPolynomiallyBoundedCoordinateDerivatives_of_second hT₂
  have hzero := integral_fderiv_scaled_eq_sqrt_mul_laplacian hT₁ hT₂ ht
  have hFderiv (z : Fin n → ℝ) : fderiv ℝ T z = fderiv ℝ F (x + z) :=
    fderiv_translate hF₁.1 x z
  have hcoord (i j : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative (coordinateDerivative T i) j z =
        coordinateDerivative (coordinateDerivative F i) j (x + z) := by
    have heq : coordinateDerivative T i = fun y => coordinateDerivative F i (x + y) := by
      funext y
      exact coordinateDerivative_translate hF₁.1 x y i
    rw [heq]
    exact coordinateDerivative_translate
      (contDiff_coordinateDerivative_of_two hF₂.1 i) x z j
  calc
    ∫ ξ, fderiv ℝ F (x + Real.sqrt t • ξ) ξ ∂(standardGaussianMeasure n) =
        ∫ ξ, fderiv ℝ T (Real.sqrt t • ξ) ξ ∂(standardGaussianMeasure n) := by
          apply integral_congr_ae
          exact ae_of_all _ fun ξ =>
            congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L ξ)
              (hFderiv (Real.sqrt t • ξ)).symm
    _ = Real.sqrt t * ∫ ξ, ∑ i,
          coordinateDerivative (coordinateDerivative T i) i (Real.sqrt t • ξ)
          ∂(standardGaussianMeasure n) := hzero
    _ = Real.sqrt t * ∫ ξ, ∑ i,
          coordinateDerivative (coordinateDerivative F i) i (x + Real.sqrt t • ξ)
          ∂(standardGaussianMeasure n) := by
            congr 1
            apply integral_congr_ae
            apply ae_of_all
            intro ξ
            apply Finset.sum_congr rfl
            intro i hi
            exact hcoord i i (Real.sqrt t • ξ)

end EhrhardGaussian.Ehrhard
