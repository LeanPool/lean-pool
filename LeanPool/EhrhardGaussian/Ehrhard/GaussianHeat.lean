/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott N. Armstrong
-/

/-
Ported from ASDExplicitGamma-dev, commit 2c9673f0bcca8062b441989bdc56f87b38715bb8.
Modified for EhrhardGaussian, 2026.
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianSmoothClass
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite-dimensional Gaussian heat flow

The heat flow is the Gaussian average of a translated observable. Its generator is one half of
the Euclidean Laplacian, as follows from Gaussian integration by parts.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open Filter
open Set
open scoped Topology
open scoped ENNReal NNReal

open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard

/-- A `C²` function and its first and second coordinate derivatives obey one polynomial bound. -/
def HasPolynomiallyBoundedSecondCoordinateDerivatives {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 2 F ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
    (∀ x, |F x| ≤ C * (1 + ‖x‖) ^ d) ∧
    (∀ i x, |coordinateDerivative F i x| ≤ C * (1 + ‖x‖) ^ d) ∧
    ∀ i j x, |coordinateDerivative (coordinateDerivative F i) j x| ≤
      C * (1 + ‖x‖) ^ d

/-- Gaussian average of `F` at `x` with covariance `t` times the identity. -/
noncomputable def shiftAverage {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (u : ℝ) : ℝ :=
  ∫ ξ, F (x + u • ξ) ∂(standardGaussianMeasure n)

/-- Gaussian average of `F` at `x` with covariance `t` times the identity. -/
noncomputable def heatAverage {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (t : ℝ) : ℝ := shiftAverage F x (Real.sqrt t)

/-- The Gaussian average of the Euclidean Laplacian of `F`. -/
noncomputable def heatLaplacianAverage {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∫ ξ, ∑ i, coordinateDerivative (coordinateDerivative F i) i
    (x + Real.sqrt t • ξ) ∂(standardGaussianMeasure n)

/-- A coordinate derivative of a `C²` function is `C¹`. -/
private lemma contDiff_coordinateDerivative_of_two {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ 2 F) (i : Fin n) :
    ContDiff ℝ 1 (coordinateDerivative F i) := by
  have h := hF.contDiff_fderiv_apply (m := 1)
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hpair : ContDiff ℝ 1
      (fun x : Fin n → ℝ => (x, (Pi.single i (1 : ℝ) : Fin n → ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hcomp := h.comp hpair
  convert hcomp using 1
  · ext x
    rfl

/-- Coordinate differentiation commutes with a scalar affine change of variables. -/
private lemma coordinateDerivative_affine_smul {n : ℕ} {G : (Fin n → ℝ) → ℝ}
    (hG : ContDiff ℝ 1 G) (x : Fin n → ℝ) (c : ℝ) (j : Fin n)
    (ξ : Fin n → ℝ) :
    coordinateDerivative (fun y => G (x + c • y)) j ξ =
      c * coordinateDerivative G j (x + c • ξ) := by
  have houter := (hG.differentiable_one (x + c • ξ)).hasFDerivAt
  have hinner : HasFDerivAt (fun y : Fin n → ℝ => x + c • y)
      (c • ContinuousLinearMap.id ℝ (Fin n → ℝ)) ξ := by
    convert (hasFDerivAt_id ξ).const_smul c |>.const_add x using 1; simp
  have hcomp := houter.comp ξ hinner
  have hderiv := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) hcomp.fderiv
  simpa [Function.comp_def, coordinateDerivative, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] using hderiv









/-- A Fréchet derivative on a finite product is the sum of its coordinate derivatives. -/
theorem fderiv_apply_eq_sum_coordinateDerivative {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (z v : Fin n → ℝ) :
    fderiv ℝ F z v = ∑ i, v i * coordinateDerivative F i z := by
  have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hv, map_sum]
  simp [coordinateDerivative, smul_eq_mul, Pi.single_apply]

/-- The norm of the derivative on a vector is bounded by the coordinate derivative bounds. -/
theorem abs_fderiv_apply_le_of_coordinate_bound {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (z v : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i, |coordinateDerivative F i z| ≤ B) :
    |fderiv ℝ F z v| ≤ (Fintype.card (Fin n) : ℝ) * ‖v‖ * B := by
  rw [fderiv_apply_eq_sum_coordinateDerivative]
  calc
    |∑ i, v i * coordinateDerivative F i z| ≤
        ∑ i, |v i * coordinateDerivative F i z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ * B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hv : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
      calc
        |v i| * |coordinateDerivative F i z| ≤ |v i| * B :=
          mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
        _ ≤ ‖v‖ * B := mul_le_mul_of_nonneg_right hv hB
    _ = (Fintype.card (Fin n) : ℝ) * ‖v‖ * B := by simp [Finset.sum_const, mul_assoc]

/-- A translated scalar multiple of a vector has a simple product norm bound. -/
theorem one_add_norm_add_smul_le {n : ℕ} (x ξ : Fin n → ℝ) (u : ℝ) :
    1 + ‖x + u • ξ‖ ≤ (1 + ‖x‖) * (1 + |u|) * (1 + ‖ξ‖) := by
  have htri : ‖x + u • ξ‖ ≤ ‖x‖ + |u| * ‖ξ‖ := by
    calc
      ‖x + u • ξ‖ ≤ ‖x‖ + ‖u • ξ‖ := norm_add_le _ _
      _ = ‖x‖ + |u| * ‖ξ‖ := by simp [norm_smul]
  have ha : 0 ≤ ‖x‖ := norm_nonneg _
  have hb : 0 ≤ |u| := abs_nonneg _
  have hc : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hab : 0 ≤ ‖x‖ * |u| := mul_nonneg ha hb
  have hac : 0 ≤ ‖x‖ * ‖ξ‖ := mul_nonneg ha hc
  have hbc : 0 ≤ |u| * ‖ξ‖ := mul_nonneg hb hc
  have habc : 0 ≤ (‖x‖ * |u|) * ‖ξ‖ := mul_nonneg hab hc
  have hprod : 1 + ‖x‖ + |u| * ‖ξ‖ ≤
      (1 + ‖x‖) * (1 + |u|) * (1 + ‖ξ‖) := by nlinarith
  calc
    1 + ‖x + u • ξ‖ ≤ 1 + ‖x‖ + |u| * ‖ξ‖ := by linarith
    _ ≤ (1 + ‖x‖) * (1 + |u|) * (1 + ‖ξ‖) := hprod

/-- Polynomial growth is preserved by a fixed affine Gaussian shift, with a bound in the Gaussian
coordinate. -/
lemma integrable_shift_of_polynomial_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) {d : ℕ}
    (hg : ∀ z, |f z| ≤ C * (1 + ‖z‖) ^ d)
    (x : Fin n → ℝ) (u : ℝ) :
    Integrable (fun ξ => f (x + u • ξ)) (standardGaussianMeasure n) := by
  have hscale : 0 ≤ (1 + ‖x‖) * (1 + |u|) := by positivity
  have hmapCont : Continuous (fun ξ : Fin n → ℝ => x + u • ξ) := by
    have hu : Continuous (fun ξ : Fin n → ℝ => u • ξ) := continuous_id.const_smul u
    exact (continuous_const : Continuous fun _ : Fin n → ℝ => x).add hu
  have hmap : Measurable (fun ξ : Fin n → ℝ => x + u • ξ) := hmapCont.measurable
  refine integrable_of_pi_polynomial_bound (hf.comp hmap)
    (mul_nonneg hC (pow_nonneg hscale d)) (d := d) ?_
  intro ξ
  have hnorm := one_add_norm_add_smul_le x ξ u
  calc
    |f (x + u • ξ)| ≤ C * (1 + ‖x + u • ξ‖) ^ d := hg _
    _ ≤ C * ((1 + ‖x‖) * (1 + |u|) * (1 + ‖ξ‖)) ^ d := by gcongr
    _ = (C * ((1 + ‖x‖) * (1 + |u|)) ^ d) * (1 + ‖ξ‖) ^ d := by
      rw [mul_pow]
      ring

/-- Multiplication by one Gaussian coordinate preserves polynomial integrability after a fixed
affine shift. -/
lemma integrable_eval_mul_shift_of_polynomial_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) {d : ℕ}
    (hg : ∀ z, |f z| ≤ C * (1 + ‖z‖) ^ d)
    (i : Fin n) (x : Fin n → ℝ) (u : ℝ) :
    Integrable (fun ξ => ξ i * f (x + u • ξ)) (standardGaussianMeasure n) := by
  let B : ℝ := (1 + ‖x‖) * (1 + |u|)
  let K : ℝ := C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hshiftCont : Continuous (fun ξ : Fin n → ℝ => x + u • ξ) := by
    have hu : Continuous (fun ξ : Fin n → ℝ => u • ξ) := continuous_id.const_smul u
    exact (continuous_const : Continuous fun _ : Fin n → ℝ => x).add hu
  have hmeas : Measurable (fun ξ : Fin n → ℝ => ξ i * f (x + u • ξ)) :=
    (measurable_pi_apply i).mul (hf.comp hshiftCont.measurable)
  refine integrable_of_pi_polynomial_bound hmeas hK (d := d + 1) ?_
  intro ξ
  have hnorm := one_add_norm_add_smul_le x ξ u
  have hcoord : |ξ i| ≤ ‖ξ‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm ξ i
  calc
    |ξ i * f (x + u • ξ)| = |ξ i| * |f (x + u • ξ)| := abs_mul _ _
    _ ≤ ‖ξ‖ * (C * (1 + ‖x + u • ξ‖) ^ d) := by
      apply mul_le_mul (hcoord) (hg _) (by positivity) (by positivity)
    _ ≤ (1 + ‖ξ‖) * (C * (B * (1 + ‖ξ‖)) ^ d) := by
      gcongr
      linarith [norm_nonneg ξ]
    _ = K * (1 + ‖ξ‖) ^ (d + 1) := by
      dsimp [K, B]
      rw [mul_pow, pow_succ]
      ring


/-- The first derivative of a Gaussian shift average is obtained by differentiating its
integrand. -/
private theorem hasDerivAt_shiftAverage_innerProduct {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (x : Fin n → ℝ) (u : ℝ) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _ (shiftAverage F x)
      (∫ ξ, fderiv ℝ F (x + u • ξ) ξ ∂(standardGaussianMeasure n)) u := by
  rcases hF.2 with ⟨C, hC, d, hfunctionBound, hcoordinateBound⟩
  let Φ : ℝ → (Fin n → ℝ) → ℝ := fun s ξ => F (x + s • ξ)
  let Φ' : ℝ → (Fin n → ℝ) → ℝ := fun s ξ => fderiv ℝ F (x + s • ξ) ξ
  let B : ℝ := (1 + ‖x‖) * (2 + |u|)
  let K : ℝ := (Fintype.card (Fin n) : ℝ) * C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hshiftCont (s : ℝ) : Continuous (fun ξ : Fin n → ℝ => x + s • ξ) := by
    have hs : Continuous (fun ξ : Fin n → ℝ => s • ξ) := continuous_id.const_smul s
    exact (continuous_const : Continuous fun _ : Fin n → ℝ => x).add hs
  have hFmeas : ∀ᶠ s in nhds u, AEStronglyMeasurable (Φ s) (standardGaussianMeasure n) := by
    filter_upwards with s
    exact ((hF.1.continuous.comp (hshiftCont s)).measurable).aestronglyMeasurable
  have hFint : Integrable (Φ u) (standardGaussianMeasure n) := by
    simpa [Φ] using integrable_shift_of_polynomial_bound hF.1.continuous.measurable
      hC hfunctionBound x u
  have hderivCont : Continuous (fun ξ : Fin n → ℝ => fderiv ℝ F (x + u • ξ) ξ) := by
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact (hfd.comp (hshiftCont u)).clm_apply continuous_id
  have hF'meas : AEStronglyMeasurable (Φ' u) (standardGaussianMeasure n) := by
    exact hderivCont.measurable.aestronglyMeasurable
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
      have hdist : |s - u| < 1 := by
        simpa [Real.dist_eq] using Metric.mem_ball.mp hs
      calc
        |s| = |(s - u) + u| := by congr 1; ring
        _ ≤ |s - u| + |u| := abs_add_le _ _
        _ ≤ 1 + |u| := by linarith
        _ = |u| + 1 := by ring
    have hnorm : 1 + ‖x + s • ξ‖ ≤ B * (1 + ‖ξ‖) := by
      calc
        1 + ‖x + s • ξ‖ ≤ (1 + ‖x‖) * (1 + |s|) * (1 + ‖ξ‖) :=
          one_add_norm_add_smul_le x ξ s
        _ ≤ B * (1 + ‖ξ‖) := by
          dsimp [B]
          calc
            (1 + ‖x‖) * (1 + |s|) * (1 + ‖ξ‖) ≤
                (1 + ‖x‖) * (2 + |u|) * (1 + ‖ξ‖) := by
                  apply mul_le_mul_of_nonneg_right
                  · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
                  · positivity
            _ = (1 + ‖x‖) * (2 + |u|) * (1 + ‖ξ‖) := rfl
    have hcoord : ∀ i, |coordinateDerivative F i (x + s • ξ)| ≤
        C * (1 + ‖x + s • ξ‖) ^ d := by
      intro i
      calc
        |coordinateDerivative F i (x + s • ξ)| ≤
            |F (x + s • ξ)| + |coordinateDerivative F i (x + s • ξ)| :=
              le_add_of_nonneg_left (abs_nonneg _)
        _ ≤ C * (1 + ‖x + s • ξ‖) ^ d := hcoordinateBound i _
    have hfd := abs_fderiv_apply_le_of_coordinate_bound
      (x + s • ξ) ξ (mul_nonneg hC (pow_nonneg (by positivity) d)) hcoord
    have hxi : ‖ξ‖ ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    have hbase : C * (1 + ‖x + s • ξ‖) ^ d ≤ C * (B * (1 + ‖ξ‖)) ^ d := by
      gcongr
    have hscale : (Fintype.card (Fin n) : ℝ) * ‖ξ‖ *
        (C * (B * (1 + ‖ξ‖)) ^ d) ≤
        (Fintype.card (Fin n) : ℝ) * (1 + ‖ξ‖) *
          (C * (B * (1 + ‖ξ‖)) ^ d) := by
      gcongr
    have halgebra : (Fintype.card (Fin n) : ℝ) * (1 + ‖ξ‖) *
        (C * (B * (1 + ‖ξ‖)) ^ d) = K * (1 + ‖ξ‖) ^ (d + 1) := by
      dsimp [K]
      rw [mul_pow, pow_succ]
      ring
    simpa [Φ', Real.norm_eq_abs] using
      (calc
        |fderiv ℝ F (x + s • ξ) ξ| ≤
            (Fintype.card (Fin n) : ℝ) * ‖ξ‖ *
              (C * (1 + ‖x + s • ξ‖) ^ d) := hfd
        _ ≤ (Fintype.card (Fin n) : ℝ) * ‖ξ‖ *
              (C * (B * (1 + ‖ξ‖)) ^ d) := by gcongr
        _ ≤ (Fintype.card (Fin n) : ℝ) * (1 + ‖ξ‖) *
              (C * (B * (1 + ‖ξ‖)) ^ d) := hscale
        _ = K * (1 + ‖ξ‖) ^ (d + 1) := halgebra)
  have hdiff : ∀ᵐ ξ ∂(standardGaussianMeasure n), ∀ s ∈ Metric.ball u 1,
      HasDerivAt (Φ · ξ) (Φ' s ξ) s := by
    apply ae_of_all
    intro ξ s hs
    have harg : HasDerivAt (fun r : ℝ => x + r • ξ) ξ s := by
      convert ((hasDerivAt_id s).smul_const ξ).const_add x using 1
      · funext r
        simp
      · simp
    have houter := (hF.1.differentiable_one (x + s • ξ)).hasFDerivAt
    have hcomp := houter.comp_hasDerivAt s harg
    simpa [Φ, Φ', Function.comp_def] using hcomp
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := Φ) (x₀ := u) (s := Metric.ball u 1) (F' := Φ') (bound := fun ξ =>
      K * (1 + ‖ξ‖) ^ (d + 1)) (Metric.ball_mem_nhds _ zero_lt_one) hFmeas hFint
      hF'meas hbound hboundInt hdiff
  change @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule _ _
    (fun s => ∫ ξ, F (x + s • ξ) ∂(standardGaussianMeasure n))
    (∫ ξ, fderiv ℝ F (x + u • ξ) ξ ∂(standardGaussianMeasure n)) u
  exact hderiv.2

/-- Version of `hasDerivAt_shiftAverage_innerProduct` in the ambient real module structure. -/
theorem hasDerivAt_shiftAverage {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (x : Fin n → ℝ) (u : ℝ) :
    HasDerivAt (shiftAverage F x)
      (∫ ξ, fderiv ℝ F (x + u • ξ) ξ ∂(standardGaussianMeasure n)) u := by
  have hmodule : (RCLike.toInnerProductSpaceReal.toModule : Module ℝ ℝ) =
      (inferInstance : Module ℝ ℝ) := by
    apply Module.ext
    rfl
  have hadd : (Real.normedAddCommGroup.toAddCommGroup : AddCommGroup ℝ) =
      (inferInstance : AddCommGroup ℝ) := rfl
  simpa only [hmodule, hadd] using hasDerivAt_shiftAverage_innerProduct hF x u

/-- A coordinate derivative of `F` remains a polynomially bounded `C¹` function after a fixed
affine Gaussian shift. -/
lemma hasPolynomiallyBoundedCoordinateDerivatives_affinePartial {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x : Fin n → ℝ) (u : ℝ) (i : Fin n) :
    HasPolynomiallyBoundedCoordinateDerivatives
      (fun ξ => coordinateDerivative F i (x + u • ξ)) := by
  rcases hF.2 with ⟨C, hC, d, hfunction, hfirst, hsecond⟩
  let B : ℝ := (1 + ‖x‖) * (1 + |u|)
  let C' : ℝ := C * (1 + |u|) * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hshift : ContDiff ℝ 1 (fun ξ : Fin n → ℝ => x + u • ξ) := by fun_prop
  have hGcont : ContDiff ℝ 1 (fun ξ : Fin n → ℝ =>
      coordinateDerivative F i (x + u • ξ)) :=
    (contDiff_coordinateDerivative_of_two hF.1 i).comp hshift
  have hnormBound (ξ : Fin n → ℝ) : 1 + ‖x + u • ξ‖ ≤ B * (1 + ‖ξ‖) := by
    calc
      1 + ‖x + u • ξ‖ ≤ (1 + ‖x‖) * (1 + |u|) * (1 + ‖ξ‖) :=
        one_add_norm_add_smul_le x ξ u
      _ = B * (1 + ‖ξ‖) := rfl
  have hpolyBound (ξ : Fin n → ℝ) :
      C * (1 + ‖x + u • ξ‖) ^ d ≤ C * B ^ d * (1 + ‖ξ‖) ^ d := by
    calc
      C * (1 + ‖x + u • ξ‖) ^ d ≤ C * (B * (1 + ‖ξ‖)) ^ d := by
        gcongr
        exact hnormBound ξ
      _ = C * B ^ d * (1 + ‖ξ‖) ^ d := by rw [mul_pow]; ring
  constructor
  · exact hGcont
  · refine ⟨C', hC', d, ?_, ?_⟩
    · intro ξ
      calc
        |coordinateDerivative F i (x + u • ξ)| ≤
            C * (1 + ‖x + u • ξ‖) ^ d := hfirst i _
        _ ≤ C * B ^ d * (1 + ‖ξ‖) ^ d := hpolyBound ξ
        _ ≤ C' * (1 + ‖ξ‖) ^ d := by
          dsimp [C']
          have hfactor : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
          gcongr
          calc
            C = C * 1 := by ring
            _ ≤ C * (1 + |u|) := mul_le_mul_of_nonneg_left hfactor hC
    · intro j ξ
      have hderiv := coordinateDerivative_affine_smul
        (contDiff_coordinateDerivative_of_two hF.1 i) x u j ξ
      calc
        |coordinateDerivative F i (x + u • ξ)| +
            |coordinateDerivative (fun η => coordinateDerivative F i (x + u • η)) j ξ|
            ≤ C * (1 + ‖x + u • ξ‖) ^ d +
                |u| * (C * (1 + ‖x + u • ξ‖) ^ d) := by
                  rw [hderiv, abs_mul]
                  exact add_le_add (hfirst i _) (mul_le_mul_of_nonneg_left
                    (hsecond i j _) (abs_nonneg _))
        _ = C * (1 + |u|) * (1 + ‖x + u • ξ‖) ^ d := by ring
        _ ≤ C * (1 + |u|) * (B * (1 + ‖ξ‖)) ^ d := by
          gcongr
          exact hnormBound ξ
        _ = C' * (1 + ‖ξ‖) ^ d := by
          dsimp [C']
          rw [mul_pow]
          ring

/-- The derivative of a Gaussian shift average is its scale parameter times the averaged
Laplacian. -/
private theorem integral_fderiv_shift_eq_smul_laplacian {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x : Fin n → ℝ) (u : ℝ) :
    ∫ ξ, fderiv ℝ F (x + u • ξ) ξ ∂(standardGaussianMeasure n) =
      u * ∫ ξ, ∑ i, coordinateDerivative (coordinateDerivative F i) i
        (x + u • ξ) ∂(standardGaussianMeasure n) := by
  rcases hF.2 with ⟨C, hC, d, hfunction, hfirst, hsecond⟩
  let term : Fin n → (Fin n → ℝ) → ℝ := fun i ξ =>
    ξ i * coordinateDerivative F i (x + u • ξ)
  have hpartialC1 (i : Fin n) : ContDiff ℝ 1 (coordinateDerivative F i) :=
    contDiff_coordinateDerivative_of_two hF.1 i
  have hpartialCont (i : Fin n) : Continuous (coordinateDerivative F i) :=
    (hpartialC1 i).continuous
  have htermInt (i : Fin n) : Integrable (term i) (standardGaussianMeasure n) := by
    simpa [term] using integrable_eval_mul_shift_of_polynomial_bound
      (hpartialCont i).measurable hC (fun z => hfirst i z) i x u
  have hsecondCont (i : Fin n) :
      Continuous (coordinateDerivative (coordinateDerivative F i) i) := by
    unfold coordinateDerivative
    exact ((hpartialC1 i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsecondInt (i : Fin n) :
      Integrable (fun ξ => coordinateDerivative (coordinateDerivative F i) i
        (x + u • ξ)) (standardGaussianMeasure n) := by
    apply integrable_shift_of_polynomial_bound (hsecondCont i).measurable hC
    exact hsecond i i
  have htermIBP (i : Fin n) :
      ∫ ξ, term i ξ ∂(standardGaussianMeasure n) =
        u * ∫ ξ, coordinateDerivative (coordinateDerivative F i) i
          (x + u • ξ) ∂(standardGaussianMeasure n) := by
    let G : (Fin n → ℝ) → ℝ := fun ξ => coordinateDerivative F i (x + u • ξ)
    have hG := hasPolynomiallyBoundedCoordinateDerivatives_affinePartial hF x u i
    have hIBP := integral_eval_mul_eq_integral_coordinateDerivative hG i
    calc
      ∫ ξ, term i ξ ∂(standardGaussianMeasure n) = ∫ ξ, ξ i * G ξ ∂(standardGaussianMeasure n) := by
        apply integral_congr_ae
        exact ae_of_all _ fun ξ => rfl
      _ = ∫ ξ, coordinateDerivative G i ξ ∂(standardGaussianMeasure n) := hIBP
      _ = ∫ ξ, u * coordinateDerivative (coordinateDerivative F i) i
          (x + u • ξ) ∂(standardGaussianMeasure n) := by
            apply integral_congr_ae
            exact ae_of_all _ fun ξ => coordinateDerivative_affine_smul
              (hpartialC1 i) x u i ξ
      _ = u * ∫ ξ, coordinateDerivative (coordinateDerivative F i) i
          (x + u • ξ) ∂(standardGaussianMeasure n) := integral_const_mul u _
  have htraceIntegral :
      ∫ ξ, ∑ i, coordinateDerivative (coordinateDerivative F i) i
        (x + u • ξ) ∂(standardGaussianMeasure n) =
      ∑ i, ∫ ξ, coordinateDerivative (coordinateDerivative F i) i
        (x + u • ξ) ∂(standardGaussianMeasure n) := by
    simpa using integral_finsetSum (μ := standardGaussianMeasure n) (s := Finset.univ)
      (f := fun i ξ => coordinateDerivative (coordinateDerivative F i) i
        (x + u • ξ)) (fun i hi => hsecondInt i)
  calc
    ∫ ξ, fderiv ℝ F (x + u • ξ) ξ ∂(standardGaussianMeasure n) =
        ∫ ξ, ∑ i, term i ξ ∂(standardGaussianMeasure n) := by
          apply integral_congr_ae
          exact ae_of_all _ fun ξ => fderiv_apply_eq_sum_coordinateDerivative
            (x + u • ξ) ξ
    _ = ∑ i, ∫ ξ, term i ξ ∂(standardGaussianMeasure n) := by
          simpa [term] using integral_finsetSum (μ := standardGaussianMeasure n)
            (s := Finset.univ) (f := fun i ξ => ξ i *
              coordinateDerivative F i (x + u • ξ)) (fun i hi => htermInt i)
    _ = ∑ i, u * ∫ ξ, coordinateDerivative (coordinateDerivative F i) i
        (x + u • ξ) ∂(standardGaussianMeasure n) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact htermIBP i
    _ = u * ∑ i, ∫ ξ, coordinateDerivative (coordinateDerivative F i) i
        (x + u • ξ) ∂(standardGaussianMeasure n) := by rw [Finset.mul_sum]
    _ = u * ∫ ξ, ∑ i, coordinateDerivative (coordinateDerivative F i) i
        (x + u • ξ) ∂(standardGaussianMeasure n) := by rw [← htraceIntegral]

/-- The finite-dimensional Gaussian heat identity at positive time. -/
theorem hasDerivAt_heatAverage {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (heatAverage F x) ((1 / 2 : ℝ) * heatLaplacianAverage F x t) t := by
  rcases hF.2 with ⟨C, hC, d, hfunction, hfirst, hsecond⟩
  have hC1 : ContDiff ℝ 1 F := hF.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hbase : HasPolynomiallyBoundedCoordinateDerivatives F := by
    refine ⟨hC1, 2 * C, ?_, d, ?_, ?_⟩
    · positivity
    · intro z
      calc
        |F z| ≤ C * (1 + ‖z‖) ^ d := hfunction z
        _ ≤ 2 * C * (1 + ‖z‖) ^ d := by
          have hnonneg : 0 ≤ C * (1 + ‖z‖) ^ d := mul_nonneg hC (by positivity)
          nlinarith
    · intro i z
      calc
        |F z| + |coordinateDerivative F i z| ≤
            C * (1 + ‖z‖) ^ d + C * (1 + ‖z‖) ^ d :=
              add_le_add (hfunction z) (hfirst i z)
        _ = 2 * C * (1 + ‖z‖) ^ d := by ring
  have hshift := hasDerivAt_shiftAverage hbase x (Real.sqrt t)
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t :=
    Real.hasDerivAt_sqrt (ne_of_gt ht)
  have hrootne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hscale := integral_fderiv_shift_eq_smul_laplacian hF x (Real.sqrt t)
  have hcomp := hshift.comp t hsqrt
  convert hcomp using 1
  · rfl
  · dsimp [heatLaplacianAverage]
    rw [hscale]
    field_simp [hrootne]








end EhrhardGaussian.Ehrhard
