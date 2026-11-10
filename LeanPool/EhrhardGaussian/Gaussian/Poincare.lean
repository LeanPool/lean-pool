/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-
Ported from RegularityStructures-dev, commit 852e51c64f977a7cdd3eacab66e0188bc0ed75a2.
Modified for EhrhardGaussian, 2026.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Finite-dimensional standard Gaussian integration by parts uses coordinate derivatives and
polynomial growth bounds (Hairer–Steele, Definition 2.20 and Remark 2.22). -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace EhrhardGaussian.Gaussian

/-- The product standard Gaussian measure on `(Fin n → ℝ)`. -/
def standardGaussianMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

instance isProbabilityMeasure_standardGaussianMeasure (n : ℕ) :
    IsProbabilityMeasure (standardGaussianMeasure n) := by
  unfold standardGaussianMeasure
  infer_instance

/-- The `i`th coordinate derivative, written using the coordinate direction in `ℝⁿ`. -/
def coordinateDerivative {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The density of the product standard Gaussian with respect to product Lebesgue measure. -/
def standardGaussianDensity {n : ℕ} (x : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i, gaussianPDF 0 1 (x i)

/-- The same density as a real-valued function, for weighted Lebesgue integrals. -/
def standardGaussianDensityReal {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

/-- The real value of the nonnegative standard Gaussian density is its usual real density. -/
theorem standardGaussianDensity_toReal {n : ℕ} (x : Fin n → ℝ) :
    (standardGaussianDensity x).toReal = standardGaussianDensityReal x := by
  simp [standardGaussianDensity, standardGaussianDensityReal]

/-- The finite-dimensional standard Gaussian density is measurable. -/
theorem measurable_standardGaussianDensity {n : ℕ} :
    Measurable (standardGaussianDensity (n := n)) := by
  unfold standardGaussianDensity
  fun_prop

private lemma hasDerivAt_gaussianPDFReal_zero_one' (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  rw [gaussianPDFReal_def]
  have harg : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ) using 1
    · norm_num
    · norm_num
      ring
  have hexp : HasDerivAt (fun y : ℝ => rexp (-y ^ 2 / 2))
      (rexp (-x ^ 2 / 2) * (-x)) x :=
    (Real.hasDerivAt_exp _).comp x harg
  have hconst : HasDerivAt (fun _ : ℝ => (√(2 * π))⁻¹) 0 x :=
    hasDerivAt_const x _
  convert hconst.mul hexp using 1
  · funext y
    congr 1
    · norm_num
    · congr 1
      simp only [NNReal.coe_one, mul_one]
      ring_nf
  · simp only [NNReal.coe_one, mul_one]
    ring_nf

private lemma fderiv_standardGaussianDensityReal {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ standardGaussianDensityReal x (Pi.single i 1) =
      -x i * standardGaussianDensityReal x := by
  classical
  unfold standardGaussianDensityReal
  rw [fderiv_finsetProd]
  · have hcoord (k : Fin n) :
        fderiv ℝ (fun y : Fin n → ℝ => gaussianPDFReal 0 1 (y k)) x
            (Pi.single i 1) =
          if k = i then -x i * gaussianPDFReal 0 1 (x i) else 0 := by
      change fderiv ℝ (gaussianPDFReal 0 1 ∘ fun y : Fin n → ℝ => y k) x
          (Pi.single i 1) = _
      have hcomp := (hasDerivAt_gaussianPDFReal_zero_one' (x k)).hasFDerivAt.comp
        (f := fun y : Fin n → ℝ => y k) x
        (hasFDerivAt_apply k x)
      rw [hcomp.fderiv]
      by_cases hki : k = i
      · subst k
        simp
      · simp [hki]
    rw [_root_.sum_apply]
    simp only [_root_.smul_apply, smul_eq_mul]
    simp_rw [hcoord]
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl]
      calc
        (∏ j ∈ Finset.univ.erase i, gaussianPDFReal 0 1 (x j)) *
              (-x i * gaussianPDFReal 0 1 (x i)) =
            -x i *
              ((∏ j ∈ Finset.univ.erase i, gaussianPDFReal 0 1 (x j)) *
                gaussianPDFReal 0 1 (x i)) := by ring
        _ = -x i * ∏ j ∈ Finset.univ, gaussianPDFReal 0 1 (x j) := by
          rw [Finset.prod_erase_mul Finset.univ
            (fun j => gaussianPDFReal 0 1 (x j)) (Finset.mem_univ i)]
    · intro j hj hji
      simp [hji]
    · simp
  · intro k hk
    change DifferentiableAt ℝ (gaussianPDFReal 0 1 ∘ fun y : Fin n → ℝ => y k) x
    exact ((hasDerivAt_gaussianPDFReal_zero_one' (x k)).hasFDerivAt.comp
      (f := fun y : Fin n → ℝ => y k) x (hasFDerivAt_apply k x)).differentiableAt

/-- The finite standard Gaussian law is Lebesgue measure weighted by its Gaussian density. -/
theorem standardGaussianMeasure_eq_withDensity (n : ℕ) :
    standardGaussianMeasure n =
      (volume : Measure (Fin n → ℝ)).withDensity standardGaussianDensity := by
  classical
  refine Measure.pi_eq (μ := fun _ : Fin n => gaussianReal 0 1) (fun s hs => ?_)
  have hset : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hset, ← lintegral_indicator hset]
  have hprod : Integrable
      (fun x : Fin n → ℝ => ∏ i, (Set.indicator (s i) (gaussianPDFReal 0 1)) (x i))
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) := by
    apply Integrable.fintype_prod
    intro i
    exact (integrable_gaussianPDFReal 0 1).indicator (hs i)
  have hnonneg : 0 ≤ᵐ[Measure.pi (fun _ : Fin n => (volume : Measure ℝ))]
      (fun x : Fin n → ℝ => ∏ i, (Set.indicator (s i) (gaussianPDFReal 0 1)) (x i)) :=
    Filter.Eventually.of_forall (fun x => Finset.prod_nonneg fun i _ => by
      by_cases hx : x i ∈ s i
      · rw [Set.indicator_of_mem hx]
        exact gaussianPDFReal_nonneg 0 1 _
      · rw [Set.indicator_of_notMem hx]
        )
  have hpoint :
      (Set.univ.pi s).indicator standardGaussianDensity =
        (fun x : Fin n → ℝ => ENNReal.ofReal
          (∏ i, (Set.indicator (s i) (gaussianPDFReal 0 1)) (x i))) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · have hxi : ∀ i, x i ∈ s i := by simpa using hx
      simp only [Set.indicator_of_mem hx, standardGaussianDensity]
      rw [ENNReal.ofReal_prod_of_nonneg]
      · congr 1
        funext i
        simp [Set.indicator_of_mem (hxi i), gaussianPDF]
      · intro i hi
        by_cases hxi' : x i ∈ s i
        · simp [Set.indicator_of_mem hxi', gaussianPDFReal_nonneg]
        · simp [Set.indicator_of_notMem hxi']
    · obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        have hnot : ¬ ∀ i, x i ∈ s i := by
          intro hall
          exact hx (Set.mem_pi.2 (fun i _ => hall i))
        exact not_forall.mp hnot
      rw [Set.indicator_of_notMem hx]
      have hzero : (s i).indicator (gaussianPDFReal 0 1) (x i) = 0 :=
        Set.indicator_of_notMem hi _
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
      simp
  rw [hpoint]
  change (∫⁻ x : Fin n → ℝ, ENNReal.ofReal
      (∏ i, (Set.indicator (s i) (gaussianPDFReal 0 1)) (x i)) ∂
        (Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hprod hnonneg]
  · rw [integral_fintype_prod_eq_prod]
    simp_rw [integral_indicator (hs _), gaussianReal_apply_eq_integral 0 one_ne_zero]
    rw [← ENNReal.ofReal_prod_of_nonneg]
    intro i hi
    exact integral_nonneg fun x => gaussianPDFReal_nonneg 0 1 x

/-- Gaussian integration by parts holds in each coordinate of a finite standard Gaussian vector. -/
theorem standardGaussianIntegrationByParts {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f)
    (_hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hint_f : Integrable (fun x => f x * standardGaussianDensityReal x) volume)
    (hint_deriv : ∀ i, Integrable
      (fun x => coordinateDerivative f i x * standardGaussianDensityReal x) volume)
    (hint_x : ∀ i, Integrable
      (fun x => x i * f x * standardGaussianDensityReal x) volume) :
    ∀ i, ∫ x, x i * f x ∂standardGaussianMeasure n =
      ∫ x, coordinateDerivative f i x ∂standardGaussianMeasure n := by
  classical
  intro i
  have hdensity_diff (x : Fin n → ℝ) :
      DifferentiableAt ℝ standardGaussianDensityReal x := by
    unfold standardGaussianDensityReal
    simpa only [Finset.prod_apply] using
      (HasFDerivAt.finsetProd (u := (Finset.univ : Finset (Fin n)))
        (g := fun (k : Fin n) (y : Fin n → ℝ) => gaussianPDFReal 0 1 (y k)) (x := x)
        (fun k hk => (hasDerivAt_gaussianPDFReal_zero_one' (x k)).hasFDerivAt.comp
          (f := fun y : Fin n → ℝ => y k) x (hasFDerivAt_apply k x))).differentiableAt
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Fin n → ℝ)))
    (hf'g := by
      simpa only [coordinateDerivative] using hint_deriv i)
    (hfg' := by
      refine (hint_x i).neg.congr ?_
      filter_upwards [] with x
      rw [fderiv_standardGaussianDensityReal]
      change -(x i * f x * standardGaussianDensityReal x) =
        f x * (-x i * standardGaussianDensityReal x)
      ring)
    (hfg := hint_f)
    (hf := fun x _ => hcont.contDiffAt.differentiableAt_one)
    (hg := fun x _ => hdensity_diff x)
    (v := Pi.single i 1) (f := f) (g := standardGaussianDensityReal)
  have htop : ∀ᵐ x : Fin n → ℝ ∂(volume : Measure (Fin n → ℝ)),
      standardGaussianDensity x < ⊤ :=
    Filter.Eventually.of_forall (fun x => by
      exact ENNReal.prod_lt_top (fun k hk => gaussianPDF_lt_top))
  have hleft :
      ∫ x, x i * f x ∂standardGaussianMeasure n =
        ∫ x, standardGaussianDensityReal x * (x i * f x) ∂volume := by
    rw [standardGaussianMeasure_eq_withDensity]
    rw [integral_withDensity_eq_integral_toReal_smul measurable_standardGaussianDensity
      htop]
    simp only [standardGaussianDensity_toReal, smul_eq_mul]
  have hright :
      ∫ x, coordinateDerivative f i x ∂standardGaussianMeasure n =
        ∫ x, standardGaussianDensityReal x * coordinateDerivative f i x ∂volume := by
    rw [standardGaussianMeasure_eq_withDensity]
    rw [integral_withDensity_eq_integral_toReal_smul measurable_standardGaussianDensity
      htop]
    simp only [standardGaussianDensity_toReal, smul_eq_mul]
  rw [hleft, hright]
  have hparts' :
      ∫ x, f x * (-x i * standardGaussianDensityReal x) ∂volume =
        -∫ x, coordinateDerivative f i x * standardGaussianDensityReal x ∂volume := by
    convert hparts using 1
    · congr 1
      funext x
      rw [fderiv_standardGaussianDensityReal]
    · rfl
  calc
    ∫ x, standardGaussianDensityReal x * (x i * f x) ∂volume =
        -∫ x, f x * (-x i * standardGaussianDensityReal x) ∂volume := by
      rw [← integral_neg]
      congr 1
      funext x
      ring
    _ = ∫ x, coordinateDerivative f i x * standardGaussianDensityReal x ∂volume := by
      rw [hparts']
      simp
    _ = ∫ x, standardGaussianDensityReal x * coordinateDerivative f i x ∂volume := by
      congr 1
      funext x
      ring

end EhrhardGaussian.Gaussian

end
