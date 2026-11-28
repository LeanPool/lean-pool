/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.BivariateNormalCDF
public import Mathlib.Algebra.Order.Star.Real

/-!
# Hoeffding's covariance identity

For square-integrable random variables `X, Y` on a probability space, the covariance is the
integral over the plane of the gap between the joint CDF and the product of the marginal CDFs:

  `cov(X, Y) = ∫∫ (P(X ≤ s, Y ≤ t) − P(X ≤ s) P(Y ≤ t)) ds dt`

(`covariance_eq_integral_cdf`; Hoeffding 1940, Höffding's lemma in McNeil–Frey–Embrechts (2015),
Chapter 7).

The proof writes each real number as the integral of its signed layer,
`a = ∫ (𝟙{s < a} − 𝟙{s < 0}) ds`, so that `X Y`, `E[X]` and `E[Y]` become integrals over the plane
of indicator expressions. Fubini swaps the expectation inside, and at each point `(s, t)` the
constants `𝟙{s < 0}`, `𝟙{t < 0}` cancel from the covariance of the indicators
`𝟙{X > s}` and `𝟙{Y > t}`. That covariance equals `P(X ≤ s, Y ≤ t) − P(X ≤ s) P(Y ≤ t)` by
inclusion–exclusion. The identity is stated for the law of `(X, Y)` on `ℝ²`
(`covariance_fst_snd_eq_integral`) and transported to random variables through their joint law.

## Consequences

* **Covariance is monotone in the joint CDF** (`covariance_le_covariance_of_cdf_le`; QRM Exercise
  Book Ex. 7.14). Two pairs with the same marginal laws whose joint CDFs are pointwise ordered have
  ordered covariances, and so ordered correlations. The marginals fix the subtracted term and the
  variances, and the joint CDF enters linearly. Combined with the Fréchet–Hoeffding bounds on joint
  CDFs (proved for copulas in `Probability/Dependence/Copula.lean`), this is the mechanism by which
  comonotone
  (resp. countermonotone) dependence attains the largest (resp. smallest) correlation for given
  marginals (MFE (2015) Theorem 7.28).
* **Default-correlation bounds** (`le_covariance_indicator_one`, `covariance_indicator_one_le`;
  Ex. 11.7). For default indicators of events with probabilities `p₁, p₂`, the covariance lies
  between `max(p₁ + p₂ − 1, 0) − p₁p₂` and `min(p₁, p₂) − p₁p₂`: these are the Fréchet bounds on
  `P(A ∩ B)`. The bounds are attained by nested events and by events whose union is certain. The
  correlation bounds follow by dividing by `√(p₁(1 − p₁)p₂(1 − p₂))`.

## Main results

* `covariance_indicator_one`: `cov(𝟙_A, 𝟙_B) = P(A ∩ B) − P(A) P(B)`.
* `integral_bivariateNormalCDF_sub_mul`: at the standard bivariate normal law with correlation
  `r ∈ [−1, 1]`, `∫∫ (N₂(s, t; r) − Φ(s) Φ(t)) ds dt = r`.
* `covariance_fst_snd_eq_integral`: Hoeffding's identity for a law on `ℝ²`.
* `covariance_eq_integral_cdf`: Hoeffding's identity for random variables.
* `integrable_cdf_sub_mul`: the Hoeffding integrand is integrable on `ℝ²`.
* `covariance_le_covariance_of_cdf_le`, `correlation_le_correlation_of_cdf_le`: ordering.
* `variance_indicator_one`, `covariance_indicator_one_le`, `le_covariance_indicator_one`,
  `covariance_indicator_one_of_subset`, `covariance_indicator_one_of_union_eq_univ`,
  `correlation_indicator_one_le`, `le_correlation_indicator_one`: default-correlation bounds.

## References

* [Höffding (1940)][Hoeffding1940]
* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Lemma 7.27
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 11.7; Ex. 7.14

## Tags

Hoeffding covariance identity, Fréchet–Hoeffding bounds, joint distribution function,
comonotonicity, default correlation, correlation bounds, dependence, MSC 62H05, MSC 60E15, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Function

/-! ### Covariance of indicators -/

section Indicator

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  {A B : Set α}

/-- An indicator is square integrable. -/
lemma memLp_indicator_one (hA : MeasurableSet A) : MemLp (A.indicator (1 : α → ℝ)) 2 μ :=
  memLp_indicator_const 2 hA.nullMeasurableSet 1 (Or.inr (measure_ne_top _ _))

/-- **Covariance of two indicators**: `cov(𝟙_A, 𝟙_B) = P(A ∩ B) − P(A) P(B)`. -/
theorem covariance_indicator_one (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cov[A.indicator 1, B.indicator 1; μ] = μ.real (A ∩ B) - μ.real A * μ.real B := by
  rw [covariance_eq_sub (memLp_indicator_one hA) (memLp_indicator_one hB), ← inter_indicator_one,
    integral_indicator_one (hA.inter hB), integral_indicator_one hA, integral_indicator_one hB]

/-- Shifting indicators by constants does not change their covariance:
`E[(𝟙_A − c)(𝟙_B − d)] − E[𝟙_A − c] E[𝟙_B − d] = P(A ∩ B) − P(A) P(B)`. -/
lemma integral_indicator_sub_mul_sub (hA : MeasurableSet A) (hB : MeasurableSet B) (c d : ℝ) :
    ∫ x, (A.indicator 1 x - c) * (B.indicator 1 x - d) ∂μ
      - (∫ x, (A.indicator 1 x - c) ∂μ) * ∫ x, (B.indicator 1 x - d) ∂μ
      = μ.real (A ∩ B) - μ.real A * μ.real B := by
  have hf : MemLp (fun x ↦ A.indicator 1 x - c) 2 μ := (memLp_indicator_one hA).sub (memLp_const c)
  have hg : MemLp (fun x ↦ B.indicator 1 x - d) 2 μ := (memLp_indicator_one hB).sub (memLp_const d)
  rw [← covariance_indicator_one hA hB,
    ← covariance_sub_const_left ((memLp_indicator_one hA).integrable one_le_two) c,
    ← covariance_sub_const_right ((memLp_indicator_one hB).integrable one_le_two) d]
  exact (covariance_eq_sub hf hg).symm

/-- **Variance of an indicator**: `Var(𝟙_A) = P(A) (1 − P(A))`. -/
theorem variance_indicator_one (hA : MeasurableSet A) :
    Var[A.indicator 1; μ] = μ.real A * (1 - μ.real A) := by
  rw [← covariance_self (memLp_indicator_one hA).aemeasurable,
    covariance_indicator_one hA hA, inter_self]
  ring

/-- Inclusion–exclusion leaves `P(A ∩ B) − P(A) P(B)` unchanged under complementing both events. -/
lemma measureReal_inter_sub_mul_compl (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ.real (Aᶜ ∩ Bᶜ) - μ.real Aᶜ * μ.real Bᶜ = μ.real (A ∩ B) - μ.real A * μ.real B := by
  have h := measureReal_union_add_inter (μ := μ) (s := A) hB
  rw [← compl_union, probReal_compl_eq_one_sub (hA.union hB), probReal_compl_eq_one_sub hA,
    probReal_compl_eq_one_sub hB]
  linarith

/-! ### Default-correlation bounds -/

/-- **Upper Fréchet bound for default covariance**:
`cov(𝟙_A, 𝟙_B) ≤ min(P(A), P(B)) − P(A) P(B)`. -/
theorem covariance_indicator_one_le (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cov[A.indicator 1, B.indicator 1; μ] ≤ min (μ.real A) (μ.real B) - μ.real A * μ.real B := by
  rw [covariance_indicator_one hA hB]
  gcongr
  exact le_min (measureReal_mono inter_subset_left) (measureReal_mono inter_subset_right)

/-- **Lower Fréchet bound for default covariance**:
`max(P(A) + P(B) − 1, 0) − P(A) P(B) ≤ cov(𝟙_A, 𝟙_B)`. -/
theorem le_covariance_indicator_one (hA : MeasurableSet A) (hB : MeasurableSet B) :
    max (μ.real A + μ.real B - 1) 0 - μ.real A * μ.real B
      ≤ cov[A.indicator 1, B.indicator 1; μ] := by
  rw [covariance_indicator_one hA hB]
  gcongr
  refine max_le ?_ measureReal_nonneg
  have h := measureReal_union_add_inter (μ := μ) (s := A) hB
  have h1 : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
  linarith

/-- The upper bound is attained by nested events: if `A ⊆ B` then
`cov(𝟙_A, 𝟙_B) = min(P(A), P(B)) − P(A) P(B)`. -/
theorem covariance_indicator_one_of_subset (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) :
    cov[A.indicator 1, B.indicator 1; μ] = min (μ.real A) (μ.real B) - μ.real A * μ.real B := by
  rw [covariance_indicator_one hA hB, inter_eq_left.2 hAB, min_eq_left (measureReal_mono hAB)]

/-- The lower bound is attained when the union is certain: if `A ∪ B = univ` then
`cov(𝟙_A, 𝟙_B) = max(P(A) + P(B) − 1, 0) − P(A) P(B)`. -/
theorem covariance_indicator_one_of_union_eq_univ (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ∪ B = univ) :
    cov[A.indicator 1, B.indicator 1; μ]
      = max (μ.real A + μ.real B - 1) 0 - μ.real A * μ.real B := by
  have h := measureReal_union_add_inter (μ := μ) (s := A) hB
  have h0 : 0 ≤ μ.real (A ∩ B) := measureReal_nonneg
  rw [hAB, probReal_univ] at h
  rw [covariance_indicator_one hA hB, max_eq_left (by linarith)]
  linarith

/-- **Upper bound on default correlation** (QRM Exercise Book Ex. 11.7):
`ρ(𝟙_A, 𝟙_B) ≤ (min(p₁, p₂) − p₁p₂) / √(p₁(1 − p₁)p₂(1 − p₂))`. -/
theorem correlation_indicator_one_le (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cov[A.indicator 1, B.indicator 1; μ] / √(Var[A.indicator 1; μ] * Var[B.indicator 1; μ])
      ≤ (min (μ.real A) (μ.real B) - μ.real A * μ.real B)
        / √(μ.real A * (1 - μ.real A) * (μ.real B * (1 - μ.real B))) := by
  rw [variance_indicator_one hA, variance_indicator_one hB]
  gcongr
  exact covariance_indicator_one_le hA hB

/-- **Lower bound on default correlation** (QRM Exercise Book Ex. 11.7):
`(max(p₁ + p₂ − 1, 0) − p₁p₂) / √(p₁(1 − p₁)p₂(1 − p₂)) ≤ ρ(𝟙_A, 𝟙_B)`. -/
theorem le_correlation_indicator_one (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (max (μ.real A + μ.real B - 1) 0 - μ.real A * μ.real B)
        / √(μ.real A * (1 - μ.real A) * (μ.real B * (1 - μ.real B)))
      ≤ cov[A.indicator 1, B.indicator 1; μ]
        / √(Var[A.indicator 1; μ] * Var[B.indicator 1; μ]) := by
  rw [variance_indicator_one hA, variance_indicator_one hB]
  gcongr
  exact le_covariance_indicator_one hA hB

end Indicator

/-! ### The signed layer of a real number -/

/-- `𝟙{s < a} − 𝟙{s < 0}`, the signed indicator of the interval between `0` and `a`. -/
private noncomputable def layer (a s : ℝ) : ℝ :=
  (Iio a).indicator 1 s - (Iio 0).indicator 1 s

private lemma layer_eq (a s : ℝ) :
    layer a s = (Ico 0 a).indicator 1 s - (Ico a 0).indicator 1 s := by
  rcases lt_or_ge s 0 with h0 | h0 <;> rcases lt_or_ge s a with ha | ha
  · simp [layer, h0, ha, h0.not_ge, ha.not_ge]
  · simp [layer, h0, ha, h0.not_ge, ha.not_gt]
  · simp [layer, h0, ha, h0.not_gt, ha.not_ge]
  · simp [layer, h0, ha, h0.not_gt, ha.not_gt]

private lemma abs_layer (a s : ℝ) :
    |layer a s| = (Ico 0 a).indicator 1 s + (Ico a 0).indicator 1 s := by
  rcases lt_or_ge s 0 with h0 | h0 <;> rcases lt_or_ge s a with ha | ha
  · simp [layer, h0, ha, h0.not_ge, ha.not_ge]
  · simp [layer, h0, ha, h0.not_ge, ha.not_gt]
  · simp [layer, h0, ha, h0.not_gt, ha.not_ge]
  · simp [layer, h0, ha, h0.not_gt, ha.not_gt]

/-- The indicator of a bounded interval `[a, b)` is integrable. -/
lemma integrable_indicator_Ico (a b : ℝ) :
    Integrable ((Ico a b).indicator (1 : ℝ → ℝ)) :=
  (integrableOn_const (by simp)).integrable_indicator measurableSet_Ico

private lemma integrable_layer (a : ℝ) : Integrable (layer a) := by
  rw [show layer a = (Ico 0 a).indicator 1 - (Ico a 0).indicator 1 from funext (layer_eq a)]
  exact (integrable_indicator_Ico 0 a).sub (integrable_indicator_Ico a 0)

/-- The signed layer integrates to its endpoint: `∫ (𝟙{s < a} − 𝟙{s < 0}) ds = a`. -/
private lemma integral_layer (a : ℝ) : ∫ s, layer a s = a := by
  simp_rw [layer_eq]
  rw [integral_sub (integrable_indicator_Ico 0 a) (integrable_indicator_Ico a 0),
    integral_indicator_one measurableSet_Ico, integral_indicator_one measurableSet_Ico,
    Real.volume_real_Ico, Real.volume_real_Ico]
  rcases le_total 0 a with h | h <;> simp [h]

private lemma integral_abs_layer (a : ℝ) : ∫ s, |layer a s| = |a| := by
  simp_rw [abs_layer]
  rw [integral_add (integrable_indicator_Ico 0 a) (integrable_indicator_Ico a 0),
    integral_indicator_one measurableSet_Ico, integral_indicator_one measurableSet_Ico,
    Real.volume_real_Ico, Real.volume_real_Ico]
  rcases le_total 0 a with h | h <;> simp [h, abs_of_nonneg, abs_of_nonpos]

private lemma measurable_layer : Measurable (uncurry layer) :=
  (measurable_const.indicator (measurableSet_lt measurable_snd measurable_fst)).sub
    (measurable_const.indicator (measurableSet_Iio.preimage measurable_snd))

/-! ### Hoeffding's identity for a law on the plane -/

section Plane

variable {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- `(x, s) ↦ layer (f x) s` is integrable against `μ ⊗ ds` when `f` is integrable. -/
private lemma integrable_layer_comp {f : ℝ × ℝ → ℝ} (hf : Measurable f) (hint : Integrable f μ) :
    Integrable (uncurry fun (x : ℝ × ℝ) s ↦ layer (f x) s) (μ.prod volume) := by
  have hmeas : Measurable (uncurry fun (x : ℝ × ℝ) s ↦ layer (f x) s) :=
    measurable_layer.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2
    ⟨ae_of_all _ fun x ↦ integrable_layer (f x), ?_⟩
  simpa only [uncurry_apply_pair, Real.norm_eq_abs, integral_abs_layer] using hint.abs

omit [IsProbabilityMeasure μ] in
/-- `(x, (s, t)) ↦ layer x.1 s · layer x.2 t` is integrable against `μ ⊗ ds dt` when the
coordinates are square integrable: its inner integral is `|x.1 x.2|`. -/
private lemma integrable_layer_mul (h₁ : MemLp Prod.fst 2 μ) (h₂ : MemLp Prod.snd 2 μ) :
    Integrable (uncurry fun (x p : ℝ × ℝ) ↦ layer x.1 p.1 * layer x.2 p.2) (μ.prod volume) := by
  have hmeas : Measurable (uncurry fun (x p : ℝ × ℝ) ↦ layer x.1 p.1 * layer x.2 p.2) :=
    (measurable_layer.comp (measurable_fst.fst.prodMk measurable_snd.fst)).mul
      (measurable_layer.comp (measurable_fst.snd.prodMk measurable_snd.snd))
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨ae_of_all _ fun x ↦ ?_, ?_⟩
  · rw [Measure.volume_eq_prod]
    exact (integrable_layer x.1).mul_prod (integrable_layer x.2)
  · have hnorm (x : ℝ × ℝ) :
        ∫ p, ‖uncurry (fun (x p : ℝ × ℝ) ↦ layer x.1 p.1 * layer x.2 p.2) (x, p)‖
          = |x.1 * x.2| := by
      simp only [uncurry_apply_pair, norm_mul, Real.norm_eq_abs]
      rw [Measure.volume_eq_prod,
        integral_prod_mul (fun s ↦ |layer x.1 s|) (fun t ↦ |layer x.2 t|), integral_abs_layer,
        integral_abs_layer, abs_mul]
    simp_rw [hnorm]
    exact (h₁.integrable_mul h₂).abs

/-- At each point of the plane, the covariance of the two layers is the Hoeffding integrand. -/
private lemma integral_layer_mul_sub (p : ℝ × ℝ) :
    ∫ x, layer x.1 p.1 * layer x.2 p.2 ∂μ - (∫ x, layer x.1 p.1 ∂μ) * ∫ x, layer x.2 p.2 ∂μ
      = μ.real (Iic p) - μ.real (Prod.fst ⁻¹' Iic p.1) * μ.real (Prod.snd ⁻¹' Iic p.2) := by
  have hA : MeasurableSet (Prod.fst ⁻¹' Ioi p.1 : Set (ℝ × ℝ)) :=
    measurableSet_Ioi.preimage measurable_fst
  have hB : MeasurableSet (Prod.snd ⁻¹' Ioi p.2 : Set (ℝ × ℝ)) :=
    measurableSet_Ioi.preimage measurable_snd
  have h1 (x : ℝ × ℝ) :
      layer x.1 p.1 = (Prod.fst ⁻¹' Ioi p.1).indicator 1 x - (Iio 0).indicator 1 p.1 := rfl
  have h2 (x : ℝ × ℝ) :
      layer x.2 p.2 = (Prod.snd ⁻¹' Ioi p.2).indicator 1 x - (Iio 0).indicator 1 p.2 := rfl
  simp_rw [h1, h2]
  rw [integral_indicator_sub_mul_sub hA hB, ← measureReal_inter_sub_mul_compl hA hB,
    ← preimage_compl, ← preimage_compl, compl_Ioi, compl_Ioi]
  rfl

/-- **Hoeffding's covariance identity for a law on `ℝ²`**: if the coordinates are square
integrable under `μ`, then `cov_μ(x₁, x₂) = ∫ (F(p) − F₁(p₁) F₂(p₂)) dp`, with `F` the joint
CDF and `F₁`, `F₂` the marginal CDFs. The integrand is integrable
(`integrable_cdf_sub_mul_fst_snd`). -/
theorem covariance_fst_snd_eq_integral (h₁ : MemLp Prod.fst 2 μ) (h₂ : MemLp Prod.snd 2 μ) :
    cov[Prod.fst, Prod.snd; μ] = ∫ p : ℝ × ℝ,
      (μ.real (Iic p) - μ.real (Prod.fst ⁻¹' Iic p.1) * μ.real (Prod.snd ⁻¹' Iic p.2)) := by
  have hF := integrable_layer_mul h₁ h₂
  have hG₁ := integrable_layer_comp measurable_fst (h₁.integrable one_le_two)
  have hG₂ := integrable_layer_comp measurable_snd (h₂.integrable one_le_two)
  have hXY : ∫ x : ℝ × ℝ, x.1 * x.2 ∂μ
      = ∫ p : ℝ × ℝ, ∫ x, layer x.1 p.1 * layer x.2 p.2 ∂μ := by
    rw [← integral_integral_swap hF]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    dsimp only
    rw [Measure.volume_eq_prod, integral_prod_mul (layer x.1) (layer x.2), integral_layer,
      integral_layer]
  have hX : ∫ x : ℝ × ℝ, x.1 ∂μ = ∫ s, ∫ x, layer x.1 s ∂μ := by
    rw [← integral_integral_swap hG₁]
    exact integral_congr_ae (ae_of_all _ fun x ↦ (integral_layer x.1).symm)
  have hY : ∫ x : ℝ × ℝ, x.2 ∂μ = ∫ t, ∫ x, layer x.2 t ∂μ := by
    rw [← integral_integral_swap hG₂]
    exact integral_congr_ae (ae_of_all _ fun x ↦ (integral_layer x.2).symm)
  have hint : Integrable fun p : ℝ × ℝ ↦ ∫ x, layer x.1 p.1 * layer x.2 p.2 ∂μ :=
    hF.integral_prod_right
  have hprod : Integrable (fun p : ℝ × ℝ ↦ (∫ x, layer x.1 p.1 ∂μ) * ∫ x, layer x.2 p.2 ∂μ) := by
    rw [Measure.volume_eq_prod]
    exact hG₁.integral_prod_right.mul_prod hG₂.integral_prod_right
  calc cov[Prod.fst, Prod.snd; μ]
        = (∫ x : ℝ × ℝ, x.1 * x.2 ∂μ) - (∫ x : ℝ × ℝ, x.1 ∂μ) * ∫ x : ℝ × ℝ, x.2 ∂μ :=
        covariance_eq_sub h₁ h₂
    _ = (∫ p : ℝ × ℝ, ∫ x, layer x.1 p.1 * layer x.2 p.2 ∂μ)
          - ∫ p : ℝ × ℝ, (∫ x, layer x.1 p.1 ∂μ) * ∫ x, layer x.2 p.2 ∂μ := by
        rw [hXY, hX, hY, Measure.volume_eq_prod,
          integral_prod_mul (fun s ↦ ∫ x, layer x.1 s ∂μ) (fun t ↦ ∫ x, layer x.2 t ∂μ)]
    _ = ∫ p : ℝ × ℝ, (∫ x, layer x.1 p.1 * layer x.2 p.2 ∂μ
          - (∫ x, layer x.1 p.1 ∂μ) * ∫ x, layer x.2 p.2 ∂μ) := (integral_sub hint hprod).symm
    _ = _ := integral_congr_ae (ae_of_all _ integral_layer_mul_sub)

/-- The Hoeffding integrand of a law on `ℝ²` with square-integrable coordinates is integrable. -/
theorem integrable_cdf_sub_mul_fst_snd (h₁ : MemLp Prod.fst 2 μ) (h₂ : MemLp Prod.snd 2 μ) :
    Integrable fun p : ℝ × ℝ ↦
      μ.real (Iic p) - μ.real (Prod.fst ⁻¹' Iic p.1) * μ.real (Prod.snd ⁻¹' Iic p.2) := by
  have hint : Integrable fun p : ℝ × ℝ ↦ ∫ x, layer x.1 p.1 * layer x.2 p.2 ∂μ :=
    (integrable_layer_mul h₁ h₂).integral_prod_right
  have hprod : Integrable (fun p : ℝ × ℝ ↦ (∫ x, layer x.1 p.1 ∂μ) * ∫ x, layer x.2 p.2 ∂μ) := by
    rw [Measure.volume_eq_prod]
    exact (integrable_layer_comp measurable_fst
        (h₁.integrable one_le_two)).integral_prod_right.mul_prod
      (integrable_layer_comp measurable_snd (h₂.integrable one_le_two)).integral_prod_right
  exact (hint.sub hprod).congr (ae_of_all _ integral_layer_mul_sub)

end Plane

/-! ### Hoeffding's identity for random variables -/

section RandomVariables

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- Square integrability of `X` and `Y` transfers to the coordinates of their joint law. -/
lemma memLp_fst_snd_map (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    MemLp Prod.fst 2 (P.map fun ω ↦ (X ω, Y ω)) ∧ MemLp Prod.snd 2 (P.map fun ω ↦ (X ω, Y ω)) :=
  have hZ := hX.aemeasurable.prodMk hY.aemeasurable
  ⟨(memLp_map_measure_iff measurable_fst.aestronglyMeasurable hZ).2 hX,
    (memLp_map_measure_iff measurable_snd.aestronglyMeasurable hZ).2 hY⟩

omit [IsProbabilityMeasure P] in
/-- The Hoeffding integrand of the joint law of `(X, Y)`, written in terms of `X` and `Y`. -/
lemma cdf_sub_mul_map (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (p : ℝ × ℝ) :
    (P.map fun ω ↦ (X ω, Y ω)).real (Iic p)
        - (P.map fun ω ↦ (X ω, Y ω)).real (Prod.fst ⁻¹' Iic p.1)
          * (P.map fun ω ↦ (X ω, Y ω)).real (Prod.snd ⁻¹' Iic p.2)
      = P.real {ω | X ω ≤ p.1 ∧ Y ω ≤ p.2}
          - P.real {ω | X ω ≤ p.1} * P.real {ω | Y ω ≤ p.2} := by
  have hZ := hX.prodMk hY
  rw [map_measureReal_apply_of_aemeasurable hZ measurableSet_Iic,
    map_measureReal_apply_of_aemeasurable hZ (measurableSet_Iic.preimage measurable_fst),
    map_measureReal_apply_of_aemeasurable hZ (measurableSet_Iic.preimage measurable_snd)]
  rfl

/-- **Hoeffding's covariance identity** (Hoeffding 1940; Höffding's lemma in
McNeil–Frey–Embrechts (2015), Chapter 7): for square-integrable `X, Y`,
`cov(X, Y) = ∫∫ (P(X ≤ s, Y ≤ t) − P(X ≤ s) P(Y ≤ t)) ds dt`. -/
theorem covariance_eq_integral_cdf (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] = ∫ p : ℝ × ℝ,
      (P.real {ω | X ω ≤ p.1 ∧ Y ω ≤ p.2} - P.real {ω | X ω ≤ p.1} * P.real {ω | Y ω ≤ p.2}) := by
  have hZ := hX.aemeasurable.prodMk hY.aemeasurable
  obtain ⟨h₁, h₂⟩ := memLp_fst_snd_map hX hY
  have hlaw : HasLaw (fun ω ↦ (X ω, Y ω)) (P.map fun ω ↦ (X ω, Y ω)) P := ⟨hZ, rfl⟩
  rw [show cov[X, Y; P] = cov[Prod.fst ∘ (fun ω ↦ (X ω, Y ω)), Prod.snd ∘ (fun ω ↦ (X ω, Y ω)); P]
    from rfl, hlaw.covariance_comp measurable_fst.aemeasurable measurable_snd.aemeasurable,
    covariance_fst_snd_eq_integral h₁ h₂]
  exact integral_congr_ae (ae_of_all _ (cdf_sub_mul_map hX.aemeasurable hY.aemeasurable))

/-- The Hoeffding integrand of square-integrable `X, Y` is integrable on `ℝ²`. -/
theorem integrable_cdf_sub_mul (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    Integrable fun p : ℝ × ℝ ↦
      P.real {ω | X ω ≤ p.1 ∧ Y ω ≤ p.2} - P.real {ω | X ω ≤ p.1} * P.real {ω | Y ω ≤ p.2} := by
  obtain ⟨h₁, h₂⟩ := memLp_fst_snd_map hX hY
  exact (integrable_cdf_sub_mul_fst_snd h₁ h₂).congr
    (ae_of_all _ (cdf_sub_mul_map hX.aemeasurable hY.aemeasurable))

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' Y' : Ω' → ℝ}

/-- **Covariance is monotone in the joint CDF** (QRM Exercise Book Ex. 7.14): if `(X, Y)` and
`(X', Y')` have the same marginal laws and `P(X ≤ s, Y ≤ t) ≤ P'(X' ≤ s, Y' ≤ t)` for all
`s, t`, then `cov(X, Y) ≤ cov(X', Y')`. -/
theorem covariance_le_covariance_of_cdf_le (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX' : MemLp X' 2 P') (hY' : MemLp Y' 2 P') (hlawX : P.map X = P'.map X')
    (hlawY : P.map Y = P'.map Y')
    (hF : ∀ s t, P.real {ω | X ω ≤ s ∧ Y ω ≤ t} ≤ P'.real {ω | X' ω ≤ s ∧ Y' ω ≤ t}) :
    cov[X, Y; P] ≤ cov[X', Y'; P'] := by
  have hmarg {Z : Ω → ℝ} {Z' : Ω' → ℝ} (hZ : AEMeasurable Z P) (hZ' : AEMeasurable Z' P')
      (h : P.map Z = P'.map Z') (s : ℝ) : P.real {ω | Z ω ≤ s} = P'.real {ω | Z' ω ≤ s} := by
    have e := congrArg (fun ν : Measure ℝ ↦ ν.real (Iic s)) h
    rw [map_measureReal_apply_of_aemeasurable hZ measurableSet_Iic,
      map_measureReal_apply_of_aemeasurable hZ' measurableSet_Iic] at e
    exact e
  rw [covariance_eq_integral_cdf hX hY, covariance_eq_integral_cdf hX' hY']
  refine integral_mono (integrable_cdf_sub_mul hX hY) (integrable_cdf_sub_mul hX' hY')
    fun p ↦ ?_
  rw [hmarg hX.aemeasurable hX'.aemeasurable hlawX, hmarg hY.aemeasurable hY'.aemeasurable hlawY]
  exact sub_le_sub_right (hF p.1 p.2) _

/-- **Correlation is monotone in the joint CDF**: under the hypotheses of
`covariance_le_covariance_of_cdf_le`, the correlations are ordered too, because equal marginal
laws have equal variances. -/
theorem correlation_le_correlation_of_cdf_le (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX' : MemLp X' 2 P') (hY' : MemLp Y' 2 P') (hlawX : P.map X = P'.map X')
    (hlawY : P.map Y = P'.map Y')
    (hF : ∀ s t, P.real {ω | X ω ≤ s ∧ Y ω ≤ t} ≤ P'.real {ω | X' ω ≤ s ∧ Y' ω ≤ t}) :
    cov[X, Y; P] / √(Var[X; P] * Var[Y; P]) ≤ cov[X', Y'; P'] / √(Var[X'; P'] * Var[Y'; P']) := by
  have hvar {Z : Ω → ℝ} {Z' : Ω' → ℝ} (hZ : AEMeasurable Z P) (hZ' : AEMeasurable Z' P')
      (h : P.map Z = P'.map Z') : Var[Z; P] = Var[Z'; P'] := by
    rw [(HasLaw.mk hZ rfl : HasLaw Z (P.map Z) P).variance_eq, h,
      (HasLaw.mk hZ' rfl : HasLaw Z' (P'.map Z') P').variance_eq]
  rw [hvar hX.aemeasurable hX'.aemeasurable hlawX, hvar hY.aemeasurable hY'.aemeasurable hlawY]
  gcongr
  exact covariance_le_covariance_of_cdf_le hX hY hX' hY' hlawX hlawY hF

end RandomVariables

/-! ### At the standard bivariate normal law -/

/-- **Hoeffding's identity at the standard bivariate normal law**: for `r ∈ [−1, 1]`,
`∫∫ (N₂(s, t; r) − Φ(s) Φ(t)) ds dt = r`. The covariance of the Cholesky pair is `r`
(`covariance_fst_snd_bivariateNormalLaw`), its joint CDF is `N₂(·, ·; r)` and its margins are
standard normal. -/
theorem integral_bivariateNormalCDF_sub_mul {r : ℝ} (hr : r ^ 2 ≤ 1) :
    ∫ p : ℝ × ℝ, (bivariateNormalCDF p.1 p.2 r - Phi p.1 * Phi p.2) = r := by
  have h := covariance_fst_snd_eq_integral (μ := bivariateNormalLaw r)
    (memLp_fst_bivariateNormalLaw r) (memLp_snd_bivariateNormalLaw r)
  rw [covariance_fst_snd_bivariateNormalLaw] at h
  refine Eq.trans ?_ h.symm
  congr 1
  funext p
  rw [bivariateNormalCDF_eq_law, Set.Iic_prod_eq,
    ← map_measureReal_apply measurable_fst measurableSet_Iic,
    ← map_measureReal_apply measurable_snd measurableSet_Iic, map_fst_bivariateNormalLaw hr,
    map_snd_bivariateNormalLaw, ← cdf_eq_real, ← cdf_eq_real, cdf_gaussianReal_zero_one]

end MathFin
