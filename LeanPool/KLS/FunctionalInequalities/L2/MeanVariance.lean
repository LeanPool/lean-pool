/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Moments.Variance

/-!
# Mean and variance in real `L²`

This module packages constant functions, the mean, centering, and variance directly in real
`L²` over a `ProbabilityMeasure`. The variance is `NNReal`-valued by construction: it is the
square of the norm of the centered element. Basic identities are stated without choosing
pointwise representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.L2

variable {α : Type*} [MeasurableSpace α]

/-- The element of real `L²(μ)` represented almost everywhere by the constant `c`. -/
def const (μ : ProbabilityMeasure α) (c : ℝ) : Lp ℝ 2 (μ : Measure α) :=
  Lp.const 2 (μ : Measure α) c

/-- The `L²` constant has the expected pointwise representative almost everywhere. -/
theorem const_coeFn (μ : ProbabilityMeasure α) (c : ℝ) :
    const μ c =ᵐ[(μ : Measure α)] fun _ ↦ c := by
  change Lp.const 2 (μ : Measure α) c =ᵐ[(μ : Measure α)] Function.const α c
  exact Lp.coeFn_const 2 (μ : Measure α) c

/-- The zero constant is the zero element of `L²`. -/
@[simp]
theorem const_zero (μ : ProbabilityMeasure α) : const μ 0 = 0 :=
  map_zero (Lp.const 2 (μ : Measure α))

/-- Embedding constants into `L²` preserves addition. -/
@[simp]
theorem const_add (μ : ProbabilityMeasure α) (c d : ℝ) :
    const μ (c + d) = const μ c + const μ d :=
  map_add (Lp.const 2 (μ : Measure α)) c d

/-- Embedding constants into real `L²` preserves scalar multiplication. -/
@[simp]
theorem const_smul (μ : ProbabilityMeasure α) (c d : ℝ) :
    const μ (c * d) = c • const μ d := by
  exact (Lp.constₗ 2 (μ : Measure α) ℝ).map_smul c d

/-- The mean of `f ∈ L²(μ)` is its real inner product with the constant one. -/
def mean (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) : ℝ :=
  inner ℝ f (const μ 1)

/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]

/-- Probability normalization makes the mean of a constant equal to that constant. -/
@[simp]
theorem mean_const (μ : ProbabilityMeasure α) (c : ℝ) : mean μ (const μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, const μ c x ∂(μ : Measure α)) = ∫ _ : α, c ∂(μ : Measure α) :=
      integral_congr_ae (const_coeFn μ c)
    _ = c := by simp

/-- The mean of zero is zero. -/
@[simp]
theorem mean_zero (μ : ProbabilityMeasure α) : mean μ 0 = 0 := by
  simp [mean]

/-- The mean preserves addition. -/
@[simp]
theorem mean_add (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f + g) = mean μ f + mean μ g := by
  rw [mean, inner_add_left]
  rfl

/-- The mean preserves real scalar multiplication. -/
@[simp]
theorem mean_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (c • f) = c * mean μ f := by
  rw [mean, inner_smul_left]
  rfl

/-- The mean preserves negation. -/
@[simp]
theorem mean_neg (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (-f) = -mean μ f := by
  simp [mean]

/-- The mean preserves subtraction. -/
@[simp]
theorem mean_sub (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f - g) = mean μ f - mean μ g := by
  rw [mean, inner_sub_left]
  rfl

/-- Centering subtracts the constant `L²` element whose value is the mean. -/
def center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    Lp ℝ 2 (μ : Measure α) :=
  f - const μ (mean μ f)

/-- The centered representative is pointwise `f - mean μ f` almost everywhere. -/
theorem center_coeFn (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ f =ᵐ[(μ : Measure α)] fun x ↦ f x - mean μ f := by
  exact (Lp.coeFn_sub f (const μ (mean μ f))).trans
    (ae_eq_rfl.sub (const_coeFn μ (mean μ f)))

/-- Centering the zero element gives zero. -/
@[simp]
theorem center_zero (μ : ProbabilityMeasure α) : center μ 0 = 0 := by
  simp [center]

/-- Every constant `L²` element centers to zero. -/
@[simp]
theorem center_const (μ : ProbabilityMeasure α) (c : ℝ) : center μ (const μ c) = 0 := by
  simp [center]

/-- Centering preserves addition. -/
@[simp]
theorem center_add (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    center μ (f + g) = center μ f + center μ g := by
  simp only [center, mean_add, const_add]
  abel

/-- Centering commutes with real scalar multiplication. -/
@[simp]
theorem center_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ (c • f) = c • center μ f := by
  simp only [center, mean_smul, const_smul, smul_sub]

/-- Adding a constant `L²` element does not change the centered part. -/
theorem center_add_const (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) (c : ℝ) :
    center μ (f + const μ c) = center μ f := by
  rw [center_add, center_const, add_zero]

/-- Adding a constant on the left does not change the centered part. -/
theorem center_const_add (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ (const μ c + f) = center μ f := by
  rw [center_add, center_const, zero_add]

/-- A centered `L²` element has mean zero. -/
@[simp]
theorem mean_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (center μ f) = 0 := by
  simp [center]

/-- Centering is idempotent. -/
@[simp]
theorem center_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ (center μ f) = center μ f := by
  simp [center]

/-- The variance of `f ∈ L²(μ)` is the squared `L²` norm of its centered part. -/
def variance (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) : NNReal :=
  ‖center μ f‖₊ ^ 2

/-- The mean is continuous in the real `L²` topology. -/
theorem continuous_mean (μ : ProbabilityMeasure α) : Continuous (mean μ) :=
  continuous_id.inner continuous_const

/-- Subtracting the mean is continuous in the real `L²` topology. -/
theorem continuous_center (μ : ProbabilityMeasure α) : Continuous (center μ) := by
  apply (continuous_id.sub ((continuous_mean μ).smul continuous_const) :
    Continuous (fun f : Lp ℝ 2 (μ : Measure α) ↦ f - mean μ f • const μ 1)).congr
  intro f
  simp only [center, ← const_smul, mul_one]
  rfl

/-- Variance is continuous in `L²`, including at constant functions. -/
theorem continuous_variance (μ : ProbabilityMeasure α) : Continuous (variance μ) :=
  (continuous_center μ).nnnorm.pow 2

/-- Coercing the `NNReal` variance to `ℝ` gives the squared norm of the centered part. -/
@[simp, norm_cast]
theorem coe_variance (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ‖center μ f‖ ^ 2 := by
  rfl

/-- Centering both arguments subtracts the product of their means from their inner product. -/
theorem inner_center_center (μ : ProbabilityMeasure α)
    (f g : Lp ℝ 2 (μ : Measure α)) :
    inner ℝ (center μ f) (center μ g) =
      inner ℝ f g - mean μ f * mean μ g := by
  have hf : const μ (mean μ f) = mean μ f • const μ 1 := by
    simpa using const_smul μ (mean μ f) 1
  have hg : const μ (mean μ g) = mean μ g • const μ 1 := by
    simpa using const_smul μ (mean μ g) 1
  rw [center, center, hf, hg]
  simp only [inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  have hfmean : inner ℝ f (const μ 1) = mean μ f := rfl
  have hgmean : inner ℝ (const μ 1) g = mean μ g := by rw [real_inner_comm]; rfl
  have hunit : inner ℝ (const μ 1) (const μ 1) = 1 := mean_const μ 1
  rw [hfmean, hgmean, hunit]
  ring

/-- Variance is nonnegative after coercion to the reals. -/
theorem variance_nonneg (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    0 ≤ (variance μ f : ℝ) :=
  NNReal.zero_le_coe

/-- The zero element has zero variance. -/
@[simp]
theorem variance_zero (μ : ProbabilityMeasure α) : variance μ 0 = 0 := by
  simp [variance]

/-- Every constant `L²` element has zero variance. -/
@[simp]
theorem variance_const (μ : ProbabilityMeasure α) (c : ℝ) : variance μ (const μ c) = 0 := by
  simp [variance]

/-- Adding a constant `L²` element does not change variance. -/
@[simp]
theorem variance_add_const (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) (c : ℝ) :
    variance μ (f + const μ c) = variance μ f := by
  simp [variance]

/-- Adding a constant on the left does not change variance. -/
@[simp]
theorem variance_const_add (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    variance μ (const μ c + f) = variance μ f := by
  simp [variance]

/-- Centering does not change variance. -/
@[simp]
theorem variance_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    variance μ (center μ f) = variance μ f := by
  simp [variance]

/-- Variance vanishes exactly when the element equals its mean as a constant `L²` element. -/
theorem variance_eq_zero_iff (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    variance μ f = 0 ↔ f = const μ (mean μ f) := by
  simp [variance, center, sub_eq_zero]

/-- Scaling an `L²` element scales its variance by the squared nonnegative norm of the scalar. -/
theorem variance_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    variance μ (c • f) = ‖c‖₊ ^ 2 * variance μ f := by
  rw [variance, center_smul, nnnorm_smul, mul_pow]
  rfl

/-- Every L2 element on a subsingleton probability space is a constant element. -/
theorem exists_eq_const_of_subsingleton [Subsingleton α] (μ : ProbabilityMeasure α)
    (f : Lp ℝ 2 (μ : Measure α)) : ∃ c : ℝ, f = const μ c := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure (μ : Measure α)
  refine ⟨f x₀, ?_⟩
  apply Lp.ext
  filter_upwards [const_coeFn μ (f x₀)] with x hx
  rw [hx]
  exact congrArg f (Subsingleton.elim x x₀)

/-- On a subsingleton carrier every `L²` element is a constant element, hence has zero variance.
The probability law forces the carrier to be nonempty. -/
theorem variance_eq_zero_of_subsingleton [Subsingleton α] (μ : ProbabilityMeasure α)
    (f : Lp ℝ 2 (μ : Measure α)) : variance μ f = 0 := by
  obtain ⟨c, rfl⟩ := exists_eq_const_of_subsingleton μ f
  exact variance_const μ c
/-- The intrinsic `L²` variance agrees, after coercion, with Mathlib's variance of the
representative supplied by the `Lp` element. -/
theorem coe_variance_eq_pointwise (μ : ProbabilityMeasure α)
    (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ProbabilityTheory.variance f (μ : Measure α) := by
  rw [coe_variance, ← real_inner_self_eq_norm_sq (center μ f),
    MeasureTheory.L2.inner_def,
    ProbabilityTheory.variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable]
  apply integral_congr_ae
  filter_upwards [center_coeFn μ f] with x hx
  rw [hx, mean_eq_integral]
  simp [Real.norm_eq_abs]

/-- Taking the mean commutes with embedding a pointwise square-integrable function into `L²`. -/
theorem mean_toLp (μ : ProbabilityMeasure α) {f : α → ℝ}
    (hf : MemLp f 2 (μ : Measure α)) :
    mean μ (hf.toLp f) = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean_eq_integral]
  exact integral_congr_ae hf.coeFn_toLp

/-- The `NNReal` variance of a pointwise square-integrable function is Mathlib's real variance
converted to `NNReal`; no information is lost because pointwise variance is nonnegative. -/
theorem variance_toLp (μ : ProbabilityMeasure α) {f : α → ℝ}
    (hf : MemLp f 2 (μ : Measure α)) :
    variance μ (hf.toLp f) =
      (ProbabilityTheory.variance f (μ : Measure α)).toNNReal := by
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg f (μ : Measure α))]
  exact (coe_variance_eq_pointwise μ (hf.toLp f)).trans
    (ProbabilityTheory.variance_congr hf.coeFn_toLp)

/-- The centered indicator has squared L2 norm `μ(s) (1-μ(s))`, including null and full sets. -/
theorem norm_center_indicatorConstLp_sq (μ : ProbabilityMeasure α)
    {s : Set α} (hs : MeasurableSet s) :
    ‖center μ (indicatorConstLp 2 hs (measure_ne_top (μ : Measure α) s) (1 : ℝ))‖ ^ 2 =
      (μ : Measure α).real s * (1 - (μ : Measure α).real s) := by
  let χ := indicatorConstLp 2 hs (measure_ne_top (μ : Measure α) s) (1 : ℝ)
  let p := (μ : Measure α).real s
  have hp : mean μ χ = p := by
    rw [mean, MeasureTheory.L2.inner_indicatorConstLp_one]
    calc
      (∫ x in s, const μ 1 x ∂(μ : Measure α)) =
          ∫ _ in s, (1 : ℝ) ∂(μ : Measure α) :=
        integral_congr_ae (ae_restrict_of_ae (const_coeFn μ 1))
      _ = p := by simp [p]
  have hχ : ‖χ‖ ^ 2 = p := by
    rw [← real_inner_self_eq_norm_sq,
      MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
    simp [p]
  have hone : ‖const μ 1‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact mean_const μ 1
  have hconst : const μ p = p • const μ 1 := by
    simpa using const_smul μ p 1
  have hcp : ‖const μ p‖ ^ 2 = p ^ 2 := by
    rw [hconst, norm_smul, Real.norm_eq_abs, mul_pow, hone]
    simp
  have hinner : inner ℝ χ (const μ p) = p ^ 2 := by
    rw [hconst, real_inner_smul_right]
    change p * mean μ χ = p ^ 2
    rw [hp]
    ring
  change ‖χ - const μ (mean μ χ)‖ ^ 2 = p * (1 - p)
  rw [hp, norm_sub_sq_real, hχ, hinner, hcp]
  ring

end FunctionalInequalities.L2

namespace FunctionalInequalities.L2

section NormSquare

variable {V : Type*} [MeasurableSpace V]

/-- The `L²` norm squared of a square-integrable function is the integral of its squared norm. -/
theorem norm_toLp_sq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {μ : Measure V} {u : V → W} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

end NormSquare

end FunctionalInequalities.L2

/-! ### Variance continuity of finite linear combinations

For finitely many real `L²` random variables, the variance of `Σᵢ cₖᵢ fᵢ` converges when the
coefficients converge (stated in namespace `Probability`). -/

section
open MeasureTheory Filter
open scoped Topology

namespace FunctionalInequalities.Probability

theorem tendsto_variance_finite_linear_combination {alpha I : Type*} [MeasurableSpace alpha]
    [Fintype I] (mu : ProbabilityMeasure alpha) (f : I → alpha → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (mu : Measure alpha)) (c : ℕ → I → ℝ) (b : I → ℝ)
    (hc : ∀ i, Tendsto (fun k => c k i) atTop (𝓝 (b i))) :
    Tendsto
      (fun k => ProbabilityTheory.variance (fun x => ∑ i, c k i * f i x) (mu : Measure alpha))
      atTop (𝓝 (ProbabilityTheory.variance (fun x => ∑ i, b i * f i x) (mu : Measure alpha))) := by
  classical
  let F (a : I → ℝ) : Lp ℝ 2 (mu : Measure alpha) := ∑ i, a i • (hf i).toLp (f i)
  have hrep (a : I → ℝ) :
    (F a : alpha → ℝ) =ᵐ[(mu : Measure alpha)] fun x => ∑ i, a i * f i x := by
    have hi (i : I) :
      (a i • (hf i).toLp (f i) : Lp ℝ 2 (mu : Measure alpha)) =ᵐ[(mu : Measure alpha)] fun x =>
        a i * f i x := by
      filter_upwards [Lp.coeFn_smul (a i) ((hf i).toLp (f i)), (hf i).coeFn_toLp] with x h1 h2
      simpa only [Pi.smul_apply, smul_eq_mul, h2] using h1
    apply (Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • (hf i).toLp (f i))).trans
    filter_upwards [ae_all_iff.mpr hi] with x hx
    exact Finset.sum_congr rfl fun i _ => hx i
  have hF : Tendsto (fun k => F (c k)) atTop (𝓝 (F b)) := by
    apply tendsto_finsetSum
    intro i _
    exact (hc i).smul tendsto_const_nhds
  have hv (a : I → ℝ) :
    (FunctionalInequalities.L2.variance mu (F a) : ℝ) =
      ProbabilityTheory.variance (fun x => ∑ i, a i * f i x) (mu : Measure alpha) :=
    (FunctionalInequalities.L2.coe_variance_eq_pointwise mu (F a)).trans
      (ProbabilityTheory.variance_congr (hrep a))
  have h :=
    (NNReal.continuous_coe.comp
          (FunctionalInequalities.L2.continuous_variance mu)).continuousAt.tendsto.comp
      hF
  change
    Tendsto (fun k => (FunctionalInequalities.L2.variance mu (F (c k)) : ℝ)) atTop
      (𝓝 (FunctionalInequalities.L2.variance mu (F b) : ℝ)) at h
  simpa only [hv] using h

end FunctionalInequalities.Probability

end
