/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Gaussian.Kernel
public import LeanPool.KLS.FunctionalInequalities.Probability.BrunnMinkowski
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Construction
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.FromBorell
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Log-concavity of Gaussian-smoothed Borell densities

This module constructs the normalized Gaussian convolution law of a Borell
density. Its continuous positive density has a continuous convex logarithmic
potential and is log-concave as a probability law. The actual normalized density
and potential are smooth. Poincare upper stability and the numerical Cheeger
passage are proved in the later `GaussianSmoothing/Poincare` and
`GaussianSmoothing/Buser` modules; this module does not assert
individual-domain perimeter convergence.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

open FunctionalInequalities.Probability.Gaussian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Convolution of a law with the normalized Gaussian law. -/
def smoothedLaw (ν : Measure V) (s : ℝ) : Measure V :=
  ν.conv (Probability.Gaussian.law s)

theorem smoothedLaw_probability {ν : Measure V} [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure (smoothedLaw ν s) := by
  let _ := Probability.Gaussian.law_probability (V := V) hs
  unfold smoothedLaw
  infer_instance

/-- The normalized convolution law has its actual Haar density. -/
theorem smoothedLaw_eq_withDensity {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) (s : ℝ) :
    smoothedLaw ν s = (volume : Measure V).withDensity
      (lconvolution (fun x => ENNReal.ofReal (ρ x))
        (fun x => ENNReal.ofReal (normalizedKernel s x)) volume) := by
  unfold smoothedLaw Probability.Gaussian.law
  rw [← hρ.withDensity_eq]
  exact conv_withDensity_eq_lconvolution hρ.measurable.ennreal_ofReal
    (normalizedKernel_measurable s).ennreal_ofReal

/-- The raw Gaussian convolution of a Borell density. It is kept extended-valued
until pointwise finite mass has been separately proved. -/
def raw (ρ : V → ℝ) (s : ℝ) (x : V) : ENNReal :=
  ∫⁻ y, ENNReal.ofReal (ρ y) * ekernel s (x - y) ∂(volume : Measure V)

/-- The pointwise density of the convolution with the normalized Gaussian. -/
def normalizedRaw (ρ : V → ℝ) (s : ℝ) (x : V) : ENNReal :=
  ∫⁻ y, ENNReal.ofReal (ρ y) * normalizedEkernel s (x - y) ∂(volume : Measure V)

theorem normalizedRaw_eq_raw_div {ρ : V → ℝ} (hρ : Measurable ρ)
    {s : ℝ} (hs : 0 < s) (x : V) :
    normalizedRaw ρ s x = raw ρ s x / ENNReal.ofReal (mass (V := V) s) := by
  have hm := mass_pos (V := V) hs
  have hf : Measurable (fun y : V => ENNReal.ofReal (ρ y) * ekernel s (x - y)) :=
    hρ.ennreal_ofReal.mul
      ((ekernel_measurable s).comp (measurable_const.sub measurable_id))
  unfold normalizedRaw raw
  simp_rw [normalizedEkernel, normalizedKernel]
  simp_rw [ENNReal.ofReal_div_of_pos hm]
  simp_rw [div_eq_mul_inv, ← mul_assoc]
  simp only [ekernel] at hf ⊢
  rw [lintegral_mul_const _ hf]

/-- The normalized pointwise convolution is the density of the probability-law
convolution, rather than only a formal integral. -/
theorem smoothedLaw_eq_withDensity_normalizedRaw {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) (s : ℝ) :
    smoothedLaw ν s = (volume : Measure V).withDensity (normalizedRaw ρ s) := by
  rw [smoothedLaw_eq_withDensity hρ s]
  congr 1
  funext x
  unfold normalizedRaw lconvolution
  refine lintegral_congr fun y => ?_
  congr 1
  simp [normalizedEkernel, sub_eq_add_neg, add_comm]

theorem raw_measurable {ρ : V → ℝ} (hρ : Measurable ρ) (s : ℝ) :
    Measurable (raw ρ s) := by
  have hprod : Measurable (fun p : V × V =>
      ENNReal.ofReal (ρ p.2) * ekernel s (p.1 - p.2)) :=
    (hρ.comp measurable_snd).ennreal_ofReal.mul
      ((ekernel_measurable s).comp (measurable_fst.sub measurable_snd))
  exact hprod.lintegral_prod_right

theorem normalizedRaw_measurable {ρ : V → ℝ} (hρ : Measurable ρ)
    {s : ℝ} (hs : 0 < s) : Measurable (normalizedRaw ρ s) := by
  have hEq : normalizedRaw ρ s =
      fun x => raw ρ s x / ENNReal.ofReal (mass (V := V) s) := by
    funext x
    exact normalizedRaw_eq_raw_div hρ hs x
  rw [hEq]
  exact (raw_measurable hρ s).div_const _

/-- The raw convolution can be integrated against the original law. -/
theorem raw_eq_lintegral {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) (s : ℝ) (x : V) :
    raw ρ s x = ∫⁻ y, ekernel s (x - y) ∂ν := by
  have hm : Measurable (fun y : V => ekernel s (x - y)) :=
    (ekernel_measurable s).comp (measurable_const.sub measurable_id)
  rw [← hρ.withDensity_eq,
    lintegral_withDensity_eq_lintegral_mul (volume : Measure V)
      hρ.measurable.ennreal_ofReal hm]
  rfl

theorem normalizedRaw_eq_lintegral {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) (s : ℝ) (x : V) :
    normalizedRaw ρ s x = ∫⁻ y, normalizedEkernel s (x - y) ∂ν := by
  have hm : Measurable (fun y : V => normalizedEkernel s (x - y)) :=
    (normalizedEkernel_measurable s).comp (measurable_const.sub measurable_id)
  rw [← hρ.withDensity_eq,
    lintegral_withDensity_eq_lintegral_mul (volume : Measure V)
      hρ.measurable.ennreal_ofReal hm]
  rfl

/-- Gaussian convolution of a probability density has finite value at every point. -/
theorem raw_le_one {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 ≤ s) (x : V) :
    raw ρ s x ≤ 1 := by
  rw [raw_eq_lintegral hρ]
  calc
    (∫⁻ y, ekernel s (x - y) ∂ν) ≤ ∫⁻ _ : V, (1 : ENNReal) ∂ν :=
      lintegral_mono (fun y => ekernel_le_one hs (x - y))
    _ = 1 := by simp

/-- Gaussian convolution of a probability density is positive at every point. -/
theorem raw_pos {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) (s : ℝ) (x : V) :
    0 < raw ρ s x := by
  rw [raw_eq_lintegral hρ]
  have hm : Measurable (fun y : V => ekernel s (x - y)) :=
    (ekernel_measurable s).comp (measurable_const.sub measurable_id)
  rw [lintegral_pos_iff_support hm]
  have hsupp : Function.support (fun y : V => ekernel s (x - y)) = Set.univ := by
    ext y
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (ekernel_pos s (x - y)).ne'
  rw [hsupp]
  simp

theorem raw_lt_top {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 ≤ s) (x : V) :
    raw ρ s x < ⊤ :=
  lt_of_le_of_lt (raw_le_one hρ hs x) (by simp)

theorem normalizedRaw_pos {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) (x : V) :
    0 < normalizedRaw ρ s x := by
  rw [normalizedRaw_eq_raw_div hρ.measurable hs]
  exact ENNReal.div_pos (raw_pos hρ s x).ne'
    ENNReal.ofReal_ne_top

theorem normalizedRaw_lt_top {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) (x : V) :
    normalizedRaw ρ s x < ⊤ := by
  rw [normalizedRaw_eq_raw_div hρ.measurable hs]
  exact ENNReal.div_lt_top (raw_lt_top hρ hs.le x).ne
    (ENNReal.ofReal_pos.mpr (mass_pos hs)).ne'

/-- The finite real-valued Gaussian convolution of a probability density. -/
def density (ρ : V → ℝ) (s : ℝ) (x : V) : ℝ := (raw ρ s x).toReal

/-- Real density of the normalized convolution probability law. -/
def normalizedDensity (ρ : V → ℝ) (s : ℝ) (x : V) : ℝ :=
  (normalizedRaw ρ s x).toReal

theorem normalizedDensity_pos {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) (x : V) :
    0 < normalizedDensity ρ s x :=
  ENNReal.toReal_pos (normalizedRaw_pos hρ hs x).ne'
    (normalizedRaw_lt_top hρ hs x).ne

theorem normalizedDensity_measurable {ρ : V → ℝ} (hρ : Measurable ρ)
    {s : ℝ} (hs : 0 < s) : Measurable (normalizedDensity ρ s) :=
  (normalizedRaw_measurable hρ hs).ennreal_toReal

theorem normalizedDensity_eq_integral {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) (x : V) :
    normalizedDensity ρ s x = ∫ y, normalizedKernel s (x - y) ∂ν := by
  have hm : Measurable (fun y : V => normalizedKernel s (x - y)) :=
    (normalizedKernel_measurable s).comp (measurable_const.sub measurable_id)
  have h := integral_eq_lintegral_of_nonneg_ae
    (μ := ν) (f := fun y : V => normalizedKernel s (x - y))
    (Filter.Eventually.of_forall fun y => (normalizedKernel_pos hs (x - y)).le)
    hm.aestronglyMeasurable
  simpa only [normalizedDensity, normalizedRaw_eq_lintegral hρ s x,
    normalizedEkernel] using h.symm

theorem normalizedDensity_continuous {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : Continuous (normalizedDensity ρ s) := by
  have hk : Continuous (normalizedKernel (V := V) s) := by
    unfold normalizedKernel kernel
    fun_prop
  have hcont : Continuous (fun x : V =>
      ∫ y, normalizedKernel s (x - y) ∂ν) := by
    apply continuous_of_dominated
      (bound := fun _ : V => (mass (V := V) s)⁻¹)
    · intro x
      exact ((normalizedKernel_measurable s).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · intro x
      exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (normalizedKernel_pos hs (x - y))]
        exact normalizedKernel_le_inv_mass hs (x - y)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun y =>
        hk.comp (continuous_id.sub continuous_const)
  have heq : (fun x : V => ∫ y, normalizedKernel s (x - y) ∂ν) =
      normalizedDensity ρ s := by
    funext x
    exact (normalizedDensity_eq_integral hρ hs x).symm
  rw [heq] at hcont
  exact hcont

theorem density_measurable {ρ : V → ℝ} (hρ : Measurable ρ) (s : ℝ) :
    Measurable (density ρ s) :=
  (raw_measurable hρ s).ennreal_toReal

theorem density_pos {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 ≤ s) (x : V) :
    0 < density ρ s x :=
  ENNReal.toReal_pos (raw_pos hρ s x).ne' (raw_lt_top hρ hs x).ne

/-- Gaussian smoothing preserves log-concavity of every Borell density representative.
The law may have a nonsmooth potential or a proper convex support. -/
theorem raw_logConcave {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 ≤ s)
    (x y : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    raw ρ s x ^ t * raw ρ s y ^ (1 - t) ≤
      raw ρ s (t • x + (1 - t) • y) := by
  let p : V → ENNReal := fun z => ENNReal.ofReal (ρ z)
  have hpLC (a b : V) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
      p a ^ u * p b ^ (1 - u) ≤ p (u • a + (1 - u) • b) := by
    have hu1' : 0 ≤ 1 - u := by linarith
    dsimp [p]
    rw [ENNReal.ofReal_rpow_of_nonneg (hρ.nonneg a) hu0.le,
      ENNReal.ofReal_rpow_of_nonneg (hρ.nonneg b) hu1',
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hρ.nonneg a) u)]
    exact ENNReal.ofReal_le_ofReal (hρ.logConcave a b u hu0 hu1)
  exact Analysis.lintegral_mul_translate_logConcave hρ.measurable.ennreal_ofReal
    (ekernel_measurable s) hpLC (ekernel_logConcave hs) x y ht0 ht1

theorem normalizedRaw_logConcave {ν : Measure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s)
    (x y : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    normalizedRaw ρ s x ^ t * normalizedRaw ρ s y ^ (1 - t) ≤
      normalizedRaw ρ s (t • x + (1 - t) • y) := by
  let p : V → ENNReal := fun z => ENNReal.ofReal (ρ z)
  have hpLC (a b : V) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
      p a ^ u * p b ^ (1 - u) ≤ p (u • a + (1 - u) • b) := by
    have hu1' : 0 ≤ 1 - u := by linarith
    dsimp [p]
    rw [ENNReal.ofReal_rpow_of_nonneg (hρ.nonneg a) hu0.le,
      ENNReal.ofReal_rpow_of_nonneg (hρ.nonneg b) hu1',
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hρ.nonneg a) u)]
    exact ENNReal.ofReal_le_ofReal (hρ.logConcave a b u hu0 hu1)
  exact Analysis.lintegral_mul_translate_logConcave hρ.measurable.ennreal_ofReal
    (normalizedEkernel_measurable s) hpLC
    (normalizedEkernel_logConcave hs) x y ht0 ht1

/-- The real Gaussian convolution is strictly positive and pointwise log-concave.
The kernel remains unnormalized; this theorem makes no approximation claim. -/
theorem density_logConcave {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 ≤ s)
    (x y : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    density ρ s x ^ t * density ρ s y ^ (1 - t) ≤
      density ρ s (t • x + (1 - t) • y) := by
  unfold density
  rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (raw_lt_top hρ hs _).ne
    (raw_logConcave hρ hs x y ht0 ht1)

theorem normalizedDensity_logConcave {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) (x y : V)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    normalizedDensity ρ s x ^ t * normalizedDensity ρ s y ^ (1 - t) ≤
      normalizedDensity ρ s (t • x + (1 - t) • y) := by
  unfold normalizedDensity
  rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (normalizedRaw_lt_top hρ hs _).ne
    (normalizedRaw_logConcave hρ hs x y ht0 ht1)

/-- The real, strictly positive, log-concave function is the density of the
normalized Gaussian convolution probability law. -/
theorem smoothedLaw_eq_withDensity_normalizedDensity {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    smoothedLaw ν s = (volume : Measure V).withDensity
      (fun x => ENNReal.ofReal (normalizedDensity ρ s x)) := by
  rw [smoothedLaw_eq_withDensity_normalizedRaw hρ s]
  congr 1
  funext x
  exact (ENNReal.ofReal_toReal (normalizedRaw_lt_top hρ hs x).ne).symm

/-- The Gaussian convolution probability law has a continuous, everywhere
positive Borell density representative. This does not assert smoothness. -/
theorem normalizedDensity_isBorellDensity {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    IsBorellDensity (smoothedLaw ν s) volume (normalizedDensity ρ s) := by
  refine ⟨normalizedDensity_measurable hρ.measurable hs,
    (fun x => (normalizedDensity_pos hρ hs x).le),
    (normalizedDensity_continuous hρ hs).upperSemicontinuous,
    (fun x y t ht0 ht1 => normalizedDensity_logConcave hρ hs x y ht0 ht1), ?_⟩
  exact (smoothedLaw_eq_withDensity_normalizedDensity hρ hs).symm

/-- The normalized Gaussian convolution as a probability measure object. -/
def smoothedProbabilityLaw (ν : ProbabilityMeasure V) (s : ℝ)
    (hs : 0 < s) : ProbabilityMeasure V :=
  ⟨smoothedLaw (ν : Measure V) s, smoothedLaw_probability hs⟩

theorem smoothedProbabilityLaw_logConcave {ν : ProbabilityMeasure V}
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ)
    {s : ℝ} (hs : 0 < s) :
    LogConcave (smoothedProbabilityLaw ν s hs) :=
  IsBorellDensity.compactLogConcave (ν := smoothedProbabilityLaw ν s hs)
    (normalizedDensity_isBorellDensity hρ hs)

theorem lintegral_normalizedDensity_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x : V, ENNReal.ofReal (normalizedDensity ρ s x) = 1 := by
  have hprob := smoothedLaw_probability (ν := ν) hs
  rw [isProbabilityMeasure_iff] at hprob
  rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs,
    withDensity_apply _ MeasurableSet.univ] at hprob
  simpa only [Measure.restrict_univ] using hprob

theorem integrable_normalizedDensity {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    Integrable (normalizedDensity ρ s) (volume : Measure V) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (normalizedDensity_measurable hρ.measurable hs).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (normalizedDensity_pos hρ hs x).le)).mp
  rw [lintegral_normalizedDensity_eq_one hρ hs]
  simp

theorem integral_normalizedDensity_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ∫ x : V, normalizedDensity ρ s x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (normalizedDensity_pos hρ hs x).le)
    (normalizedDensity_measurable hρ.measurable hs).aestronglyMeasurable]
  rw [lintegral_normalizedDensity_eq_one hρ hs]
  simp

/-- Continuous convex potential for the normalized Gaussian convolution law. -/
def potential (ρ : V → ℝ) (s : ℝ) (x : V) : ℝ :=
  -Real.log (normalizedDensity ρ s x)

theorem potential_continuous {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : Continuous (potential ρ s) := by
  unfold potential
  exact ((normalizedDensity_continuous hρ hs).log
    (fun x => (normalizedDensity_pos hρ hs x).ne')).neg

theorem potential_convex {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : ConvexOn ℝ univ (potential ρ s) := by
  have hB := normalizedDensity_isBorellDensity hρ hs
  have hpos : {x : V | 0 < normalizedDensity ρ s x} = univ := by
    ext x
    simp [normalizedDensity_pos hρ hs x]
  have hconc := hB.concaveOn_log
  rw [hpos] at hconc
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := hconc.2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  dsimp [potential]
  linarith

/-- The normalized Gaussian convolution is exactly the tilted law of its
continuous convex logarithmic potential. Higher smoothness of the potential is a
separate analytic obligation. -/
theorem smoothedLaw_eq_tilted_potential {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    smoothedLaw ν s = (volume : Measure V).tilted (-(potential ρ s)) := by
  have hExp (x : V) : Real.exp (-potential ρ s x) =
      normalizedDensity ρ s x := by
    simp [potential, Real.exp_log (normalizedDensity_pos hρ hs x)]
  rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs]
  unfold Measure.tilted
  simp only [Pi.neg_apply]
  simp_rw [hExp]
  rw [integral_normalizedDensity_eq_one hρ hs]
  simp


/-! ### First-order regularity of the actual Gaussian convolution -/

section KernelDerivatives

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
private theorem kernel_hasFDerivAt (s : ℝ) (z : V) :
    HasFDerivAt (normalizedKernel (V := V) s)
      ((-2 * s * normalizedKernel s z) • innerSL ℝ z) z := by
  have h0 : HasFDerivAt (fun z : V => ‖z‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h1 : HasFDerivAt (fun z : V => -s * ‖z‖ ^ 2)
      (-s • (2 • innerSL ℝ z)) z := h0.const_mul (-s)
  have h2 := h1.exp
  have h3 := h2.const_mul ((mass (V := V) s)⁻¹)
  have hfun : normalizedKernel (V := V) s =
      (fun y => (mass (V := V) s)⁻¹ * Real.exp (-s * ‖y‖ ^ 2)) := by
    funext y
    simp [normalizedKernel, kernel, div_eq_mul_inv, mul_comm]
  rw [hfun]
  have heq : ((-2 * s * normalizedKernel s z) • innerSL ℝ z) =
      ((mass (V := V) s)⁻¹ • Real.exp (-s * ‖z‖ ^ 2) • -s • 2 • innerSL ℝ z) := by
    ext w
    simp only [smul_apply, smul_eq_mul]
    simp [normalizedKernel, kernel, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hfun] at heq
  rw [heq]
  exact h3


private theorem kernel_fderiv_norm_le (s : ℝ) (hs : 0 < s) (z : V) :
    ‖fderiv ℝ (normalizedKernel (V := V) s) z‖ ≤
      2 * s / mass (V := V) s * (Real.sqrt s)⁻¹ := by
  rw [(kernel_hasFDerivAt s z).fderiv, norm_smul, Real.norm_eq_abs,
    show -2 * s * normalizedKernel s z = -(2 * s * normalizedKernel s z) by ring,
    abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * s),
    abs_of_pos (normalizedKernel_pos hs z), innerSL_apply_norm]
  have hb := Real.abs_mulExpNegMulSq_le hs (x := ‖z‖)
  change |‖z‖ * Real.exp (-(s * ‖z‖ * ‖z‖))| ≤ (Real.sqrt s)⁻¹ at hb
  have hb' : ‖z‖ * Real.exp (-(s * ‖z‖ * ‖z‖)) ≤ (Real.sqrt s)⁻¹ :=
    (le_abs_self _).trans hb
  calc
    2 * s * normalizedKernel s z * ‖z‖ =
        (2 * s / mass (V := V) s) *
          (‖z‖ * Real.exp (-(s * ‖z‖ * ‖z‖))) := by
            simp [normalizedKernel, kernel]; ring_nf
    _ ≤ (2 * s / mass (V := V) s) * (Real.sqrt s)⁻¹ :=
      mul_le_mul_of_nonneg_left hb' (div_nonneg (by positivity) (mass_pos hs).le)

end KernelDerivatives

private def kernelDerivative (s : ℝ) (z : V) : V →L[ℝ] ℝ :=
  (-2 * s * normalizedKernel s z) • innerSL ℝ z

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem kernelDerivative_continuous (s : ℝ) :
    Continuous (kernelDerivative (V := V) s) := by
  unfold kernelDerivative normalizedKernel kernel
  fun_prop

private theorem density_hasFDerivAt {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) (x : V) :
    HasFDerivAt (normalizedDensity ρ s) (∫ y, kernelDerivative s (x - y) ∂ν) x := by
  have hInt (x : V) : Integrable (fun y : V => normalizedKernel s (x - y)) ν := by
    apply
      Integrable.mono' (integrable_const ((mass (V := V) s)⁻¹))
        ((normalizedKernel_measurable s).comp
            (measurable_const.sub measurable_id)).aestronglyMeasurable
    exact
      Filter.Eventually.of_forall fun y => by
        change ‖normalizedKernel s (x - y)‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_pos (normalizedKernel_pos hs (x - y))]
        exact normalizedKernel_le_inv_mass hs (x - y)
  have hDeriv (x y : V) :
    HasFDerivAt (fun x : V => normalizedKernel s (x - y)) (kernelDerivative s (x - y)) x := by
    have h := (kernel_hasFDerivAt s (x - y)).comp x (hasFDerivAt_sub_const y)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, kernelDerivative] using h
  have h :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x y : V =>
      normalizedKernel s (x - y)) (F' := fun x y => kernelDerivative s (x - y)) (s := Set.univ)
      (bound := fun _ : V => 2 * s / mass (V := V) s * (Real.sqrt s)⁻¹) (μ := ν) (x₀ := x)
      Filter.univ_mem
      (Filter.Eventually.of_forall fun x =>
        ((normalizedKernel_measurable s).comp
            (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (hInt x)
      ((kernelDerivative_continuous s).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y x _ => by
        simpa only [kernelDerivative, ← (kernel_hasFDerivAt s (x - y)).fderiv] using
          kernel_fderiv_norm_le s hs (x - y))
      (integrable_const _) (Filter.Eventually.of_forall fun y x _ => hDeriv x y)
  have heq : normalizedDensity ρ s = (fun x => ∫ y, normalizedKernel s (x - y) ∂ν) := by
    funext x
    exact normalizedDensity_eq_integral hρ hs x
  rw [heq]
  exact h

/-- First derivative of the actual normalized Gaussian convolution density.
The integrand is the derivative of the Gaussian kernel, and its norm is
uniformly integrable against the source probability law. -/
theorem normalizedDensity_hasFDerivAt {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) (x : V) :
    HasFDerivAt (normalizedDensity ρ s)
      (∫ y, (-2 * s * normalizedKernel s (x-y)) • innerSL ℝ (x-y) ∂ν) x := by
  simpa only [kernelDerivative] using density_hasFDerivAt hρ hs x

/-- The actual convolution density is continuously differentiable. -/
theorem normalizedDensity_contDiff_one {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ 1 (normalizedDensity ρ s) := by
  have hc : Continuous (fun x : V => ∫ y, kernelDerivative s (x-y) ∂ν) := by
    apply continuous_of_dominated
      (bound := fun _ : V => 2 * s / mass (V := V) s * (Real.sqrt s)⁻¹)
    · intro x
      exact ((kernelDerivative_continuous s).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
    · intro x
      exact Filter.Eventually.of_forall fun y => by
        simpa only [kernelDerivative, ← (kernel_hasFDerivAt s (x-y)).fderiv] using
          kernel_fderiv_norm_le s hs (x-y)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun y =>
        (kernelDerivative_continuous s).comp (continuous_id.sub continuous_const)
  apply contDiff_one_iff_fderiv.mpr
  constructor
  · intro x
    exact (density_hasFDerivAt hρ hs x).differentiableAt
  · have hf : (fderiv ℝ (normalizedDensity ρ s)) =
        (fun x : V => ∫ y, kernelDerivative s (x-y) ∂ν) := by
      funext x
      exact (density_hasFDerivAt hρ hs x).fderiv
    rw [hf]
    exact hc

/-- The logarithmic potential of the actual convolution is continuously differentiable. -/
theorem potential_contDiff_one {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 1 (potential ρ s) := by
  unfold potential
  exact
    ((normalizedDensity_contDiff_one hρ hs).log
        (fun x => (normalizedDensity_pos hρ hs x).ne')).neg


/-! ### Second-order regularity of the actual Gaussian convolution -/

section KernelDerivativeRegularity

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
private theorem kernelDerivative_fderiv_norm_le (s : ℝ) (hs : 0 < s) (z : V) :
    ‖fderiv ℝ (kernelDerivative s) z‖ ≤ 6 * s / mass (V := V) s := by
  have hc := (kernel_hasFDerivAt s z).const_mul (-2 * s)
  have hi := (innerSL ℝ : V →L[ℝ] (V →L[ℝ] ℝ)).hasFDerivAt (x := z)
  rw [show fderiv ℝ (kernelDerivative s) z = _ from (hc.smul hi).fderiv]
  have hc_bound : |-2 * s * normalizedKernel s z| ≤
      2 * s / mass (V := V) s := by
    rw [show -2 * s * normalizedKernel s z = -(2 * s * normalizedKernel s z) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (by positivity) (normalizedKernel_pos hs z).le)]
    simpa [div_eq_mul_inv, mul_assoc] using
      (mul_le_mul_of_nonneg_left (normalizedKernel_le_inv_mass hs z) (by positivity : 0 ≤ 2 * s))
  have hfirst : ‖(-2 * s * normalizedKernel s z) • (innerSL ℝ : V →L[ℝ] (V →L[ℝ] ℝ))‖ ≤
      2 * s / mass (V := V) s := by
    refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (by positivity) (mass_pos hs).le) ?_
    intro w
    change ‖(-2 * s * normalizedKernel s z) • innerSL ℝ w‖ ≤
      (2 * s / mass (V := V) s) * ‖w‖
    rw [norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
    exact mul_le_mul_of_nonneg_right hc_bound (norm_nonneg _)
  have htail : s * ‖z‖ ^ 2 * normalizedKernel s z ≤
      (mass (V := V) s)⁻¹ := by
    have ht : s * ‖z‖ ^ 2 ≤ Real.exp (s * ‖z‖ ^ 2) := by
      nlinarith [Real.add_one_le_exp (s * ‖z‖ ^ 2)]
    have hmul : (s * ‖z‖ ^ 2) * Real.exp (-(s * ‖z‖ ^ 2)) ≤ 1 := by
      rw [Real.exp_neg]
      exact (div_le_one (Real.exp_pos _)).mpr ht
    calc
      s * ‖z‖ ^ 2 * normalizedKernel s z =
          ((s * ‖z‖ ^ 2) * Real.exp (-(s * ‖z‖ ^ 2))) / mass (V := V) s := by
            simp [normalizedKernel, kernel]; ring_nf
      _ ≤ 1 / mass (V := V) s :=
        div_le_div_of_nonneg_right hmul (mass_pos hs).le
      _ = _ := one_div _
  have hsecond : ‖((-2 * s) • ((-2 * s * normalizedKernel s z) • innerSL ℝ z)).smulRight
      (innerSL ℝ z)‖ ≤ 4 * s / mass (V := V) s := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, innerSL_apply_norm,
      show -2 * s = -(2 * s) by ring, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ 2 * s),
      abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * s),
      abs_of_pos (normalizedKernel_pos hs z)]
    calc
      2 * s * (2 * s * normalizedKernel s z * ‖z‖) * ‖z‖ =
          4 * s * (s * ‖z‖ ^ 2 * normalizedKernel s z) := by ring
      _ ≤ 4 * s * (mass (V := V) s)⁻¹ :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = 4 * s / mass (V := V) s := by ring
  calc
    _ ≤ ‖(-2 * s * normalizedKernel s z) • (innerSL ℝ : V →L[ℝ] (V →L[ℝ] ℝ))‖ +
        ‖((-2 * s) • ((-2 * s * normalizedKernel s z) • innerSL ℝ z)).smulRight
          (innerSL ℝ z)‖ := by
      let A : V →L[ℝ] (V →L[ℝ] ℝ) := (-2 * s * normalizedKernel s z) • innerSL ℝ
      let B : V →L[ℝ] (V →L[ℝ] ℝ) :=
        ((-2 * s) • ((-2 * s * normalizedKernel s z) • innerSL ℝ z)).smulRight
          (innerSL ℝ z)
      change ‖A + B‖ ≤ ‖A‖ + ‖B‖
      exact norm_add_le A B
    _ ≤ (2 * s / mass (V := V) s) + (4 * s / mass (V := V) s) :=
      add_le_add hfirst hsecond
    _ = 6 * s / mass (V := V) s := by ring


private theorem kernelDerivative_contDiff (s : ℝ) :
    ContDiff ℝ 2 (kernelDerivative (V := V) s) := by
  have hn : ContDiff ℝ 2 (fun z : V => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have hnorm : ContDiff ℝ 2 (fun z : V => -s * ‖z‖ ^ 2) := by
    simpa only [smul_eq_mul] using (ContDiff.const_smul (-s) hn)
  have he : ContDiff ℝ 2 (fun z : V => Real.exp (-s * ‖z‖ ^ 2)) :=
    Real.contDiff_exp.comp hnorm
  have hk : ContDiff ℝ 2 (normalizedKernel (V := V) s) := by
    have h := he.div_const (mass (V := V) s)
    have hfun : normalizedKernel (V := V) s =
        (fun z : V => Real.exp (-s * ‖z‖ ^ 2) / mass (V := V) s) := by
      funext z
      rfl
    rw [hfun]
    exact h
  unfold kernelDerivative
  exact ((ContDiff.const_smul (-2 * s) hk).smul (innerSL ℝ).contDiff)

end KernelDerivativeRegularity

private theorem derivativeIntegral_contDiff_one {ν : Measure V} [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 1 (fun x : V => ∫ y, kernelDerivative s (x-y) ∂ν) := by
  let K : ℝ := 6 * s / mass (V := V) s
  have hkcont : Continuous (fun z : V => fderiv ℝ (kernelDerivative s) z) :=
    (kernelDerivative_contDiff s).continuous_fderiv (by norm_num)
  have hbound (z : V) : ‖kernelDerivative s z‖ ≤
      2 * s / mass (V := V) s * (Real.sqrt s)⁻¹ := by
    simpa only [kernelDerivative, ← (kernel_hasFDerivAt s z).fderiv] using
      kernel_fderiv_norm_le s hs z
  have hint (x : V) : Integrable (fun y : V => kernelDerivative s (x-y)) ν := by
    apply Integrable.mono' (integrable_const (2 * s / mass (V := V) s * (Real.sqrt s)⁻¹))
      (((kernelDerivative_continuous s).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun y => hbound (x-y)
  have hdiff (x y : V) : HasFDerivAt
      (fun x : V => kernelDerivative s (x-y))
      (fderiv ℝ (kernelDerivative s) (x-y)) x := by
    have h := ((kernelDerivative_contDiff s).differentiable (by norm_num) (x-y)).hasFDerivAt.comp
      x (hasFDerivAt_sub_const y)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using h
  have hAt (x : V) : HasFDerivAt
      (fun x : V => ∫ y, kernelDerivative s (x-y) ∂ν)
      (∫ y, fderiv ℝ (kernelDerivative s) (x-y) ∂ν) x := by
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun x y : V => kernelDerivative s (x-y))
      (F' := fun x y => fderiv ℝ (kernelDerivative s) (x-y))
      (s := Set.univ) (bound := fun _ : V => K)
      (μ := ν) (x₀ := x)
      Filter.univ_mem
      (Filter.Eventually.of_forall fun x =>
        (((kernelDerivative_continuous s).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable))
      (hint x)
      ((hkcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y x _ => kernelDerivative_fderiv_norm_le s hs (x-y))
      (integrable_const _)
      (Filter.Eventually.of_forall fun y x _ => hdiff x y)
  have hcont : Continuous (fun x : V =>
      ∫ y, fderiv ℝ (kernelDerivative s) (x-y) ∂ν) := by
    apply continuous_of_dominated (bound := fun _ : V => K)
    · intro x
      exact (hkcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · intro x
      exact Filter.Eventually.of_forall fun y => kernelDerivative_fderiv_norm_le s hs (x-y)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun y =>
        hkcont.comp (continuous_id.sub continuous_const)
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨_, hcont, hAt⟩

/-- The actual normalized Gaussian convolution density is twice continuously differentiable. -/
theorem normalizedDensity_contDiff_two {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ 2 (normalizedDensity ρ s) := by
  change ContDiff ℝ (1 + 1) (normalizedDensity ρ s)
  exact contDiff_succ_iff_hasFDerivAt.mpr
    ⟨_, derivativeIntegral_contDiff_one hs, fun x => density_hasFDerivAt hρ hs x⟩

/-- The logarithmic potential of the actual convolution is twice continuously differentiable. -/
theorem potential_contDiff_two {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ 2 (potential ρ s) := by
  unfold potential
  exact ((normalizedDensity_contDiff_two hρ hs).log
    (fun x => (normalizedDensity_pos hρ hs x).ne')).neg


/-! ### All-order regularity of the actual Gaussian convolution -/

section AllOrderRegularity

open Filter Topology
open scoped ContDiff

private theorem pow_mul_exp_neg_sq_bounded (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → r ^ n * Real.exp (-b * r ^ 2) ≤ C := by
  let F : ℝ → ℝ := fun r => |r| ^ n * Real.exp (-b * r ^ 2)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hlim : Tendsto F (cocompact ℝ) (𝓝 0) := by
    convert tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (n : ℝ) using 1
    ext r
    simp [F, Real.rpow_natCast]
  have hF1 : 0 < F 1 := by simp only [neg_mul, abs_one, one_pow, mul_one, one_mul, F]; positivity
  have hev : ∀ᶠ r in cocompact ℝ, F r ≤ F 1 := by
    filter_upwards [hlim.eventually (eventually_lt_nhds hF1)] with r hr
    exact hr.le
  obtain ⟨r₀, hr₀⟩ := hF.exists_forall_ge' 1 hev
  refine ⟨F r₀, fun r hr => ?_⟩
  simpa [F, abs_of_nonneg hr] using hr₀ r

private theorem one_add_pow_mul_exp_neg_sq_bounded (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
      (1 + r) ^ n * Real.exp (-b * r ^ 2) ≤ C := by
  obtain ⟨C0, h0⟩ := pow_mul_exp_neg_sq_bounded b hb 0
  obtain ⟨Cn, hn⟩ := pow_mul_exp_neg_sq_bounded b hb n
  refine ⟨(2 : ℝ) ^ n * (C0 + Cn), fun r hr => ?_⟩
  have hpow : (1 + r) ^ n ≤ (2 : ℝ) ^ n * (1 + r ^ n) := by
    rcases le_total r 1 with h | h
    · calc
        (1 + r) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
        _ ≤ (2 : ℝ) ^ n * (1 + r ^ n) := by
          have hh : (1 : ℝ) ≤ 1 + r ^ n := by nlinarith [pow_nonneg hr n]
          simpa using mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (2 : ℝ) ^ n)
    · calc
        (1 + r) ^ n ≤ (2 * r) ^ n := by gcongr; linarith
        _ = (2 : ℝ) ^ n * r ^ n := mul_pow _ _ _
        _ ≤ (2 : ℝ) ^ n * (1 + r ^ n) := by gcongr; simp
  have he : 0 ≤ Real.exp (-b * r ^ 2) := (Real.exp_pos _).le
  calc
    _ ≤ ((2 : ℝ) ^ n * (1 + r ^ n)) * Real.exp (-b * r ^ 2) :=
      mul_le_mul_of_nonneg_right hpow he
    _ = (2 : ℝ) ^ n * (Real.exp (-b * r ^ 2) +
      r ^ n * Real.exp (-b * r ^ 2)) := by ring
    _ ≤ (2 : ℝ) ^ n * (C0 + Cn) := by
      gcongr
      · simpa using h0 r hr
      · exact hn r hr

section StructuredSpace

variable {V : Type*}
  [NormedAddCommGroup V]

section InnerProduct

variable [InnerProductSpace ℝ V]

private theorem gaussian_deriv_poly_bound (s : ℝ) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : V,
      ‖iteratedFDeriv ℝ n (fun z : V => Real.exp (-s * ‖z‖ ^ 2)) z‖ ≤
        C * (1 + ‖z‖) ^ k * Real.exp (-s * ‖z‖ ^ 2) := by
  let f : V → ℝ := fun z => -s * ‖z‖ ^ 2
  have hf : f.HasTemperateGrowth := by
    dsimp [f]
    fun_prop
  obtain ⟨k, C, hC, hbound⟩ := hf.norm_iteratedFDeriv_le_uniform n
  refine ⟨k * n, n.factorial * (1 + C) ^ n, by positivity, fun z => ?_⟩
  have houter : ∀ i, i ≤ n →
      ‖iteratedFDeriv ℝ i Real.exp (f z)‖ ≤ Real.exp (f z) := by
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp]
    simp
  have hinner : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i f z‖ ≤ ((1 + C) * (1 + ‖z‖) ^ k) ^ i := by
    intro i hi hi'
    calc
      _ ≤ C * (1 + ‖z‖) ^ k := hbound i hi' z
      _ ≤ (1 + C) * (1 + ‖z‖) ^ k := by gcongr; simp
      _ ≤ ((1 + C) * (1 + ‖z‖) ^ k) ^ i := by
        apply le_self_pow₀ (one_le_mul_of_one_le_of_one_le (by simp [hC])
          (by simp [one_le_pow₀]))
        omega
  have h := norm_iteratedFDeriv_comp_le (N := (↑(⊤ : ℕ∞))) Real.contDiff_exp hf.1
    (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)) z houter hinner
  convert h using 1
  · rfl
  · simp only [mul_pow, pow_mul, mul_assoc]
    ring

private theorem gaussian_deriv_bound (s : ℝ) (hs : 0 < s) (n : ℕ) :
    ∃ B : ℝ, ∀ z : V,
      ‖iteratedFDeriv ℝ n (fun z : V => Real.exp (-s * ‖z‖ ^ 2)) z‖ ≤ B := by
  obtain ⟨k, C, hC, hpoly⟩ := gaussian_deriv_poly_bound (V := V) s n
  obtain ⟨B, hB⟩ := one_add_pow_mul_exp_neg_sq_bounded s hs k
  refine ⟨C * B, fun z => (hpoly z).trans ?_⟩
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left (hB ‖z‖ (norm_nonneg z)) hC)

end InnerProduct

private theorem smooth_integral_of_uniform_derivatives [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [IsProbabilityMeasure ν] (g : V → ℝ)
    (hg : ContDiff ℝ ∞ g) (hB : ∀ n : ℕ, ∃ B : ℝ, ∀ z : V, ‖iteratedFDeriv ℝ n g z‖ ≤ B) :
    ContDiff ℝ ∞ (fun x : V => ∫ y, g (x - y) ∂ν) := by
  let J (n : ℕ) (x : V) := ∫ y, iteratedFDeriv ℝ n g (x - y) ∂ν
  have hcont (n : ℕ) : Continuous (iteratedFDeriv ℝ n g) :=
    hg.continuous_iteratedFDeriv (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
  have hint (n : ℕ) (x : V) : Integrable (fun y : V => iteratedFDeriv ℝ n g (x - y)) ν := by
    obtain ⟨B, hbound⟩ := hB n
    apply
      Integrable.mono' (integrable_const B)
        ((hcont n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => hbound (x - y)
  have hJn : ∀ m : ℕ, ∀ n : ℕ, ContDiff ℝ m (J n) := by
    intro m
    induction m with
    | zero =>
      intro n
      apply contDiff_zero.mpr
      dsimp [J]
      obtain ⟨B, hbound⟩ := hB n
      apply continuous_of_dominated (bound := fun _ : V => B)
      · intro x
        exact ((hcont n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · intro x
        exact Filter.Eventually.of_forall fun y => hbound (x - y)
      · exact integrable_const _
      · exact
          Filter.Eventually.of_forall fun y =>
            (hcont n).comp (continuous_id.sub continuous_const)
    | succ m ih =>
      intro n
      let : NormedAddCommGroup (V [×(n + 1)]→L[ℝ] ℝ) :=
        ContinuousMultilinearMap.normedAddCommGroup'
      let : NormedSpace ℝ (V [×(n + 1)]→L[ℝ] ℝ) := ContinuousMultilinearMap.normedSpace'
      let : NormedAddCommGroup (V [×n]→L[ℝ] ℝ) := ContinuousMultilinearMap.normedAddCommGroup'
      let : NormedSpace ℝ (V [×n]→L[ℝ] ℝ) := ContinuousMultilinearMap.normedSpace'
      let L : (V [×(n + 1)]→L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] (V [×n]→L[ℝ] ℝ)) :=
        { toFun := ContinuousMultilinearMap.curryLeft
          map_add' := by intros; rfl
          map_smul' := by intros; rfl
          cont :=
            (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℝ).continuous }
      have hderiv_cont : ContDiff ℝ m (fun x => L (J (n + 1) x)) := by
        simpa only [Function.comp_def] using L.contDiff.comp (ih (n + 1))
      have hAt (x : V) : HasFDerivAt (J n) (L (J (n + 1) x)) x := by
        have hfcont : Continuous (fun z : V => fderiv ℝ (iteratedFDeriv ℝ n g) z) := by
          rw [fderiv_iteratedFDeriv]
          exact L.continuous.comp (hcont (n + 1))
        have hfbound (z : V) : ‖fderiv ℝ (iteratedFDeriv ℝ n g) z‖ ≤ (hB (n + 1)).choose := by
          rw [norm_fderiv_iteratedFDeriv]
          exact (hB (n + 1)).choose_spec z
        have hdiff (x y : V) :
          HasFDerivAt (fun x : V => iteratedFDeriv ℝ n g (x - y))
            (fderiv ℝ (iteratedFDeriv ℝ n g) (x - y)) x := by
          have hreg : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
            hg.differentiable_iteratedFDeriv (by exact_mod_cast (ENat.natCast_lt_top n))
          have h := (hreg (x - y)).hasFDerivAt.comp x (hasFDerivAt_sub_const y)
          simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using h
        have h :=
          hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x y : V =>
            iteratedFDeriv ℝ n g (x - y)) (F' := fun x y =>
            fderiv ℝ (iteratedFDeriv ℝ n g) (x - y)) (s := Set.univ) (bound := fun _ : V =>
            (hB (n + 1)).choose) (μ := ν) (x₀ := x) Filter.univ_mem
            (Filter.Eventually.of_forall fun x =>
              ((hcont n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
            (hint n x) ((hfcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
            (Filter.Eventually.of_forall fun y x _ => hfbound (x - y)) (integrable_const _)
            (Filter.Eventually.of_forall fun y x _ => hdiff x y)
        have heq : (∫ y, fderiv ℝ (iteratedFDeriv ℝ n g) (x - y) ∂ν) = L (J (n + 1) x) := by
          calc
            _ = ∫ y, L (iteratedFDeriv ℝ (n + 1) g (x - y)) ∂ν := by congr 1
            _ = L (J (n + 1) x) := by exact L.integral_comp_comm (hint (n + 1) x)
        rw [heq] at h
        exact h
      exact contDiff_succ_iff_hasFDerivAt.mpr ⟨_, hderiv_cont, hAt⟩
  apply contDiff_infty.mpr
  intro m
  let : NormedAddCommGroup (V [×0]→L[ℝ] ℝ) := ContinuousMultilinearMap.normedAddCommGroup'
  let : NormedSpace ℝ (V [×0]→L[ℝ] ℝ) := ContinuousMultilinearMap.normedSpace'
  let e := continuousMultilinearCurryFin0 ℝ V ℝ
  have hc : ContDiff ℝ m (fun x => e (J 0 x)) := by
    simpa only [Function.comp_def] using e.contDiff.comp (hJn m 0)
  have heq : (fun x => e (J 0 x)) = (fun x : V => ∫ y, g (x - y) ∂ν) := by
    funext x
    dsimp [J]
    change (∫ y, iteratedFDeriv ℝ 0 g (x - y) ∂ν) (0 : Fin 0 → V) = _
    rw [ContinuousMultilinearMap.integral_apply (hint 0 x)]
    simp only [iteratedFDeriv_zero_apply]
  rw [← heq]
  exact hc

end StructuredSpace


omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem kernel_contDiff_infty (s : ℝ) :
    ContDiff ℝ ∞ (kernel (V := V) s) := by
  have hn : ContDiff ℝ ∞ (fun z : V => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have hnorm : ContDiff ℝ ∞ (fun z : V => -s * ‖z‖ ^ 2) := by
    simpa only [smul_eq_mul] using (ContDiff.const_smul (-s) hn)
  exact Real.contDiff_exp.comp hnorm

/-- The actual normalized convolution density is smooth at every positive
inverse variance, with no moment or regularity assumption on the source law. -/
theorem normalizedDensity_contDiff_infty {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (normalizedDensity ρ s) := by
  have hconv : ContDiff ℝ ∞ (fun x : V => ∫ y, kernel s (x-y) ∂ν) := by
    apply smooth_integral_of_uniform_derivatives ν (kernel s) (kernel_contDiff_infty s)
    intro n
    change ∃ B : ℝ, ∀ z : V,
      ‖iteratedFDeriv ℝ n (fun z : V => Real.exp (-s * ‖z‖ ^ 2)) z‖ ≤ B
    exact gaussian_deriv_bound (V := V) s hs n
  have heq : normalizedDensity ρ s =
      (fun x => (∫ y, kernel s (x-y) ∂ν) / mass (V := V) s) := by
    funext x
    rw [normalizedDensity_eq_integral hρ hs x]
    simp only [normalizedKernel, div_eq_mul_inv, integral_mul_const]
  rw [heq]
  exact hconv.div_const _

/-- The negative logarithm of the actual normalized convolution is smooth,
including on a zero-dimensional ambient space. -/
theorem potential_contDiff_infty {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (potential ρ s) := by
  unfold potential
  exact ((normalizedDensity_contDiff_infty hρ hs).log
    (fun x => (normalizedDensity_pos hρ hs x).ne')).neg

end AllOrderRegularity

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
