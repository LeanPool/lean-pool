/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.RiskClosedForms
public import LeanPool.MathFin.Risk.GaussianValueAtRisk
public import LeanPool.MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Value-at-risk is not subadditive

Subadditivity, `ρ(X + Y) ≤ ρ(X) + ρ(Y)`, is the coherence axiom that expresses diversification:
merging two positions should not create risk. Value-at-risk fails it. This file proves three
situations from McNeil–Frey–Embrechts, *Quantitative Risk Management* (2015), Section 2.3.5, and
the QRM Exercise Book, in which VaR is **superadditive**, `VaR_α(X + Y) > VaR_α(X) + VaR_α(Y)`,
and one law family in which it is subadditive at the levels used in practice, for every correlation.

* **Independent defaults** (Exercises 2.20 and 2.27). For `d` independent `{0, 1}`-valued losses
  that each occur with probability `p`, VaR is superadditive exactly when
  `(1 − p)^d < α ≤ 1 − p` (`valueAtRisk_sum_bernoulli_superadditive_iff`). At such a level every
  single loan is riskless at the `α`-quantile while the portfolio is not. For two loans the
  portfolio VaR is exactly `1` against a sum of `0` (`valueAtRisk_sum_bernoulli_of_card_two`).
* **Infinite-mean Pareto losses** (Exercise 2.28). For independent losses with
  `F(x) = 1 − x^{−1/2}` on `[1, ∞)` (Mathlib's `paretoMeasure 1 (1/2)`), the law of the sum has
  CDF `1 − 2√(x − 1)/x` for `x ≥ 2` (`cdf_conv_paretoMeasure_half`), and VaR is superadditive at
  **every** level (`valueAtRisk_add_gt_of_paretoHalf`). With a tail this heavy diversification
  increases risk at every confidence level.
* **Jointly Gaussian losses** (Exercise 2.22). For a Gaussian pair with correlation below one,
  VaR is subadditive exactly when `α ≥ 1/2` (`valueAtRisk_add_le_iff_of_hasGaussianLaw`): on a
  Gaussian pair it holds at the levels used in practice, whatever the correlation
  (`valueAtRisk_add_le_of_hasGaussianLaw`, from the subadditivity of the standard deviation,
  `sqrt_variance_add_le`), and fails below the median when the correlation is below one.

Expected shortfall is subadditive for every pair of integrable losses
(`Risk/ExpectedShortfall.lean`); the contrast is the reason the Basel III market-risk
framework replaced VaR by ES.

## Main results

* `valueAtRisk_of_bernoulli`: `VaR_α` of a `{0, 1}` loss is `0` or `1` according to
  `α ≤ 1 − p`.
* `valueAtRisk_sum_bernoulli_superadditive_iff`: the exact superadditivity region for `d`
  independent Bernoulli losses.
* `valueAtRisk_sum_bernoulli_of_card_two`: two loans, for `(1 − p)² < α ≤ 1 − p`: portfolio VaR
  `1`, single-loan VaR `0`.
* `cdf_conv`: the CDF of a convolution is `∫ F_ν(x − a) dμ(a)`.
* `cdf_conv_paretoMeasure_half`: the sum of two independent `Pareto(1, 1/2)` losses has CDF
  `1 − 2√(x − 1)/x` on `[2, ∞)`.
* `valueAtRisk_add_gt_of_paretoHalf`: VaR is superadditive at every level for them.
* `valueAtRisk_add_le_of_hasGaussianLaw`: for a jointly Gaussian pair, VaR is subadditive at every
  level `α ≥ 1/2`, for every correlation.
* `valueAtRisk_add_le_iff_of_hasGaussianLaw`: for a Gaussian pair with correlation `< 1`,
  subadditivity holds iff `α ≥ 1/2`.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Ch 2.3; Example 2.25
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 2.20, 2.27; Ex. 2.22; Ex. 2.28

## Tags

VaR not subadditive, superadditivity, diversification paradox, independent defaults,
infinite-mean Pareto, Gaussian VaR subadditivity, Basel III, MSC 91G70, MSC 60E15, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {α : ℝ}

/-! ### Independent Bernoulli losses -/

section Bernoulli

variable [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ} {p : ℝ}

/-- A `{0, 1}`-valued loss that occurs with probability `p` is absent with probability `1 − p`. -/
lemma measureReal_eq_zero_of_bernoulli {Z : Ω → ℝ} (hZ : Measurable Z)
    (h01 : ∀ ω, Z ω = 0 ∨ Z ω = 1) (hp : P.real {ω | Z ω = 1} = p) :
    P.real {ω | Z ω = 0} = 1 - p := by
  have hs : MeasurableSet {ω | Z ω = 1} := hZ (measurableSet_singleton 1)
  rw [← hp, ← probReal_compl_eq_one_sub hs]
  congr 1
  ext ω
  rcases h01 ω with h | h <;> simp [h]

/-- **VaR of a Bernoulli loss**: a `{0, 1}`-valued loss that occurs with probability `p` has
`VaR_α = 0` when `α ≤ 1 − p` and `VaR_α = 1` otherwise. -/
theorem valueAtRisk_of_bernoulli {Z : Ω → ℝ} (hZ : Measurable Z) (h01 : ∀ ω, Z ω = 0 ∨ Z ω = 1)
    (hp : P.real {ω | Z ω = 1} = p) (hα : α ∈ Ioo 0 1) :
    valueAtRisk Z P α = if α ≤ 1 - p then 0 else 1 := by
  have hzero := measureReal_eq_zero_of_bernoulli hZ h01 hp
  have hneg (x : ℝ) (hx : x < 0) : P.real {ω | Z ω ≤ x} = 0 := by
    rw [show {ω | Z ω ≤ x} = ∅ from eq_empty_of_forall_notMem fun ω hω ↦ by
      rcases h01 ω with h | h <;> simp only [mem_ofPred_eq, h] at hω <;> linarith]
    simp
  have hsub (x : ℝ) (hx : x < 1) : {ω | Z ω ≤ x} ⊆ {ω | Z ω = 0} := fun ω hω ↦
    (h01 ω).resolve_right fun h ↦ by simp only [mem_ofPred_eq, h] at hω; linarith
  split_ifs with h
  · refine (valueAtRisk_eq_iff hZ.aemeasurable hα).2 ⟨?_, fun x hx ↦ by rw [hneg x hx]; exact hα.1⟩
    rwa [show {ω | Z ω ≤ 0} = {ω | Z ω = 0} from
      (hsub 0 zero_lt_one).antisymm fun ω hω ↦ hω.le, hzero]
  · refine (valueAtRisk_eq_iff hZ.aemeasurable hα).2 ⟨?_, fun x hx ↦ ?_⟩
    · rw [show {ω | Z ω ≤ 1} = univ from eq_univ_of_forall fun ω ↦ by
        rcases h01 ω with h | h <;> simp [h], probReal_univ]
      exact hα.2.le
    · calc P.real {ω | Z ω ≤ x} ≤ P.real {ω | Z ω = 0} := measureReal_mono (hsub x hx)
        _ = 1 - p := hzero
        _ < α := not_le.1 h

/-- Below level `1` the portfolio loss vanishes exactly when no loss occurs. -/
lemma setOf_sum_le_eq_iInter (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    {ω | ∑ i, Y i ω ≤ x} = ⋂ i, {ω | Y i ω = 0} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter]
  refine ⟨fun h i ↦ (h01 i ω).resolve_right fun hi ↦ ?_, fun h ↦ by simp [h, hx0]⟩
  have : Y i ω ≤ ∑ j, Y j ω :=
    Finset.single_le_sum (f := fun j ↦ Y j ω)
      (fun j _ ↦ by rcases h01 j ω with h | h <;> simp [h]) (Finset.mem_univ i)
  linarith

/-- With independent losses, no default occurs with probability `(1 − p)^d`. -/
lemma measureReal_iInter_setOf_eq_zero_eq_pow (hmeas : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (hp : ∀ i, P.real {ω | Y i ω = 1} = p)
    (hind : iIndepFun Y P) :
    P.real (⋂ i, {ω | Y i ω = 0}) = (1 - p) ^ Fintype.card ι := by
  rw [measureReal_def, hind.meas_iInter (s := fun i ↦ {ω | Y i ω = 0})
      fun i ↦ ⟨{0}, measurableSet_singleton 0, rfl⟩, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, measureReal_eq_zero_of_bernoulli (hmeas _) (h01 _) (hp _),
    Finset.prod_const, Finset.card_univ]

/-- If defaults are rarer than `1 − α` jointly, the portfolio VaR is at least one default. -/
private lemma one_le_valueAtRisk_sum (hmeas : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (hp : ∀ i, P.real {ω | Y i ω = 1} = p)
    (hind : iIndepFun Y P) (hα : α ∈ Ioo 0 1) (h : (1 - p) ^ Fintype.card ι < α) :
    1 ≤ valueAtRisk (fun ω ↦ ∑ i, Y i ω) P α := by
  have hS : AEMeasurable (fun ω ↦ ∑ i, Y i ω) P :=
    (Finset.measurable_sum _ fun i _ ↦ hmeas i).aemeasurable
  have hnn (ω : Ω) : 0 ≤ ∑ i, Y i ω :=
    Finset.sum_nonneg fun i _ ↦ by rcases h01 i ω with h | h <;> simp [h]
  refine le_of_forall_lt fun x hx ↦ (lt_valueAtRisk_iff hS hα).2 ?_
  rcases lt_or_ge x 0 with hx0 | hx0
  · rw [show {ω | ∑ i, Y i ω ≤ x} = ∅ from eq_empty_of_forall_notMem fun ω hω ↦
      (hx0.trans_le (hnn ω)).not_ge hω, measureReal_empty]
    exact hα.1
  · rwa [setOf_sum_le_eq_iInter h01 hx0 hx,
      measureReal_iInter_setOf_eq_zero_eq_pow hmeas h01 hp hind]

/-- **VaR is superadditive for independent defaults exactly on `((1 − p)^d, 1 − p]`**
(QRM Exercise Book, Exercises 2.20 and 2.27). For `d` independent `{0, 1}`-valued losses that
each occur with probability `p`,
`VaR_α(Y₁ + ⋯ + Y_d) > VaR_α(Y₁) + ⋯ + VaR_α(Y_d) ↔ (1 − p)^d < α ≤ 1 − p`. -/
theorem valueAtRisk_sum_bernoulli_superadditive_iff (hmeas : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (hp : ∀ i, P.real {ω | Y i ω = 1} = p)
    (hind : iIndepFun Y P) (hα : α ∈ Ioo 0 1) :
    ∑ i, valueAtRisk (Y i) P α < valueAtRisk (fun ω ↦ ∑ i, Y i ω) P α ↔
      (1 - p) ^ Fintype.card ι < α ∧ α ≤ 1 - p := by
  have hS : AEMeasurable (fun ω ↦ ∑ i, Y i ω) P :=
    (Finset.measurable_sum _ fun i _ ↦ hmeas i).aemeasurable
  simp_rw [valueAtRisk_of_bernoulli (hmeas _) (h01 _) (hp _) hα]
  by_cases h1p : α ≤ 1 - p
  · simp only [h1p, ↓reduceIte, Finset.sum_const_zero, and_true]
    refine ⟨fun hlt ↦ lt_of_not_ge fun hle ↦ hlt.not_ge ?_, fun h ↦
      zero_lt_one.trans_le (one_le_valueAtRisk_sum hmeas h01 hp hind hα h)⟩
    -- at `α ≤ (1 − p)^d` the portfolio VaR is `0`
    refine (valueAtRisk_le_iff hS hα).2 ?_
    rw [setOf_sum_le_eq_iInter h01 le_rfl zero_lt_one,
      measureReal_iInter_setOf_eq_zero_eq_pow hmeas h01 hp hind]
    exact hle
  · simp only [h1p, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      and_false, iff_false, not_lt]
    -- the portfolio loss never exceeds `d`
    refine (valueAtRisk_le_iff hS hα).2 ?_
    rw [show {ω | ∑ i, Y i ω ≤ Fintype.card ι} = univ from eq_univ_of_forall fun ω ↦
      (Finset.sum_le_sum fun i _ ↦ show Y i ω ≤ 1 by rcases h01 i ω with h | h <;> simp [h]).trans
        (by simp), probReal_univ]
    exact hα.2.le

/-- **Two defaultable loans** (QRM Exercise Book, Exercise 2.20): for two independent
`{0, 1}`-valued losses with default probability `p` and a level `(1 − p)² < α ≤ 1 − p`, each loan
has `VaR_α = 0` while the portfolio has `VaR_α = 1`. -/
theorem valueAtRisk_sum_bernoulli_of_card_two (hcard : Fintype.card ι = 2)
    (hmeas : ∀ i, Measurable (Y i)) (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hp : ∀ i, P.real {ω | Y i ω = 1} = p) (hind : iIndepFun Y P) (hα : α ∈ Ioo 0 1)
    (hlo : (1 - p) ^ 2 < α) (hhi : α ≤ 1 - p) :
    valueAtRisk (fun ω ↦ ∑ i, Y i ω) P α = 1 ∧ ∀ i, valueAtRisk (Y i) P α = 0 := by
  have hS : AEMeasurable (fun ω ↦ ∑ i, Y i ω) P :=
    (Finset.measurable_sum _ fun i _ ↦ hmeas i).aemeasurable
  refine ⟨le_antisymm ((valueAtRisk_le_iff hS hα).2 ?_)
      (one_le_valueAtRisk_sum hmeas h01 hp hind hα (by rwa [hcard])),
    fun i ↦ by rw [valueAtRisk_of_bernoulli (hmeas i) (h01 i) (hp i) hα, ite_eq_left hhi]⟩
  -- the portfolio loss exceeds `1` only if both loans default, with probability `p²`
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hp01 : 0 ≤ p ∧ p ≤ 1 := by
    rw [← hp i₀]
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have hsub : (⋂ i, {ω | Y i ω = 1})ᶜ ⊆ {ω | ∑ i, Y i ω ≤ 1} := by
    classical
    intro ω hω
    obtain ⟨j, hj⟩ : ∃ j, Y j ω ≠ 1 := by simpa using hω
    have hj0 : Y j ω = 0 := (h01 j ω).resolve_right hj
    have hle : ∑ i ∈ Finset.univ.erase j, Y i ω ≤ ∑ _i ∈ Finset.univ.erase j, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ by rcases h01 i ω with h | h <;> simp [h]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      hcard] at hle
    rw [mem_ofPred_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hj0, zero_add]
    simpa using hle
  have hall : P.real (⋂ i, {ω | Y i ω = 1}) = p ^ 2 := by
    rw [measureReal_def, hind.meas_iInter (s := fun i ↦ {ω | Y i ω = 1})
        fun i ↦ ⟨{1}, measurableSet_singleton 1, rfl⟩, ENNReal.toReal_prod]
    simp_rw [← measureReal_def, hp, Finset.prod_const, Finset.card_univ, hcard]
  calc α ≤ 1 - p := hhi
    _ ≤ 1 - p ^ 2 := by nlinarith [hp01.1, hp01.2]
    _ = P.real (⋂ i, {ω | Y i ω = 1})ᶜ := by
        have hm : MeasurableSet (⋂ i, {ω | Y i ω = 1}) :=
          MeasurableSet.iInter fun i ↦ hmeas i (measurableSet_singleton 1)
        rw [probReal_compl_eq_one_sub hm, hall]
    _ ≤ P.real {ω | ∑ i, Y i ω ≤ 1} := measureReal_mono hsub

end Bernoulli

/-! ### Infinite-mean Pareto losses -/

section Pareto

/-- **The CDF of a convolution**: `F_{μ ∗ ν}(x) = ∫ F_ν(x − a) dμ(a)`. -/
theorem cdf_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x : ℝ) :
    cdf (μ ∗ ν) x = ∫ a, cdf ν (x - a) ∂μ := by
  have hmeas : Measurable fun a ↦ cdf ν (x - a) :=
    (monotone_cdf ν).measurable.comp (measurable_const.sub measurable_id)
  have hint : Integrable (fun a ↦ cdf ν (x - a)) μ :=
    (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
      (ae_of_all _ fun a ↦ by rw [Real.norm_of_nonneg (cdf_nonneg ν _)]; exact cdf_le_one ν _)
  have hin (a : ℝ) :
      ∫⁻ b, (Iic x).indicator 1 (a + b) ∂ν = ENNReal.ofReal (cdf ν (x - a)) := by
    rw [ofReal_cdf, ← lintegral_indicator_one measurableSet_Iic]
    congr 1
    ext b
    simp only [indicator_apply, mem_Iic, le_sub_iff_add_le', Pi.one_apply]
  rw [cdf_eq_real, measureReal_def, ← lintegral_indicator_one measurableSet_Iic,
    Measure.lintegral_conv (measurable_one.indicator measurableSet_Iic)]
  simp_rw [hin]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ cdf_nonneg ν _),
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ cdf_nonneg ν _)]

/-- Integrals against the Pareto law are integrals against its density. -/
lemma integral_paretoMeasure {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (f : ℝ → ℝ) :
    ∫ a, f a ∂paretoMeasure t r = ∫ a, paretoPDFReal t r a * f a := by
  have hm : Measurable (paretoPDF t r) := (measurable_paretoPDFReal t r).ennreal_ofReal
  rw [paretoMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  congr 1
  ext a
  rw [paretoPDF, ENNReal.toReal_ofReal (paretoPDFReal_nonneg ht hr a), smul_eq_mul]

/-- The antiderivative of the convolution integrand of `cdf_conv_paretoMeasure_half`. -/
lemma hasDerivAt_convAntideriv {x a : ℝ} (ha : 0 < a) (hxa : 0 < x - a) :
    HasDerivAt (fun a ↦ -(√a)⁻¹ + √(x - a) / (x * √a))
      ((1 - (√(x - a))⁻¹) / (2 * a * √a)) a := by
  have hu : 0 < √a := sqrt_pos.2 ha
  have hw : 0 < √(x - a) := sqrt_pos.2 hxa
  have hx : 0 < x := by linarith
  have hA : HasDerivAt (fun a ↦ √a) (1 / (2 * √a)) a := hasDerivAt_sqrt ha.ne'
  have hB : HasDerivAt (fun a ↦ √(x - a)) (-1 / (2 * √(x - a))) a :=
    ((hasDerivAt_id' a).const_sub x).sqrt hxa.ne'
  have hD := (hA.inv hu.ne').neg.add (hB.div (hA.const_mul x) (by positivity))
  refine hD.congr_deriv ?_
  have ha2 : √a ^ 2 = a := sq_sqrt ha.le
  have hw2 : √(x - a) ^ 2 = x - a := sq_sqrt hxa.le
  generalize √a = u at *
  generalize √(x - a) = w at *
  subst ha2
  obtain rfl : x = w ^ 2 + u ^ 2 := by linarith
  have hu' : u ≠ 0 := hu.ne'
  have hw' : w ≠ 0 := hw.ne'
  have hx' : w ^ 2 + u ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **The convolution CDF of two infinite-mean Pareto laws** (QRM Exercise Book,
Exercise 2.28): for `F(x) = 1 − x^{−1/2}` on `[1, ∞)`, the law of the sum of two independent
copies has CDF `(F ∗ F)(x) = 1 − 2√(x − 1)/x` for `x ≥ 2`. -/
theorem cdf_conv_paretoMeasure_half {x : ℝ} (hx : 2 ≤ x) :
    cdf (paretoMeasure 1 (1 / 2) ∗ paretoMeasure 1 (1 / 2)) x = 1 - 2 * √(x - 1) / x := by
  have := isProbabilityMeasure_paretoMeasure (t := 1) (r := 1 / 2) one_pos (by norm_num)
  have hx1 : (1 : ℝ) ≤ x - 1 := by linarith
  -- the integrand `a ↦ f(a) F(x − a)` lives on `[1, x − 1]`
  have hsupp (a : ℝ) (ha : a ∉ Icc 1 (x - 1)) :
      paretoPDFReal 1 (1 / 2) a * cdf (paretoMeasure 1 (1 / 2)) (x - a) = 0 := by
    rcases not_and_or.1 ha with ha1 | ha1
    · rw [paretoPDFReal, ite_eq_right ha1, zero_mul]
    · rw [cdf_paretoMeasure_of_lt one_pos (by norm_num : (0 : ℝ) < 1 / 2)
        (by linarith [not_le.1 ha1] : x - a < 1), mul_zero]
  -- on `[1, x − 1]` it is `(1 − 1/√(x − a))/(2a√a)`
  have heq : EqOn (fun a ↦ paretoPDFReal 1 (1 / 2) a * cdf (paretoMeasure 1 (1 / 2)) (x - a))
      (fun a ↦ (1 - (√(x - a))⁻¹) / (2 * a * √a)) (uIcc 1 (x - 1)) := by
    intro a ha
    rw [uIcc_of_le hx1] at ha
    have ha0 : 0 < a := zero_lt_one.trans_le ha.1
    have hxa : 1 ≤ x - a := by linarith [ha.2]
    have hu : 0 < √a := sqrt_pos.2 ha0
    have hw : 0 < √(x - a) := sqrt_pos.2 (by linarith)
    have e1 : a ^ (-(1 / 2 + 1) : ℝ) = (a * √a)⁻¹ := by
      rw [rpow_neg ha0.le, show (1 / 2 + 1 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add ha0, rpow_one,
        ← sqrt_eq_rpow]
    have e2 : (1 / (x - a)) ^ (1 / 2 : ℝ) = (√(x - a))⁻¹ := by
      rw [← sqrt_eq_rpow, one_div, sqrt_inv]
    simp only [paretoPDFReal, ite_eq_left ha.1, one_rpow, mul_one,
      cdf_paretoMeasure_of_le one_pos (by norm_num : (0 : ℝ) < 1 / 2) hxa]
    rw [e1, e2]
    field_simp
  have hint : IntervalIntegrable (fun a ↦ (1 - (√(x - a))⁻¹) / (2 * a * √a)) volume 1 (x - 1) := by
    refine ContinuousOn.intervalIntegrable fun a ha ↦ ?_
    rw [uIcc_of_le hx1] at ha
    have ha0 : 0 < a := zero_lt_one.trans_le ha.1
    have hw : √(x - a) ≠ 0 := (sqrt_pos.2 (by linarith [ha.2])).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := first | assumption | positivity))
  rw [cdf_conv, integral_paretoMeasure (r := 1 / 2) zero_le_one (by norm_num),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hx1, intervalIntegral.integral_congr heq,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun a ↦ -(√a)⁻¹ + √(x - a) / (x * √a)) (fun a ha ↦ ?_) hint]
  · simp only [sub_sub_cancel, sqrt_one, inv_one, mul_one]
    have hv : 0 < √(x - 1) := sqrt_pos.2 (by linarith)
    have hv2 : √(x - 1) ^ 2 = x - 1 := sq_sqrt (by linarith)
    generalize √(x - 1) = v at *
    obtain rfl : x = v ^ 2 + 1 := by linarith
    have hv' : v ≠ 0 := hv.ne'
    have hx' : v ^ 2 + 1 ≠ 0 := by positivity
    field_simp
    ring
  · rw [uIcc_of_le hx1] at ha
    exact hasDerivAt_convAntideriv (zero_lt_one.trans_le ha.1) (by linarith [ha.2])

/-- **VaR is superadditive at every level for infinite-mean Pareto losses** (QRM Exercise Book,
Exercise 2.28): if `L₁, L₂` are independent with `F(x) = 1 − x^{−1/2}` on `[1, ∞)`, then
`VaR_α(L₁ + L₂) > VaR_α(L₁) + VaR_α(L₂)` for every `α ∈ (0, 1)`. -/
theorem valueAtRisk_add_gt_of_paretoHalf {L₁ L₂ : Ω → ℝ}
    (h₁ : HasLaw L₁ (paretoMeasure 1 (1 / 2)) P) (h₂ : HasLaw L₂ (paretoMeasure 1 (1 / 2)) P)
    (hind : IndepFun L₁ L₂ P) (hα : α ∈ Ioo 0 1) :
    valueAtRisk L₁ P α + valueAtRisk L₂ P α < valueAtRisk (fun ω ↦ L₁ ω + L₂ ω) P α := by
  have := isProbabilityMeasure_paretoMeasure (t := 1) (r := 1 / 2) one_pos (by norm_num)
  have hS : HasLaw (fun ω ↦ L₁ ω + L₂ ω)
      (paretoMeasure 1 (1 / 2) ∗ paretoMeasure 1 (1 / 2)) P :=
    hind.hasLaw_fun_add h₁ h₂
  have hs0 : 0 < 1 - α := sub_pos.2 hα.2
  have hs1 : 1 - α < 1 := by linarith [hα.1]
  -- each marginal VaR is `(1 − α)^{−2}`
  have hVaR : quantile (paretoMeasure 1 (1 / 2)) α = ((1 - α) ^ 2)⁻¹ := by
    rw [quantile_paretoMeasure (r := 1 / 2) one_pos (by norm_num) hα, one_mul,
      show -(1 / 2 : ℝ)⁻¹ = -2 by norm_num, rpow_neg hs0.le, rpow_two]
  rw [valueAtRisk_eq_quantile h₁, valueAtRisk_eq_quantile h₂, valueAtRisk_eq_quantile hS, hVaR,
    lt_quantile_iff hα]
  have hsq : (1 - α) ^ 2 < 1 := by nlinarith
  have htwo : 2 ≤ ((1 - α) ^ 2)⁻¹ + ((1 - α) ^ 2)⁻¹ := by
    have : 1 < ((1 - α) ^ 2)⁻¹ := (one_lt_inv₀ (by positivity)).2 hsq
    linarith
  rw [cdf_conv_paretoMeasure_half htwo]
  -- `2t − 1 > t` for `t = (1 − α)^{−2} > 1`
  set s := 1 - α with hs
  have hv : 0 < √((s ^ 2)⁻¹ + (s ^ 2)⁻¹ - 1) := sqrt_pos.2 (by linarith)
  have hv2 : √((s ^ 2)⁻¹ + (s ^ 2)⁻¹ - 1) ^ 2 = (s ^ 2)⁻¹ + (s ^ 2)⁻¹ - 1 :=
    sq_sqrt (by linarith)
  generalize √((s ^ 2)⁻¹ + (s ^ 2)⁻¹ - 1) = v at *
  have hα' : α = 1 - s := by rw [hs]; ring
  rw [hα']
  have hs0' : s ≠ 0 := hs0.ne'
  have hvs : (v * s) ^ 2 = 2 - s ^ 2 := by
    rw [mul_pow, hv2]
    field_simp
    ring
  have hvs1 : 1 < v * s := by nlinarith [mul_pos hv hs0]
  rw [show 2 * v / ((s ^ 2)⁻¹ + (s ^ 2)⁻¹) = v * s ^ 2 by field_simp; ring]
  nlinarith

end Pareto

/-! ### Jointly Gaussian losses -/

section Gaussian

/-- **Gaussian VaR is subadditive at levels above the median**: for a jointly Gaussian pair,
`VaR_α(X + Y) ≤ VaR_α(X) + VaR_α(Y)` when `α ≥ 1/2`. `VaR = E + sd Φ⁻¹(α)` and the standard
deviation is subadditive, so no hypothesis on the correlation is needed. -/
theorem valueAtRisk_add_le_of_hasGaussianLaw {X Y : Ω → ℝ}
    (h : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) (hα : α ∈ Ioo 0 1) (hα₂ : 1 / 2 ≤ α) :
    valueAtRisk (fun ω ↦ X ω + Y ω) P α ≤ valueAtRisk X P α + valueAtRisk Y P α := by
  have := h.isProbabilityMeasure
  rw [valueAtRisk_of_hasGaussianLaw h.fun_add hα, valueAtRisk_of_hasGaussianLaw h.fst hα,
    valueAtRisk_of_hasGaussianLaw h.snd hα, integral_add h.fst.integrable h.snd.integrable]
  nlinarith [mul_le_mul_of_nonneg_right (sqrt_variance_add_le h.fst.memLp_two h.snd.memLp_two)
    ((PhiInv_nonneg_iff hα).2 hα₂)]

/-- **Gaussian VaR is subadditive exactly above the median** (QRM Exercise Book, Exercise 2.22):
for a jointly Gaussian pair `(X₁, X₂)` with correlation below one
(`cov[X₁, X₂] < σ₁σ₂`), `VaR_α(X₁ + X₂) ≤ VaR_α(X₁) + VaR_α(X₂) ↔ α ≥ 1/2`. -/
theorem valueAtRisk_add_le_iff_of_hasGaussianLaw {X₁ X₂ : Ω → ℝ}
    (h : HasGaussianLaw (fun ω ↦ (X₁ ω, X₂ ω)) P)
    (hcorr : cov[X₁, X₂; P] < √Var[X₁; P] * √Var[X₂; P]) (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun ω ↦ X₁ ω + X₂ ω) P α ≤ valueAtRisk X₁ P α + valueAtRisk X₂ P α ↔
      1 / 2 ≤ α := by
  refine ⟨fun hle ↦ ?_, valueAtRisk_add_le_of_hasGaussianLaw h hα⟩
  have := h.isProbabilityMeasure
  have h₁ := h.fst
  have h₂ := h.snd
  have hσ : √Var[fun ω ↦ X₁ ω + X₂ ω; P] < √Var[X₁; P] + √Var[X₂; P] := by
    have hvar : Var[fun ω ↦ X₁ ω + X₂ ω; P] = Var[X₁; P] + 2 * cov[X₁, X₂; P] + Var[X₂; P] :=
      variance_add h₁.memLp_two h₂.memLp_two
    have hs₁ := sq_sqrt (variance_nonneg X₁ P)
    have hs₂ := sq_sqrt (variance_nonneg X₂ P)
    calc √Var[fun ω ↦ X₁ ω + X₂ ω; P] < √((√Var[X₁; P] + √Var[X₂; P]) ^ 2) :=
          sqrt_lt_sqrt (variance_nonneg _ P) (by rw [hvar]; nlinarith)
      _ = √Var[X₁; P] + √Var[X₂; P] := sqrt_sq (by positivity)
  rw [valueAtRisk_of_hasGaussianLaw h.fun_add hα, valueAtRisk_of_hasGaussianLaw h₁ hα,
    valueAtRisk_of_hasGaussianLaw h₂ hα, integral_add h₁.integrable h₂.integrable] at hle
  rw [← PhiInv_nonneg_iff hα]
  by_contra! hz
  nlinarith [mul_lt_mul_of_neg_right hσ hz]

end Gaussian

end MathFin
