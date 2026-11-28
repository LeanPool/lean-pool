/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.ExpectedShortfall

/-!
# Spectral risk measures

A **spectral risk measure** weights the value-at-risk curve of a loss by a spectrum `φ`:

  `ρ_φ(X) = ∫₀¹ φ(u) · VaR_u(X) du`

(`spectralRiskMeasure`; Acerbi, *Spectral measures of risk: a coherent representation of
subjective risk aversion*, J. Banking Finance 26 (2002), 1505–1518). The VaR curve is
`valueAtRisk` of `Risk/ValueAtRisk.lean`, the quantile function of the law of the loss.
Two spectra recover measures the library already has:

* the constant spectrum `φ ≡ 1` gives the mean, `ρ_1(X) = E[X]` (`spectralRiskMeasure_one`),
  because the quantile function pushes the uniform law on `(0, 1)` forward to the law of `X`;
* the spectrum `(1 − α)⁻¹ 𝟙_{(α, 1)}` (`esSpectrum`) gives expected shortfall
  (`spectralRiskMeasure_esSpectrum`).

A convex combination `∑ₖ wₖ (1 − αₖ)⁻¹ 𝟙_{(αₖ, 1)}` of expected-shortfall spectra is a
nondecreasing step spectrum. Its spectral risk is the same convex combination of expected
shortfalls (`spectralRiskMeasure_sum_esSpectrum`), and that mixture is a coherent risk measure on
the integrable losses (`isCoherentRiskMeasure_spectralRiskFinite_expectedShortfall`,
`isCoherentRiskMeasure_spectralRiskMeasure_sum_esSpectrum`). Each coherence axiom of the mixture
is a finite-weight lemma of this file applied to the coherent expected shortfall
(`expectedShortfall_isCoherentRiskMeasure`). Acerbi's theorem (Theorem 4.1 there), that every
nonnegative nondecreasing spectrum integrating to one gives a coherent measure, is proved here only
for these step spectra.

The finite weighted sum `spectralRiskFinite s φ Q = ∑ᵢ φᵢ Qᵢ` carries the algebra: translation
invariance, monotonicity and convex combinations in the weights. With `Qₖ = ES_{αₖ}(X)` it is the
mixture of expected shortfalls above.

## Main definitions

* `spectralRiskMeasure`: the spectral risk measure `ρ_φ(X) = ∫₀¹ φ(u) · VaR_u(X) du` with
  spectrum `φ`.
* `esSpectrum`: the expected-shortfall spectrum `(1 − α)⁻¹ 𝟙_{(α, 1)}`, uniform weight on the
  levels above `α`.
* `spectralRiskFinite`: the finite spectral sum `∑ᵢ φᵢ Qᵢ` of values `Q` with weights `φ`.

## Main results

* `spectralRisk_translation`, `spectralRisk_mono`,
  `spectralRisk_convex_combination_normalized`, `spectralRisk_convex_combination`: the finite
  weighted sum and its algebra.
* `isCoherentRiskMeasure_spectralRiskFinite_expectedShortfall`: a convex combination of expected
  shortfalls is a coherent risk measure.
* `spectralRiskFinite_expectedShortfall_isLUB_representingSet`: on a finite space the mixture is
  the supremum of expected loss over its representing set.
* `spectralRiskMeasure_one`: the constant spectrum gives the mean.
* `spectralRiskMeasure_esSpectrum`: the expected-shortfall spectrum gives expected shortfall.
* `spectralRiskMeasure_sum_esSpectrum`: a step spectrum gives the mixture of expected shortfalls.
* `isCoherentRiskMeasure_spectralRiskMeasure_sum_esSpectrum`: step-spectrum spectral risk
  measures are coherent.

## References

* [C. Acerbi, *Spectral measures of risk: A coherent representation of subjective risk
  aversion*][Acerbi2002], Theorem 4.1

## Tags

spectral risk measure, Acerbi, risk aversion spectrum, expected shortfall mixture,
coherent risk measure, quantile weighting, MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

variable {ι : Type*}

/-! ### The finite weighted sum -/

/-- Finite spectral sum: the weighted sum `∑ᵢ φᵢ Qᵢ` of the values `Q` with weights `φ`. With
`Qₖ = ES_{αₖ}(X)` it is a mixture of expected shortfalls
(`spectralRiskMeasure_sum_esSpectrum`). -/
noncomputable def spectralRiskFinite (s : Finset ι) (φ : ι → ℝ) (Q : ι → ℝ) : ℝ :=
  ∑ i ∈ s, φ i * Q i

/-- **Translation invariance**: if `Σ φ = 1`, then `ρ(Q + c·𝟙) = ρ(Q) + c`. -/
theorem spectralRisk_translation (s : Finset ι) (φ : ι → ℝ) (Q : ι → ℝ)
    (c : ℝ) (h_norm : ∑ i ∈ s, φ i = 1) :
    spectralRiskFinite s φ (fun i ↦ Q i + c) =
      spectralRiskFinite s φ Q + c := by
  unfold spectralRiskFinite
  rw [show (fun i ↦ φ i * (Q i + c)) = (fun i ↦ φ i * Q i + φ i * c) from by
        funext i; ring]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, h_norm, one_mul]

/-- **Monotonicity**: with nonnegative weights, pointwise dominance of the values `Q ≤ Q'` on `s`
gives `ρ_φ(Q) ≤ ρ_φ(Q')`. -/
theorem spectralRisk_mono (s : Finset ι) (φ Q Q' : ι → ℝ)
    (hφ : ∀ i ∈ s, 0 ≤ φ i) (hQ : ∀ i ∈ s, Q i ≤ Q' i) :
    spectralRiskFinite s φ Q ≤ spectralRiskFinite s φ Q' := by
  unfold spectralRiskFinite
  exact Finset.sum_le_sum fun i hi ↦
    mul_le_mul_of_nonneg_left (hQ i hi) (hφ i hi)

/-- The finite spectral sum depends on the values only on `s`. -/
theorem spectralRiskFinite_congr {s : Finset ι} {φ Q Q' : ι → ℝ} (h : ∀ i ∈ s, Q i = Q' i) :
    spectralRiskFinite s φ Q = spectralRiskFinite s φ Q' :=
  Finset.sum_congr rfl fun i hi ↦ by rw [h i hi]

/-- **Convex combination of normalized spectra remains normalized**:
`t Σ φ + (1−t) Σ ψ = t · 1 + (1−t) · 1 = 1`. The convex-combination weight
`t·φ + (1−t)·ψ` is therefore a valid spectral weight. -/
theorem spectralRisk_convex_combination_normalized
    (s : Finset ι) (φ ψ : ι → ℝ) (t : ℝ)
    (hφ : ∑ i ∈ s, φ i = 1) (hψ : ∑ i ∈ s, ψ i = 1) :
    ∑ i ∈ s, (t * φ i + (1 - t) * ψ i) = 1 := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hφ, hψ]
  ring

/-- **Convex combination of spectral sums**: a convex combination of two finite spectral sums
acts on the values through the convex combination of the weights. -/
theorem spectralRisk_convex_combination
    (s : Finset ι) (φ ψ : ι → ℝ) (Q : ι → ℝ) (t : ℝ) :
    t * spectralRiskFinite s φ Q + (1 - t) * spectralRiskFinite s ψ Q =
      spectralRiskFinite s (fun i ↦ t * φ i + (1 - t) * ψ i) Q := by
  unfold spectralRiskFinite
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  ring

/-! ### Mixtures of expected shortfalls -/

open MeasureTheory Set

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {α : ℝ}

/-- **A convex combination of expected shortfalls is coherent**: for weights `w ≥ 0` with
`∑ w = 1` and levels `αₖ ∈ (0, 1)`, `X ↦ ∑ₖ wₖ ES_{αₖ}(X)` satisfies the four axioms of a coherent
risk measure on the integrable losses. Each axiom is the finite-sum lemma of this file applied to
the corresponding axiom of expected shortfall (`expectedShortfall_isCoherentRiskMeasure`). -/
theorem isCoherentRiskMeasure_spectralRiskFinite_expectedShortfall [IsProbabilityMeasure P]
    (s : Finset ι) {w α : ι → ℝ} (hw : ∀ k ∈ s, 0 ≤ w k) (hw1 : ∑ k ∈ s, w k = 1)
    (hα : ∀ k ∈ s, α k ∈ Ioo 0 1) :
    IsCoherentRiskMeasure P fun X ↦ spectralRiskFinite s w fun k ↦ expectedShortfall X P (α k)
    where
  mono _ _ hX hY hXY :=
    spectralRisk_mono s w _ _ hw fun k hk ↦ expectedShortfall_mono hX hY hXY (hα k hk)
  add_const X hX m :=
    (spectralRiskFinite_congr (Q' := fun k ↦ expectedShortfall X P (α k) + m)
      fun k hk ↦ expectedShortfall_add_const hX (hα k hk) m).trans
      (spectralRisk_translation s w (fun k ↦ expectedShortfall X P (α k)) m hw1)
  const_mul X hX c hc := by
    simp only [spectralRiskFinite, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk ↦ by
      rw [expectedShortfall_const_mul hX (hα k hk) hc]
      ring
  add_le X Y hX hY := by
    refine (spectralRisk_mono s w _ _ hw fun k hk ↦
      expectedShortfall_add_le hX hY (hα k hk)).trans_eq ?_
    simp only [spectralRiskFinite, mul_add, Finset.sum_add_distrib]

/-- **Mixtures of expected shortfall in the ADEH framework**: on a finite probability space,
`L ↦ ∑ₖ wₖ ES_{αₖ}(L)` is a coherent risk measure
(`isCoherentRiskMeasure_spectralRiskFinite_expectedShortfall`), so `coherentRisk_isLUB` represents
it as a supremum of expected losses over its representing set. -/
theorem spectralRiskFinite_expectedShortfall_isLUB_representingSet {κ : Type*} [Fintype κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] (Q : Measure κ) [IsProbabilityMeasure Q]
    (s : Finset ι) {w α : ι → ℝ} (hw : ∀ k ∈ s, 0 ≤ w k) (hw1 : ∑ k ∈ s, w k = 1)
    (hα : ∀ k ∈ s, α k ∈ Ioo 0 1) (L : κ → ℝ) :
    IsLUB ((fun q ↦ ∑ i, q i * L i) ''
        representingSet fun L : κ → ℝ ↦ spectralRiskFinite s w fun k ↦ expectedShortfall L Q (α k))
      (spectralRiskFinite s w fun k ↦ expectedShortfall L Q (α k)) :=
  coherentRisk_isLUB
    (isCoherentRiskMeasure_spectralRiskFinite_expectedShortfall (P := Q) s hw hw1 hα) L

/-! ### The spectral risk of a loss -/

/-- The **spectral risk measure** with spectrum `φ`: `ρ_φ(X) = ∫₀¹ φ(u) · VaR_u(X) du`. -/
noncomputable def spectralRiskMeasure (φ : ℝ → ℝ) (X : Ω → ℝ) (P : Measure Ω) : ℝ :=
  ∫ u in Ioo 0 1, φ u * valueAtRisk X P u

/-- The **expected-shortfall spectrum** `(1 − α)⁻¹ 𝟙_{(α, 1)}`: uniform weight on the levels
above `α`. -/
noncomputable def esSpectrum (α : ℝ) : ℝ → ℝ :=
  (Ioo α 1).indicator fun _ ↦ (1 - α)⁻¹

/-- Weighting a function by the expected-shortfall spectrum restricts it to `(α, 1)`. -/
lemma esSpectrum_mul (α : ℝ) (g : ℝ → ℝ) (u : ℝ) :
    esSpectrum α u * g u = (Ioo α 1).indicator (fun v ↦ (1 - α)⁻¹ * g v) u :=
  (indicator_mul_left (Ioo α 1) (fun _ ↦ (1 - α)⁻¹) g).symm

/-- **The constant spectrum gives the mean**: `∫₀¹ VaR_u(X) du = E[X]`. The VaR curve is the
quantile function of the law of `X`, which pushes the uniform law on `(0, 1)` forward to that
law (`integral_eq_setIntegral_quantile`). -/
theorem spectralRiskMeasure_one [IsProbabilityMeasure P] (hX : AEMeasurable X P) :
    spectralRiskMeasure 1 X P = ∫ ω, X ω ∂P := by
  have hq := integral_eq_setIntegral_quantile (μ := P.map X) (f := fun x ↦ x) (by fun_prop)
  rw [integral_map hX (by fun_prop)] at hq
  simp only [spectralRiskMeasure, Pi.one_apply, one_mul]
  exact hq.symm

/-- **The expected-shortfall spectrum gives expected shortfall**: for `α ∈ (0, 1)`,
`∫₀¹ (1 − α)⁻¹ 𝟙_{(α, 1)}(u) VaR_u(X) du = ES_α(X)`. -/
theorem spectralRiskMeasure_esSpectrum (hα : α ∈ Ioo 0 1) :
    spectralRiskMeasure (esSpectrum α) X P = expectedShortfall X P α := by
  simp_rw [spectralRiskMeasure, esSpectrum_mul α (valueAtRisk X P)]
  rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.2 (Ioo_subset_Ioo_left hα.1.le),
    integral_const_mul, expectedShortfall]

/-- **A step spectrum gives a mixture of expected shortfalls**: for an integrable loss and levels
`αₖ ∈ (0, 1)`, the spectral risk of `∑ₖ wₖ (1 − αₖ)⁻¹ 𝟙_{(αₖ, 1)}` is `∑ₖ wₖ ES_{αₖ}(X)`. -/
theorem spectralRiskMeasure_sum_esSpectrum [IsProbabilityMeasure P] (hX : Integrable X P)
    (s : Finset ι) (w : ι → ℝ) {α : ι → ℝ} (hα : ∀ k ∈ s, α k ∈ Ioo 0 1) :
    spectralRiskMeasure (fun u ↦ ∑ k ∈ s, w k * esSpectrum (α k) u) X P =
      spectralRiskFinite s w fun k ↦ expectedShortfall X P (α k) := by
  have hint (k : ι) :
      IntegrableOn (fun u ↦ w k * (esSpectrum (α k) u * valueAtRisk X P u)) (Ioo 0 1) := by
    simp_rw [esSpectrum_mul (α k) (valueAtRisk X P)]
    exact ((Integrable.const_mul (integrableOn_valueAtRisk hX) _).indicator
      measurableSet_Ioo).const_mul _
  simp_rw [spectralRiskMeasure, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum s fun k _ ↦ hint k]
  exact Finset.sum_congr rfl fun k hk ↦ by
    rw [integral_const_mul]
    exact congrArg (w k * ·) (spectralRiskMeasure_esSpectrum (hα k hk))

/-- **Step-spectrum spectral risk measures are coherent**: for weights `w ≥ 0` with `∑ w = 1` and
levels `αₖ ∈ (0, 1)`, the spectral risk measure of the nondecreasing step spectrum
`∑ₖ wₖ (1 − αₖ)⁻¹ 𝟙_{(αₖ, 1)}` is a coherent risk measure on the integrable losses. On those
losses it is the mixture of expected shortfalls (`spectralRiskMeasure_sum_esSpectrum`), which is
coherent (`isCoherentRiskMeasure_spectralRiskFinite_expectedShortfall`). -/
theorem isCoherentRiskMeasure_spectralRiskMeasure_sum_esSpectrum [IsProbabilityMeasure P]
    (s : Finset ι) {w α : ι → ℝ} (hw : ∀ k ∈ s, 0 ≤ w k) (hw1 : ∑ k ∈ s, w k = 1)
    (hα : ∀ k ∈ s, α k ∈ Ioo 0 1) :
    IsCoherentRiskMeasure P
      (spectralRiskMeasure (fun u ↦ ∑ k ∈ s, w k * esSpectrum (α k) u) · P) := by
  have e (X : Ω → ℝ) (hX : Integrable X P) := spectralRiskMeasure_sum_esSpectrum hX s w hα
  have h := isCoherentRiskMeasure_spectralRiskFinite_expectedShortfall (P := P) s hw hw1 hα
  exact
    { mono := fun X Y hX hY hXY ↦
        (e X hX).trans_le ((h.mono hX hY hXY).trans_eq (e Y hY).symm)
      add_const := fun X hX m ↦
        (e (fun ω ↦ X ω + m) (hX.add (integrable_const m))).trans
          ((h.add_const hX m).trans (congrArg (· + m) (e X hX).symm))
      const_mul := fun X hX c hc ↦
        (e (fun ω ↦ c * X ω) (hX.const_mul c)).trans
          ((h.const_mul hX hc).trans (congrArg (c * ·) (e X hX).symm))
      add_le := fun X Y hX hY ↦
        (e (fun ω ↦ X ω + Y ω) (hX.add hY)).trans_le
          ((h.add_le hX hY).trans_eq (congrArg₂ (· + ·) (e X hX) (e Y hY)).symm) }

end MathFin
