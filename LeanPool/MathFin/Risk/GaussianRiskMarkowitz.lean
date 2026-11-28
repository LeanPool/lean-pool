/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.VaRSuperadditivity
public import LeanPool.MathFin.Choice.Portfolio.Equicorrelation
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# For Gaussian risk factors, VaR and ES rank portfolios as Markowitz does

Value-at-risk and expected shortfall are translation invariant, positively homogeneous and law
invariant (`Risk/ValueAtRisk.lean`). Those three properties alone already give the
**location–scale principle**: a loss whose law is that of `m + s Z` (`s ≥ 0`) has

  `VaR_α = m + s · VaR_α(Z)`   and   `ES_α = m + s · ES_α(Z)`

(`valueAtRisk_of_map_eq_affine`, `expectedShortfall_of_map_eq_affine`). So within a location–scale
family the risk measures order losses of equal mean by their scale, as soon as the standardized
risk is positive (`valueAtRisk_le_iff_of_map_eq_affine`,
`expectedShortfall_le_iff_of_map_eq_affine`).

A Gaussian vector of risk-factor changes `X = (X₁, …, X_d)` makes every linear portfolio loss
`⟨w, X⟩ = ∑ wᵢ Xᵢ` a member of one such family. The loss is Gaussian (`HasGaussianLaw.map_fun`),
its mean is `∑ wᵢ E Xᵢ`, and its variance is the Markowitz double sum `wᵀ Σ w` of the covariance
kernel (`hasLaw_portfolio_gaussianReal`). The variance identification is the self-dot identity of
`Choice/Portfolio/CovariancePSD.lean`. Hence

  `VaR_α(⟨w, X⟩) = ∑ wᵢ E Xᵢ + √(wᵀ Σ w) · Φ⁻¹(α)`   (`valueAtRisk_portfolio_gaussian`).

**The bridge** (McNeil–Frey–Embrechts (2015), Chapter 8; QRM Exercise 8.6). Among portfolios
with the same expected loss, VaR at any level `α > 1/2` and ES at any such level order portfolios
exactly as the portfolio variance does (`valueAtRisk_portfolio_le_iff`,
`expectedShortfall_portfolio_le_iff`). Consequently a portfolio minimizes VaR, or ES, over any
admissible set of weights with a common expected loss exactly when it is a Markowitz
minimum-variance portfolio there (`isMinOn_valueAtRisk_iff_isMinOn_portfolioVarN`,
`isMinOn_expectedShortfall_iff_isMinOn_portfolioVarN`). This is a certified unification of two
known textbook facts, not new finance.

On the linear space of portfolio losses VaR is also **subadditive** at every level `α ≥ 1/2`
(`valueAtRisk_portfolio_add_le`, QRM Exercise 8.4). Two portfolio losses of a Gaussian vector
are a jointly Gaussian pair (`hasGaussianLaw_portfolio_pair`), so this is the pair theorem
`valueAtRisk_add_le_of_hasGaussianLaw`, which rests on the subadditivity of the standard deviation
(`sqrt_variance_add_le`). Outside the Gaussian world subadditivity fails (`Risk/`
superadditivity examples).

The general elliptical case of Exercise 8.6 is covered by the location–scale theorems once the
family hypothesis (every portfolio loss is `m + s Z` in law for one standardized `Z`) is
supplied. Elliptical distributions themselves are not formalized here; the Gaussian family is
the instance proved.

## Main results

* `valueAtRisk_of_map_eq_affine`, `expectedShortfall_of_map_eq_affine`: the location–scale
  principle.
* `valueAtRisk_le_iff_of_map_eq_affine`, `expectedShortfall_le_iff_of_map_eq_affine`: within a
  location–scale family and at equal means, the risk measures order losses by scale.
* `hasGaussianLaw_portfolio_pair`: two portfolio losses of a Gaussian vector are jointly Gaussian.
* `hasLaw_portfolio_gaussianReal`: `⟨w, X⟩ ~ N(∑ wᵢ E Xᵢ, wᵀ Σ w)` for a Gaussian vector `X`.
* `valueAtRisk_portfolio_gaussian`, `expectedShortfall_portfolio_gaussian`: the closed forms.
* `valueAtRisk_portfolio_le_iff`, `expectedShortfall_portfolio_le_iff`: VaR, ES and variance order
  equal-mean portfolios identically (`α > 1/2`).
* `isMinOn_valueAtRisk_iff_isMinOn_portfolioVarN`,
  `isMinOn_expectedShortfall_iff_isMinOn_portfolioVarN`: VaR- and ES-optimal portfolios are the
  Markowitz portfolios (QRM Ex. 8.6).
* `valueAtRisk_portfolio_add_le`: VaR is subadditive on Gaussian portfolio losses for `α ≥ 1/2`
  (QRM Ex. 8.4).
* `valueAtRisk_equal_weight_equicorrelated`: the VaR of an equally weighted equicorrelated
  Gaussian portfolio, `m + σ √(ρ + (1 − ρ)/d) Φ⁻¹(α)` (QRM Ex. 6.16).

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Section 8.2
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 8.4; Ex. 8.6

## Tags

value-at-risk, expected shortfall, location–scale family, Markowitz, subadditivity,
elliptical distributions, MSC 91G70, MSC 91G10, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-! ### The location–scale principle -/

section LocationScale

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {Q : Measure Ω'} {L L' : Ω → ℝ} {Z : Ω' → ℝ} {α m s s' : ℝ}

/-- VaR depends on a loss only through its law, across probability spaces. -/
lemma valueAtRisk_congr_map (h : P.map L = Q.map Z) (α : ℝ) :
    valueAtRisk L P α = valueAtRisk Z Q α := by
  rw [valueAtRisk, valueAtRisk, h]

/-- ES depends on a loss only through its law, across probability spaces. -/
lemma expectedShortfall_congr_map (h : P.map L = Q.map Z) (α : ℝ) :
    expectedShortfall L P α = expectedShortfall Z Q α := by
  simp only [expectedShortfall, valueAtRisk_congr_map h]

variable [IsProbabilityMeasure Q]

/-- **Location–scale principle for VaR**: a loss with the law of `m + s Z` (`s ≥ 0`) has
`VaR_α = m + s VaR_α(Z)`. -/
theorem valueAtRisk_of_map_eq_affine (hZ : AEMeasurable Z Q) (hs : 0 ≤ s)
    (h : P.map L = Q.map fun ω ↦ m + s * Z ω) (hα : α ∈ Ioo 0 1) :
    valueAtRisk L P α = m + s * valueAtRisk Z Q α := by
  rw [valueAtRisk_congr_map h, valueAtRisk_comp (h := fun z ↦ m + s * z) hZ
    (monotone_const.add (monotone_id.const_mul hs))
    (by fun_prop : Continuous fun z : ℝ ↦ m + s * z).lowerSemicontinuous hα]

/-- **Location–scale principle for ES**: a loss with the law of `m + s Z` (`s ≥ 0`, `Z`
integrable) has `ES_α = m + s ES_α(Z)`. Translation invariance and positive homogeneity of ES,
transported along the law. -/
theorem expectedShortfall_of_map_eq_affine (hZ : Integrable Z Q) (hs : 0 ≤ s)
    (h : P.map L = Q.map fun ω ↦ m + s * Z ω) (hα : α ∈ Ioo 0 1) :
    expectedShortfall L P α = m + s * expectedShortfall Z Q α :=
  calc expectedShortfall L P α = expectedShortfall (fun ω ↦ s * Z ω + m) Q α := by
        rw [expectedShortfall_congr_map h]; simp_rw [add_comm m]
    _ = expectedShortfall (fun ω ↦ s * Z ω) Q α + m :=
        expectedShortfall_add_const (hZ.const_mul s) hα m
    _ = m + s * expectedShortfall Z Q α := by
        rw [expectedShortfall_const_mul hZ hα hs, add_comm]

/-- **At equal means, VaR orders a location–scale family by scale**: if `L`, `L'` have the laws
of `m + s Z` and `m + s' Z` and `VaR_α(Z) > 0`, then `VaR_α(L) ≤ VaR_α(L') ↔ s ≤ s'`. -/
theorem valueAtRisk_le_iff_of_map_eq_affine (hZ : AEMeasurable Z Q) (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (h : P.map L = Q.map fun ω ↦ m + s * Z ω) (h' : P.map L' = Q.map fun ω ↦ m + s' * Z ω)
    (hα : α ∈ Ioo 0 1) (hpos : 0 < valueAtRisk Z Q α) :
    valueAtRisk L P α ≤ valueAtRisk L' P α ↔ s ≤ s' := by
  rw [valueAtRisk_of_map_eq_affine hZ hs h hα, valueAtRisk_of_map_eq_affine hZ hs' h' hα,
    add_le_add_iff_left, mul_le_mul_iff_left₀ hpos]

/-- **At equal means, ES orders a location–scale family by scale**: if `L`, `L'` have the laws
of `m + s Z` and `m + s' Z` and `ES_α(Z) > 0`, then `ES_α(L) ≤ ES_α(L') ↔ s ≤ s'`. -/
theorem expectedShortfall_le_iff_of_map_eq_affine (hZ : Integrable Z Q) (hs : 0 ≤ s)
    (hs' : 0 ≤ s') (h : P.map L = Q.map fun ω ↦ m + s * Z ω)
    (h' : P.map L' = Q.map fun ω ↦ m + s' * Z ω) (hα : α ∈ Ioo 0 1)
    (hpos : 0 < expectedShortfall Z Q α) :
    expectedShortfall L P α ≤ expectedShortfall L' P α ↔ s ≤ s' := by
  rw [expectedShortfall_of_map_eq_affine hZ hs h hα,
    expectedShortfall_of_map_eq_affine hZ hs' h' hα, add_le_add_iff_left,
    mul_le_mul_iff_left₀ hpos]

end LocationScale

/-! ### Gaussian portfolios -/

section Portfolio

variable {ι : Type*} [Fintype ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ι → Ω → ℝ} {α : ℝ}

/-- **Two portfolio losses of a Gaussian vector are jointly Gaussian**: `(∑ wᵢ Xᵢ, ∑ w'ᵢ Xᵢ)` is
the image of the Gaussian vector `X` under a linear map. -/
theorem hasGaussianLaw_portfolio_pair (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (w w' : ι → ℝ) :
    HasGaussianLaw (fun ω ↦ (∑ i, w i * X i ω, ∑ i, w' i * X i ω)) P := by
  simpa using hX.map_fun
    ((∑ i, w i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).prod
      (∑ i, w' i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i))

/-- **A Gaussian portfolio loss**: if the risk-factor vector `X` is Gaussian, the portfolio loss
`∑ wᵢ Xᵢ` has law `N(∑ wᵢ E Xᵢ, wᵀ Σ w)`, with `Σ` the covariance kernel of `X`. -/
theorem hasLaw_portfolio_gaussianReal (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (w : ι → ℝ) :
    HasLaw (fun ω ↦ ∑ i, w i * X i ω)
      (gaussianReal (∑ i, w i * P[X i])
        (portfolioVarN Finset.univ w fun i j ↦ cov[X i, X j; P]).toNNReal) P := by
  have := hX.isProbabilityMeasure
  have hL := (hasGaussianLaw_portfolio_pair hX w w).fst
  refine ⟨hL.aemeasurable, ?_⟩
  rw [hL.map_eq_gaussianReal,
    portfolioVarN_covariance_eq_variance Finset.univ w X fun i _ ↦ (hX.eval i).memLp_two]
  congr 1
  · rw [integral_finsetSum _ fun i _ ↦ (hX.eval i).integrable.const_mul (w i)]
    simp_rw [integral_const_mul]
  · congr 2
    ext ω
    simp

/-- The Markowitz variance of a Gaussian portfolio is nonnegative. -/
lemma portfolioVarN_gaussian_nonneg (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (w : ι → ℝ) :
    0 ≤ portfolioVarN Finset.univ w fun i j ↦ cov[X i, X j; P] :=
  have := hX.isProbabilityMeasure
  portfolioVarN_covariance_nonneg Finset.univ w X fun i _ ↦ (hX.eval i).memLp_two

/-- A Gaussian portfolio loss is `mean + (standard deviation) · Z` in law, `Z ~ N(0, 1)`. -/
lemma map_portfolio_eq_affine (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (w : ι → ℝ) :
    P.map (fun ω ↦ ∑ i, w i * X i ω) =
      (gaussianReal 0 1).map fun z ↦
        ∑ i, w i * P[X i] + √(portfolioVarN Finset.univ w fun i j ↦ cov[X i, X j; P]) * z := by
  rw [(hasLaw_portfolio_gaussianReal hX w).map_eq,
    gaussianReal_eq_map_standard (∑ i, w i * P[X i]),
    Real.coe_toNNReal _ (portfolioVarN_gaussian_nonneg hX w)]
  congr 1
  ext z
  ring

/-- **VaR of a Gaussian portfolio**: `VaR_α(∑ wᵢ Xᵢ) = ∑ wᵢ E Xᵢ + √(wᵀ Σ w) · Φ⁻¹(α)`. -/
theorem valueAtRisk_portfolio_gaussian (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (w : ι → ℝ)
    (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun ω ↦ ∑ i, w i * X i ω) P α =
      ∑ i, w i * P[X i] + √(portfolioVarN Finset.univ w fun i j ↦ cov[X i, X j; P]) * PhiInv α := by
  have := hX.isProbabilityMeasure
  rw [valueAtRisk_eq_quantile (hasLaw_portfolio_gaussianReal hX w), quantile_gaussianReal _ _ hα,
    Real.coe_toNNReal _ (portfolioVarN_gaussian_nonneg hX w)]

/-- The VaR of the standard normal law is `Φ⁻¹(α)`. -/
lemma valueAtRisk_id_gaussianReal (α : ℝ) :
    valueAtRisk id (gaussianReal 0 1) α = PhiInv α := by
  rw [valueAtRisk, Measure.map_id, PhiInv]

/-- **ES of a Gaussian portfolio**: `ES_α(∑ wᵢ Xᵢ) = ∑ wᵢ E Xᵢ + √(wᵀ Σ w) · ES_α(N(0, 1))`. -/
theorem expectedShortfall_portfolio_gaussian (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P)
    (w : ι → ℝ) (hα : α ∈ Ioo 0 1) :
    expectedShortfall (fun ω ↦ ∑ i, w i * X i ω) P α =
      ∑ i, w i * P[X i] + √(portfolioVarN Finset.univ w fun i j ↦ cov[X i, X j; P]) *
        expectedShortfall id (gaussianReal 0 1) α :=
  expectedShortfall_of_map_eq_affine IsGaussian.integrable_id (Real.sqrt_nonneg _)
    (map_portfolio_eq_affine hX w) hα

/-- Above the median the standard normal VaR is positive. -/
lemma zero_lt_valueAtRisk_id_gaussianReal (hα : α ∈ Ioo (1 / 2) 1) :
    0 < valueAtRisk id (gaussianReal 0 1) α := by
  have hα' : α ∈ Ioo 0 1 := ⟨by linarith [hα.1], hα.2⟩
  rw [valueAtRisk_id_gaussianReal, PhiInv_pos_iff hα']
  exact hα.1

/-- **The bridge for VaR** (QRM Exercise 8.6): among Gaussian portfolios with the same expected
loss, VaR at a level `α > 1/2` orders portfolios exactly as the Markowitz variance does. -/
theorem valueAtRisk_portfolio_le_iff (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P)
    (hα : α ∈ Ioo (1 / 2) 1) {w w' : ι → ℝ}
    (hmean : ∑ i, w i * P[X i] = ∑ i, w' i * P[X i]) :
    valueAtRisk (fun ω ↦ ∑ i, w i * X i ω) P α ≤ valueAtRisk (fun ω ↦ ∑ i, w' i * X i ω) P α ↔
      portfolioVarN Finset.univ w (fun i j ↦ cov[X i, X j; P]) ≤
        portfolioVarN Finset.univ w' fun i j ↦ cov[X i, X j; P] := by
  have h' := map_portfolio_eq_affine hX w'
  rw [← hmean] at h'
  rw [valueAtRisk_le_iff_of_map_eq_affine IsGaussian.integrable_id.aemeasurable
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (map_portfolio_eq_affine hX w) h'
    ⟨by linarith [hα.1], hα.2⟩ (zero_lt_valueAtRisk_id_gaussianReal hα),
    Real.sqrt_le_sqrt_iff (portfolioVarN_gaussian_nonneg hX w')]

/-- **The bridge for ES** (QRM Exercise 8.6): among Gaussian portfolios with the same expected
loss, ES at a level `α > 1/2` orders portfolios exactly as the Markowitz variance does. -/
theorem expectedShortfall_portfolio_le_iff (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P)
    (hα : α ∈ Ioo (1 / 2) 1) {w w' : ι → ℝ}
    (hmean : ∑ i, w i * P[X i] = ∑ i, w' i * P[X i]) :
    expectedShortfall (fun ω ↦ ∑ i, w i * X i ω) P α ≤
        expectedShortfall (fun ω ↦ ∑ i, w' i * X i ω) P α ↔
      portfolioVarN Finset.univ w (fun i j ↦ cov[X i, X j; P]) ≤
        portfolioVarN Finset.univ w' fun i j ↦ cov[X i, X j; P] := by
  have hα' : α ∈ Ioo 0 1 := ⟨by linarith [hα.1], hα.2⟩
  have h' := map_portfolio_eq_affine hX w'
  rw [← hmean] at h'
  rw [expectedShortfall_le_iff_of_map_eq_affine IsGaussian.integrable_id (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (map_portfolio_eq_affine hX w) h' hα'
    ((zero_lt_valueAtRisk_id_gaussianReal hα).trans_le
      (valueAtRisk_le_expectedShortfall IsGaussian.integrable_id hα')),
    Real.sqrt_le_sqrt_iff (portfolioVarN_gaussian_nonneg hX w')]

/-- **VaR-optimal portfolios are Markowitz portfolios** (QRM Exercise 8.6): on any set of
admissible weights sharing a common expected loss, a portfolio minimizes VaR at a level
`α > 1/2` exactly when it minimizes the Markowitz variance. -/
theorem isMinOn_valueAtRisk_iff_isMinOn_portfolioVarN (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P)
    (hα : α ∈ Ioo (1 / 2) 1) {S : Set (ι → ℝ)} {c : ℝ} (hS : ∀ w ∈ S, ∑ i, w i * P[X i] = c)
    {w₀ : ι → ℝ} (hw₀ : w₀ ∈ S) :
    IsMinOn (fun w ↦ valueAtRisk (fun ω ↦ ∑ i, w i * X i ω) P α) S w₀ ↔
      IsMinOn (fun w ↦ portfolioVarN Finset.univ w fun i j ↦ cov[X i, X j; P]) S w₀ := by
  simp only [isMinOn_iff]
  exact forall₂_congr fun w hw ↦
    valueAtRisk_portfolio_le_iff hX hα ((hS w₀ hw₀).trans (hS w hw).symm)

/-- **ES-optimal portfolios are Markowitz portfolios** (QRM Exercise 8.6): on any set of
admissible weights sharing a common expected loss, a portfolio minimizes ES at a level
`α > 1/2` exactly when it minimizes the Markowitz variance. -/
theorem isMinOn_expectedShortfall_iff_isMinOn_portfolioVarN
    (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (hα : α ∈ Ioo (1 / 2) 1) {S : Set (ι → ℝ)} {c : ℝ}
    (hS : ∀ w ∈ S, ∑ i, w i * P[X i] = c) {w₀ : ι → ℝ} (hw₀ : w₀ ∈ S) :
    IsMinOn (fun w ↦ expectedShortfall (fun ω ↦ ∑ i, w i * X i ω) P α) S w₀ ↔
      IsMinOn (fun w ↦ portfolioVarN Finset.univ w fun i j ↦ cov[X i, X j; P]) S w₀ := by
  simp only [isMinOn_iff]
  exact forall₂_congr fun w hw ↦
    expectedShortfall_portfolio_le_iff hX hα ((hS w₀ hw₀).trans (hS w hw).symm)

/-- **VaR is subadditive on Gaussian portfolio losses** (QRM Exercise 8.4): on the linear space
`{∑ wᵢ Xᵢ}` of a Gaussian vector, `VaR_α(L + L') ≤ VaR_α(L) + VaR_α(L')` at every level
`α ∈ [1/2, 1)`. -/
theorem valueAtRisk_portfolio_add_le (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P)
    (hα : α ∈ Ico (1 / 2) 1) (w w' : ι → ℝ) :
    valueAtRisk (fun ω ↦ ∑ i, w i * X i ω + ∑ i, w' i * X i ω) P α ≤
      valueAtRisk (fun ω ↦ ∑ i, w i * X i ω) P α +
        valueAtRisk (fun ω ↦ ∑ i, w' i * X i ω) P α :=
  valueAtRisk_add_le_of_hasGaussianLaw (hasGaussianLaw_portfolio_pair hX w w')
    ⟨by linarith [hα.1], hα.2⟩ hα.1

/-- **The diversification floor for VaR** (QRM Exercise 6.16): if `d` jointly Gaussian losses have
a common mean `m`, a common standard deviation `σ` and a common correlation `ρ`, their average
has `VaR_α = m + σ √(ρ + (1 − ρ)/d) Φ⁻¹(α)`. As `d` grows the idiosyncratic term `(1 − ρ)/d`
vanishes, but the common term `ρ` does not. -/
theorem valueAtRisk_equal_weight_equicorrelated [Nonempty ι]
    (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) {m σ ρ : ℝ} (hσ : 0 ≤ σ)
    (hmean : ∀ i, P[X i] = m) (hvar : ∀ i, Var[X i; P] = σ ^ 2)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; P] = ρ * σ ^ 2) (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun ω ↦ ∑ i, (Fintype.card ι : ℝ)⁻¹ * X i ω) P α =
      m + σ * √(ρ + (1 - ρ) / Fintype.card ι) * PhiInv α := by
  classical
  have hd : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [valueAtRisk_portfolio_gaussian hX _ hα,
    portfolioVarN_covariance_eq_mul_equicorrelation X (fun i ↦ (hX.eval i).aemeasurable) hvar
      hcov, portfolioVarN_equicorrelation_equal_weights, Real.sqrt_mul (sq_nonneg σ),
    Real.sqrt_sq hσ]
  simp only [hmean, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_inv_cancel₀ hd, one_mul]

end Portfolio

end MathFin
