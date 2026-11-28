/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.Gaussian
public import LeanPool.MathFin.Risk.GaussianExpectedShortfall
public import LeanPool.MathFin.Risk.GaussianValueAtRisk

/-!
# Coherence of Gaussian value-at-risk and expected shortfall

The closed forms `gaussianVaR μ σ z = μ + σ z` and `gaussianCVaR μ σ z α = μ + σ ϕ(z)/(1 − α)`
(`Risk/Gaussian.lean`) are the value-at-risk and the expected shortfall of a loss
`L ~ N(μ, σ²)` at the normal quantile `z = Φ⁻¹(α)` (`valueAtRisk_of_hasLaw_gaussianReal`,
`expectedShortfall_of_hasLaw_gaussianReal`). This file records how the four axioms of Artzner,
Delbaen, Eber and Heath (1999) read on them.

**Expected shortfall.** It is coherent on every integrable loss, Gaussian or not
(`expectedShortfall_isCoherentRiskMeasure`, an instance of the library's one coherence structure
`IsCoherentRiskMeasure`). Translation, homogeneity and monotonicity of Gaussian expected shortfall
need nothing Gaussian: they are the structure's axioms. What the Gaussian family adds is the closed
form of the sum. A jointly Gaussian pair has a Gaussian sum, so the structure's
`ES(X + Y) ≤ ES X + ES Y` is the parameter inequality `gaussianCVaR_sd_add_le`, with the variance of
the sum in the volatility slot.
**Value-at-risk.** It is not coherent in general (`Risk/VaRSuperadditivity.lean`), but on a
jointly Gaussian pair at a level `α ≥ 1/2` it is subadditive
(`valueAtRisk_add_le_of_hasGaussianLaw` there), because `VaR = E + sd Φ⁻¹(α)` and the standard
deviation is subadditive (`sqrt_variance_add_le`).

**The random-variable side.** For a Gaussian loss `X`, the Gaussian laws of the affine images
`X + c` and `λ X` (`gaussianReal_add_const`, `gaussianReal_const_mul`) turn the value-at-risk and
the expected shortfall of the image into the closed forms at the transformed parameters, and the
parameter identities below finish the proofs:
`valueAtRisk_add_const_of_hasGaussianLaw`, `valueAtRisk_const_mul_of_hasGaussianLaw`,
`expectedShortfall_add_const_of_hasGaussianLaw`, `expectedShortfall_const_mul_of_hasGaussianLaw`.
(Translation and homogeneity of VaR and ES hold for every loss, `valueAtRisk_add_const`,
`expectedShortfall_add_const`; what these state is that the closed form is carried along.)

**The parameter formulas.** `gaussianVaR_translation`, `gaussianCVaR_translation`,
`gaussianVaR_positiveHomogeneity`, `gaussianCVaR_positiveHomogeneity`, `gaussianVaR_monotone_mean`,
`gaussianCVaR_monotone_mean`, `joint_stdev_le`, `gaussianVaR_subadditive` and
`gaussianCVaR_subadditive` are identities and inequalities about the two real functions `μ + σ z`
and `μ + σ ϕ(z)/(1 − α)` on all real parameters, including `σ < 0` and `α ≥ 1`, where neither is
the risk measure of any law. They stay as parameter algebra for that reason, and the translation
and homogeneity ones are the lemmas the random-variable theorems consume. Monotonicity in the mean
orders the parameters at equal volatility, not random variables, so it keeps its parameter form.
In `gaussianVaR_subadditive` and `gaussianCVaR_subadditive` the correlation `ρ` is a free parameter;
`valueAtRisk_add_le_of_hasGaussianLaw` and `gaussianCVaR_sd_add_le` are the statements at the
correlation a pair actually has.

## Main results

* `gaussianCVaR_sd_add_le`: the closed-form CVaR of a jointly Gaussian pair is subadditive, with
  the exact volatility of the sum; a corollary of the coherence of expected shortfall.
* `joint_stdev_le`: `√(σ₁² + 2 ρ σ₁ σ₂ + σ₂²) ≤ σ₁ + σ₂` for `ρ ≤ 1` and `σ_i ≥ 0`.
* The parameter formulas listed above, and the four random-variable theorems that consume the
  translation and homogeneity ones.

## References

* [C. Acerbi and D. Tasche, *On the coherence of expected shortfall*][AcerbiTasche2002]
* [P. Artzner et al., *Coherent measures of risk*][ArtznerDelbaenEberHeath1999]
* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Ch 2.3

## Tags

coherence of VaR, expected shortfall coherence, Gaussian VaR, subadditivity,
jointly Gaussian losses, translation invariance, MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

open Real MeasureTheory Set ProbabilityTheory

/-- **VaR translation invariance**: `VaR(L + c) = VaR(L) + c`. -/
lemma gaussianVaR_translation (μ σ z c : ℝ) :
    gaussianVaR (μ + c) σ z = gaussianVaR μ σ z + c := by
  unfold gaussianVaR; ring

/-- **CVaR translation invariance**: `CVaR(L + c) = CVaR(L) + c`. -/
lemma gaussianCVaR_translation (μ σ z α c : ℝ) :
    gaussianCVaR (μ + c) σ z α = gaussianCVaR μ σ z α + c := by
  unfold gaussianCVaR; ring

/-- **VaR positive homogeneity**: `VaR(λ·L) = λ·VaR(L)` for `λ ≥ 0`. The volatility
scales by `|λ|·σ`, so the hypothesis `0 ≤ λ` is load-bearing (it discharges `|λ| = λ`). -/
lemma gaussianVaR_positiveHomogeneity (μ σ z : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    gaussianVaR (l * μ) (|l| * σ) z = l * gaussianVaR μ σ z := by
  unfold gaussianVaR; rw [abs_of_nonneg hl]; ring

/-- **CVaR positive homogeneity**: `CVaR(λ·L) = λ·CVaR(L)` for `λ ≥ 0` (volatility
scales by `|λ|·σ`, so `0 ≤ λ` is load-bearing). -/
lemma gaussianCVaR_positiveHomogeneity (μ σ z α : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    gaussianCVaR (l * μ) (|l| * σ) z α = l * gaussianCVaR μ σ z α := by
  unfold gaussianCVaR; rw [abs_of_nonneg hl]; ring

/-- **VaR monotonicity in mean** at the same volatility and right-tail quantile:
if `μ₁ ≤ μ₂` and `σ ≥ 0`, then `VaR(L₁) ≤ VaR(L₂)`. -/
lemma gaussianVaR_monotone_mean {μ₁ μ₂ σ z : ℝ}
    (hμ : μ₁ ≤ μ₂) :
    gaussianVaR μ₁ σ z ≤ gaussianVaR μ₂ σ z := by
  unfold gaussianVaR
  linarith

/-- **CVaR monotonicity in mean** at the same volatility: if `μ₁ ≤ μ₂`, then
`CVaR(L₁) ≤ CVaR(L₂)`. -/
lemma gaussianCVaR_monotone_mean {μ₁ μ₂ σ z α : ℝ}
    (hμ : μ₁ ≤ μ₂) :
    gaussianCVaR μ₁ σ z α ≤ gaussianCVaR μ₂ σ z α := by
  unfold gaussianCVaR
  linarith

/-- **Joint-standard-deviation triangle inequality**:
`√(σ₁² + 2 ρ σ₁ σ₂ + σ₂²) ≤ σ₁ + σ₂` whenever `ρ ≤ 1` and `σ_i ≥ 0`. This is
the substantive inequality behind gaussian subadditivity. -/
lemma joint_stdev_le {σ₁ σ₂ ρ : ℝ}
    (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) (hρ : ρ ≤ 1) :
    Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2) ≤ σ₁ + σ₂ := by
  have h_sum_sq : σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2 ≤ (σ₁ + σ₂) ^ 2 := by
    have h_prod : 0 ≤ σ₁ * σ₂ := mul_nonneg h₁ h₂
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ) h_prod]
  have h_sum_nn : 0 ≤ σ₁ + σ₂ := add_nonneg h₁ h₂
  have : Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2) ≤
      Real.sqrt ((σ₁ + σ₂) ^ 2) := Real.sqrt_le_sqrt h_sum_sq
  rwa [Real.sqrt_sq h_sum_nn] at this

/-- **Gaussian VaR subadditivity**: for joint-gaussian `L₁ + L₂ ~ N(μ₁ + μ₂, σ₊²)`
with `σ₊ = √(σ₁² + 2 ρ σ₁ σ₂ + σ₂²)` and `ρ ≤ 1`, `σ_i ≥ 0`, `z ≥ 0`:
`VaR(L₁ + L₂) ≤ VaR(L₁) + VaR(L₂)`. -/
lemma gaussianVaR_subadditive {μ₁ μ₂ σ₁ σ₂ ρ z : ℝ}
    (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) (hρ : ρ ≤ 1) (hz : 0 ≤ z) :
    gaussianVaR (μ₁ + μ₂)
        (Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2)) z ≤
      gaussianVaR μ₁ σ₁ z + gaussianVaR μ₂ σ₂ z := by
  unfold gaussianVaR
  have h_stdev : Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2) ≤ σ₁ + σ₂ :=
    joint_stdev_le h₁ h₂ hρ
  nlinarith

/-- **Gaussian CVaR subadditivity**: same setup as `gaussianVaR_subadditive`,
plus the level `α < 1`. -/
lemma gaussianCVaR_subadditive {μ₁ μ₂ σ₁ σ₂ ρ z α : ℝ}
    (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) (hρ : ρ ≤ 1) (hα : α < 1) :
    gaussianCVaR (μ₁ + μ₂)
        (Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2)) z α ≤
      gaussianCVaR μ₁ σ₁ z α + gaussianCVaR μ₂ σ₂ z α := by
  unfold gaussianCVaR
  have h_stdev : Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2) ≤ σ₁ + σ₂ :=
    joint_stdev_le h₁ h₂ hρ
  have h_one_alpha : 0 < 1 - α := by linarith
  have h_pdf_nn : 0 ≤ gaussianPDFReal 0 1 z := gaussianPDFReal_nonneg _ _ _
  have h_factor_nn : 0 ≤ gaussianPDFReal 0 1 z / (1 - α) :=
    div_nonneg h_pdf_nn h_one_alpha.le
  have h_mul : Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2) *
        (gaussianPDFReal 0 1 z / (1 - α)) ≤
      (σ₁ + σ₂) * (gaussianPDFReal 0 1 z / (1 - α)) :=
    mul_le_mul_of_nonneg_right h_stdev h_factor_nn
  linarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : Ω → ℝ} {α : ℝ}

/-- **Closed-form CVaR is subadditive on jointly Gaussian losses**: for a jointly Gaussian pair
`(X, Y)` (degenerate margins allowed), the closed form `gaussianCVaR` at the
mean `E X + E Y` and the standard deviation of `X + Y` is at most the sum of the closed forms at
the margins. It is the subadditivity of expected shortfall (`expectedShortfall_add_le`) read
through the Gaussian laws of `X`, `Y` and `X + Y`. -/
theorem gaussianCVaR_sd_add_le (h : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) (hα : α ∈ Ioo 0 1) :
    gaussianCVaR (P[X] + P[Y]) √Var[fun ω ↦ X ω + Y ω; P] (PhiInv α) α ≤
      gaussianCVaR P[X] √Var[X; P] (PhiInv α) α + gaussianCVaR P[Y] √Var[Y; P] (PhiInv α) α := by
  have := h.isProbabilityMeasure
  have key := expectedShortfall_add_le h.fst.integrable h.snd.integrable hα
  rwa [expectedShortfall_of_hasGaussianLaw h.fun_add hα,
    expectedShortfall_of_hasGaussianLaw h.fst hα, expectedShortfall_of_hasGaussianLaw h.snd hα,
    integral_add h.fst.integrable h.snd.integrable] at key

/-! ### The random-variable side: the affine images of a Gaussian loss -/

/-- A Gaussian loss, as the law `N(E X, Var X)` of `Risk/Gaussian.lean`. -/
lemma hasLaw_gaussianReal_of_hasGaussianLaw (hX : HasGaussianLaw X P) :
    HasLaw X (gaussianReal P[X] Var[X; P].toNNReal) P :=
  ⟨hX.aemeasurable, hX.map_eq_gaussianReal⟩

/-- **Translation of a Gaussian loss**, through the Gaussian law `N(E X + c, Var X)` of `X + c`:
`VaR_α(X + c) = gaussianVaR (E X) (sd X) Φ⁻¹(α) + c`. The location shift of
`gaussianVaR_translation`, read as the value-at-risk of the shifted loss. -/
theorem valueAtRisk_add_const_of_hasGaussianLaw (hX : HasGaussianLaw X P) (hα : α ∈ Ioo 0 1)
    (c : ℝ) :
    valueAtRisk (fun ω ↦ X ω + c) P α = gaussianVaR P[X] √Var[X; P] (PhiInv α) + c := by
  rw [valueAtRisk_of_hasLaw_gaussianReal
    (gaussianReal_add_const (hasLaw_gaussianReal_of_hasGaussianLaw hX) c) hα,
    Real.coe_toNNReal _ (variance_nonneg X P), gaussianVaR_translation]

/-- **Positive homogeneity of a Gaussian loss**, through the Gaussian law
`N(λ E X, λ² Var X)` of `λ X`: `VaR_α(λ X) = λ · gaussianVaR (E X) (sd X) Φ⁻¹(α)` for `λ ≥ 0`. The
scaling of `gaussianVaR_positiveHomogeneity`, read as the value-at-risk of the scaled loss. -/
theorem valueAtRisk_const_mul_of_hasGaussianLaw (hX : HasGaussianLaw X P) (hα : α ∈ Ioo 0 1)
    {l : ℝ} (hl : 0 ≤ l) :
    valueAtRisk (fun ω ↦ l * X ω) P α = l * gaussianVaR P[X] √Var[X; P] (PhiInv α) := by
  rw [valueAtRisk_of_hasLaw_gaussianReal
    (gaussianReal_const_mul (hasLaw_gaussianReal_of_hasGaussianLaw hX) l) hα,
    NNReal.coe_mul, NNReal.coe_mk, Real.sqrt_mul (sq_nonneg l), Real.sqrt_sq_eq_abs,
    Real.coe_toNNReal _ (variance_nonneg X P), gaussianVaR_positiveHomogeneity _ _ _ hl]

/-- **Translation of a Gaussian loss**, expected shortfall: `ES_α(X + c) =
gaussianCVaR (E X) (sd X) Φ⁻¹(α) α + c`, the Gaussian law of `X + c` through
`expectedShortfall_of_hasGaussianLaw` and `gaussianCVaR_translation`. -/
theorem expectedShortfall_add_const_of_hasGaussianLaw (hX : HasGaussianLaw X P)
    (hα : α ∈ Ioo 0 1) (c : ℝ) :
    expectedShortfall (fun ω ↦ X ω + c) P α =
      gaussianCVaR P[X] √Var[X; P] (PhiInv α) α + c := by
  have := hX.isProbabilityMeasure
  rw [expectedShortfall_of_hasGaussianLaw
    (gaussianReal_add_const (hasLaw_gaussianReal_of_hasGaussianLaw hX) c).hasGaussianLaw hα,
    variance_add_const hX.aemeasurable.aestronglyMeasurable,
    integral_add hX.integrable (integrable_const c)]
  simp [gaussianCVaR_translation]

/-- **Positive homogeneity of a Gaussian loss**, expected shortfall: `ES_α(λ X) =
λ · gaussianCVaR (E X) (sd X) Φ⁻¹(α) α` for `λ ≥ 0`, the Gaussian law of `λ X` through
`expectedShortfall_of_hasGaussianLaw` and `gaussianCVaR_positiveHomogeneity`. -/
theorem expectedShortfall_const_mul_of_hasGaussianLaw (hX : HasGaussianLaw X P)
    (hα : α ∈ Ioo 0 1) {l : ℝ} (hl : 0 ≤ l) :
    expectedShortfall (fun ω ↦ l * X ω) P α =
      l * gaussianCVaR P[X] √Var[X; P] (PhiInv α) α := by
  rw [expectedShortfall_of_hasGaussianLaw
    (gaussianReal_const_mul (hasLaw_gaussianReal_of_hasGaussianLaw hX) l).hasGaussianLaw hα,
    variance_const_mul, integral_const_mul, Real.sqrt_mul (sq_nonneg l), Real.sqrt_sq_eq_abs,
    gaussianCVaR_positiveHomogeneity _ _ _ _ hl]

end MathFin
