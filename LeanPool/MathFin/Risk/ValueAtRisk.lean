/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.Quantile
public import Mathlib.Algebra.Order.Star.Real

/-!
# Value-at-risk and expected shortfall of a general loss

For a loss `X` on a probability space `(Ω, P)` and a confidence level `α ∈ (0, 1)`:

* **value-at-risk** is the `α`-quantile of the law of `X`,
  `VaR_α(X) = inf {x | α ≤ P(X ≤ x)}` (`valueAtRisk`);
* **expected shortfall** is the average of the value-at-risk over the levels above `α`,
  `ES_α(X) = (1 − α)⁻¹ ∫_α^1 VaR_u(X) du` (`expectedShortfall`).

These are the definitions of McNeil, Frey and Embrechts, *Quantitative Risk Management* (2015),
Definitions 2.8 and 2.12. They apply to every law, including laws with atoms. The closed forms of
`Risk/Gaussian.lean`, written in a quantile parameter `z`, are the Gaussian instances
(`Risk/GaussianValueAtRisk.lean`).

Both functionals depend on `X` only through its law, so every property is a property of the
quantile function (`Probability/Laws/Quantile.lean`). In particular VaR commutes with monotone
lower-semicontinuous maps (`valueAtRisk_comp`). Translation invariance, positive homogeneity and
comonotone additivity are the three instances of that one fact.

Subadditivity of expected shortfall, the one coherence axiom that value-at-risk lacks, is in
`Risk/ExpectedShortfall.lean`.

## Main definitions

* `valueAtRisk`: the value-at-risk `VaR_α(X) = inf {x | α ≤ P(X ≤ x)}`, the `α`-quantile of the
  law of the loss `X`.
* `expectedShortfall`: the expected shortfall `ES_α(X) = (1 − α)⁻¹ ∫_α^1 VaR_u(X) du`, the
  average of the value-at-risk over the levels above `α`.

## Main results

* `valueAtRisk_le_iff`: `VaR_α(X) ≤ x ↔ α ≤ P(X ≤ x)`.
* `valueAtRisk_mono`: a loss that is almost surely larger has a larger VaR.
* `valueAtRisk_comp`: `VaR_α(h ∘ X) = h (VaR_α(X))` for monotone lower-semicontinuous `h`.
* `valueAtRisk_add_const`, `valueAtRisk_const_mul`: translation invariance and positive
  homogeneity.
* `valueAtRisk_add_of_comonotone`: VaR is additive for comonotone losses.
* `integrableOn_valueAtRisk`: an integrable loss has an integrable VaR curve.
* `valueAtRisk_le_expectedShortfall`: `VaR_α ≤ ES_α`.
* `expectedShortfall_add_const`, `expectedShortfall_const_mul`, `expectedShortfall_mono`.
* `valueAtRisk_const`, `expectedShortfall_const`: a constant loss is its own VaR and ES.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Proposition 7.20
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 2.8

## Tags

value at risk, expected shortfall, quantile function, VaR, confidence level, comonotone additivity,
tail risk, MSC 91G70, MSC 60E05, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : Ω → ℝ} {α x : ℝ}

/-- **Value-at-risk** of a loss `X` at confidence level `α`: the `α`-quantile of the law of `X`,
`VaR_α(X) = inf {x | α ≤ P(X ≤ x)}`. -/
noncomputable def valueAtRisk (X : Ω → ℝ) (P : Measure Ω) (α : ℝ) : ℝ :=
  quantile (P.map X) α

/-- **Expected shortfall** of a loss `X` at confidence level `α`: the average value-at-risk over
the levels above `α`, `ES_α(X) = (1 − α)⁻¹ ∫_α^1 VaR_u(X) du`. -/
noncomputable def expectedShortfall (X : Ω → ℝ) (P : Measure Ω) (α : ℝ) : ℝ :=
  (1 - α)⁻¹ * ∫ u in Ioo α 1, valueAtRisk X P u

/-- VaR depends on a loss only through its law. -/
lemma valueAtRisk_eq_quantile {μ : Measure ℝ} (hX : HasLaw X μ P) :
    valueAtRisk X P α = quantile μ α := by
  rw [valueAtRisk, hX.map_eq]

variable [IsProbabilityMeasure P]

/-! ### Value-at-risk -/

/-- The Galois connection for VaR: `VaR_α(X) ≤ x ↔ α ≤ P(X ≤ x)`. -/
theorem valueAtRisk_le_iff (hX : AEMeasurable X P) (hα : α ∈ Ioo 0 1) :
    valueAtRisk X P α ≤ x ↔ α ≤ P.real {ω | X ω ≤ x} := by
  rw [valueAtRisk, quantile_le_iff hα, cdf_eq_real,
    map_measureReal_apply_of_aemeasurable hX measurableSet_Iic]
  rfl

/-- `x < VaR_α(X) ↔ P(X ≤ x) < α`. -/
theorem lt_valueAtRisk_iff (hX : AEMeasurable X P) (hα : α ∈ Ioo 0 1) :
    x < valueAtRisk X P α ↔ P.real {ω | X ω ≤ x} < α := by
  simpa only [not_le] using (valueAtRisk_le_iff hX hα).not

/-- The loss stays at or below its VaR with probability at least `α`. -/
lemma le_measureReal_le_valueAtRisk (hX : AEMeasurable X P) (hα : α ∈ Ioo 0 1) :
    α ≤ P.real {ω | X ω ≤ valueAtRisk X P α} :=
  (valueAtRisk_le_iff hX hα).1 le_rfl

/-- **Monotonicity**: a loss that is almost surely larger has a larger VaR. -/
theorem valueAtRisk_mono (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (hXY : X ≤ᵐ[P] Y)
    (hα : α ∈ Ioo 0 1) : valueAtRisk X P α ≤ valueAtRisk Y P α :=
  (valueAtRisk_le_iff hX hα).2 <| (le_measureReal_le_valueAtRisk hY hα).trans <|
    ENNReal.toReal_mono (measure_ne_top _ _) <| measure_mono_ae <|
      hXY.mono fun _ h hy ↦ h.trans hy

/-- **VaR commutes with monotone lower-semicontinuous maps**: `VaR_α(h ∘ X) = h (VaR_α(X))`
(McNeil–Frey–Embrechts, Proposition A.3). -/
theorem valueAtRisk_comp (hX : AEMeasurable X P) {h : ℝ → ℝ} (hmono : Monotone h)
    (hlsc : LowerSemicontinuous h) (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun ω ↦ h (X ω)) P α = h (valueAtRisk X P α) := by
  rw [valueAtRisk, valueAtRisk, ← quantile_map hmono hlsc hα,
    AEMeasurable.map_map_of_aemeasurable hmono.measurable.aemeasurable hX]
  rfl

/-- **Translation invariance**: `VaR_α(X + m) = VaR_α(X) + m`. -/
theorem valueAtRisk_add_const (hX : AEMeasurable X P) (hα : α ∈ Ioo 0 1) (m : ℝ) :
    valueAtRisk (fun ω ↦ X ω + m) P α = valueAtRisk X P α + m :=
  valueAtRisk_comp (h := fun x ↦ x + m) hX (monotone_id.add_const m)
    (continuous_add_const m).lowerSemicontinuous hα

/-- **Positive homogeneity**: `VaR_α(c X) = c VaR_α(X)` for `c ≥ 0`. -/
theorem valueAtRisk_const_mul (hX : AEMeasurable X P) (hα : α ∈ Ioo 0 1) {c : ℝ} (hc : 0 ≤ c) :
    valueAtRisk (fun ω ↦ c * X ω) P α = c * valueAtRisk X P α :=
  valueAtRisk_comp (h := fun x ↦ c * x) hX (fun _ _ h ↦ mul_le_mul_of_nonneg_left h hc)
    (continuous_const_mul c).lowerSemicontinuous hα

/-- **VaR is comonotone additive**: losses that are monotone lower-semicontinuous functions of a
common risk factor `Z` have additive VaR. -/
theorem valueAtRisk_add_of_comonotone {Z : Ω → ℝ} (hZ : AEMeasurable Z P) {f g : ℝ → ℝ}
    (hf : Monotone f) (hf' : LowerSemicontinuous f) (hg : Monotone g)
    (hg' : LowerSemicontinuous g) (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun ω ↦ f (Z ω) + g (Z ω)) P α =
      valueAtRisk (fun ω ↦ f (Z ω)) P α + valueAtRisk (fun ω ↦ g (Z ω)) P α := by
  rw [valueAtRisk_comp hZ (hf.add hg) (hf'.add hg') hα, valueAtRisk_comp hZ hf hf' hα,
    valueAtRisk_comp hZ hg hg' hα]

/-- VaR is additive over a loss and an increasing affine image of it,
`VaR_α(X + (aX + b)) = VaR_α(X) + VaR_α(aX + b)` for `a ≥ 0` (MFE Exercise 2.8). -/
theorem valueAtRisk_add_affine (hX : AEMeasurable X P) (hα : α ∈ Ioo 0 1) {a : ℝ} (ha : 0 ≤ a)
    (b : ℝ) :
    valueAtRisk (fun ω ↦ X ω + (a * X ω + b)) P α =
      valueAtRisk X P α + valueAtRisk (fun ω ↦ a * X ω + b) P α :=
  valueAtRisk_add_of_comonotone (f := fun x ↦ x) (g := fun x ↦ a * x + b) hX monotone_id
    continuous_id.lowerSemicontinuous
    ((monotone_id.const_mul ha).add_const b)
    (by fun_prop : Continuous fun x ↦ a * x + b).lowerSemicontinuous hα

/-! ### Expected shortfall -/

/-- An integrable loss has an integrable VaR curve on `(0, 1)`. -/
theorem integrableOn_valueAtRisk (hX : Integrable X P) :
    IntegrableOn (fun u ↦ valueAtRisk X P u) (Ioo 0 1) := by
  exact (integrableOn_comp_quantile_iff (f := id) aestronglyMeasurable_id).2 <|
    (integrable_map_measure aestronglyMeasurable_id hX.aemeasurable).2 hX

omit [IsProbabilityMeasure P] in
/-- The VaR curve is monotone in the confidence level. -/
lemma valueAtRisk_mono_level (hα : α ∈ Ioo 0 1) {β : ℝ} (hβ : β ∈ Ioo 0 1) (hαβ : α ≤ β) :
    valueAtRisk X P α ≤ valueAtRisk X P β :=
  monotoneOn_quantile hα hβ hαβ

/-- **ES dominates VaR**: `VaR_α(X) ≤ ES_α(X)`, since the average is taken over the levels where
the VaR curve is at least `VaR_α(X)`. -/
theorem valueAtRisk_le_expectedShortfall (hX : Integrable X P) (hα : α ∈ Ioo 0 1) :
    valueAtRisk X P α ≤ expectedShortfall X P α := by
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  rw [expectedShortfall, le_inv_mul_iff₀ h1α]
  calc (1 - α) * valueAtRisk X P α = ∫ _ in Ioo α 1, valueAtRisk X P α := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hα.2.le, smul_eq_mul]
    _ ≤ ∫ u in Ioo α 1, valueAtRisk X P u :=
        setIntegral_mono_on (integrableOn_const (by simp))
          ((integrableOn_valueAtRisk hX).mono_set (Ioo_subset_Ioo_left hα.1.le))
          measurableSet_Ioo fun u hu ↦
            valueAtRisk_mono_level hα ⟨hα.1.trans hu.1, hu.2⟩ hu.1.le

/-- **Translation invariance** of ES: `ES_α(X + m) = ES_α(X) + m`. -/
theorem expectedShortfall_add_const (hX : Integrable X P) (hα : α ∈ Ioo 0 1) (m : ℝ) :
    expectedShortfall (fun ω ↦ X ω + m) P α = expectedShortfall X P α + m := by
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  have hint : IntegrableOn (fun u ↦ valueAtRisk X P u) (Ioo α 1) :=
    (integrableOn_valueAtRisk hX).mono_set (Ioo_subset_Ioo_left hα.1.le)
  rw [expectedShortfall, expectedShortfall,
    setIntegral_congr_fun measurableSet_Ioo fun u hu ↦
      valueAtRisk_add_const hX.aemeasurable ⟨hα.1.trans hu.1, hu.2⟩ m,
    integral_add hint (integrableOn_const (by simp)), setIntegral_const,
    Real.volume_real_Ioo_of_le hα.2.le, smul_eq_mul]
  field_simp

/-- **Positive homogeneity** of ES: `ES_α(c X) = c ES_α(X)` for `c ≥ 0`. -/
theorem expectedShortfall_const_mul (hX : Integrable X P) (hα : α ∈ Ioo 0 1) {c : ℝ}
    (hc : 0 ≤ c) : expectedShortfall (fun ω ↦ c * X ω) P α = c * expectedShortfall X P α := by
  rw [expectedShortfall, expectedShortfall,
    setIntegral_congr_fun measurableSet_Ioo fun u hu ↦
      valueAtRisk_const_mul hX.aemeasurable ⟨hα.1.trans hu.1, hu.2⟩ hc,
    integral_const_mul]
  ring

/-- **Monotonicity** of ES: a loss that is almost surely larger has a larger ES. -/
theorem expectedShortfall_mono (hX : Integrable X P) (hY : Integrable Y P) (hXY : X ≤ᵐ[P] Y)
    (hα : α ∈ Ioo 0 1) : expectedShortfall X P α ≤ expectedShortfall Y P α := by
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  refine mul_le_mul_of_nonneg_left (setIntegral_mono_on
    ((integrableOn_valueAtRisk hX).mono_set (Ioo_subset_Ioo_left hα.1.le))
    ((integrableOn_valueAtRisk hY).mono_set (Ioo_subset_Ioo_left hα.1.le)) measurableSet_Ioo
    fun u hu ↦ valueAtRisk_mono hX.aemeasurable hY.aemeasurable hXY ⟨hα.1.trans hu.1, hu.2⟩)
    (inv_nonneg.2 h1α.le)

/-- The value-at-risk of a constant loss is the constant. -/
theorem valueAtRisk_const (c : ℝ) (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun _ ↦ c) P α = c := by
  rw [valueAtRisk, Measure.map_const, measure_univ, one_smul, quantile_dirac c hα]

/-- The expected shortfall of a constant loss is the constant. -/
theorem expectedShortfall_const (c : ℝ) (hα : α ∈ Ioo 0 1) :
    expectedShortfall (fun _ ↦ c) P α = c := by
  have h1α : (1 - α) ≠ 0 := (sub_pos.2 hα.2).ne'
  rw [expectedShortfall, setIntegral_congr_fun measurableSet_Ioo
    fun u hu ↦ valueAtRisk_const (P := P) c ⟨hα.1.trans hu.1, hu.2⟩, setIntegral_const,
    Real.volume_real_Ioo_of_le hα.2.le, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h1α, one_mul]

end MathFin
