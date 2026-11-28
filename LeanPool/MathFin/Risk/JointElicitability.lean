/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.Elicitability

/-!
# Joint elicitability of (VaR, ES): a Fissler–Ziegel score

Expected shortfall alone is not elicitable (`not_isElicitable_expectedShortfall`, for this
library's upper-tail `expectedShortfall`), but in the profit sign convention the pair (lower
`α`-quantile, lower-tail expected shortfall) is jointly elicitable: Fissler and Ziegel (2016),
*Higher order elicitability and Osband's principle*, Ann. Statist. 44(4), Corollary 5.5. This file
transcribes their scoring function (5.5) and proves strict consistency of its simplest strictly
consistent member. The loss-convention pair (`valueAtRisk`, `expectedShortfall`) is not treated
here.

## The source formula

Transcribed from the LaTeX source of arXiv:1503.08123v3, Corollary 5.5, equation (5.5). On the
action domain `{x ∈ ℝ² : x₁ ≥ x₂}`,

`S(x₁, x₂, y) = (𝟙{y ≤ x₁} − α) G₁(x₁) − 𝟙{y ≤ x₁} G₁(y)`
`             + G₂(x₂) (x₂ − x₁ + α⁻¹ 𝟙{y ≤ x₁} (x₁ − y)) − 𝒢₂(x₂) + a(y)`,

with `𝒢₂' = G₂`. It is strictly consistent for `(VaR_α, ES_α)` if `G₁` is increasing and `𝒢₂` is
strictly increasing and strictly convex; the paper remarks after Corollary 5.5 that `G₁ = 0` is
allowed. The paper uses the **profit** sign convention: `VaR_α(F) = F⁻¹(α)` is the lower
`α`-quantile and `ES_α(F) = α⁻¹ ∫₀^α VaR_u(F) du` (its (5.1)) averages the *lower* tail, so
`ES_α ≤ VaR_α`. That lower-tail functional is `lowerExpectedShortfall` here. It is the reflection of
the loss-convention `expectedShortfall` of `Risk/ValueAtRisk.lean`, which averages the upper
tail: `lowerExpectedShortfall_eq_neg_expectedShortfall`.

## The member proved

`G₁ = 0`, `a = 0`, `𝒢₂ = G₂ = exp`. With `G₁ = 0` the monotonicity condition linking the two
coordinates disappears, so strict consistency holds on all of `ℝ²`, not only on `x₁ ≥ x₂`. The
proof reduces to the pinball loss: `α⁻¹ 𝟙{y ≤ v}(v − y) − v = α⁻¹ S_α(v, y) − y`, so the expected
score is `exp e · (e − E[Y] + α⁻¹ E[S_α(v, Y)]) − exp e`. The `v`-part is minimized only at the
quantile (`strictlyElicits_pinballLoss`), with minimum value `−ES_α`; what remains,
`exp e · (e − ES_α − 1)`, is minimized only at `e = ES_α` by `1 + t < exp t`.

## Main definitions

* `fisslerZiegelScore`: the Fissler–Ziegel score for `(VaR_α, ES_α)` in the profit convention,
  equation (5.5) of Fissler–Ziegel (2016), for functions `G₁, G₂, 𝒢₂, a`.
* `fisslerZiegelExpScore`: its member with `G₁ = 0`, `𝒢₂ = G₂ = exp` and `a = 0`.
* `lowerExpectedShortfall`: the lower-tail expected shortfall `α⁻¹ ∫₀^α VaR_u(μ) du`, the mean of
  the worst `α`-fraction of outcomes in the profit convention.

## Main results

* `lowerExpectedShortfall_eq_neg_expectedShortfall`: `ES^{lower}_α(μ) = −ES_{1−α}(−Y)` for
  `Y ~ μ`, bridging to the loss-convention `expectedShortfall`.
* `strictlyElicits_fisslerZiegelExpScore`: for `α ∈ (0, 1)` the member strictly elicits, in the
  sense of `StrictlyElicits` at value type `ℝ × ℝ`, the profit-convention pair
  `(quantile μ α, lowerExpectedShortfall μ α)`, over all of `ℝ²`, on probability laws with finite
  mean and unique `α`-quantile.
* `isElicitable_quantile_lowerExpectedShortfall`: the pair is jointly elicitable. Joint
  elicitability is elicitability at value type `ℝ × ℝ`, so `IsElicitable.apply_mixture` gives
  the convexity of the joint level sets (Fissler–Ziegel 2016, Proposition 2.14).

## References

* [T. Fissler and J. F. Ziegel, *Higher order elicitability and Osband's
  principle*][FisslerZiegel2016], Corollary 5.5

## Tags

joint elicitability, Fissler-Ziegel, VaR and ES, scoring function, backtesting expected shortfall,
Osband's principle, MSC 91G70, MSC 62F10, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

variable {α : ℝ}

/-! ### The Fissler–Ziegel scoring family -/

/-- The **Fissler–Ziegel score** for `(VaR_α, ES_α)`, equation (5.5) of Fissler–Ziegel (2016), in
their profit sign convention, for a forecast pair `x = (x₁, x₂)` of VaR and ES and an outcome `y`:
```
(𝟙{y ≤ x₁} − α) G₁(x₁) − 𝟙{y ≤ x₁} G₁(y)
  + G₂(x₂)(x₂ − x₁ + α⁻¹ 𝟙{y ≤ x₁}(x₁ − y)) − 𝒢₂(x₂) + a(y).
```
Their Corollary 5.5 requires `𝒢₂' = G₂`. -/
noncomputable def fisslerZiegelScore (G₁ G₂ 𝒢₂ a : ℝ → ℝ) (α : ℝ) (x : ℝ × ℝ) (y : ℝ) : ℝ :=
  ((if y ≤ x.1 then 1 else 0) - α) * G₁ x.1 - (if y ≤ x.1 then 1 else 0) * G₁ y +
    G₂ x.2 * (x.2 - x.1 + α⁻¹ * (if y ≤ x.1 then 1 else 0) * (x.1 - y)) - 𝒢₂ x.2 + a y

/-- The member of the Fissler–Ziegel family with `G₁ = 0`, `𝒢₂ = G₂ = exp` and `a = 0`. -/
noncomputable def fisslerZiegelExpScore (α : ℝ) : ℝ × ℝ → ℝ → ℝ :=
  fisslerZiegelScore 0 Real.exp Real.exp 0 α

/-- The exponential member through the pinball loss, for `α ≠ 0`:
`S((v, e), y) = exp e · (e − y + α⁻¹ S_α(v, y)) − exp e`. -/
lemma fisslerZiegelExpScore_eq (hα : α ≠ 0) (x : ℝ × ℝ) (y : ℝ) :
    fisslerZiegelExpScore α x y =
      Real.exp x.2 * (x.2 - y + α⁻¹ * pinballLoss α x.1 y) - Real.exp x.2 := by
  rw [fisslerZiegelExpScore, fisslerZiegelScore, pinballLoss_eq_ite]
  simp only [Pi.zero_apply, mul_zero, sub_zero, add_zero]
  congr 2
  field_simp
  split_ifs <;> ring

/-- The **lower-tail expected shortfall** `ES_α(μ) = α⁻¹ ∫₀^α VaR_u(μ) du`, equation (5.1) of
Fissler–Ziegel (2016): the mean of the worst `α`-fraction of outcomes in the profit convention. -/
noncomputable def lowerExpectedShortfall (μ : Measure ℝ) (α : ℝ) : ℝ :=
  α⁻¹ * ∫ u in Ioc 0 α, quantile μ u

/-- At the lower `α`-quantile, the `v`-part of the expected score is minus the lower-tail expected
shortfall: `E[Y] − α⁻¹ E[S_α(VaR_α, Y)] = ES_α`, for `α ∈ (0, 1)` and a law with finite mean. That
this value is the minimum over `v` is `strictlyElicits_pinballLoss`, stated for laws whose
`α`-quantile is unique. -/
lemma integral_sub_inv_mul_integral_pinballLoss {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable id μ) (hα : α ∈ Ioo 0 1) :
    ∫ y, y ∂μ - α⁻¹ * ∫ y, pinballLoss α (quantile μ α) y ∂μ = lowerExpectedShortfall μ α := by
  have hvar (u : ℝ) : valueAtRisk id μ u = quantile μ u := by rw [valueAtRisk, Measure.map_id]
  have h := integral_pinballLoss (P := μ) (X := id) hint hα (quantile μ α)
  simp only [id] at h
  rw [h, ← hvar, rockafellarUryasev_valueAtRisk hint hα, expectedShortfall]
  simp_rw [hvar]
  have hq := integrableOn_valueAtRisk (P := μ) hint
  simp_rw [hvar] at hq
  have hmean : ∫ y, y ∂μ = (∫ u in Ioc 0 α, quantile μ u) + ∫ u in Ioo α 1, quantile μ u := by
    rw [integral_eq_setIntegral_quantile (f := fun y : ℝ ↦ y) (by fun_prop),
      ← Ioc_union_Ioo_eq_Ioo hα.1.le hα.2, setIntegral_union
      (Ioc_disjoint_Ioi_same.mono_right Ioo_subset_Ioi_self) measurableSet_Ioo
      (hq.mono_set fun u hu ↦ ⟨hu.1, hu.2.trans_lt hα.2⟩)
      (hq.mono_set (Ioo_subset_Ioo_left hα.1.le))]
  rw [hmean, lowerExpectedShortfall]
  have h1α : 1 - α ≠ 0 := (sub_pos.2 hα.2).ne'
  have hα0 : α ≠ 0 := hα.1.ne'
  field_simp
  ring

/-- Reflecting both the forecast and the outcome swaps the two sides of the pinball loss, and the
level `α` with `1 − α`. -/
lemma pinballLoss_neg_neg (α v y : ℝ) : pinballLoss (1 - α) (-v) (-y) = pinballLoss α v y := by
  simp only [pinballLoss, sub_sub_cancel, neg_sub_neg]
  ring

/-- **The lower-tail expected shortfall is the reflected expected shortfall**: for a probability
law `μ` with finite mean and `α ∈ (0, 1)`,

  `ES^{lower}_α(μ) = −ES_{1−α}(−Y)`,   `Y ~ μ`,

the profit-convention functional of Fissler–Ziegel is the loss-convention `expectedShortfall` of
the loss `−Y` at level `1 − α`, with its sign flipped. Both sides are the Rockafellar–Uryasev
extremum of the same expected pinball loss (`pinballLoss_neg_neg`): the reflected objective at
`−v` is `α⁻¹ E[S_α(v, Y)] − E[Y]`, minimized at the reflected quantile (`expectedShortfall` at
level `1 − α`) and by `v = quantile μ α` (`integral_pinballLoss_valueAtRisk_le`). -/
theorem lowerExpectedShortfall_eq_neg_expectedShortfall {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable id μ) (hα : α ∈ Ioo 0 1) :
    lowerExpectedShortfall μ α = -expectedShortfall (fun y : ℝ ↦ -y) μ (1 - α) := by
  have hβ : 1 - α ∈ Ioo (0 : ℝ) 1 := ⟨sub_pos.2 hα.2, sub_lt_self _ hα.1⟩
  have hα0 : α ≠ 0 := hα.1.ne'
  have hX : Integrable (fun y : ℝ ↦ -y) μ := hint.neg
  have hvar : valueAtRisk id μ α = quantile μ α := by rw [valueAtRisk, Measure.map_id]
  -- the reflected objective at `-v` is `g v`, built from the expected pinball loss
  have hRU (v : ℝ) : rockafellarUryasev (fun y : ℝ ↦ -y) μ (1 - α) (-v)
      = α⁻¹ * ∫ y, pinballLoss α v y ∂μ - ∫ y, y ∂μ := by
    have h := integral_pinballLoss (P := μ) (X := fun y : ℝ ↦ -y) hX hβ (-v)
    simp only [pinballLoss_neg_neg, sub_sub_cancel] at h
    rw [integral_neg] at h
    rw [h]
    field_simp
    ring
  have hr := integral_sub_inv_mul_integral_pinballLoss hint hα
  have hle := expectedShortfall_le_rockafellarUryasev hX hβ (-quantile μ α)
  rw [hRU] at hle
  -- the reflected VaR is a competitor `-v*` for the pinball minimization
  have hge := rockafellarUryasev_valueAtRisk hX hβ
  have hmin := integral_pinballLoss_valueAtRisk_le (P := μ) (X := id) hint hα
    (-valueAtRisk (fun y : ℝ ↦ -y) μ (1 - α))
  rw [hvar] at hmin
  have := hRU (-valueAtRisk (fun y : ℝ ↦ -y) μ (1 - α))
  rw [neg_neg] at this
  rw [this] at hge
  have hαi : 0 < α⁻¹ := inv_pos.2 hα.1
  have := mul_le_mul_of_nonneg_left hmin hαi.le
  simp only [id] at this
  linarith

/-- **The exponential Fissler–Ziegel score strictly elicits the profit-convention
`(VaR_α, ES_α)`** (Fissler–Ziegel 2016, Corollary 5.5, with `G₁ = 0` and `𝒢₂ = exp`) on the laws
with finite mean whose `α`-quantile is unique: the true pair (lower `α`-quantile, lower-tail
expected shortfall) is the unique minimizer of the expected score over all of `ℝ²`. The paper's
own domain is `A₀ = {x₁ ≥ x₂}`; the extension to all of `ℝ²` is this file's own observation (see
the module docstring), not the paper's claim — `G₁ = 0` removes the term that ties the two
coordinates together. -/
theorem strictlyElicits_fisslerZiegelExpScore (hα : α ∈ Ioo 0 1) :
    StrictlyElicits (fisslerZiegelExpScore α)
      (fun μ ↦ (quantile μ α, lowerExpectedShortfall μ α))
      {μ | IsProbabilityMeasure μ ∧ Integrable id μ ∧ ∀ x, quantile μ α < x → α < cdf μ x} := by
  intro μ hμC
  obtain ⟨hpi, hplt⟩ := strictlyElicits_pinballLoss hα μ hμC
  obtain ⟨hμ, hint, -⟩ := hμC
  have hα0 : α ≠ 0 := hα.1.ne'
  have hint' : Integrable (fun y : ℝ ↦ y) μ := hint
  have hS (v e : ℝ) : fisslerZiegelExpScore α (v, e) = fun y ↦
      Real.exp e * (e - y + α⁻¹ * pinballLoss α v y) - Real.exp e :=
    funext (fisslerZiegelExpScore_eq hα0 (v, e))
  have hA (e : ℝ) : Integrable (fun y : ℝ ↦ e - y) μ := (integrable_const e).sub hint'
  have hB (v : ℝ) : Integrable (fun y ↦ α⁻¹ * pinballLoss α v y) μ := (hpi v).const_mul _
  have hi (v e : ℝ) : Integrable (fun y ↦ e - y + α⁻¹ * pinballLoss α v y) μ :=
    (hA e).add (hB v)
  -- the expected score, in terms of the expected pinball loss
  have hE (v e : ℝ) : ∫ y, fisslerZiegelExpScore α (v, e) y ∂μ =
      Real.exp e * (e - ∫ y, y ∂μ + α⁻¹ * ∫ y, pinballLoss α v y ∂μ) - Real.exp e := by
    rw [hS, integral_sub ((hi v e).const_mul _) (integrable_const _), integral_const_mul,
      integral_add (hA e) (hB v), integral_sub (integrable_const e) hint', integral_const,
      integral_const, integral_const_mul]
    simp
  refine ⟨fun ⟨v, e⟩ ↦ hS v e ▸ ((hi v e).const_mul _).sub (integrable_const _),
    fun ⟨v, e⟩ hne ↦ ?_⟩
  dsimp only at hne ⊢
  have hr := integral_sub_inv_mul_integral_pinballLoss hint hα
  set q := quantile μ α
  set r := lowerExpectedShortfall μ α
  rw [hE, hE]
  -- `D ≥ 0` is the pinball excess, strictly positive off the quantile
  set D := ∫ y, pinballLoss α v y ∂μ - ∫ y, pinballLoss α q y ∂μ
  have hD : 0 ≤ D := by
    rcases eq_or_ne v q with rfl | hv
    · simp [D]
    · exact (sub_pos.2 (hplt v hv)).le
  have hαi : 0 < α⁻¹ := inv_pos.2 hα.1
  -- the strict convexity of `exp`: `1 + t < exp t` off `0` makes `exp t · (t − 1) + 1` strictly
  -- positive, since `exp t · (t − 1) + 1 = exp t · (exp (−t) − (1 − t))`
  have hexp (t : ℝ) (ht : t ≠ 0) : 0 < Real.exp t * (t - 1) + 1 := by
    have hm : Real.exp t * (t - 1) + 1 = Real.exp t * (Real.exp (-t) - (1 - t)) := by
      have h1 : Real.exp t * Real.exp (-t) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      linear_combination (-1 : ℝ) * h1
    rw [hm]
    exact mul_pos (Real.exp_pos t) (by linarith [Real.add_one_lt_exp (neg_ne_zero.2 ht)])
  -- rewrite both sides through `r` and `D`
  have hLHS : Real.exp r * (r - ∫ y, y ∂μ + α⁻¹ * ∫ y, pinballLoss α q y ∂μ) - Real.exp r =
      -Real.exp r := by
    linear_combination (-Real.exp r) * hr
  have hRHS : Real.exp e * (e - ∫ y, y ∂μ + α⁻¹ * ∫ y, pinballLoss α v y ∂μ) - Real.exp e =
      Real.exp e * (e - r - 1) + Real.exp e * (α⁻¹ * D) := by
    simp only [D]; linear_combination (-Real.exp e) * hr
  rw [hLHS, hRHS]
  have hsplit : Real.exp e * (e - r - 1) + Real.exp r =
      Real.exp r * (Real.exp (e - r) * (e - r - 1) + 1) := by
    rw [mul_add, ← mul_assoc, ← Real.exp_add, add_sub_cancel]; ring
  have hED : 0 ≤ Real.exp e * (α⁻¹ * D) := mul_nonneg (Real.exp_pos e).le (mul_nonneg hαi.le hD)
  rcases eq_or_ne e r with he | he
  · have hv : v ≠ q := fun hv ↦ hne (by rw [hv, he])
    have hDpos : 0 < D := sub_pos.2 (hplt v hv)
    have : 0 < Real.exp e * (α⁻¹ * D) := mul_pos (Real.exp_pos e) (mul_pos hαi hDpos)
    rw [he] at this ⊢
    linarith
  · have h1 := hexp (e - r) (sub_ne_zero.2 he)
    have h2 := mul_pos (Real.exp_pos r) h1
    linarith [hsplit]

/-- **The profit-convention pair (lower `α`-quantile, `lowerExpectedShortfall`) is jointly
elicitable** (Fissler–Ziegel 2016, Corollary 5.5) on the laws with finite mean and unique
`α`-quantile, although the (upper-tail, loss-convention) `expectedShortfall` alone is not
(`not_isElicitable_expectedShortfall`). -/
theorem isElicitable_quantile_lowerExpectedShortfall (hα : α ∈ Ioo 0 1) :
    IsElicitable (fun μ ↦ (quantile μ α, lowerExpectedShortfall μ α))
      {μ | IsProbabilityMeasure μ ∧ Integrable id μ ∧ ∀ x, quantile μ α < x → α < cdf μ x} :=
  ⟨_, strictlyElicits_fisslerZiegelExpScore hα⟩

end MathFin
