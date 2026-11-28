/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.Elicitability

/-!
# Expectiles

The **`α`-expectile** of an integrable loss `Y` is the threshold `e` at which the
`α`-weighted expected excess above `e` balances the `(1 − α)`-weighted expected shortfall below
it:

  `α · E[(Y − e)⁺] = (1 − α) · E[(e − Y)⁺]`

(McNeil–Frey–Embrechts, §8.2.6; QRM Exercise Book, Exercises 8.13–8.14). Write
`expectileGap α Y e = α E[(Y − e)⁺] − (1 − α) E[(e − Y)⁺]`. Because `(y − e)⁺ − (e − y)⁺ = y − e`,
the gap equals `(2α − 1)·E[(Y − e)⁺] + (1 − α)(E[Y] − e)`. The map `e ↦ E[(Y − e)⁺]` is
`1`-Lipschitz and antitone, so the gap falls with slope at most `−min(α, 1 − α)`
(`expectileGap_sub_le`). A continuous function falling at a linear rate has exactly one root.
That root is the expectile (`existsUnique_expectileGap_eq_zero`).

Raising the level raises the gap pointwise, since `∂/∂α = E[(Y − e)⁺] + E[(e − Y)⁺] ≥ 0`, so it
moves the root to the right: **expectiles are nondecreasing in the level**
(`expectile_mono`, Exercise 8.13). At the level `1/2` the gap is `(E[Y] − e)/2`, so the
`1/2`-expectile is the mean (`expectile_half`).

For a law with finite second moment the expectile is also the forecast that minimizes the
expected **asymmetric squared loss** `S(e, y) = α ((y − e)⁺)² + (1 − α) ((e − y)⁺)²`
(`expectileLoss`; Newey and Powell, *Asymmetric least squares estimation and testing*,
Econometrica 55 (1987), 819–847). The loss is strongly convex in the forecast with modulus
`min(α, 1 − α)`, and minus half its derivative at `e` is `g = α (y − e)⁺ − (1 − α)(e − y)⁺`
(`expectileLoss_ge`, a pointwise bound). The expectation of `g` is the gap, which vanishes at the
expectile, so integrating the bound there gives
`E[S(e, Y)] ≥ E[S(e_α, Y)] + min(α, 1 − α)(e − e_α)²`. Hence the loss strictly elicits the
expectile, in the sense of `StrictlyElicits` (`Risk/Elicitability.lean`), on the laws with
finite second moment (`strictlyElicits_expectileLoss`). The quantile is elicited by the pinball
loss (`strictlyElicits_pinballLoss`); expected shortfall is not elicitable
(`not_isElicitable_expectedShortfall`). Whether the expectile is a coherent risk measure for
`α ≥ 1/2` is not treated here.

## Main definitions

* `expectileGap`: the gap `α E[(Y − e)⁺] − (1 − α) E[(e − Y)⁺]`, whose root is the expectile.
* `expectile`: the `α`-expectile of `Y`, the infimum of the thresholds with a nonpositive gap.
* `expectileLoss`: the asymmetric squared loss `α ((y − e)⁺)² + (1 − α) ((e − y)⁺)²` of a
  forecast `e` for an outcome `y`.

## Main results

* `expectileGap_sub_le`: the gap falls at rate at least `min(α, 1 − α)`.
* `existsUnique_expectileGap_eq_zero`: for integrable `Y` and `α ∈ (0, 1)`, the gap has a unique
  root.
* `expectileGap_expectile`: for integrable `Y` and `α ∈ (0, 1)`, the expectile is that root.
* `expectile_mono`: expectiles are nondecreasing in the level.
* `expectile_half`: the `1/2`-expectile is the mean.
* `expectileLoss_ge`: a strong-convexity inequality for the asymmetric squared loss.
* `strictlyElicits_expectileLoss`: the asymmetric squared loss strictly elicits the expectile on
  the probability laws with a finite second moment.

## References

* [T. Gneiting, *Making and evaluating point forecasts*][Gneiting2011]
* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Section 8.2.6
* [W. K. Newey and J. L. Powell, *Asymmetric least squares estimation and testing*][NeweyPowell1987]
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 8.13; Ex. 8.13, 8.14

## Tags

expectile, asymmetric least squares, Newey-Powell, asymmetric squared loss, risk measure,
elicitability, MSC 91G70, MSC 62F10, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : Ω → ℝ} {α : ℝ}

/-- The **expectile gap** `α E[(Y − e)⁺] − (1 − α) E[(e − Y)⁺]`, whose root is the
`α`-expectile. -/
noncomputable def expectileGap (α : ℝ) (Y : Ω → ℝ) (P : Measure Ω) (e : ℝ) : ℝ :=
  α * ∫ ω, max (Y ω - e) 0 ∂P - (1 - α) * ∫ ω, max (e - Y ω) 0 ∂P

/-- The **`α`-expectile** of `Y`: the infimum of the thresholds with a nonpositive gap, which is
the unique root of the gap for an integrable `Y` and `α ∈ (0, 1)` (`expectileGap_expectile`). -/
noncomputable def expectile (α : ℝ) (Y : Ω → ℝ) (P : Measure Ω) : ℝ :=
  sInf {e | expectileGap α Y P e ≤ 0}

/-- The gap in terms of the upper partial moment alone:
`(2α − 1)·E[(Y − e)⁺] + (1 − α)(E[Y] − e)`, from `(e − y)⁺ = (y − e)⁺ − (y − e)`. -/
lemma expectileGap_eq (hY : Integrable Y P) (e : ℝ) :
    expectileGap α Y P e =
      (2 * α - 1) * ∫ ω, max (Y ω - e) 0 ∂P + (1 - α) * ((∫ ω, Y ω ∂P) - e) := by
  have hpt : (fun ω ↦ max (e - Y ω) 0) = fun ω ↦ max (Y ω - e) 0 - (Y ω - e) := by
    ext ω
    rcases le_total (Y ω) e with h | h
    · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h)]
      ring
    · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]
      ring
  have hYe : Integrable (fun ω ↦ Y ω - e) P := hY.sub (integrable_const e)
  have hM : Integrable (fun ω ↦ max (Y ω - e) 0) P := hYe.pos_part
  rw [expectileGap, hpt, integral_sub hM hYe,
    integral_sub hY (integrable_const e), integral_const, probReal_univ, one_smul]
  ring

/-- The upper partial moment `e ↦ E[(Y − e)⁺]` is antitone and falls by at most the increment. -/
lemma upperPartialMoment_sub (hY : Integrable Y P) {e e' : ℝ} (h : e ≤ e') :
    0 ≤ (∫ ω, max (Y ω - e) 0 ∂P) - ∫ ω, max (Y ω - e') 0 ∂P ∧
      (∫ ω, max (Y ω - e) 0 ∂P) - ∫ ω, max (Y ω - e') 0 ∂P ≤ e' - e := by
  have hM (e : ℝ) : Integrable (fun ω ↦ max (Y ω - e) 0) P :=
    (hY.sub (integrable_const e)).pos_part
  rw [← integral_sub (hM e) (hM e')]
  refine ⟨integral_nonneg fun ω ↦ sub_nonneg.2 (max_le_max (by linarith) le_rfl), ?_⟩
  calc ∫ ω, (max (Y ω - e) 0 - max (Y ω - e') 0) ∂P ≤ ∫ _, (e' - e) ∂P :=
        integral_mono ((hM e).sub (hM e'))
          (integrable_const _) fun ω ↦ sub_le_iff_le_add.2 <|
            max_le (by linarith [le_max_left (Y ω - e') 0])
              (by linarith [le_max_right (Y ω - e') 0])
    _ = e' - e := by simp

/-- **The gap falls at a linear rate**: for `e ≤ e'`,
`min(α, 1 − α)·(e' − e) ≤ gap(e) − gap(e')`. -/
theorem expectileGap_sub_le (hY : Integrable Y P) {e e' : ℝ} (h : e ≤ e') :
    min α (1 - α) * (e' - e) ≤ expectileGap α Y P e - expectileGap α Y P e' := by
  rw [expectileGap_eq hY, expectileGap_eq hY]
  obtain ⟨h0, h1⟩ := upperPartialMoment_sub hY h
  rcases le_total 0 (2 * α - 1) with hs | hs
  · nlinarith [mul_nonneg hs h0,
      mul_le_mul_of_nonneg_right (min_le_right α (1 - α)) (sub_nonneg.2 h)]
  · nlinarith [mul_le_mul_of_nonpos_left h1 hs,
      mul_le_mul_of_nonneg_right (min_le_left α (1 - α)) (sub_nonneg.2 h)]

/-- The gap is continuous: the upper partial moment is `1`-Lipschitz. -/
lemma continuous_expectileGap (hY : Integrable Y P) : Continuous (expectileGap α Y P) := by
  have hm : Continuous fun e ↦ ∫ ω, max (Y ω - e) 0 ∂P := by
    refine (LipschitzWith.of_dist_le_mul fun e e' ↦ ?_).continuous (K := 1)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rcases le_total e e' with h | h
    · obtain ⟨h0, h1⟩ := upperPartialMoment_sub hY h
      rw [abs_of_nonneg h0, abs_of_nonpos (sub_nonpos.2 h)]
      linarith
    · obtain ⟨h0, h1⟩ := upperPartialMoment_sub hY h
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (sub_nonneg.2 h)]
      linarith
  simp_rw [funext (expectileGap_eq (α := α) hY)]
  fun_prop

/-- **The expectile exists and is unique**: the gap has exactly one root. -/
theorem existsUnique_expectileGap_eq_zero (hY : Integrable Y P) (hα : α ∈ Ioo 0 1) :
    ∃! e, expectileGap α Y P e = 0 := by
  have hc : 0 < min α (1 - α) := lt_min hα.1 (sub_pos.2 hα.2)
  set G := expectileGap α Y P
  set t := |G 0| / min α (1 - α)
  have ht : min α (1 - α) * t = |G 0| := mul_div_cancel₀ _ hc.ne'
  have ht0 : 0 ≤ t := div_nonneg (abs_nonneg _) hc.le
  have hlo : 0 ≤ G (-t) := by
    have := expectileGap_sub_le (α := α) hY (show -t ≤ 0 by linarith)
    linarith [neg_abs_le (G 0)]
  have hhi : G t ≤ 0 := by
    have := expectileGap_sub_le (α := α) hY ht0
    linarith [le_abs_self (G 0)]
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc' (by linarith : -t ≤ t)
    (continuous_expectileGap hY).continuousOn ⟨hhi, hlo⟩
  refine ⟨r, hr, fun r' hr' ↦ ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · nlinarith [expectileGap_sub_le (α := α) hY h.le, mul_pos hc (sub_pos.2 h)]
  · nlinarith [expectileGap_sub_le (α := α) hY h.le, mul_pos hc (sub_pos.2 h)]

/-- **The expectile is the root of the gap**: the thresholds with a nonpositive gap are exactly
`[e_α, ∞)`, so their infimum `expectile α Y P` is the root. -/
theorem expectileGap_expectile (hY : Integrable Y P) (hα : α ∈ Ioo 0 1) :
    expectileGap α Y P (expectile α Y P) = 0 := by
  have hc : 0 < min α (1 - α) := lt_min hα.1 (sub_pos.2 hα.2)
  obtain ⟨r, hr, -⟩ := existsUnique_expectileGap_eq_zero hY hα
  have hset : {e | expectileGap α Y P e ≤ 0} = Ici r := by
    ext e
    refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
    · by_contra h
      rw [mem_Ici, not_le] at h
      have he' : expectileGap α Y P e ≤ 0 := he
      nlinarith [expectileGap_sub_le (α := α) hY h.le, mul_pos hc (sub_pos.2 h)]
    · have he' : r ≤ e := he
      change expectileGap α Y P e ≤ 0
      nlinarith [expectileGap_sub_le (α := α) hY he', mul_nonneg hc.le (sub_nonneg.2 he')]
  rw [expectile, hset, csInf_Ici, hr]

/-- **Expectiles are nondecreasing in the level** (QRM Exercise 8.13): raising the level raises
the gap at every threshold, which moves its root to the right. -/
theorem expectile_mono (hY : Integrable Y P) (hα : α ∈ Ioo 0 1) {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (hαβ : α ≤ β) : expectile α Y P ≤ expectile β Y P := by
  set e := expectile α Y P
  have hA : 0 ≤ ∫ ω, max (Y ω - e) 0 ∂P := integral_nonneg fun _ ↦ le_max_right _ _
  have hB : 0 ≤ ∫ ω, max (e - Y ω) 0 ∂P := integral_nonneg fun _ ↦ le_max_right _ _
  have hge : 0 ≤ expectileGap β Y P e := by
    have h := expectileGap_expectile hY hα
    rw [expectileGap] at h ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hαβ) hA, mul_nonneg (sub_nonneg.2 hαβ) hB]
  by_contra hlt
  rw [not_le] at hlt
  have := expectileGap_sub_le (α := β) hY hlt.le
  rw [expectileGap_expectile hY hβ] at this
  nlinarith [mul_pos (lt_min hβ.1 (sub_pos.2 hβ.2)) (sub_pos.2 hlt)]

/-- **The `1/2`-expectile is the mean**: at the level `1/2` the gap is `(E[Y] − e)/2`
(`expectileGap_eq`), whose root is `E[Y]`. -/
theorem expectile_half (hY : Integrable Y P) : expectile (1 / 2) Y P = ∫ ω, Y ω ∂P := by
  have hα : (1 / 2 : ℝ) ∈ Ioo 0 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨r, -, hr⟩ := existsUnique_expectileGap_eq_zero hY hα
  have hmean : expectileGap (1 / 2) Y P (∫ ω, Y ω ∂P) = 0 := by
    rw [expectileGap_eq hY]
    ring
  rw [hr _ (expectileGap_expectile hY hα), hr _ hmean]

/-! ### Elicitability -/

/-- The **asymmetric squared loss** `S(e, y) = α ((y − e)⁺)² + (1 − α) ((e − y)⁺)²` of a forecast
`e` for an outcome `y`. -/
noncomputable def expectileLoss (α e y : ℝ) : ℝ :=
  α * max (y - e) 0 ^ 2 + (1 - α) * max (e - y) 0 ^ 2

/-- **The asymmetric squared loss is strongly convex in the forecast**, with modulus
`min(α, 1 − α)`: moving the forecast from `e` to `e'` raises the loss by at least
`−2 (e' − e) g + min(α, 1 − α)(e' − e)²`, where `g = α (y − e)⁺ − (1 − α)(e − y)⁺` is minus half
the derivative of the loss at `e`. The four cases are the positions of `y` relative to `e` and
`e'`. -/
lemma expectileLoss_ge (e e' y : ℝ) :
    min α (1 - α) * (e' - e) ^ 2 ≤
      expectileLoss α e' y - expectileLoss α e y +
        2 * (e' - e) * (α * max (y - e) 0 - (1 - α) * max (e - y) 0) := by
  have h1 := min_le_left α (1 - α)
  have h2 := min_le_right α (1 - α)
  unfold expectileLoss
  rcases le_total e y with hy | hy <;> rcases le_total e' y with hy' | hy'
  · rw [max_eq_left (sub_nonneg.2 hy), max_eq_right (sub_nonpos.2 hy),
      max_eq_left (sub_nonneg.2 hy'), max_eq_right (sub_nonpos.2 hy')]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (e' - e))]
  · rw [max_eq_left (sub_nonneg.2 hy), max_eq_right (sub_nonpos.2 hy),
      max_eq_right (sub_nonpos.2 hy'), max_eq_left (sub_nonneg.2 hy')]
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (e' - y)),
      mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (y - e)),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hy)) (sub_nonneg.2 hy')]
  · rw [max_eq_right (sub_nonpos.2 hy), max_eq_left (sub_nonneg.2 hy),
      max_eq_left (sub_nonneg.2 hy'), max_eq_right (sub_nonpos.2 hy')]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (y - e')),
      mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (e - y)),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hy)) (sub_nonneg.2 hy')]
  · rw [max_eq_right (sub_nonpos.2 hy), max_eq_left (sub_nonneg.2 hy),
      max_eq_right (sub_nonpos.2 hy'), max_eq_left (sub_nonneg.2 hy')]
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (e' - e))]

/-- **The asymmetric squared loss strictly elicits the expectile**: for `α ∈ (0, 1)` and a law
`μ` on `ℝ` with finite second moment, every expected loss `∫ S(e, y) dμ(y)` is finite and the
`α`-expectile of `μ` is its unique minimizer. Integrating `expectileLoss_ge` at the expectile,
where the gap vanishes, gives `E[S(e, Y)] − E[S(e_α, Y)] ≥ min(α, 1 − α)(e − e_α)² > 0` for
`e ≠ e_α`. -/
theorem strictlyElicits_expectileLoss (hα : α ∈ Ioo 0 1) :
    StrictlyElicits (expectileLoss α) (fun μ ↦ expectile α id μ)
      {μ | IsProbabilityMeasure μ ∧ MemLp id 2 μ} := by
  rintro μ ⟨hμ, h2⟩
  have hint : Integrable id μ := h2.integrable one_le_two
  have hp (e : ℝ) : Integrable (fun y : ℝ ↦ max (y - e) 0) μ :=
    (hint.sub (integrable_const e)).pos_part
  have hn (e : ℝ) : Integrable (fun y : ℝ ↦ max (e - y) 0) μ :=
    ((integrable_const e).sub hint).pos_part
  have hp2 (e : ℝ) : Integrable (fun y : ℝ ↦ max (y - e) 0 ^ 2) μ :=
    (h2.sub (memLp_const e)).pos_part.integrable_sq
  have hn2 (e : ℝ) : Integrable (fun y : ℝ ↦ max (e - y) 0 ^ 2) μ :=
    ((memLp_const e).sub h2).pos_part.integrable_sq
  have hS (e : ℝ) : Integrable (expectileLoss α e) μ :=
    ((hp2 e).const_mul α).add ((hn2 e).const_mul (1 - α))
  refine ⟨hS, fun e he ↦ ?_⟩
  have he' : e ≠ expectile α id μ := he
  change ∫ y, expectileLoss α (expectile α id μ) y ∂μ < ∫ y, expectileLoss α e y ∂μ
  set r := expectile α id μ
  have hgap : α * ∫ y, max (y - r) 0 ∂μ - (1 - α) * ∫ y, max (r - y) 0 ∂μ = 0 :=
    expectileGap_expectile hint hα
  have hdiff : Integrable (fun y ↦ expectileLoss α e y - expectileLoss α r y) μ :=
    (hS e).sub (hS r)
  have hg : Integrable (fun y ↦ α * max (y - r) 0 - (1 - α) * max (r - y) 0) μ :=
    ((hp r).const_mul α).sub ((hn r).const_mul (1 - α))
  have hD : ∫ y, (expectileLoss α e y - expectileLoss α r y +
        2 * (e - r) * (α * max (y - r) 0 - (1 - α) * max (r - y) 0)) ∂μ =
      ∫ y, expectileLoss α e y ∂μ - ∫ y, expectileLoss α r y ∂μ := by
    rw [integral_add hdiff (hg.const_mul _), integral_sub (hS e) (hS r), integral_const_mul,
      integral_sub ((hp r).const_mul α) ((hn r).const_mul (1 - α)), integral_const_mul,
      integral_const_mul, hgap, mul_zero, add_zero]
  have hlow : min α (1 - α) * (e - r) ^ 2 ≤
      ∫ y, expectileLoss α e y ∂μ - ∫ y, expectileLoss α r y ∂μ :=
    calc min α (1 - α) * (e - r) ^ 2 = ∫ _, min α (1 - α) * (e - r) ^ 2 ∂μ := by simp
      _ ≤ ∫ y, (expectileLoss α e y - expectileLoss α r y +
            2 * (e - r) * (α * max (y - r) 0 - (1 - α) * max (r - y) 0)) ∂μ :=
          integral_mono (integrable_const _) (hdiff.add (hg.const_mul _))
            fun y ↦ expectileLoss_ge r e y
      _ = _ := hD
  have hpos : 0 < min α (1 - α) * (e - r) ^ 2 :=
    mul_pos (lt_min hα.1 (sub_pos.2 hα.2)) (sq_pos_of_ne_zero (sub_ne_zero.2 he'))
  linarith

end MathFin
