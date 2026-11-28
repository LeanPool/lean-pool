/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.ValueAtRisk
public import LeanPool.MathFin.Risk.AcceptanceSet
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Order.CompletePartialOrder

/-!
# Expected shortfall is coherent: the Rockafellar–Uryasev theorem for every integrable loss

For an integrable loss `X` and a level `α ∈ (0, 1)`, the **Rockafellar–Uryasev theorem** says that
expected shortfall is the minimum of the one-parameter objective

  `g(c) = c + (1 − α)⁻¹ E[(X − c)⁺]`,

and that the minimum is attained at `c = VaR_α(X)` (`isLeast_rockafellarUryasev`,
`rockafellarUryasev_valueAtRisk`). The Gaussian case is `Risk/RockafellarUryasev.lean`;
this file proves it for every integrable loss, atoms included.

The proof is the Gaussian file's pointwise certificate, moved to quantile coordinates. Under the
quantile transform `E[(X − c)⁺] = ∫₀¹ (q(u) − c)⁺ du` with `q = VaR_·(X)`, and pointwise

  `(q(u) − c)⁺ ≥ (q(u) − c) · 𝟙{u > α}`,

which integrates to `g(c) ≥ ES_α(X)`. At `c = q(α)` the certificate is exact, because `q` is
monotone: the positive part vanishes on `(0, α]` and is the identity on `(α, 1)`. In quantile
coordinates an atom of `X` is a flat stretch of `q`, so the argument needs no case analysis
for atoms.

**Coherence follows in one line per axiom** (`expectedShortfall_isCoherentRiskMeasure`).
Subadditivity, the axiom that value-at-risk fails (`Risk/VaRSuperadditivity.lean`), is
`(a + b)⁺ ≤ a⁺ + b⁺` inside the objective at `c = VaR_α(X) + VaR_α(Y)`. This is the result behind
the Basel III move of market-risk capital from `VaR₉₉` to `ES₉₇.₅`.

**The dual representation** (`isGreatest_integral_mul_expectedShortfall`) says ES is a
worst-case expectation. `ES_α(X)` is the largest value of `E[D·X]` over densities
`0 ≤ D ≤ (1 − α)⁻¹` with `E[D] = 1`. The maximizer loads the tail event `{X > VaR_α(X)}`, plus the
fraction of the atom at `VaR_α(X)` needed to make up mass `1 − α`. The value
`ES_α(X) = (1 − α)⁻¹ (E[X·𝟙{X > q}] + q·(1 − α − P(X > q)))` at `q = VaR_α(X)` is the formula of
Acerbi and Tasche (`expectedShortfall_eq_acerbiTasche`).

## Main definitions

* `rockafellarUryasev`: the objective `c ↦ c + (1 − α)⁻¹ E[(X − c)⁺]` of a loss `X` at level
  `α`.

## Main results

* `isLeast_rockafellarUryasev`: `ES_α(X)` is its minimum; `rockafellarUryasev_valueAtRisk`: the
  minimum is attained at `VaR_α(X)`.
* `expectedShortfall_add_le`: subadditivity of ES.
* `expectedShortfall_isCoherentRiskMeasure`: ES is a coherent risk measure.
* `expectedShortfall_eq_acerbiTasche`: the Acerbi–Tasche formula.
* `expectedShortfall_eq_setIntegral_tail`: without atoms, ES is the mean of the `α`-tail.
* `isGreatest_integral_mul_expectedShortfall`: the dual representation of ES.
* `representingSet_expectedShortfall`: on a finite probability space the ADEH representing set of
  ES is exactly the probability vectors `q` with `qᵢ ≤ (1 − α)⁻¹ P{i}`, the densities bounded by
  `(1 − α)⁻¹`.
* `expectedShortfall_isLUB_representingSet`: on a finite probability space ES is a coherent risk
  measure of `Risk/AcceptanceSet.lean`, so the finite representation theorem
  `coherentRisk_isLUB` applies to it.

## References

* [C. Acerbi and D. Tasche, *On the coherence of expected shortfall*][AcerbiTasche2002]
* [P. Artzner et al., *Coherent measures of risk*][ArtznerDelbaenEberHeath1999]
* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Proposition 8.13; Section 8.1; Section 8.1.3; Section 8.2
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 2.6, 8.2(c); Ex. 8.19; Ex. 8.2(a); Ex. 8.2(b)
* [Rockafellar and Uryasev (2000)][RockafellarUryasev2000]
* [Rockafellar and Uryasev (2002)][RockafellarUryasev2002]

## Tags

expected shortfall, conditional VaR, Rockafellar-Uryasev, tail risk, Acerbi-Tasche,
coherent risk measure, Basel III, dual representation, MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : Ω → ℝ} {α : ℝ}

/-- The **Rockafellar–Uryasev objective** of a loss `X` at level `α`:
`c ↦ c + (1 − α)⁻¹ E[(X − c)⁺]`. -/
noncomputable def rockafellarUryasev (X : Ω → ℝ) (P : Measure Ω) (α c : ℝ) : ℝ :=
  c + (1 - α)⁻¹ * ∫ ω, max (X ω - c) 0 ∂P

variable [IsProbabilityMeasure P]

/-- The expected positive part of `X − c` in quantile coordinates:
`E[(X − c)⁺] = ∫₀¹ (VaR_u(X) − c)⁺ du`. -/
lemma integral_max_sub_eq_setIntegral_valueAtRisk (hX : AEMeasurable X P) (c : ℝ) :
    ∫ ω, max (X ω - c) 0 ∂P = ∫ u in Ioo 0 1, max (valueAtRisk X P u - c) 0 := by
  calc ∫ ω, max (X ω - c) 0 ∂P = ∫ x, max (x - c) 0 ∂P.map X :=
        (integral_map (f := fun x ↦ max (x - c) 0) hX (by fun_prop)).symm
    _ = ∫ u in Ioo 0 1, max (valueAtRisk X P u - c) 0 :=
        integral_eq_setIntegral_quantile (by fun_prop)

/-- `u ↦ (VaR_u(X) − c)⁺` is integrable on `(0, 1)` for an integrable loss. -/
lemma integrableOn_max_valueAtRisk_sub (hX : Integrable X P) (c : ℝ) :
    IntegrableOn (fun u ↦ max (valueAtRisk X P u - c) 0) (Ioo 0 1) :=
  ((integrableOn_valueAtRisk hX).sub (integrableOn_const (by simp))).pos_part

/-- The shortfall part of the objective, integrated over the tail levels:
`∫_α^1 (VaR_u(X) − c) du = ∫_α^1 VaR_u(X) du − (1 − α) c`. -/
private lemma setIntegral_valueAtRisk_sub (hX : Integrable X P) (hα : α ∈ Ioo 0 1) (c : ℝ) :
    ∫ u in Ioo α 1, (valueAtRisk X P u - c) =
      (∫ u in Ioo α 1, valueAtRisk X P u) - (1 - α) * c := by
  rw [integral_sub ((integrableOn_valueAtRisk hX).mono_set (Ioo_subset_Ioo_left hα.1.le))
    (integrableOn_const (by simp)), setIntegral_const, Real.volume_real_Ioo_of_le hα.2.le,
    smul_eq_mul]

/-- **The Rockafellar–Uryasev inequality**: `ES_α(X) ≤ c + (1 − α)⁻¹ E[(X − c)⁺]` for every
threshold `c`. The certificate `(q(u) − c)⁺ ≥ (q(u) − c)·𝟙{u > α}`, integrated over `(0, 1)`. -/
theorem expectedShortfall_le_rockafellarUryasev (hX : Integrable X P) (hα : α ∈ Ioo 0 1)
    (c : ℝ) : expectedShortfall X P α ≤ rockafellarUryasev X P α c := by
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  have hcert : ∫ u in Ioo α 1, (valueAtRisk X P u - c) ≤
      ∫ u in Ioo 0 1, max (valueAtRisk X P u - c) 0 :=
    (setIntegral_mono_on
        (((integrableOn_valueAtRisk hX).sub (integrableOn_const (by simp))).mono_set
          (Ioo_subset_Ioo_left hα.1.le))
        ((integrableOn_max_valueAtRisk_sub hX c).mono_set (Ioo_subset_Ioo_left hα.1.le))
        measurableSet_Ioo fun _ _ ↦ le_max_left _ _).trans <|
      setIntegral_mono_set (integrableOn_max_valueAtRisk_sub hX c)
        (ae_of_all _ fun _ ↦ le_max_right _ _)
        (Filter.Eventually.of_forall fun _ h ↦ Ioo_subset_Ioo_left hα.1.le h)
  rw [setIntegral_valueAtRisk_sub hX hα] at hcert
  rw [rockafellarUryasev, integral_max_sub_eq_setIntegral_valueAtRisk hX.aemeasurable,
    expectedShortfall, inv_mul_le_iff₀ h1α, mul_add, mul_inv_cancel_left₀ h1α.ne']
  linarith

/-- **The Rockafellar–Uryasev objective attains ES at VaR**: at `c = VaR_α(X)` the certificate is
exact, since the VaR curve lies below `VaR_α(X)` on `(0, α]` and above it on `(α, 1)`. -/
theorem rockafellarUryasev_valueAtRisk (hX : Integrable X P) (hα : α ∈ Ioo 0 1) :
    rockafellarUryasev X P α (valueAtRisk X P α) = expectedShortfall X P α := by
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  set q := valueAtRisk X P α
  have hsplit : ∫ u in Ioo 0 1, max (valueAtRisk X P u - q) 0 =
      ∫ u in Ioo α 1, (valueAtRisk X P u - q) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (Ioo_subset_Ioo_left hα.1.le) fun u hu ↦ max_eq_right <| sub_nonpos.2 <|
        valueAtRisk_mono_level hu.1 hα (not_lt.1 fun h ↦ hu.2 ⟨h, hu.1.2⟩)]
    exact setIntegral_congr_fun measurableSet_Ioo fun u hu ↦ max_eq_left <| sub_nonneg.2 <|
      valueAtRisk_mono_level hα ⟨hα.1.trans hu.1, hu.2⟩ hu.1.le
  rw [rockafellarUryasev, integral_max_sub_eq_setIntegral_valueAtRisk hX.aemeasurable, hsplit,
    setIntegral_valueAtRisk_sub hX hα, expectedShortfall]
  field_simp
  ring

/-- **The Rockafellar–Uryasev theorem** for an arbitrary integrable loss: `ES_α(X)` is the least
value of `c ↦ c + (1 − α)⁻¹ E[(X − c)⁺]`. The minimizer `c = VaR_α(X)` is named in
`rockafellarUryasev_valueAtRisk`. -/
theorem isLeast_rockafellarUryasev (hX : Integrable X P) (hα : α ∈ Ioo 0 1) :
    IsLeast (range (rockafellarUryasev X P α)) (expectedShortfall X P α) :=
  ⟨⟨_, rockafellarUryasev_valueAtRisk hX hα⟩, by
    rintro _ ⟨c, rfl⟩
    exact expectedShortfall_le_rockafellarUryasev hX hα c⟩

/-! ### Coherence -/

/-- **Subadditivity of expected shortfall**: `ES_α(X + Y) ≤ ES_α(X) + ES_α(Y)`. Evaluate the
Rockafellar–Uryasev objective of `X + Y` at `VaR_α(X) + VaR_α(Y)` and split the positive part,
`(a + b)⁺ ≤ a⁺ + b⁺`. -/
theorem expectedShortfall_add_le (hX : Integrable X P) (hY : Integrable Y P)
    (hα : α ∈ Ioo 0 1) :
    expectedShortfall (fun ω ↦ X ω + Y ω) P α ≤
      expectedShortfall X P α + expectedShortfall Y P α := by
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  set a := valueAtRisk X P α
  set b := valueAtRisk Y P α
  have hXa : Integrable (fun ω ↦ max (X ω - a) 0) P := (hX.sub (integrable_const a)).pos_part
  have hYb : Integrable (fun ω ↦ max (Y ω - b) 0) P := (hY.sub (integrable_const b)).pos_part
  have hsplit : ∫ ω, max (X ω + Y ω - (a + b)) 0 ∂P ≤
      (∫ ω, max (X ω - a) 0 ∂P) + ∫ ω, max (Y ω - b) 0 ∂P := by
    rw [← integral_add hXa hYb]
    refine integral_mono (((hX.add hY).sub (integrable_const _)).pos_part) (hXa.add hYb)
      fun ω ↦ ?_
    rw [max_le_iff]
    exact ⟨by linarith [le_max_left (X ω - a) 0, le_max_left (Y ω - b) 0],
      add_nonneg (le_max_right _ _) (le_max_right _ _)⟩
  calc expectedShortfall (fun ω ↦ X ω + Y ω) P α
      ≤ rockafellarUryasev (fun ω ↦ X ω + Y ω) P α (a + b) :=
        expectedShortfall_le_rockafellarUryasev (hX.add hY) hα _
    _ ≤ rockafellarUryasev X P α a + rockafellarUryasev Y P α b := by
        simp only [rockafellarUryasev]
        have := mul_le_mul_of_nonneg_left hsplit (inv_nonneg.2 h1α.le)
        linarith
    _ = expectedShortfall X P α + expectedShortfall Y P α := by
        rw [rockafellarUryasev_valueAtRisk hX hα, rockafellarUryasev_valueAtRisk hY hα]

/-- **Expected shortfall is a coherent risk measure** on the integrable losses (Acerbi and Tasche
2002; McNeil–Frey–Embrechts, Proposition 8.13 context). -/
theorem expectedShortfall_isCoherentRiskMeasure (hα : α ∈ Ioo 0 1) :
    IsCoherentRiskMeasure P (fun X ↦ expectedShortfall X P α) where
  mono _ _ hX hY hXY := expectedShortfall_mono hX hY hXY hα
  add_const _ hX m := expectedShortfall_add_const hX hα m
  const_mul _ hX _ hc := expectedShortfall_const_mul hX hα hc
  add_le _ _ hX hY := expectedShortfall_add_le hX hY hα

/-! ### The Acerbi–Tasche formula and the dual representation -/

/-- **The Acerbi–Tasche formula**: with `q = VaR_α(X)`,
`ES_α(X) = (1 − α)⁻¹ (E[X·𝟙{X > q}] + q·(1 − α − P(X > q)))`. The correction term is the part of
the atom at `q` that lies in the `α`-tail; it vanishes when `P(X = q) = 0`. -/
theorem expectedShortfall_eq_acerbiTasche (hX : Integrable X P) (hα : α ∈ Ioo 0 1) :
    expectedShortfall X P α =
      (1 - α)⁻¹ * ((∫ ω in {ω | valueAtRisk X P α < X ω}, X ω ∂P) +
        valueAtRisk X P α * (1 - α - P.real {ω | valueAtRisk X P α < X ω})) := by
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  set q := valueAtRisk X P α
  have hmeas : NullMeasurableSet {ω | q < X ω} P :=
    nullMeasurableSet_lt aemeasurable_const hX.aemeasurable
  have hpos : ∫ ω, max (X ω - q) 0 ∂P = (∫ ω in {ω | q < X ω}, X ω ∂P) -
      q * P.real {ω | q < X ω} := by
    rw [show (fun ω ↦ max (X ω - q) 0) = {ω | q < X ω}.indicator (fun ω ↦ X ω - q) from
        funext fun ω ↦ by
          by_cases h : q < X ω
          · rw [indicator_of_mem (show ω ∈ {ω | q < X ω} from h),
              max_eq_left (sub_nonneg.2 h.le)]
          · rw [indicator_of_notMem (show ω ∉ {ω | q < X ω} from h),
              max_eq_right (sub_nonpos.2 (not_lt.1 h))],
      integral_indicator₀ hmeas, integral_sub hX.integrableOn (integrableOn_const (by simp)),
      setIntegral_const, smul_eq_mul, mul_comm]
  rw [← rockafellarUryasev_valueAtRisk hX hα, rockafellarUryasev, hpos]
  field_simp
  ring

/-- **Without atoms the `α`-tail has mass `1 − α`**: if the law of `X` has a continuous CDF, then
`P(X > VaR_α(X)) = 1 − α`. -/
theorem measureReal_valueAtRisk_lt (hX : AEMeasurable X P) (hF : Continuous (cdf (P.map X)))
    (hα : α ∈ Ioo 0 1) : P.real {ω | valueAtRisk X P α < X ω} = 1 - α := by
  rw [show {ω | valueAtRisk X P α < X ω} = X ⁻¹' (Iic (valueAtRisk X P α))ᶜ by ext; simp,
    ← map_measureReal_apply_of_aemeasurable hX measurableSet_Iic.compl,
    probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, valueAtRisk, cdf_quantile hF hα]

/-- **Without atoms ES is the mean of the tail**: if the law of `X` has a continuous CDF, the
correction term of `expectedShortfall_eq_acerbiTasche` vanishes and
`ES_α(X) = (1 − α)⁻¹ E[X·𝟙{X > VaR_α(X)}]`. The tail event has mass `1 − α`
(`measureReal_valueAtRisk_lt`), so this is the mean of `X` over it. -/
theorem expectedShortfall_eq_setIntegral_tail (hX : Integrable X P)
    (hF : Continuous (cdf (P.map X))) (hα : α ∈ Ioo 0 1) :
    expectedShortfall X P α = (1 - α)⁻¹ * ∫ ω in {ω | valueAtRisk X P α < X ω}, X ω ∂P := by
  rw [expectedShortfall_eq_acerbiTasche hX hα, measureReal_valueAtRisk_lt hX.aemeasurable hF hα]
  ring

/-- The mass strictly below the `α`-quantile is at most `α`: under the quantile transform, the
levels whose quantile lies below `quantile μ α` are levels below `α`. -/
lemma measure_Iio_quantile_le {μ : Measure ℝ} [IsProbabilityMeasure μ] (hα : α ∈ Ioo 0 1) :
    μ (Iio (quantile μ α)) ≤ ENNReal.ofReal α :=
  calc μ (Iio (quantile μ α))
      = volume.restrict (Ioo 0 1) {u | quantile μ u < quantile μ α} :=
        ((hasLaw_quantile μ).measure_eq (p := fun x ↦ x < quantile μ α) measurableSet_Iio).symm
    _ = volume ({u | quantile μ u < quantile μ α} ∩ Ioo 0 1) :=
        Measure.restrict_apply' measurableSet_Ioo
    _ ≤ volume (Ioo 0 α) := measure_mono fun u ⟨hu, hu01⟩ ↦
        ⟨hu01.1, lt_of_not_ge fun h ↦ (monotoneOn_quantile hα hu01 h).not_gt hu⟩
    _ = ENNReal.ofReal α := by simp

/-- **ES dominates every stress expectation**: for a density `D` with `0 ≤ D ≤ (1 − α)⁻¹` and
`E[D] = 1`, `E[D·X] ≤ ES_α(X)`. Pointwise `D·X ≤ q·D + (1 − α)⁻¹ (X − q)⁺` with
`q = VaR_α(X)`, and the right side integrates to the Rockafellar–Uryasev objective at `q`. -/
theorem integral_mul_le_expectedShortfall (hX : Integrable X P) (hα : α ∈ Ioo 0 1)
    {D : Ω → ℝ} (hD : AEStronglyMeasurable D P) (hD0 : ∀ᵐ ω ∂P, 0 ≤ D ω)
    (hD1 : ∀ᵐ ω ∂P, D ω ≤ (1 - α)⁻¹) (hDint : ∫ ω, D ω ∂P = 1) :
    ∫ ω, D ω * X ω ∂P ≤ expectedShortfall X P α := by
  set q := valueAtRisk X P α
  have hbdd : ∀ᵐ ω ∂P, ‖D ω‖ ≤ (1 - α)⁻¹ :=
    (hD0.and hD1).mono fun ω h ↦ (Real.norm_of_nonneg h.1).trans_le h.2
  have hDi : Integrable D P := (integrable_const _).mono' hD hbdd
  have hpos : Integrable (fun ω ↦ max (X ω - q) 0) P := (hX.sub (integrable_const q)).pos_part
  calc ∫ ω, D ω * X ω ∂P ≤ ∫ ω, (q * D ω + (1 - α)⁻¹ * max (X ω - q) 0) ∂P :=
        integral_mono_ae (hX.bdd_mul hD hbdd) ((hDi.const_mul q).add (hpos.const_mul _)) <|
          (hD0.and hD1).mono fun ω ⟨h0, h1⟩ ↦ by
            nlinarith [mul_le_mul_of_nonneg_left (le_max_left (X ω - q) 0) h0,
              mul_le_mul_of_nonneg_right h1 (le_max_right (X ω - q) 0)]
    _ = rockafellarUryasev X P α q := by
        rw [integral_add (hDi.const_mul q) (hpos.const_mul _), integral_const_mul,
          integral_const_mul, hDint, mul_one, rockafellarUryasev]
    _ = expectedShortfall X P α := rockafellarUryasev_valueAtRisk hX hα

/-- **The ES-maximizing stress density** is a function of the loss: `(1 − α)⁻¹` on the tail
`{X > q}`, the fraction `β ∈ [0, 1]` of it on the atom `{X = q}` that completes the tail mass to
`1 − α`, and `0` below, where `q = VaR_α(X)`. It makes the pointwise bound of
`integral_mul_le_expectedShortfall` exact: `g(x)·(x − q) = (1 − α)⁻¹ (x − q)⁺` for every `x`. -/
theorem exists_density_integral_mul_eq_expectedShortfall (hX : Integrable X P)
    (hα : α ∈ Ioo 0 1) :
    ∃ g : ℝ → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ (1 - α)⁻¹) ∧
      ∫ ω, g (X ω) ∂P = 1 ∧ ∫ ω, g (X ω) * X ω ∂P = expectedShortfall X P α := by
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  set q := valueAtRisk X P α
  -- the tail above `q` has mass at most `1 − α`, and with the atom at least `1 − α`
  have ha : (P.map X).real (Ioi q) ≤ 1 - α := by
    have hcdf : α ≤ (P.map X).real (Iic q) := (cdf_eq_real (P.map X) q) ▸ le_cdf_quantile hα
    rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    linarith
  have hab : 1 - α ≤ (P.map X).real (Ioi q) + (P.map X).real {q} := by
    have hlt : (P.map X).real (Iio q) ≤ α :=
      ENNReal.toReal_le_of_le_ofReal hα.1.le (measure_Iio_quantile_le hα)
    have hunion : Ioi q ∪ {q} = (Iio q)ᶜ := by
      ext x
      simp only [mem_union, mem_Ioi, mem_singleton_iff, mem_compl_iff, mem_Iio, not_lt]
      constructor
      · rintro (h | rfl)
        exacts [h.le, le_rfl]
      · intro h
        rcases h.lt_or_eq with h | h
        exacts [Or.inl h, Or.inr h.symm]
    rw [← measureReal_union (μ := P.map X)
      (show Disjoint (Ioi q) {q} from disjoint_singleton_right.2 (lt_irrefl q))
      (measurableSet_singleton q), hunion, probReal_compl_eq_one_sub measurableSet_Iio]
    linarith
  obtain ⟨β, hβ0, hβ1, hβb⟩ : ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
      β * (P.map X).real {q} = 1 - α - (P.map X).real (Ioi q) := by
    rcases (measureReal_nonneg (μ := P.map X) (s := {q})).lt_or_eq with hb | hb
    · exact ⟨(1 - α - (P.map X).real (Ioi q)) / (P.map X).real {q},
        div_nonneg (by linarith) hb.le, (div_le_one hb).2 (by linarith),
        div_mul_cancel₀ _ hb.ne'⟩
    · exact ⟨0, le_rfl, zero_le_one, by rw [zero_mul]; linarith⟩
  set g : ℝ → ℝ := fun x ↦
    (1 - α)⁻¹ * ((Ioi q).indicator 1 x + β * ({q} : Set ℝ).indicator 1 x)
  have hg : Measurable g := measurable_const.mul <|
    (measurable_one.indicator measurableSet_Ioi).add <|
      measurable_const.mul (measurable_one.indicator (measurableSet_singleton q))
  have hsum (x : ℝ) : (Ioi q).indicator (1 : ℝ → ℝ) x + β * ({q} : Set ℝ).indicator 1 x ≤ 1 := by
    rcases lt_trichotomy x q with h | rfl | h
    · rw [indicator_of_notMem (show x ∉ Ioi q from not_lt.2 h.le),
        indicator_of_notMem (show x ∉ ({q} : Set ℝ) from h.ne)]
      simp
    · rw [indicator_of_notMem (show q ∉ Ioi q from lt_irrefl q),
        indicator_of_mem (mem_singleton q), Pi.one_apply]
      linarith
    · rw [indicator_of_mem (show x ∈ Ioi q from h),
        indicator_of_notMem (show x ∉ ({q} : Set ℝ) from h.ne'), Pi.one_apply]
      simp
  have hg0 (x : ℝ) : 0 ≤ g x := mul_nonneg (inv_nonneg.2 h1α.le) <|
    add_nonneg (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
      (mul_nonneg hβ0 (indicator_nonneg (fun _ _ ↦ zero_le_one) _))
  have hg1 (x : ℝ) : g x ≤ (1 - α)⁻¹ := mul_le_of_le_one_right (inv_nonneg.2 h1α.le) (hsum x)
  -- the density makes the stress bound exact: `g x · (x − q) = (1 − α)⁻¹ (x − q)⁺`
  have hgx (x : ℝ) : g x * (x - q) = (1 - α)⁻¹ * max (x - q) 0 := by
    rcases lt_trichotomy x q with h | rfl | h
    · rw [max_eq_right (sub_nonpos.2 h.le)]
      simp only [g, indicator_of_notMem (show x ∉ Ioi q from not_lt.2 h.le),
        indicator_of_notMem (show x ∉ ({q} : Set ℝ) from h.ne)]
      ring
    · simp
    · rw [max_eq_left (sub_nonneg.2 h.le)]
      simp only [g, indicator_of_mem (show x ∈ Ioi q from h),
        indicator_of_notMem (show x ∉ ({q} : Set ℝ) from h.ne'), Pi.one_apply]
      ring
  have hgX : Integrable (fun ω ↦ g (X ω)) P :=
    (integrable_const (1 - α)⁻¹).mono' (hg.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ (Real.norm_of_nonneg (hg0 _)).trans_le (hg1 _))
  have hgint : ∫ ω, g (X ω) ∂P = 1 := by
    have h1 : Integrable ((Ioi q).indicator (1 : ℝ → ℝ)) (P.map X) :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
    have h2 : Integrable (({q} : Set ℝ).indicator (1 : ℝ → ℝ)) (P.map X) :=
      (integrable_const (1 : ℝ)).indicator (measurableSet_singleton q)
    rw [← integral_map (f := g) hX.aemeasurable hg.aestronglyMeasurable]
    simp only [g]
    rw [integral_const_mul, integral_add h1 (h2.const_mul β), integral_const_mul,
      integral_indicator_one measurableSet_Ioi, integral_indicator_one (measurableSet_singleton q),
      hβb]
    field_simp
    ring
  have hpos : Integrable (fun ω ↦ max (X ω - q) 0) P := (hX.sub (integrable_const q)).pos_part
  refine ⟨g, hg, hg0, hg1, hgint, ?_⟩
  clear_value g
  calc ∫ ω, g (X ω) * X ω ∂P
      = ∫ ω, (q * g (X ω) + (1 - α)⁻¹ * max (X ω - q) 0) ∂P := by
        congr 1
        ext ω
        rw [← hgx (X ω)]
        ring
    _ = q * ∫ ω, g (X ω) ∂P + (1 - α)⁻¹ * ∫ ω, max (X ω - q) 0 ∂P := by
        rw [integral_add (hgX.const_mul q) (hpos.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = rockafellarUryasev X P α q := by rw [hgint, mul_one, rockafellarUryasev]
    _ = expectedShortfall X P α := rockafellarUryasev_valueAtRisk hX hα

/-- **The dual representation of expected shortfall** (QRM Exercise 8.2): `ES_α(X)` is the
greatest value of `E[D·X]` over the stress densities `0 ≤ D ≤ (1 − α)⁻¹` with `E[D] = 1`. -/
theorem isGreatest_integral_mul_expectedShortfall (hX : Integrable X P) (hα : α ∈ Ioo 0 1) :
    IsGreatest {r | ∃ D : Ω → ℝ, AEStronglyMeasurable D P ∧ (∀ᵐ ω ∂P, 0 ≤ D ω) ∧
      (∀ᵐ ω ∂P, D ω ≤ (1 - α)⁻¹) ∧ ∫ ω, D ω ∂P = 1 ∧ r = ∫ ω, D ω * X ω ∂P}
      (expectedShortfall X P α) := by
  obtain ⟨g, hg, hg0, hg1, hgint, hgX⟩ := exists_density_integral_mul_eq_expectedShortfall hX hα
  refine ⟨⟨fun ω ↦ g (X ω), (hg.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable,
    ae_of_all _ fun _ ↦ hg0 _, ae_of_all _ fun _ ↦ hg1 _, hgint, hgX.symm⟩, ?_⟩
  rintro r ⟨D, hD, hD0, hD1, hDint, rfl⟩
  exact integral_mul_le_expectedShortfall hX hα hD hD0 hD1 hDint

/-- **ES is nondecreasing in the level** (QRM Exercise 8.2b): raising `α` relaxes the bound
`D ≤ (1 − α)⁻¹` on the stress densities, so the dual representation maximizes over a larger set. -/
theorem expectedShortfall_mono_level (hX : Integrable X P) (hα : α ∈ Ioo 0 1) {β : ℝ}
    (hβ : β ∈ Ioo 0 1) (hαβ : α ≤ β) : expectedShortfall X P α ≤ expectedShortfall X P β := by
  obtain ⟨D, hD, hD0, hD1, hDint, hDX⟩ := (isGreatest_integral_mul_expectedShortfall hX hα).1
  rw [hDX]
  exact integral_mul_le_expectedShortfall hX hβ hD hD0
    (hD1.mono fun _ h ↦ h.trans (inv_anti₀ (sub_pos.2 hβ.2) (by linarith))) hDint

/-! ### Finite state spaces: ES in the ADEH framework -/

/-- **The representing set of expected shortfall**: on a finite probability space the ADEH
representing set of `ES_α` is exactly the set of probability vectors `q` with `qᵢ ≤ (1 − α)⁻¹ P{i}`,
that is, the probability densities `q/P` bounded by `(1 − α)⁻¹` (a state of null mass carries no
`q`-mass). `⊇` is the dual bound `integral_mul_le_expectedShortfall` for the density `q/P`;
`⊆` tests the acceptable loss `𝟙{i} − (1 − α)⁻¹ P{i}`, whose shortfall is nonpositive by the
Rockafellar–Uryasev bound at `c = 0`. -/
theorem representingSet_expectedShortfall {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (P : Measure ι) [IsProbabilityMeasure P] (hα : α ∈ Ioo 0 1) :
    representingSet (fun L : ι → ℝ ↦ expectedShortfall L P α) =
      {q | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ ∀ i, q i ≤ (1 - α)⁻¹ * P.real {i}} := by
  classical
  have h1α : 0 < (1 - α)⁻¹ := inv_pos.2 (sub_pos.2 hα.2)
  ext q
  constructor
  · rintro ⟨hq0, hq1, hq⟩
    refine ⟨hq0, hq1, fun i ↦ ?_⟩
    have hint : ∫ ω, max ((Pi.single i 1 : ι → ℝ) ω - 0) 0 ∂P = P.real {i} := by
      have : (fun ω ↦ max ((Pi.single i 1 : ι → ℝ) ω - 0) 0) = Pi.single i 1 := by
        ext ω
        by_cases h : ω = i <;> simp [h]
      rw [this, integral_fintype (μ := P) Integrable.of_finite]
      simp [Pi.single_apply]
    have hZ : expectedShortfall
        (fun j ↦ (Pi.single i 1 : ι → ℝ) j + -((1 - α)⁻¹ * P.real {i})) P α ≤ 0 := by
      rw [expectedShortfall_add_const Integrable.of_finite hα]
      have := expectedShortfall_le_rockafellarUryasev
        (Integrable.of_finite : Integrable ((Pi.single i 1 : ι → ℝ)) P) hα 0
      rw [rockafellarUryasev, hint, zero_add] at this
      linarith
    have h2 : ∑ j, q j * (Pi.single i 1 : ι → ℝ) j = q i := by simp [Pi.single_apply]
    have h3 := hq _ hZ
    rw [Finset.sum_congr rfl fun j _ ↦ mul_add (q j) _ _, Finset.sum_add_distrib, h2,
      ← Finset.sum_mul, hq1, one_mul] at h3
    linarith
  · rintro ⟨hq0, hq1, hqp⟩
    refine ⟨hq0, hq1, fun Z hZ ↦ ?_⟩
    set D : ι → ℝ := fun i ↦ q i / P.real {i} with hD
    have hDp (i : ι) : D i * P.real {i} = q i := by
      by_cases hp : P.real {i} = 0
      · have h := hqp i
        rw [hp, mul_zero] at h
        rw [hp, mul_zero]
        exact (le_antisymm h (hq0 i)).symm
      · exact div_mul_cancel₀ _ hp
    have hDle (i : ι) : D i ≤ (1 - α)⁻¹ := by
      by_cases hp : P.real {i} = 0
      · simpa [hD, hp] using h1α.le
      · exact (div_le_iff₀ (lt_of_le_of_ne measureReal_nonneg (Ne.symm hp))).2 (hqp i)
    have hDint : ∫ ω, D ω ∂P = 1 := by
      rw [integral_fintype (μ := P) Integrable.of_finite]
      simp only [smul_eq_mul]
      rw [← hq1]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]; exact hDp i
    have hle := integral_mul_le_expectedShortfall (Integrable.of_finite : Integrable Z P) hα
      (Integrable.of_finite : Integrable D P).aestronglyMeasurable
      (ae_of_all _ fun i ↦ div_nonneg (hq0 i) measureReal_nonneg) (ae_of_all _ hDle) hDint
    rw [integral_fintype (μ := P) Integrable.of_finite] at hle
    refine le_trans (le_of_eq ?_) (hle.trans hZ)
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_eq_mul]; linear_combination (-(Z i)) * hDp i

/-- **ES has an ADEH representation**: on a finite probability space, `ES_α(L)` is the least upper
bound of the expected losses `∑ qᵢ Lᵢ` over the representing set of `ES_α`
(`coherentRisk_isLUB` applied to `expectedShortfall_isCoherentRiskMeasure`). By
`representingSet_expectedShortfall` that set is the densities bounded by `(1 − α)⁻¹`, the set over
which `isGreatest_integral_mul_expectedShortfall` attains the same supremum. -/
theorem expectedShortfall_isLUB_representingSet {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (P : Measure ι) [IsProbabilityMeasure P] (hα : α ∈ Ioo 0 1)
    (L : ι → ℝ) :
    IsLUB ((fun q ↦ ∑ i, q i * L i) '' representingSet fun L : ι → ℝ ↦ expectedShortfall L P α)
      (expectedShortfall L P α) :=
  coherentRisk_isLUB (expectedShortfall_isCoherentRiskMeasure hα) L

end MathFin
