/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.ExpectedShortfall

/-!
# Elicitability: value-at-risk is elicitable, expected shortfall is not

A functional `T` of laws on `ℝ`, with values in any type `V`, is **elicitable** on a class `C` of
laws if it is the unique minimizer of an expected score: some scoring function `S(x, y)` makes
`T μ` the unique minimizer of `x ↦ ∫ S(x, y) dμ(y)` for every `μ ∈ C` (Gneiting 2011;
McNeil–Frey–Embrechts (2015), §9.3). Real-valued functionals (`V = ℝ`) are the single-valued case;
a **jointly** elicitable pair `(T₁, T₂)` is elicitability at `V = ℝ × ℝ`
(`Risk/JointElicitability.lean`).
Elicitability is what makes a risk forecast comparable with realized losses: competing forecasts
are ranked by their average realized scores (QRM Exercise Book, Exercises 9.5 and 9.16).

* **Elicitable functionals have convex level sets** (`StrictlyElicits.apply_mixture`). If
  `T μ = T ν`, then `T` takes the same value on every mixture of `μ` and `ν` in the class. The
  expected score is affine along a mixture of laws (`integral_mixture`), the property
  `expectedUtility_mix` of `Choice/Utility/VonNeumannMorgenstern.lean` records for expected utility.
  So the common minimizer of the two expected scores also minimizes their mixture.
* **VaR is elicitable** (`strictlyElicits_pinballLoss`). The pinball loss
  `S_α(x, y) = (𝟙{y ≤ x} − α)(x − y)` elicits the `α`-quantile on the laws with finite mean whose
  `α`-quantile is unique. The expected pinball loss is `1 − α` times the Rockafellar–Uryasev
  objective, minus a constant (`integral_pinballLoss`). So VaR minimizing it is the
  Rockafellar–Uryasev theorem of `Risk/ExpectedShortfall.lean`. Uniqueness is the exact
  excess formula `rockafellarUryasev_sub_expectedShortfall`: `g(c) − ES_α(X)` integrates the
  distance of the VaR curve from `c` over the levels on the wrong side of `α`.
* **ES is not elicitable** (`not_isElicitable_expectedShortfall`). For every `α ∈ (0, 1)`, the
  point mass `δ₀` and the two-point law `esLevelWitness α = ((1+α)/2) δ₋₁ + ((1−α)/2) δ₁` both have
  `ES_α = 0`. Their mixture `(1 − α) δ₀ + α · esLevelWitness α` has `ES_α = α/2`. So the level set
  `{ES_α = 0}` is not convex, and no scoring function elicits `ES_α` on any class containing these
  three laws, in particular on all laws with finite mean
  (`not_isElicitable_expectedShortfall_integrable`).

With `Risk/ExpectedShortfall.lean` this gives one half of each side of the regulatory
trade-off: expected shortfall is coherent but not elicitable, while value-at-risk is elicitable.
Its failure of subadditivity is proved in `Risk/VaRSuperadditivity.lean`.

## Main definitions

* `StrictlyElicits`: the scoring function `S` strictly elicits the functional `T` on a class `C`
  of laws, i.e. `T μ` is the unique minimizer of `x ↦ ∫ S(x, y) dμ(y)` for every `μ ∈ C`.
* `IsElicitable`: some scoring function strictly elicits `T` on `C`.
* `pinballLoss`: the pinball loss `(𝟙{y ≤ x} − α)(x − y)` of a quantile forecast `x` against a
  realized loss `y`.
* `esLevelWitness`, `esLevelMixture`: the two-point law `((1 + α)/2) δ₋₁ + ((1 − α)/2) δ₁` and
  the mixture `(1 − α) δ₀ + α · esLevelWitness α` used to show that expected shortfall is not
  elicitable.

## Main results

* `StrictlyElicits.apply_mixture`: on a class closed under the mixture, a strictly elicited
  functional is constant on mixtures of laws with equal values (convex level sets).
* `integral_pinballLoss`: the expected pinball loss in terms of `rockafellarUryasev`.
* `integral_pinballLoss_valueAtRisk_le`: VaR minimizes the expected pinball loss.
* `rockafellarUryasev_sub_expectedShortfall`: the exact Rockafellar–Uryasev excess.
* `expectedShortfall_lt_rockafellarUryasev`: when the quantile is unique, `ES_α < RU(c)` for every
  `c ≠ VaR_α`, so VaR is the unique minimizer of the Rockafellar–Uryasev function.
* `strictlyElicits_pinballLoss`: the pinball loss strictly elicits the `α`-quantile on the laws
  with a finite mean and a unique `α`-quantile.
* `not_isElicitable_expectedShortfall`: for `α ∈ (0, 1)`, `ES_α` is not elicitable on any class of
  laws containing `δ₀`, `esLevelWitness α` and `esLevelMixture α`.

## References

* [T. Gneiting, *Making and evaluating point forecasts*][Gneiting2011]
* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Section 9.3
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 9.5(c); Ex. 9.5, 9.16

## Tags

elicitability, pinball loss, quantile loss, scoring function, backtesting, VaR vs ES,
forecast comparison, MSC 91G70, MSC 62F10, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-! ### Elicitability and convex level sets -/

/-- The scoring function `S` **strictly elicits** the functional `T` on the class `C` of laws on
`ℝ`, with values in `V`: for every `μ ∈ C` each expected score `∫ S x y dμ(y)` is finite, and
`T μ` is the unique minimizer of `x ↦ ∫ S x y dμ(y)` over `x : V`. -/
def StrictlyElicits {V : Type*} (S : V → ℝ → ℝ) (T : Measure ℝ → V) (C : Set (Measure ℝ)) :
    Prop :=
  ∀ μ ∈ C, (∀ x, Integrable (S x) μ) ∧ ∀ x, x ≠ T μ → ∫ y, S (T μ) y ∂μ < ∫ y, S x y ∂μ

/-- A functional of laws is **elicitable** on `C` if some scoring function strictly elicits it. -/
def IsElicitable {V : Type*} (T : Measure ℝ → V) (C : Set (Measure ℝ)) : Prop :=
  ∃ S, StrictlyElicits S T C

variable {V : Type*} {S : V → ℝ → ℝ} {T : Measure ℝ → V} {C : Set (Measure ℝ)}

/-- The integral against a mixture of laws is the mixture of the integrals. -/
lemma integral_mixture {f : ℝ → ℝ} {μ ν : Measure ℝ} (hμ : Integrable f μ)
    (hν : Integrable f ν) {c : ℝ≥0} (hc : c ≤ 1) :
    ∫ y, f y ∂(c • μ + (1 - c) • ν) = c * ∫ y, f y ∂μ + (1 - c : ℝ) * ∫ y, f y ∂ν := by
  rw [integral_add_measure hμ.smul_measure_nnreal hν.smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def,
    smul_eq_mul, smul_eq_mul, NNReal.coe_sub hc, NNReal.coe_one]

/-- A mixture of two probability measures is a probability measure. -/
lemma isProbabilityMeasure_mixture {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : ℝ≥0} (hc : c ≤ 1) :
    IsProbabilityMeasure (c • μ + (1 - c) • ν) :=
  ⟨by simpa using add_tsub_cancel_of_le (show (c : ℝ≥0∞) ≤ 1 by exact_mod_cast hc)⟩

/-- **Elicitable functionals have convex level sets** (Osband 1985; Gneiting 2011, Theorem 6).
If `T μ = T ν` and the mixture `c μ + (1 − c) ν` lies in `C`, then `T` takes the same value on the
mixture: the common minimizer of the two expected scores minimizes their mixture, and the
minimizer of the mixed expected score is unique. -/
theorem StrictlyElicits.apply_mixture (hS : StrictlyElicits S T C) {μ ν : Measure ℝ}
    (hμ : μ ∈ C) (hν : ν ∈ C) {c : ℝ≥0} (hc : c ≤ 1) (hm : c • μ + (1 - c) • ν ∈ C)
    (hμν : T μ = T ν) : T (c • μ + (1 - c) • ν) = T μ := by
  by_contra hne
  obtain ⟨hμi, hμlt⟩ := hS μ hμ
  obtain ⟨hνi, hνlt⟩ := hS ν hν
  have h1 := (hμlt _ hne).le
  have h2 := (hνlt _ (hμν ▸ hne)).le
  have h3 := (hS _ hm).2 _ (Ne.symm hne)
  rw [← hμν] at h2
  rw [integral_mixture (hμi _) (hνi _) hc, integral_mixture (hμi _) (hνi _) hc] at h3
  have hc1 : (0 : ℝ) ≤ 1 - c := sub_nonneg.2 (by exact_mod_cast hc)
  nlinarith [mul_le_mul_of_nonneg_left h1 c.coe_nonneg, mul_le_mul_of_nonneg_left h2 hc1]

/-- An elicitable functional has convex level sets. -/
theorem IsElicitable.apply_mixture (hT : IsElicitable T C) {μ ν : Measure ℝ} (hμ : μ ∈ C)
    (hν : ν ∈ C) {c : ℝ≥0} (hc : c ≤ 1) (hm : c • μ + (1 - c) • ν ∈ C) (hμν : T μ = T ν) :
    T (c • μ + (1 - c) • ν) = T μ :=
  hT.choose_spec.apply_mixture hμ hν hc hm hμν

/-! ### The pinball loss and the Rockafellar–Uryasev objective -/

/-- The **pinball loss** at level `α`, the score of a quantile forecast `x` against a realized loss
`y`: `S_α(x, y) = (1 − α)(x − y)⁺ + α (y − x)⁺`. -/
noncomputable def pinballLoss (α x y : ℝ) : ℝ :=
  (1 - α) * max (x - y) 0 + α * max (y - x) 0

/-- The pinball loss in its textbook form `(𝟙{y ≤ x} − α)(x − y)`. -/
lemma pinballLoss_eq_ite (α x y : ℝ) :
    pinballLoss α x y = ((if y ≤ x then 1 else 0) - α) * (x - y) := by
  unfold pinballLoss
  split_ifs with h
  · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h)]
    ring
  · rw [max_eq_right (sub_nonpos.2 (not_le.1 h).le), max_eq_left (sub_nonneg.2 (not_le.1 h).le)]
    ring

/-- The pinball loss is the shortfall `(y − x)⁺` plus a function affine in `(x, y)`. -/
lemma pinballLoss_eq_max_add (α x y : ℝ) :
    pinballLoss α x y = max (y - x) 0 + (1 - α) * x - (1 - α) * y := by
  unfold pinballLoss
  rcases le_total y x with h | h
  · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h)]
    ring
  · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]
    ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {α : ℝ}

/-- **The expected pinball loss is the Rockafellar–Uryasev objective**, rescaled:
`E[S_α(x, X)] = (1 − α)·(x + (1 − α)⁻¹ E[(X − x)⁺]) − (1 − α)·E[X]`. -/
theorem integral_pinballLoss (hX : Integrable X P) (hα : α ∈ Ioo 0 1) (x : ℝ) :
    ∫ ω, pinballLoss α x (X ω) ∂P =
      (1 - α) * rockafellarUryasev X P α x - (1 - α) * ∫ ω, X ω ∂P := by
  have h1α : 1 - α ≠ 0 := (sub_pos.2 hα.2).ne'
  have hpos : Integrable (fun ω ↦ max (X ω - x) 0) P := (hX.sub (integrable_const x)).pos_part
  have h1 : Integrable (fun ω ↦ max (X ω - x) 0 + (1 - α) * x) P := hpos.add (integrable_const _)
  have h2 : Integrable (fun ω ↦ (1 - α) * X ω) P := hX.const_mul _
  simp_rw [pinballLoss_eq_max_add]
  rw [integral_sub h1 h2,
    integral_add hpos (integrable_const _), integral_const, integral_const_mul, rockafellarUryasev,
    probReal_univ, one_smul, mul_add, mul_inv_cancel_left₀ h1α]
  ring

/-- **VaR minimizes the expected pinball loss**: the Rockafellar–Uryasev theorem, rescaled. -/
theorem integral_pinballLoss_valueAtRisk_le (hX : Integrable X P) (hα : α ∈ Ioo 0 1) (x : ℝ) :
    ∫ ω, pinballLoss α (valueAtRisk X P α) (X ω) ∂P ≤ ∫ ω, pinballLoss α x (X ω) ∂P := by
  rw [integral_pinballLoss hX hα, integral_pinballLoss hX hα, rockafellarUryasev_valueAtRisk hX hα]
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left
    (expectedShortfall_le_rockafellarUryasev hX hα x) (sub_pos.2 hα.2).le) _

/-- **The exact Rockafellar–Uryasev excess**: with `q(u) = VaR_u(X)`,
`g(c) − ES_α(X) = (1 − α)⁻¹ (∫_{(0, α]} (q(u) − c)⁺ du + ∫_{(α, 1)} (c − q(u))⁺ du)`.
The excess integrates the distance of the VaR curve from `c` over the levels on the wrong side
of `α`: levels below `α` whose quantile is above `c`, and levels above `α` whose quantile is
below `c`. -/
theorem rockafellarUryasev_sub_expectedShortfall (hX : Integrable X P) (hα : α ∈ Ioo 0 1)
    (c : ℝ) :
    rockafellarUryasev X P α c - expectedShortfall X P α =
      (1 - α)⁻¹ * ((∫ u in Ioc 0 α, max (valueAtRisk X P u - c) 0) +
        ∫ u in Ioo α 1, max (c - valueAtRisk X P u) 0) := by
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  have hq : IntegrableOn (fun u ↦ valueAtRisk X P u) (Ioo α 1) :=
    (integrableOn_valueAtRisk hX).mono_set (Ioo_subset_Ioo_left hα.1.le)
  have hpos := integrableOn_max_valueAtRisk_sub hX c
  have hneg : IntegrableOn (fun u ↦ max (c - valueAtRisk X P u) 0) (Ioo α 1) :=
    ((integrableOn_const (by simp)).sub hq).pos_part
  -- split `(0, 1)` at `α`, and on `(α, 1)` write `t⁺ = t + (−t)⁺`
  have hqc : IntegrableOn (fun u ↦ valueAtRisk X P u - c) (Ioo α 1) :=
    hq.sub (integrableOn_const (C := c) (by simp))
  have hsplit : ∫ u in Ioo 0 1, max (valueAtRisk X P u - c) 0 =
      (∫ u in Ioc 0 α, max (valueAtRisk X P u - c) 0) +
        ((∫ u in Ioo α 1, valueAtRisk X P u) - (1 - α) * c +
          ∫ u in Ioo α 1, max (c - valueAtRisk X P u) 0) := by
    rw [← Ioc_union_Ioo_eq_Ioo hα.1.le hα.2, setIntegral_union
      (Ioc_disjoint_Ioi_same.mono_right Ioo_subset_Ioi_self) measurableSet_Ioo
      (hpos.mono_set fun u hu ↦ ⟨hu.1, hu.2.trans_lt hα.2⟩)
      (hpos.mono_set (Ioo_subset_Ioo_left hα.1.le))]
    congr 1
    rw [setIntegral_congr_fun measurableSet_Ioo fun u _ ↦
        (show max (valueAtRisk X P u - c) 0 =
          (valueAtRisk X P u - c) + max (c - valueAtRisk X P u) 0 by
          rcases le_total c (valueAtRisk X P u) with h | h
          · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h), add_zero]
          · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]; ring),
      integral_add hqc hneg,
      integral_sub hq (integrableOn_const (by simp)), setIntegral_const,
      Real.volume_real_Ioo_of_le hα.2.le, smul_eq_mul]
  rw [rockafellarUryasev, integral_max_sub_eq_setIntegral_valueAtRisk hX.aemeasurable, hsplit,
    expectedShortfall]
  field_simp
  ring

/-- A nonnegative integrand that is at least `δ > 0` on a nondegenerate interval inside the
domain has a positive integral. -/
lemma setIntegral_pos_of_ge_on_Ioo {f : ℝ → ℝ} {s : Set ℝ} (hf : IntegrableOn f s)
    (hf0 : ∀ u ∈ s, 0 ≤ f u) {a b δ : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ s) (hδ : 0 < δ)
    (hfδ : ∀ u ∈ Ioo a b, δ ≤ f u) (hs : MeasurableSet s) : 0 < ∫ u in s, f u := by
  calc (0 : ℝ) < ∫ _ in Ioo a b, δ := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hab.le, smul_eq_mul]
        exact mul_pos (sub_pos.2 hab) hδ
    _ ≤ ∫ u in Ioo a b, f u :=
        setIntegral_mono_on (integrableOn_const (by simp)) (hf.mono_set hsub) measurableSet_Ioo hfδ
    _ ≤ ∫ u in s, f u :=
        setIntegral_mono_set hf ((ae_restrict_iff' hs).2 (ae_of_all _ hf0))
          (Filter.Eventually.of_forall fun _ h ↦ hsub h)

/-- **VaR is the unique minimizer of the Rockafellar–Uryasev objective** when the `α`-quantile is
unique, i.e. the distribution function exceeds `α` right after `VaR_α(X)`. Below VaR the levels
`(P(X ≤ c), α]` have quantiles above `c`; above VaR the levels `(α, P(X ≤ x))` have quantiles at
most `x < c`. Either way the exact excess `rockafellarUryasev_sub_expectedShortfall` is positive. -/
theorem expectedShortfall_lt_rockafellarUryasev (hX : Integrable X P) (hα : α ∈ Ioo 0 1)
    (huniq : ∀ x, valueAtRisk X P α < x → α < P.real {ω | X ω ≤ x}) {c : ℝ}
    (hc : c ≠ valueAtRisk X P α) : expectedShortfall X P α < rockafellarUryasev X P α c := by
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  set q := valueAtRisk X P α
  have hX' := hX.aemeasurable
  have hlo : IntegrableOn (fun u ↦ max (valueAtRisk X P u - c) 0) (Ioc 0 α) :=
    (integrableOn_max_valueAtRisk_sub hX c).mono_set fun u hu ↦ ⟨hu.1, hu.2.trans_lt hα.2⟩
  have hhi : IntegrableOn (fun u ↦ max (c - valueAtRisk X P u) 0) (Ioo α 1) :=
    ((integrableOn_const (by simp)).sub
      ((integrableOn_valueAtRisk hX).mono_set (Ioo_subset_Ioo_left hα.1.le))).pos_part
  have hlo0 : 0 ≤ ∫ u in Ioc 0 α, max (valueAtRisk X P u - c) 0 :=
    setIntegral_nonneg measurableSet_Ioc fun _ _ ↦ le_max_right _ _
  have hhi0 : 0 ≤ ∫ u in Ioo α 1, max (c - valueAtRisk X P u) 0 :=
    setIntegral_nonneg measurableSet_Ioo fun _ _ ↦ le_max_right _ _
  have hpos : 0 < (∫ u in Ioc 0 α, max (valueAtRisk X P u - c) 0) +
      ∫ u in Ioo α 1, max (c - valueAtRisk X P u) 0 := by
    rcases hc.lt_or_gt with hcq | hcq
    · -- below VaR: on `(P(X ≤ c'), α)` with `c < c' < q` the quantile is above `c'`
      obtain ⟨c', hcc', hc'q⟩ := exists_between hcq
      have hF : P.real {ω | X ω ≤ c'} < α := (lt_valueAtRisk_iff hX' hα).1 hc'q
      have hF0 : 0 ≤ P.real {ω | X ω ≤ c'} := measureReal_nonneg
      refine add_pos_of_pos_of_nonneg (setIntegral_pos_of_ge_on_Ioo
        (a := max 0 (P.real {ω | X ω ≤ c'})) (b := α) hlo (fun _ _ ↦ le_max_right _ _)
        (max_lt hα.1 hF)
        (fun u hu ↦ ⟨(le_max_left 0 _).trans_lt hu.1, hu.2.le⟩)
        (sub_pos.2 hcc') (fun u hu ↦ ?_) measurableSet_Ioc) hhi0
      have hu' : u ∈ Ioo 0 1 := ⟨(le_max_left 0 _).trans_lt hu.1, hu.2.trans hα.2⟩
      have : c' < valueAtRisk X P u :=
        (lt_valueAtRisk_iff hX' hu').2 ((le_max_right 0 _).trans_lt hu.1)
      exact le_max_of_le_left (by linarith)
    · -- above VaR: on `(α, P(X ≤ x))` with `q < x < c` the quantile is at most `x`
      obtain ⟨x, hqx, hxc⟩ := exists_between hcq
      have hF : α < P.real {ω | X ω ≤ x} := huniq x hqx
      have hF1 : P.real {ω | X ω ≤ x} ≤ 1 := measureReal_le_one
      refine add_pos_of_nonneg_of_pos hlo0 (setIntegral_pos_of_ge_on_Ioo (a := α)
        (b := min (P.real {ω | X ω ≤ x}) 1) hhi
        (fun _ _ ↦ le_max_right _ _) (lt_min hF hα.2)
        (fun u hu ↦ ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩) (sub_pos.2 hxc) (fun u hu ↦ ?_)
        measurableSet_Ioo)
      have hu' : u ∈ Ioo 0 1 := ⟨hα.1.trans hu.1, hu.2.trans_le (min_le_right _ _)⟩
      have : valueAtRisk X P u ≤ x :=
        (valueAtRisk_le_iff hX' hu').2 (hu.2.trans_le (min_le_left _ _)).le
      exact le_max_of_le_left (by linarith)
  have := rockafellarUryasev_sub_expectedShortfall hX hα c
  have : 0 < rockafellarUryasev X P α c - expectedShortfall X P α := by
    rw [this]; exact mul_pos (inv_pos.2 h1α) hpos
  linarith

/-- **The pinball loss strictly elicits the `α`-quantile** on the laws with finite mean whose
`α`-quantile is unique: there the quantile is the unique minimizer of the expected pinball loss. -/
theorem strictlyElicits_pinballLoss (hα : α ∈ Ioo 0 1) :
    StrictlyElicits (pinballLoss α) (fun μ ↦ quantile μ α)
      {μ | IsProbabilityMeasure μ ∧ Integrable id μ ∧
        ∀ x, quantile μ α < x → α < cdf μ x} := by
  rintro μ ⟨hμ, hint, huniq⟩
  have hvar : valueAtRisk id μ α = quantile μ α := by rw [valueAtRisk, Measure.map_id]
  refine ⟨fun x ↦ ?_, fun x hx ↦ ?_⟩
  · have hp : Integrable (fun y : ℝ ↦ max (y - x) 0) μ := (hint.sub (integrable_const x)).pos_part
    rw [show pinballLoss α x = fun y ↦ max (y - x) 0 + (1 - α) * x - (1 - α) * y from
      funext (pinballLoss_eq_max_add α x)]
    exact (hp.add (integrable_const _)).sub (hint.const_mul _)
  · have h := integral_pinballLoss (P := μ) (X := id) hint hα
    simp only [id] at h
    dsimp only
    rw [h, h, ← hvar, rockafellarUryasev_valueAtRisk hint hα]
    refine sub_lt_sub_right (mul_lt_mul_of_pos_left
      (expectedShortfall_lt_rockafellarUryasev hint hα (fun y hy ↦ ?_) (hvar ▸ hx))
      (sub_pos.2 hα.2)) _
    rw [hvar] at hy
    have h' := huniq y hy
    rw [cdf_eq_real] at h'
    exact h'

/-! ### Expected shortfall is not elicitable -/

/-- A scaled point mass integrates every real function. -/
lemma integrable_smul_dirac (f : ℝ → ℝ) (c : ℝ≥0) (a : ℝ) :
    Integrable f (c • Measure.dirac a) :=
  (integrable_dirac eNorm_lt_top).smul_measure_nnreal

/-- The integral against a scaled point mass is the scaled evaluation. -/
lemma integral_smul_dirac (f : ℝ → ℝ) (c : ℝ≥0) (a : ℝ) :
    ∫ y, f y ∂(c • Measure.dirac a) = c * f a := by
  rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul]

/-- The two-point law `((1 + α)/2) δ₋₁ + ((1 − α)/2) δ₁`: at level `α` its expected shortfall is
`0`, the same as that of the point mass `δ₀`. -/
noncomputable def esLevelWitness (α : ℝ) : Measure ℝ :=
  ((1 + α) / 2).toNNReal • Measure.dirac (-1) + ((1 - α) / 2).toNNReal • Measure.dirac 1

/-- The mixture `(1 − α) δ₀ + α · esLevelWitness α`, whose expected shortfall at level `α` is
`α/2`. -/
noncomputable def esLevelMixture (α : ℝ) : Measure ℝ :=
  (1 - α).toNNReal • Measure.dirac 0 + (1 - (1 - α).toNNReal) • esLevelWitness α

private lemma integrable_esLevelWitness (f : ℝ → ℝ) : Integrable f (esLevelWitness α) :=
  (integrable_smul_dirac f _ _).add_measure (integrable_smul_dirac f _ _)

private lemma integral_esLevelWitness (hα : α ∈ Ioo 0 1) (f : ℝ → ℝ) :
    ∫ y, f y ∂esLevelWitness α = (1 + α) / 2 * f (-1) + (1 - α) / 2 * f 1 := by
  rw [esLevelWitness, integral_add_measure (integrable_smul_dirac f _ _)
    (integrable_smul_dirac f _ _), integral_smul_dirac, integral_smul_dirac,
    Real.coe_toNNReal _ (by linarith [hα.1]), Real.coe_toNNReal _ (by linarith [hα.2])]

private lemma integral_esLevelMixture (hα : α ∈ Ioo 0 1) (f : ℝ → ℝ) :
    ∫ y, f y ∂esLevelMixture α =
      (1 - α) * f 0 + α * ((1 + α) / 2 * f (-1) + (1 - α) / 2 * f 1) := by
  have hc : ((1 - (1 - α).toNNReal : ℝ≥0) : ℝ) = α := by
    rw [NNReal.coe_sub (by simpa using hα.1.le), NNReal.coe_one,
      Real.coe_toNNReal _ (by linarith [hα.2])]
    ring
  rw [esLevelMixture, integral_add_measure (integrable_smul_dirac f _ _)
    (integrable_esLevelWitness f).smul_measure_nnreal, integral_smul_dirac,
    integral_smul_nnreal_measure, integral_esLevelWitness hα, NNReal.smul_def, smul_eq_mul, hc,
    Real.coe_toNNReal _ (by linarith [hα.2])]

private lemma isProbabilityMeasure_esLevelWitness (hα : α ∈ Ioo 0 1) :
    IsProbabilityMeasure (esLevelWitness α) := by
  constructor
  have h := integral_esLevelWitness hα fun _ ↦ (1 : ℝ)
  rw [integral_const, smul_eq_mul, mul_one] at h
  have h1 : (esLevelWitness α).real univ = 1 := by linarith
  rw [measureReal_def, ENNReal.toReal_eq_one_iff] at h1
  exact h1

private lemma isProbabilityMeasure_esLevelMixture (hα : α ∈ Ioo 0 1) :
    IsProbabilityMeasure (esLevelMixture α) := by
  have := isProbabilityMeasure_esLevelWitness hα
  exact isProbabilityMeasure_mixture (by simpa using hα.1.le)

/-- An `ES_α` value is pinned by a Rockafellar–Uryasev threshold from above and an admissible
stress density from below. -/
private lemma expectedShortfall_eq_of_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable id μ) (hα : α ∈ Ioo 0 1) {v c : ℝ} {D : ℝ → ℝ}
    (hc : rockafellarUryasev id μ α c ≤ v) (hD : Measurable D) (hD0 : ∀ y, 0 ≤ D y)
    (hD1 : ∀ y, D y ≤ (1 - α)⁻¹) (hDint : ∫ y, D y ∂μ = 1) (hDv : v ≤ ∫ y, D y * y ∂μ) :
    expectedShortfall id μ α = v :=
  le_antisymm ((expectedShortfall_le_rockafellarUryasev hint hα c).trans hc)
    (hDv.trans (integral_mul_le_expectedShortfall hint hα hD.aestronglyMeasurable
      (ae_of_all _ hD0) (ae_of_all _ hD1) hDint))

/-- `ES_α(δ₀) = 0`. -/
lemma expectedShortfall_dirac_zero (hα : α ∈ Ioo 0 1) :
    expectedShortfall id (Measure.dirac 0) α = 0 :=
  expectedShortfall_eq_of_bounds (integrable_dirac eNorm_lt_top) hα (c := 0) (D := fun _ ↦ 1)
    (by simp [rockafellarUryasev]) measurable_const (fun _ ↦ zero_le_one)
    (fun _ ↦ by rw [one_le_inv₀ (sub_pos.2 hα.2)]; linarith [hα.1]) (by simp) (by simp)

/-- `ES_α` of the two-point witness is `0`. -/
lemma expectedShortfall_esLevelWitness (hα : α ∈ Ioo 0 1) :
    expectedShortfall id (esLevelWitness α) α = 0 := by
  have := isProbabilityMeasure_esLevelWitness hα
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  have h1a : 1 + α ≠ 0 := by linarith [hα.1]
  have hβ : (1 + α)⁻¹ ≤ (1 - α)⁻¹ := inv_anti₀ h1α (by linarith [hα.1])
  refine expectedShortfall_eq_of_bounds (integrable_esLevelWitness _) hα (c := -1)
    (D := fun y ↦ if 0 < y then (1 - α)⁻¹ else (1 + α)⁻¹) ?_
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)
    (fun y ↦ by split_ifs; exacts [(inv_pos.2 h1α).le, inv_nonneg.2 (by linarith [hα.1])])
    (fun y ↦ by split_ifs; exacts [le_rfl, hβ]) ?_ ?_
  · rw [rockafellarUryasev, integral_esLevelWitness hα]
    norm_num
    rw [inv_mul_cancel₀ h1α.ne']
  · rw [integral_esLevelWitness hα]
    norm_num
    field_simp
    ring
  · rw [integral_esLevelWitness hα]
    norm_num
    apply le_of_eq
    field_simp

/-- `ES_α` of the mixture `(1 − α) δ₀ + α · esLevelWitness α` is `α/2`. -/
lemma expectedShortfall_esLevelMixture (hα : α ∈ Ioo 0 1) :
    expectedShortfall id (esLevelMixture α) α = α / 2 := by
  have := isProbabilityMeasure_esLevelMixture hα
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  have hγ : (1 - α / 2) / (1 - α) ≤ (1 - α)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 h1α.le) (by linarith [hα.1])
  have hγ0 : 0 ≤ (1 - α / 2) / (1 - α) := div_nonneg (by linarith [hα.2]) h1α.le
  refine expectedShortfall_eq_of_bounds (μ := esLevelMixture α)
    ((integrable_smul_dirac id _ _).add_measure (integrable_esLevelWitness id).smul_measure_nnreal)
    hα (c := 0)
    (D := fun y ↦ if 0 < y then (1 - α)⁻¹ else if y < 0 then 0 else (1 - α / 2) / (1 - α)) ?_
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
        measurable_const))
    (fun y ↦ by split_ifs; exacts [(inv_pos.2 h1α).le, le_rfl, hγ0])
    (fun y ↦ by split_ifs; exacts [le_rfl, inv_nonneg.2 h1α.le, hγ]) ?_ ?_
  · rw [rockafellarUryasev, integral_esLevelMixture hα]
    norm_num
    apply le_of_eq
    field_simp
  · rw [integral_esLevelMixture hα]
    norm_num
    field_simp
    ring
  · rw [integral_esLevelMixture hα]
    norm_num
    apply le_of_eq
    field_simp

/-- **Expected shortfall is not elicitable** (Gneiting 2011): for every `α ∈ (0, 1)`, no scoring
function elicits `ES_α` on a class of laws containing `δ₀`, `esLevelWitness α` and their mixture
`esLevelMixture α`. The two laws share `ES_α = 0` while the mixture has `ES_α = α/2`, so the level
set `{ES_α = 0}` is not convex (`IsElicitable.apply_mixture`). -/
theorem not_isElicitable_expectedShortfall (hα : α ∈ Ioo 0 1) {C : Set (Measure ℝ)}
    (h0 : Measure.dirac 0 ∈ C) (hW : esLevelWitness α ∈ C) (hM : esLevelMixture α ∈ C) :
    ¬ IsElicitable (fun μ ↦ expectedShortfall id μ α) C := fun hT ↦ by
  have h := hT.apply_mixture h0 hW (c := (1 - α).toNNReal) (by simpa using hα.1.le) hM
    (by rw [expectedShortfall_dirac_zero hα, expectedShortfall_esLevelWitness hα])
  rw [show (1 - α).toNNReal • Measure.dirac 0 + (1 - (1 - α).toNNReal) • esLevelWitness α =
      esLevelMixture α from rfl, expectedShortfall_esLevelMixture hα,
    expectedShortfall_dirac_zero hα] at h
  linarith [hα.1]

/-- `ES_α` is not elicitable on the laws with finite mean. -/
theorem not_isElicitable_expectedShortfall_integrable (hα : α ∈ Ioo 0 1) :
    ¬ IsElicitable (fun μ ↦ expectedShortfall id μ α)
      {μ | IsProbabilityMeasure μ ∧ Integrable id μ} :=
  not_isElicitable_expectedShortfall hα ⟨inferInstance, integrable_dirac eNorm_lt_top⟩
    ⟨isProbabilityMeasure_esLevelWitness hα, integrable_esLevelWitness _⟩
    ⟨isProbabilityMeasure_esLevelMixture hα,
      (integrable_smul_dirac id _ _).add_measure (integrable_esLevelWitness id).smul_measure_nnreal⟩

end MathFin
