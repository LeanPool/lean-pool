/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityStepIntegral

/-!
# Weighted covariances of compensated boxes

Second moments and cross moments of compensated masses `Ñ((a,b] × A)` weighted by a
past-measurable factor: the weighted second moment, vanishing of the cross terms for disjoint
marks and for time-ordered boxes, and the same-time bilinear covariance in the marks. These
combine into the isometry for a single time interval carrying several marks.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Weighted second moment of a future-box compensated value.** For a past-at-`a`
(i.e. `ℱ_a`-)measurable weight `g` and a future box `(a,b] × A`,
`E[g·Ñ((a,b]×A)²] = E[g]·ν̂((a,b]×A).toReal`: `g` is independent of `Ñ(box)`
(`indepFun_past_compensated_box`), hence of its square, and `E[Ñ(box)²] = ν̂(box)`. -/
lemma weighted_box_sq_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAf : ν A ≠ ⊤)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g) :
    ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P)
        * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal := by
  have hbox_meas : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hbox_fin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAf
  have h_indep := indepFun_past_compensated_box N ℱ hℱ ha hab hA hAf hg
  have h_indep_sq : ProbabilityTheory.IndepFun g
      (fun ω => (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2) P :=
    h_indep.comp measurable_id (measurable_id.pow_const 2)
  rw [h_indep_sq.integral_fun_mul_eq_mul_integral
      ((hg.mono (ℱ.le' a)).measurable.aestronglyMeasurable)
      (((ENNReal.measurable_toReal.comp
        (N.measurable_eval hbox_meas)).sub_const _).pow_const 2).aestronglyMeasurable,
    compensated_second_moment N hbox_meas hbox_fin]

/-- **Same-time, disjoint-mark weighted cross term vanishes.** For an `ℱ_a`-measurable
bounded weight `g` and two future boxes `(a,b]×A`, `(a,b]×A'` on **disjoint** marks
`A, A'`, `E[g·Ñ((a,b]×A)·Ñ((a,b]×A')] = 0`. Polarising through the union box
`(a,b]×(A∪A')` reduces each term to `weighted_box_sq_eq`, and `ν̂(R∪R') = ν̂(R)+ν̂(R')`
(disjoint) makes the combination cancel. **No strengthening of the per-box past/future
independence is needed.** -/
lemma weighted_box_cross_disjoint_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {A A' : Set E} (hA : MeasurableSet A) (hA' : MeasurableSet A')
    (hAf : ν A ≠ ⊤) (hA'f : ν A' ≠ ⊤) (hdisjA : Disjoint A A')
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g)
    {M : ℝ} (hgb : ∀ ω, |g ω| ≤ M) :
    ∫ ω, g ω
        * (N.compensated (Set.Ioc a b ×ˢ A) ω * N.compensated (Set.Ioc a b ×ˢ A') ω) ∂P = 0 := by
  set R := Set.Ioc a b ×ˢ A with hRdef
  set R' := Set.Ioc a b ×ˢ A' with hR'def
  have hRmeas : MeasurableSet R := measurableSet_Ioc.prod hA
  have hR'meas : MeasurableSet R' := measurableSet_Ioc.prod hA'
  have hRf : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAf
  have hR'f : LevyStochCalc.Poisson.referenceIntensity ν R' ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hA'f
  have hUAf : ν (A ∪ A') ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hAf, hA'f⟩) (measure_union_le A A')
  have hRUeq : R ∪ R' = Set.Ioc a b ×ˢ (A ∪ A') := Set.prod_union.symm
  have hRUf : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∪ A')) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hUAf
  have hRdisj : Disjoint R R' := Set.disjoint_prod.mpr (Or.inr hdisjA)
  -- a.e. compensated additivity on the disjoint union.
  have hadd_ae : (fun ω => N.compensated (R ∪ R') ω)
      =ᵐ[P] (fun ω => N.compensated R ω + N.compensated R' ω) := by
    filter_upwards [N.integer_valued (hRmeas.union hR'meas) (hRUeq ▸ hRUf)] with ω hω
    obtain ⟨n, hn⟩ := hω
    have hUfin : N.N ω (R ∪ R') ≠ ⊤ := by rw [hn]; exact ENNReal.natCast_ne_top n
    have hRne : N.N ω R ≠ ⊤ := ne_top_of_le_ne_top hUfin (measure_mono Set.subset_union_left)
    have hR'ne : N.N ω R' ≠ ⊤ := ne_top_of_le_ne_top hUfin (measure_mono Set.subset_union_right)
    simp only [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
    rw [show N.N ω (R ∪ R') = N.N ω R + N.N ω R' from measure_union hRdisj hR'meas,
      show LevyStochCalc.Poisson.referenceIntensity ν (R ∪ R')
          = LevyStochCalc.Poisson.referenceIntensity ν R
            + LevyStochCalc.Poisson.referenceIntensity ν R' from measure_union hRdisj hR'meas,
      ENNReal.toReal_add hRne hR'ne, ENNReal.toReal_add hRf hR'f]
    ring
  -- integrability of `g·Ñ(box)²` (bounded weight × square-integrable).
  have hg_aesm : MeasureTheory.AEStronglyMeasurable g P :=
    (hg.mono (ℱ.le' a)).measurable.aestronglyMeasurable
  have hgbnd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ M :=
    Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have hiR : MeasureTheory.Integrable (fun ω => g ω * (N.compensated R ω) ^ 2) P :=
    (compensated_sq_integrable N hRmeas hRf).bdd_mul hg_aesm hgbnd
  have hiR' : MeasureTheory.Integrable (fun ω => g ω * (N.compensated R' ω) ^ 2) P :=
    (compensated_sq_integrable N hR'meas hR'f).bdd_mul hg_aesm hgbnd
  have hiU : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (R ∪ R') ω) ^ 2) P :=
    (compensated_sq_integrable N (hRmeas.union hR'meas) (hRUeq ▸ hRUf)).bdd_mul hg_aesm hgbnd
  -- pointwise polarisation (a.e., using the additivity).
  have hpt_ae : (fun ω => g ω * (N.compensated R ω * N.compensated R' ω))
      =ᵐ[P] (fun ω => 2⁻¹ * (g ω * (N.compensated (R ∪ R') ω) ^ 2)
          - 2⁻¹ * (g ω * (N.compensated R ω) ^ 2)
          - 2⁻¹ * (g ω * (N.compensated R' ω) ^ 2)) := by
    filter_upwards [hadd_ae] with ω h
    rw [h]; ring
  have hfX : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated (R ∪ R') ω) ^ 2)) P := hiU.const_mul 2⁻¹
  have hfY : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated R ω) ^ 2)) P := hiR.const_mul 2⁻¹
  have hfZ : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated R' ω) ^ 2)) P := hiR'.const_mul 2⁻¹
  have hfXY : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated (R ∪ R') ω) ^ 2)
        - 2⁻¹ * (g ω * (N.compensated R ω) ^ 2)) P := hfX.sub hfY
  rw [MeasureTheory.integral_congr_ae hpt_ae,
    MeasureTheory.integral_sub hfXY hfZ,
    MeasureTheory.integral_sub hfX hfY,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  -- evaluate each weighted square via `weighted_box_sq_eq`.
  rw [show (∫ ω, g ω * (N.compensated (R ∪ R') ω) ^ 2 ∂P)
        = ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ (A ∪ A')) ω) ^ 2 ∂P from by rw [hRUeq],
    weighted_box_sq_eq N ℱ hℱ ha hab (hA.union hA') hUAf hg,
    weighted_box_sq_eq N ℱ hℱ ha hab hA hAf hg, weighted_box_sq_eq N ℱ hℱ ha hab hA' hA'f hg]
  -- `ν̂(R∪R') = ν̂(R)+ν̂(R')` (disjoint) ⇒ the bracket cancels.
  have hrefU : (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∪ A'))).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν R).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν R').toReal := by
    rw [← hRUeq, show LevyStochCalc.Poisson.referenceIntensity ν (R ∪ R')
          = LevyStochCalc.Poisson.referenceIntensity ν R
            + LevyStochCalc.Poisson.referenceIntensity ν R' from measure_union hRdisj hR'meas,
      ENNReal.toReal_add hRf hR'f]
  rw [hrefU]; ring

/-- **Time-ordered weighted cross term vanishes.** For an `ℱ_c`-measurable weight `g`
and boxes `(a,b]×A`, `(c,d]×A'` with `b ≤ c` (time-ordered), the earlier factor
`g·Ñ((a,b]×A)` is past-at-`c` measurable while `Ñ((c,d]×A')` is a future increment, so
`E[g·Ñ((a,b]×A)·Ñ((c,d]×A')] = E[g·Ñ((a,b]×A)]·E[Ñ((c,d]×A')] = 0`. The full-box
analogue of `offDiagonal_increment_zero` (the weight is measurable up to the *later*
box's start `c`, which is what the cross-`φ` isometry supplies). -/
lemma weighted_box_cross_timeordered_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b c d : ℝ} (hc : 0 ≤ c) (hbc : b ≤ c) (hcd : c < d)
    {A A' : Set E} (hA : MeasurableSet A) (hA' : MeasurableSet A') (hA'f : ν A' ≠ ⊤)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ c) g) :
    ∫ ω, g ω
        * (N.compensated (Set.Ioc a b ×ˢ A) ω * N.compensated (Set.Ioc c d ×ˢ A') ω) ∂P = 0 := by
  have hRmeas : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hR'meas : MeasurableSet (Set.Ioc c d ×ˢ A') := measurableSet_Ioc.prod hA'
  have hR'f : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc c d ×ˢ A') ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hA'f
  have hRsub : Set.Ioc a b ×ˢ A ⊆ Set.Iic c ×ˢ Set.univ :=
    fun x hx => ⟨le_trans hx.1.2 hbc, Set.mem_univ _⟩
  -- `Ñ((a,b]×A)` is past-at-`c` measurable.
  have hÑR_c : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq c)
      (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) := by
    unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
    exact (((hℱ.measurable hRsub
      hRmeas).ennreal_toReal).sub measurable_const).stronglyMeasurable
  have hf_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq c)
      (fun ω => g ω * N.compensated (Set.Ioc a b ×ˢ A) ω) :=
    hg.mul hÑR_c
  have h_indep : ProbabilityTheory.IndepFun
      (fun ω => g ω * N.compensated (Set.Ioc a b ×ˢ A) ω)
      (fun ω => N.compensated (Set.Ioc c d ×ˢ A') ω) P :=
    indepFun_past_compensated_box N ℱ hℱ hc hcd hA' hA'f hf_meas
  rw [show (fun ω => g ω
        * (N.compensated (Set.Ioc a b ×ˢ A) ω * N.compensated (Set.Ioc c d ×ˢ A') ω))
      = (fun ω => (g ω * N.compensated (Set.Ioc a b ×ˢ A) ω)
          * N.compensated (Set.Ioc c d ×ˢ A') ω) from by funext ω; ring,
    h_indep.integral_fun_mul_eq_mul_integral
      (hf_meas.mono (ℱ.le' c)).measurable.aestronglyMeasurable
      ((ENNReal.measurable_toReal.comp
        (N.measurable_eval hR'meas)).sub_const _).aestronglyMeasurable,
    compensated_mean_zero N hR'meas hR'f, mul_zero]

/-- **Weighted disjoint-difference second moment.** For an `ℱ_a`-measurable bounded
weight `g` and two same-time boxes on disjoint marks `C, D`,
`E[g·(Ñ((a,b]×C) − Ñ((a,b]×D))²] = E[g]·ν̂((a,b]×C) + E[g]·ν̂((a,b]×D)`. Polarisation
expansion: squares via `weighted_box_sq_eq`, cross via `weighted_box_cross_disjoint_zero`. -/
lemma weighted_box_diff_sq_disjoint
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {C D : Set E} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCf : ν C ≠ ⊤) (hDf : ν D ≠ ⊤) (hdisjCD : Disjoint C D)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g)
    {M : ℝ} (hgb : ∀ ω, |g ω| ≤ M) :
    ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
        - N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ C)).toReal
        + (∫ ω, g ω ∂P)
          * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ D)).toReal := by
  have hCm : MeasurableSet (Set.Ioc a b ×ˢ C) := measurableSet_Ioc.prod hC
  have hDm : MeasurableSet (Set.Ioc a b ×ˢ D) := measurableSet_Ioc.prod hD
  have hCf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ C) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hCf
  have hDf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ D) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hDf
  have hg_aesm : MeasureTheory.AEStronglyMeasurable g P :=
    (hg.mono (ℱ.le' a)).measurable.aestronglyMeasurable
  have hgbnd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ M :=
    Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have hiC : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω) ^ 2) P :=
    (compensated_sq_integrable N hCm hCf').bdd_mul hg_aesm hgbnd
  have hiD : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2) P :=
    (compensated_sq_integrable N hDm hDf').bdd_mul hg_aesm hgbnd
  have hiCD : MeasureTheory.Integrable
      (fun ω => 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
        * N.compensated (Set.Ioc a b ×ˢ D) ω))) P :=
    ((compensated_cross_integrable N hCm hDm hCf' hDf').bdd_mul hg_aesm hgbnd).const_mul 2
  have hmid : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω) ^ 2
        - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
          * N.compensated (Set.Ioc a b ×ˢ D) ω))) P := hiC.sub hiCD
  have hpt : (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
        - N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2)
      = (fun ω => (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω) ^ 2
          - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
            * N.compensated (Set.Ioc a b ×ˢ D) ω)))
          + g ω * (N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2) := by
    funext ω; ring
  rw [hpt, MeasureTheory.integral_add hmid hiD,
    MeasureTheory.integral_sub hiC hiCD, MeasureTheory.integral_const_mul,
    weighted_box_cross_disjoint_zero N ℱ hℱ ha hab hC hD hCf hDf hdisjCD hg hgb,
    weighted_box_sq_eq N ℱ hℱ ha hab hC hCf hg, weighted_box_sq_eq N ℱ hℱ ha hab hD hDf hg]
  ring

/-- **Weighted same-time bilinear covariance.** For an `ℱ_a`-measurable bounded weight `g`
and two same-time boxes on arbitrary marks `A, A'`,
`E[g·Ñ((a,b]×A)·Ñ((a,b]×A')] = E[g]·ν̂((a,b]×(A∩A'))`. The weighted polarisation of
`weighted_box_sq_eq` (`Ñ(R)−Ñ(R') =ᵃᵉ Ñ((a,b]×(A∖A'))−Ñ((a,b]×(A'∖A))`, the weighted
disjoint difference value, and intensity inclusion–exclusion). Enables the
overlapping-mark step-integral isometry. -/
lemma weighted_box_cross_sametime
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {A A' : Set E} (hA : MeasurableSet A) (hA' : MeasurableSet A')
    (hAf : ν A ≠ ⊤) (hA'f : ν A' ≠ ⊤)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g)
    {M : ℝ} (hgb : ∀ ω, |g ω| ≤ M) :
    ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        * N.compensated (Set.Ioc a b ×ˢ A') ω) ∂P
      = (∫ ω, g ω ∂P)
        * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A'))).toReal := by
  have hAm : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hA'm : MeasurableSet (Set.Ioc a b ×ˢ A') := measurableSet_Ioc.prod hA'
  have hAf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAf
  have hA'f' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A') ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hA'f
  have hmcf : ν (A \ A') ≠ ⊤ := ne_top_of_le_ne_top hAf (measure_mono Set.sdiff_subset)
  have hmdf : ν (A' \ A) ≠ ⊤ := ne_top_of_le_ne_top hA'f (measure_mono Set.sdiff_subset)
  have hmif : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A')) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top (ne_top_of_le_ne_top hAf (measure_mono
      Set.inter_subset_left))
  have hmcf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A \ A')) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hmcf
  have hmdf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A' \ A)) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hmdf
  -- box set identities.
  have hBdiff : Set.Ioc a b ×ˢ A \ Set.Ioc a b ×ˢ A' = Set.Ioc a b ×ˢ (A \ A') := by
    ext ⟨x, e⟩; simp only [Set.mem_sdiff, Set.mem_prod]; tauto
  have hBa'diff : Set.Ioc a b ×ˢ A' \ Set.Ioc a b ×ˢ A = Set.Ioc a b ×ˢ (A' \ A) := by
    ext ⟨x, e⟩; simp only [Set.mem_sdiff, Set.mem_prod]; tauto
  have hBinter : Set.Ioc a b ×ˢ A ∩ Set.Ioc a b ×ˢ A' = Set.Ioc a b ×ˢ (A ∩ A') := by
    ext ⟨x, e⟩; simp only [Set.mem_inter_iff, Set.mem_prod]; tauto
  -- a.e. `Ñ(R) − Ñ(R') = Ñ((a,b]×(A∖A')) − Ñ((a,b]×(A'∖A))`.
  have hsub_ae : (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω)
      =ᵐ[P] (fun ω => N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
        - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω) := by
    filter_upwards [compensated_inter_add_diff_ae N hAm hA'm hAf',
      compensated_inter_add_diff_ae N hA'm hAm hA'f'] with ω h1 h2
    rw [h1, h2, Set.inter_comm (Set.Ioc a b ×ˢ A') (Set.Ioc a b ×ˢ A), hBdiff, hBa'diff]
    ring
  have hg_aesm : MeasureTheory.AEStronglyMeasurable g P :=
    (hg.mono (ℱ.le' a)).measurable.aestronglyMeasurable
  have hgbnd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ M :=
    Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  -- `∫ g·(Ñ(R)−Ñ(R'))²` via the weighted disjoint-difference value.
  have hsq_ae : (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2)
      =ᵐ[P] (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
        - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω) ^ 2) :=
    hsub_ae.mono (fun ω h => by
      change g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
          - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2
        = g ω * (N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
          - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω) ^ 2
      rw [show N.compensated (Set.Ioc a b ×ˢ A) ω - N.compensated (Set.Ioc a b ×ˢ A') ω
          = N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
            - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω from h])
  have hsq_eq : ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν
            (Set.Ioc a b ×ˢ (A \ A'))).toReal
        + (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν
            (Set.Ioc a b ×ˢ (A' \ A))).toReal :=
    (MeasureTheory.integral_congr_ae hsq_ae).trans
      (weighted_box_diff_sq_disjoint N ℱ hℱ ha hab (hA.diff hA') (hA'.diff hA) hmcf hmdf
        disjoint_sdiff_sdiff hg hgb)
  -- weighted polarisation expansion (cross term left symbolic).
  have hexp : ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal
        - 2 * (∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
            * N.compensated (Set.Ioc a b ×ˢ A') ω) ∂P)
        + (∫ ω, g ω ∂P)
          * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A')).toReal := by
    have hiA : MeasureTheory.Integrable
        (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2) P :=
      (compensated_sq_integrable N hAm hAf').bdd_mul hg_aesm hgbnd
    have hiA' : MeasureTheory.Integrable
        (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2) P :=
      (compensated_sq_integrable N hA'm hA'f').bdd_mul hg_aesm hgbnd
    have hicross : MeasureTheory.Integrable
        (fun ω => 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
          * N.compensated (Set.Ioc a b ×ˢ A') ω))) P :=
      ((compensated_cross_integrable N hAm hA'm hAf' hA'f').bdd_mul hg_aesm hgbnd).const_mul 2
    have hmid : MeasureTheory.Integrable
        (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2
          - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
            * N.compensated (Set.Ioc a b ×ˢ A') ω))) P := hiA.sub hicross
    rw [show (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
            - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2)
          = fun ω => (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2
            - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
              * N.compensated (Set.Ioc a b ×ˢ A') ω)))
            + g ω * (N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2 from funext (fun ω => by ring),
      MeasureTheory.integral_add hmid hiA', MeasureTheory.integral_sub hiA hicross,
      MeasureTheory.integral_const_mul,
      weighted_box_sq_eq N ℱ hℱ ha hab hA hAf hg, weighted_box_sq_eq N ℱ hℱ ha hab hA' hA'f hg]
  -- intensity inclusion–exclusion (in `toReal`).
  have hrefBa : (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A'))).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A \ A'))).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)
          = LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A ∩ Set.Ioc a b ×ˢ A')
            + LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A \ Set.Ioc a b ×ˢ A')
          from (measure_inter_add_sdiff _ hA'm).symm,
      hBinter, hBdiff, ENNReal.toReal_add hmif hmcf']
  have hrefBa' : (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A')).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A'))).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A' \ A))).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A')
          = LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A' ∩ Set.Ioc a b ×ˢ A)
            + LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A' \ Set.Ioc a b ×ˢ A)
          from (measure_inter_add_sdiff _ hAm).symm,
      Set.inter_comm (Set.Ioc a b ×ˢ A') (Set.Ioc a b ×ˢ A), hBinter, hBa'diff,
      ENNReal.toReal_add hmif hmdf']
  have key := hsq_eq.symm.trans hexp
  rw [hrefBa, hrefBa'] at key
  linear_combination (1 / 2 : ℝ) * key

/-- **Cross term of two disjoint-mark full-rect sums vanishes.** For a shared time
partition `p`, pairwise-disjoint marks (`Disjoint (A i) (A' i)`), and adapted bounded
coefficients, `E[(∑ᵢ ξᵢ Ñ((pᵢ,pᵢ₊₁]×Aᵢ))·(∑ⱼ ξ'ⱼ Ñ((pⱼ,pⱼ₊₁]×A'ⱼ))] = 0`. Every term
of the `(i,j)` double sum vanishes: `i=j` (same interval, disjoint marks) by
`weighted_box_cross_disjoint_zero`, `i≠j` (time-ordered) by
`weighted_box_cross_timeordered_zero`. The bilinear cross-vanishing underlying the
multi-mark step-integral isometry. -/
lemma crossSum_disjointMark_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    (A A' : Fin N₀ → Set E)
    (hAm : ∀ i, MeasurableSet (A i)) (hA'm : ∀ i, MeasurableSet (A' i))
    (hAf : ∀ i, ν (A i) ≠ ⊤) (hA'f : ∀ i, ν (A' i) ≠ ⊤)
    (hdisj : ∀ i, Disjoint (A i) (A' i))
    (ξ ξ' : Fin N₀ → Ω → ℝ)
    (hξb : ∀ i, ∃ M, ∀ ω, |ξ i ω| ≤ M) (hξ'b : ∀ i, ∃ M, ∀ ω, |ξ' i ω| ≤ M)
    (hξm : ∀ i, Measurable (ξ i)) (hξ'm : ∀ i, Measurable (ξ' i))
    (h_adapt : ∀ i, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ i))
    (h_adapt' : ∀ i, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ' i)) :
    ∫ ω, (∑ i : Fin N₀, ξ i ω
            * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
        * (∑ j : Fin N₀, ξ' j ω
            * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω) ∂P = 0 := by
  -- partition facts.
  have hpnn : ∀ k : Fin (N₀ + 1), 0 ≤ p k := fun k => by
    have := hpmono.monotone (Fin.zero_le k); rwa [hp0] at this
  have hlt : ∀ i : Fin N₀, p i.castSucc < p i.succ := fun i => hpmono Fin.castSucc_lt_succ
  -- measurability + finiteness of the boxes.
  have hRm : ∀ i, MeasurableSet (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) :=
    fun i => measurableSet_Ioc.prod (hAm i)
  have hR'm : ∀ i, MeasurableSet (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A' i) :=
    fun i => measurableSet_Ioc.prod (hA'm i)
  have hRf : ∀ i, LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ≠ ⊤ :=
    fun i => referenceIntensity_Ioc_prod_ne_top (hAf i)
  have hR'f : ∀ i, LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A' i) ≠ ⊤ :=
    fun i => referenceIntensity_Ioc_prod_ne_top (hA'f i)
  -- integrability of each cross product term.
  have hint : ∀ i j : Fin N₀, MeasureTheory.Integrable
      (fun ω => (ξ i ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
        * (ξ' j ω * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω)) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := hξb i
    obtain ⟨Mj, hMj⟩ := hξ'b j
    have hcross := compensated_cross_integrable N (hRm i) (hR'm j) (hRf i) (hR'f j)
    have heq : (fun ω => (ξ i ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
          * (ξ' j ω * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω))
        = (fun ω => (ξ i ω * ξ' j ω)
          * (N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω
            * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω)) := by
      funext ω; ring
    rw [heq]
    refine hcross.bdd_mul (c := Mi * Mj) ((hξm i).mul (hξ'm j)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMi ω) (hMj ω) (abs_nonneg _) ((abs_nonneg _).trans (hMi ω))
  -- expand the product of sums into a double sum and integrate term-by-term.
  rw [show (fun ω => (∑ i : Fin N₀, ξ i ω
            * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
          * (∑ j : Fin N₀, ξ' j ω
            * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω))
      = fun ω => ∑ i : Fin N₀, ∑ j : Fin N₀,
          (ξ i ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
          * (ξ' j ω * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω) from
    funext (fun ω => Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _
      (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => hint i j))]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => hint i j)]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  -- reassociate to `g·(Ñ·Ñ)` with `g = ξᵢ·ξ'ⱼ`.
  rw [show (fun ω => (ξ i ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
          * (ξ' j ω * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω))
      = fun ω => (ξ i ω * ξ' j ω)
          * (N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω
            * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω) from
    funext (fun ω => by ring)]
  rcases lt_trichotomy i j with hij | hij | hij
  · -- i < j: time-ordered (`pᵢ₊₁ ≤ pⱼ`).
    have hbc : p i.succ ≤ p j.castSucc :=
      hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
    exact weighted_box_cross_timeordered_zero N ℱ hℱ (hpnn _) hbc (hlt j)
      (hAm i) (hA'm j) (hA'f j)
      (((h_adapt i).mono (ℱ.mono ((hlt i).le.trans hbc))).mul (h_adapt' j))
  · -- i = j: same interval, disjoint marks.
    subst hij
    obtain ⟨Mi, hMi⟩ := hξb i
    obtain ⟨Mj, hMj⟩ := hξ'b i
    have hbnd : ∀ ω, |ξ i ω * ξ' i ω| ≤ Mi * Mj := fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hMi ω) (hMj ω) (abs_nonneg _) ((abs_nonneg _).trans (hMi ω))
    exact weighted_box_cross_disjoint_zero N ℱ hℱ (hpnn _) (hlt i)
      (hAm i) (hA'm i) (hAf i) (hA'f i) (hdisj i) ((h_adapt i).mul (h_adapt' i)) hbnd
  · -- j < i: time-ordered the other way (commute the two compensated factors).
    have hbc : p j.succ ≤ p i.castSucc :=
      hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
    rw [show (fun ω => (ξ i ω * ξ' j ω)
            * (N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω
              * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω))
        = fun ω => (ξ i ω * ξ' j ω)
            * (N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω
              * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω) from
      funext (fun ω => by ring)]
    exact weighted_box_cross_timeordered_zero N ℱ hℱ (hpnn _) hbc (hlt i)
      (hA'm j) (hAm i) (hAf i)
      ((h_adapt i).mul ((h_adapt' j).mono (ℱ.mono ((hlt j).le.trans hbc))))

/-- **Multi-mark step-integral L² isometry (sum form).** For a shared partition `p`,
pairwise-disjoint marks `B k`, and adapted bounded coefficients `ξ i k`,
`E[(∑ₖ ∑ᵢ ξᵢₖ Ñ((pᵢ,pᵢ₊₁]×Bₖ))²] = ∑ₖ ∑ᵢ ν̂((pᵢ,pᵢ₊₁]×Bₖ)·E[ξᵢₖ²]`. The `k`-level
expansion: the diagonal `E[Iₖ²]` is the single-mark isometry
(`simpleIntegral_L2_isometry_compensatedPoisson_sumForm`), the cross `E[IₖIₖ']` (`k≠k'`)
vanishes by `crossSum_disjointMark_zero` (disjoint marks). -/
lemma stepIntegral_multimark_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {N₀ K : ℕ} {T : ℝ} (hT : 0 < T)
    (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpleT : p (Fin.last N₀) ≤ T) (hpmono : StrictMono p)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (hBdisj : Pairwise (fun k k' => Disjoint (B k) (B k')))
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k))
    (h_adapt : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ i k)) :
    ∫ ω, (∑ k : Fin K, ∑ i : Fin N₀,
        ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2 ∂P
      = ∑ k : Fin K, ∑ i : Fin N₀,
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k)).toReal * ∫ ω, (ξ i k ω) ^ 2 ∂P := by
  -- the single-mark predictable for each mark `B k` (shared partition `p`).
  let φ : Fin K → SimplePredictable Ω E ν T := fun k =>
    { N := N₀, partition := p, partition_zero := hp0, partition_le_T := hpleT
      partition_strictMono := hpmono, A := fun _ => B k, A_measurable := fun _ => hBm k
      A_finite := fun _ => hBf k, ξ := fun i => ξ i k, ξ_bounded := fun i => hξb i k
      ξ_measurable := fun i => hξm i k }
  have hI_eq : ∀ k ω, simpleIntegral N (φ k) T ω
      = ∑ i : Fin N₀, ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω := by
    intro k ω; rw [simpleIntegral_eq_sum_fullRect]; rfl
  have hmemLp : ∀ k, MeasureTheory.MemLp (fun ω => simpleIntegral N (φ k) T ω) 2 P :=
    fun k => simpleIntegral_memLp_compensated N ℱ hℱ hT (φ k) (fun i => h_adapt i k)
  have hII : ∀ k k', MeasureTheory.Integrable
      (fun ω => simpleIntegral N (φ k) T ω * simpleIntegral N (φ k') T ω) P :=
    fun k k' => (hmemLp k).integrable_mul (hmemLp k')
  -- rewrite the integrand and the goal in terms of `simpleIntegral N (φ k) T`.
  have hrw : (fun ω => (∑ k : Fin K, ∑ i : Fin N₀,
        ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2)
      = fun ω => (∑ k : Fin K, simpleIntegral N (φ k) T ω) ^ 2 := by
    funext ω; congr 1; exact Finset.sum_congr rfl (fun k _ => (hI_eq k ω).symm)
  rw [hrw, show (fun ω => (∑ k : Fin K, simpleIntegral N (φ k) T ω) ^ 2)
        = fun ω => ∑ k : Fin K, ∑ k' : Fin K,
            simpleIntegral N (φ k) T ω * simpleIntegral N (φ k') T ω from
      funext (fun ω => by rw [sq]; exact Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _ (fun k _ => MeasureTheory.integrable_finsetSum _
      (fun k' _ => hII k k'))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun k' _ => hII k k')]
  rw [Finset.sum_eq_single k]
  · -- diagonal `k' = k`: single-mark isometry.
    rw [show (fun ω => simpleIntegral N (φ k) T ω * simpleIntegral N (φ k) T ω)
          = fun ω => (simpleIntegral N (φ k) T ω) ^ 2 from funext (fun ω => (sq _).symm)]
    exact simpleIntegral_L2_isometry_compensatedPoisson_sumForm N ℱ hℱ (φ k) (fun i => h_adapt i k)
  · -- off-diagonal `k' ≠ k`: disjoint-mark cross vanishes.
    intro k' _ hk'
    simp_rw [hI_eq]
    exact crossSum_disjointMark_zero N ℱ hℱ p hp0 hpmono (fun _ => B k) (fun _ => B k')
      (fun _ => hBm k) (fun _ => hBm k') (fun _ => hBf k) (fun _ => hBf k')
      (fun _ => hBdisj (Ne.symm hk')) (fun i => ξ i k) (fun i => ξ i k')
      (fun i => hξb i k) (fun i => hξb i k') (fun i => hξm i k) (fun i => hξm i k')
      (fun i => h_adapt i k) (fun i => h_adapt i k')
  · intro h; exact absurd (Finset.mem_univ k) h

end LevyStochCalc.Poisson.Compensated
