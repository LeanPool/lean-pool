/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedSimple
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedIsometry
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedIsometryL2
public import LeanPool.KLS.LevyStochCalc.Poisson.NaturalFiltration
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Martingale property of the simple compensated-Poisson integral

`simpleIntegral N φ` is adapted to a Poisson filtration `ℱ` of `N`: each time-rectangle
`timeRect i t` lies in the past `Iic t ×ˢ univ`, so its compensated mass is `ℱ_t`-measurable,
and the coefficient `ξᵢ` is `ℱ_t`-measurable once `t` reaches the partition point (the term
vanishing before). Each summand is `P`-integrable, its conditional expectation satisfies
`𝔼[ξᵢ·Ñ(timeRect i t) | ℱ_s] =ᵐ ξᵢ·Ñ(timeRect i s)` for `0 ≤ s ≤ t`, and summing over the
partition gives the martingale property of `t ↦ simpleIntegral N φ t`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Per-term `ℱ_t`-adaptedness** of the compensated simple integral. For
`t ≥ tᵢ` the coefficient `ξᵢ` is `ℱ_t`-measurable and the time-rectangle's
compensated mass is `ℱ_t`-measurable (it lives in the past `Iic t ×ˢ univ`); for
`t < tᵢ` the time-rectangle is empty and the term is `0`. -/
lemma simpleIntegral_term_adapted_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (t : ℝ)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t)
      (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) := by
  have hpre_lt_post : φ.partition i.castSucc < φ.partition i.succ :=
    φ.partition_strictMono Fin.castSucc_lt_succ
  by_cases ht_pre : φ.partition i.castSucc ≤ t
  · -- `tᵢ ≤ t`: the rectangle is in the past and `ξᵢ` is `ℱ_t`-measurable.
    have h_rect_sub : φ.timeRect i t ⊆ Set.Iic t ×ˢ Set.univ := by
      intro p hp
      rw [SimplePredictable.timeRect, Set.mem_prod] at hp
      exact ⟨le_trans hp.1.2 (min_le_right _ _), Set.mem_univ _⟩
    have h_rect_meas : MeasurableSet (φ.timeRect i t) := by
      rw [SimplePredictable.timeRect]
      exact measurableSet_Ioc.prod (φ.A_measurable i)
    have h_comp : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
        (N.compensated (φ.timeRect i t)) := by
      unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
      exact (((hℱ.measurable h_rect_sub
        h_rect_meas).ennreal_toReal).sub measurable_const).stronglyMeasurable
    exact (h_adapt_i.mono (ℱ.mono ht_pre)).mul h_comp
  · -- `t < tᵢ`: the time-rectangle is empty, so the term is `0`.
    push Not at ht_pre
    have h_min_pre : min (φ.partition i.castSucc) t = t := min_eq_right (le_of_lt ht_pre)
    have h_min_post : min (φ.partition i.succ) t = t :=
      min_eq_right (le_of_lt (lt_trans ht_pre hpre_lt_post))
    have h_rect_empty : φ.timeRect i t = ∅ := by
      rw [SimplePredictable.timeRect, h_min_pre, h_min_post, Set.Ioc_self, Set.empty_prod]
    have h_zero : (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) = fun _ => (0 : ℝ) := by
      funext ω
      rw [h_rect_empty]
      unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
      simp
    rw [h_zero]; exact stronglyMeasurable_const

/-- **`ℱ`-adaptedness of the compensated simple integral.** For an adapted simple
integrand `φ`, the process `t ↦ simpleIntegral N φ t` is strongly adapted to the
natural filtration of `N`. -/
lemma simpleIntegral_stronglyAdapted_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    MeasureTheory.StronglyAdapted ℱ
      (fun t => simpleIntegral N φ t) := by
  intro t
  change @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ t)
    (fun ω => ∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.timeRect i t) ω)
  exact Finset.stronglyMeasurable_fun_sum _
    (fun i _ => simpleIntegral_term_adapted_compensated N ℱ hℱ φ i t (h_adapt i))

/-- **First-moment integrability of a compensated mass.** For `B` with finite
reference intensity, `ω ↦ Ñ(B) = N(B) − referenceIntensity B` is `P`-integrable.
Pushforward through `poisson_law` to `poissonMeasure r`, where `n ↦ n − r` is
integrable (the Poisson law has a finite first moment). -/
lemma compensated_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => N.compensated B ω) P := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  rw [show (fun ω => N.compensated B ω)
        = (fun x : ℝ≥0∞ => x.toReal - c) ∘ (fun ω => N.N ω B) from rfl,
    ← MeasureTheory.integrable_map_measure
      (ENNReal.measurable_toReal.sub_const c).aestronglyMeasurable h_NB_meas.aemeasurable,
    N.poisson_law hB h_finite, LevyStochCalc.Poisson.poissonMeasureENN,
    MeasureTheory.integrable_map_measure
      (ENNReal.measurable_toReal.sub_const c).aestronglyMeasurable
      (measurable_from_nat).aemeasurable]
  have h_eq : ((fun x : ℝ≥0∞ => x.toReal - c) ∘ fun n : ℕ => (n : ℝ≥0∞))
      = fun n : ℕ => (n : ℝ) - c := by
    funext n; rw [Function.comp_apply, show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp]
  rw [h_eq]
  have h_int_id : MeasureTheory.Integrable
      (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
    rw [ProbabilityTheory.integrable_poissonMeasure_iff]
    have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
      rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
    simp_rw [h_norm, show ∀ n : ℕ, Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ)
        * (↑n : ℝ) = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ))
      from fun n => by ring]
    exact (summable_pow_div_factorial_mul_nat (↑r)).mul_left _
  exact h_int_id.sub (MeasureTheory.integrable_const c)

/-- The reference intensity of a clamped time-rectangle `timeRect i t` is finite:
it is `volume(Ioc …) · ν(Aᵢ)` with both factors finite (`Aᵢ` has finite `ν`-mass). -/
lemma referenceIntensity_timeRect_ne_top
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (t : ℝ) :
    LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t) ≠ ⊤ := by
  rw [SimplePredictable.timeRect, LevyStochCalc.Poisson.referenceIntensity,
    MeasureTheory.Measure.prod_prod]
  refine ENNReal.mul_ne_top ?_ (φ.A_finite i)
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  exact ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_left)

/-- **Per-term integrability** of the compensated simple integral: each summand
`ξᵢ · Ñ(timeRect i t)` is `P`-integrable (`ξᵢ` bounded, the compensated mass
integrable by `compensated_integrable` since `timeRect i t` has finite intensity). -/
lemma simpleIntegral_term_integrable_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (t : ℝ) :
    MeasureTheory.Integrable (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) P := by
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have h_rect_meas : MeasurableSet (φ.timeRect i t) := by
    rw [SimplePredictable.timeRect]; exact measurableSet_Ioc.prod (φ.A_measurable i)
  refine MeasureTheory.Integrable.bdd_mul
    (compensated_integrable N h_rect_meas (referenceIntensity_timeRect_ne_top φ i t))
    (φ.ξ_measurable i).aestronglyMeasurable (c := |M|) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]; exact (hM ω).trans (le_abs_self _)

/-- **Conditional mean-zero of a future compensated increment.** For `0 ≤ s < t'`
and a finite-mass mark set `A`, the compensated mass of the future time-rectangle
`(s, t'] ×ˢ A` has zero conditional expectation given `ℱ_s`: it is independent of
`ℱ_s` (`joint_past_future_independent`) with mean `0` (`compensated_mean_zero`), so
`condExp_indep_eq` collapses the conditional expectation to the (zero) mean. -/
lemma compensated_condExp_future_eq_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {s t' : ℝ} (hs : 0 ≤ s) (hst : s < t') {A : Set E} (hA : MeasurableSet A)
    (hA_fin : ν A ≠ ⊤) :
    P[fun ω => N.compensated (Set.Ioc s t' ×ˢ A) ω
        | ℱ s]
      =ᵐ[P] fun _ => (0 : ℝ) := by
  set B : Set (ℝ × E) := Set.Ioc s t' ×ˢ A with hB
  have hB_meas : MeasurableSet B := measurableSet_Ioc.prod hA
  have h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤ := by
    rw [hB, LevyStochCalc.Poisson.referenceIntensity, MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ hA_fin
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hle₁ := (N.measurable_eval hB_meas).comap_le
  have hle₂ := ℱ.le' s
  have hg : @Measurable Ω ℝ≥0∞ (MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) _
      (fun ω => N.N ω B) := fun u hu => ⟨u, hu, rfl⟩
  have hf : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (fun ω => N.compensated B ω) :=
    ((hg.ennreal_toReal).sub_const _).stronglyMeasurable
  have hindep : ProbabilityTheory.Indep (MeasurableSpace.comap (fun ω => N.N ω B) inferInstance)
      (ℱ s) P := by
    exact (hℱ.indep hs hst hA hA_fin).symm
  refine (MeasureTheory.condExp_indep_eq hle₁ hle₂ hf hindep).trans ?_
  filter_upwards with ω
  exact compensated_mean_zero N hB_meas h_finite

/-- **Conditional mean-zero of a time-rectangle increment `(a, b] ×ˢ A`** whose
lower endpoint dominates the conditioning time when non-degenerate. Degenerate
(`a = b`) increments are `0`; for `a = s` it is the base future increment; for
`s < a` the tower property reduces it to the base case at `ℱ_a`. -/
lemma compensated_condExp_Ioc_eq_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {s a b : ℝ} (hs : 0 ≤ s) (hab : a ≤ b) (hlow : a < b → s ≤ a)
    {A : Set E} (hA : MeasurableSet A) (hA_fin : ν A ≠ ⊤) :
    P[fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω
        | ℱ s]
      =ᵐ[P] fun _ => (0 : ℝ) := by
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · have hemp : (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) = fun _ => (0 : ℝ) := by
      funext ω
      rw [← hab_eq, Set.Ioc_self, Set.empty_prod]
      unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated; simp
    rw [hemp]
    exact Filter.EventuallyEq.of_eq
      (MeasureTheory.condExp_const (ℱ.le' s) (0 : ℝ))
  · have hsa := hlow hab_lt
    rcases eq_or_lt_of_le hsa with hsa_eq | hsa_lt
    · rw [← hsa_eq]
      exact compensated_condExp_future_eq_zero N ℱ hℱ hs (hsa_eq ▸ hab_lt) hA hA_fin
    · have h_base := compensated_condExp_future_eq_zero N ℱ hℱ (le_trans hs hsa) hab_lt hA hA_fin
      have hm₂a := ℱ.le' a
      have : SigmaFinite (P.trim hm₂a) := inferInstance
      have h_tower := MeasureTheory.condExp_condExp_of_le (μ := P)
        (f := fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω)
        (ℱ.mono hsa) hm₂a
      refine h_tower.symm.trans ((MeasureTheory.condExp_congr_ae h_base).trans ?_)
      exact Filter.EventuallyEq.of_eq
        (MeasureTheory.condExp_const (ℱ.le' s) (0 : ℝ))

/-- **a.e.-additivity of the compensated mass on disjoint finite-intensity sets.**
`Ñ(B ∪ C) =ᵐ Ñ(B) + Ñ(C)`. The reference intensity is a measure (additive
everywhere), and `N(B), N(C)` are a.e. finite (`integer_valued`), so the `toReal`
of the `N`-sum splits a.e. -/
lemma compensated_union_ae
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C)
    (hB_fin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hC_fin : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤) :
    (fun ω => N.compensated (B ∪ C) ω)
      =ᵐ[P] fun ω => N.compensated B ω + N.compensated C ω := by
  filter_upwards [N.integer_valued hB hB_fin, N.integer_valued hC hC_fin] with ω hnB hnC
  obtain ⟨nB, hnB⟩ := hnB
  obtain ⟨nC, hnC⟩ := hnC
  unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
  rw [MeasureTheory.measure_union hBC hC, MeasureTheory.measure_union hBC hC,
    ENNReal.toReal_add (by rw [hnB]; exact ENNReal.natCast_ne_top nB)
      (by rw [hnC]; exact ENNReal.natCast_ne_top nC),
    ENNReal.toReal_add hB_fin hC_fin]
  ring

/-- General finiteness of the reference intensity of a time-rectangle `(a, b] ×ˢ A`
when `A` has finite `ν`-mass. -/
lemma referenceIntensity_Ioc_prod_ne_top
    {ν : Measure E} [SigmaFinite ν] {a b : ℝ} {A : Set E} (hA_fin : ν A ≠ ⊤) :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ := by
  rw [LevyStochCalc.Poisson.referenceIntensity, MeasureTheory.Measure.prod_prod]
  refine ENNReal.mul_ne_top ?_ hA_fin
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  exact ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_left)

-- The Case-B tower-property chain (`condExp_mul` + `condExp_condExp_of_le`) is
-- heartbeat-heavy; raise the budget for this single proof.
/-- **Per-term conditional-expectation identity** for the compensated simple integral:
`𝔼[ξᵢ·Ñ(timeRect i t) | ℱ_s] =ᵐ ξᵢ·Ñ(timeRect i s)` (for `0 ≤ s ≤ t`). Case A
(`tᵢ ≤ s`): `ξᵢ` is `ℱ_s`-measurable; split `Ñ(timeRect i t) = Ñ(timeRect i s) +
Ñ(future)`, pull out `ξᵢ`, and the future increment's conditional mean is `0`. Case B
(`s < tᵢ`): `timeRect i s = ∅`, so the RHS is `0`; pull out `ξᵢ` at `ℱ_{tᵢ}`, use the
future conditional mean-zero, then the tower property to `ℱ_s`. -/
lemma simpleIntegral_term_condExp_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    {s t : ℝ} (hst : s ≤ t) :
    P[fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω
        | ℱ s]
      =ᵐ[P] fun ω => φ.ξ i ω * N.compensated (φ.timeRect i s) ω := by
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have hξmeas : Measurable (φ.ξ i) := φ.ξ_measurable i
  have hpc_lt_ps : φ.partition i.castSucc < φ.partition i.succ :=
    φ.partition_strictMono Fin.castSucc_lt_succ
  have hpc_nn : 0 ≤ φ.partition i.castSucc := by
    have := φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [φ.partition_zero] at this
  have hAfin := φ.A_finite i
  have hAmeas := φ.A_measurable i
  have hξÑ_int : ∀ B : Set (ℝ × E), MeasurableSet B →
      LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤ →
      MeasureTheory.Integrable ((φ.ξ i) * fun ω => N.compensated B ω) P := by
    intro B hBmeas hBfin
    refine MeasureTheory.Integrable.bdd_mul (compensated_integrable N hBmeas hBfin)
      hξmeas.aestronglyMeasurable (c := |M|) ?_
    filter_upwards with ω; rw [Real.norm_eq_abs]; exact (hM ω).trans (le_abs_self _)
  change P[(φ.ξ i) * fun ω => N.compensated (φ.timeRect i t) ω | ℱ.seq s]
    =ᵐ[P] (φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω
  by_cases hpc_s : φ.partition i.castSucc ≤ s
  · -- Case A
    have hs_nn : 0 ≤ s := hpc_nn.trans hpc_s
    have hξ_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s) (φ.ξ i) :=
      h_adapt_i.mono (ℱ.mono hpc_s)
    have h_min_pc_s : min (φ.partition i.castSucc) s = φ.partition i.castSucc := min_eq_left hpc_s
    have h_min_pc_t : min (φ.partition i.castSucc) t = φ.partition i.castSucc :=
      min_eq_left (hpc_s.trans hst)
    set bs := min (φ.partition i.succ) s with hbs
    set bt := min (φ.partition i.succ) t with hbt
    have hpc_le_bs : φ.partition i.castSucc ≤ bs := le_min hpc_lt_ps.le hpc_s
    have hbs_le_bt : bs ≤ bt := min_le_min (le_refl _) hst
    set newset : Set (ℝ × E) := Set.Ioc bs bt ×ˢ φ.A i with hnew
    have h_rect_s : φ.timeRect i s = Set.Ioc (φ.partition i.castSucc) bs ×ˢ φ.A i := by
      rw [SimplePredictable.timeRect, h_min_pc_s]
    have h_rect_t : φ.timeRect i t = Set.Ioc (φ.partition i.castSucc) bt ×ˢ φ.A i := by
      rw [SimplePredictable.timeRect, h_min_pc_t]
    have h_union : φ.timeRect i t = φ.timeRect i s ∪ newset := by
      rw [h_rect_t, h_rect_s, hnew, ← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc hpc_le_bs hbs_le_bt]
    have hrect_s_meas : MeasurableSet (φ.timeRect i s) := by
      rw [h_rect_s]; exact measurableSet_Ioc.prod hAmeas
    have hnew_meas : MeasurableSet newset := by rw [hnew]; exact measurableSet_Ioc.prod hAmeas
    have h_disj : Disjoint (φ.timeRect i s) newset := by
      rw [h_rect_s, hnew]
      exact Set.disjoint_left.mpr (fun p hp1 hp2 => absurd hp2.1.1 (not_lt.mpr hp1.1.2))
    have hrect_s_fin : LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i s) ≠ ⊤ :=
      h_rect_s ▸ referenceIntensity_Ioc_prod_ne_top hAfin
    have hnew_fin : LevyStochCalc.Poisson.referenceIntensity ν newset ≠ ⊤ := by
      rw [hnew]; exact referenceIntensity_Ioc_prod_ne_top hAfin
    have hcompadd : (fun ω => N.compensated (φ.timeRect i t) ω) =ᵐ[P]
        (fun ω => N.compensated (φ.timeRect i s) ω) + fun ω => N.compensated newset ω :=
      h_union ▸ compensated_union_ae N hrect_s_meas hnew_meas h_disj hrect_s_fin hnew_fin
    have hsplit : ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i t) ω) =ᵐ[P]
        ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω)
          + (φ.ξ i) * fun ω => N.compensated newset ω := by
      filter_upwards [hcompadd] with ω hω
      simp only [Pi.mul_apply, Pi.add_apply] at hω ⊢
      rw [hω]; ring
    refine (MeasureTheory.condExp_congr_ae hsplit).trans ?_
    have hint_s := hξÑ_int (φ.timeRect i s) hrect_s_meas hrect_s_fin
    have hint_new := hξÑ_int newset hnew_meas hnew_fin
    refine (MeasureTheory.condExp_add hint_s hint_new (ℱ.seq s)).trans ?_
    have hself := MeasureTheory.condExp_of_stronglyMeasurable (ℱ.le' s)
      (show @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
        ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω) from
        simpleIntegral_term_adapted_compensated N ℱ hℱ φ i s h_adapt_i) hint_s
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := ℱ.seq s) hξ_Fs hint_new (compensated_integrable N hnew_meas hnew_fin)
    have hnew_zero : P[fun ω => N.compensated newset ω | ℱ.seq s] =ᵐ[P] fun _ => (0 : ℝ) := by
      refine compensated_condExp_Ioc_eq_zero N ℱ hℱ hs_nn hbs_le_bt (fun hlt => ?_) hAmeas hAfin
      have hps_gt : s < φ.partition i.succ := by
        by_contra hle; push Not at hle
        rw [hbs, hbt, min_eq_left hle, min_eq_left (hle.trans hst)] at hlt
        exact lt_irrefl _ hlt
      rw [hbs]; exact (min_eq_right hps_gt.le).ge
    rw [hself]
    filter_upwards [hpull, hnew_zero] with ω hp hz
    simp only [Pi.add_apply, Pi.mul_apply] at hp ⊢
    rw [hp, hz]; ring
  · -- Case B
    push Not at hpc_s
    have h_rect_s_empty : φ.timeRect i s = ∅ := by
      rw [SimplePredictable.timeRect, min_eq_right hpc_s.le,
        min_eq_right (hpc_s.le.trans hpc_lt_ps.le), Set.Ioc_self, Set.empty_prod]
    have h_rhs_zero : ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω) = fun _ => (0 : ℝ) := by
      funext ω; simp only [Pi.mul_apply]; rw [h_rect_s_empty]
      unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated; simp
    rw [h_rhs_zero]
    have hrect_t_meas : MeasurableSet (φ.timeRect i t) := by
      rw [SimplePredictable.timeRect]; exact measurableSet_Ioc.prod hAmeas
    have hrect_t_fin := referenceIntensity_timeRect_ne_top φ i t
    set gt : Ω → ℝ := fun ω => N.compensated (φ.timeRect i t) ω with hgt
    set ft : Ω → ℝ := (φ.ξ i) * gt with hft
    have hpull : P[ft | ℱ.seq (φ.partition i.castSucc)] =ᵐ[P]
        (φ.ξ i) * P[gt | ℱ.seq (φ.partition i.castSucc)] :=
      MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := ℱ.seq (φ.partition i.castSucc)) h_adapt_i
        (hξÑ_int (φ.timeRect i t) hrect_t_meas hrect_t_fin)
        (compensated_integrable N hrect_t_meas hrect_t_fin)
    have ht_zero : P[gt | ℱ.seq (φ.partition i.castSucc)] =ᵐ[P] fun _ => (0 : ℝ) := by
      rw [hgt, SimplePredictable.timeRect]
      refine compensated_condExp_Ioc_eq_zero N ℱ hℱ hpc_nn
        (min_le_min hpc_lt_ps.le (le_refl t)) (fun hlt => ?_) hAmeas hAfin
      have hpct : φ.partition i.castSucc ≤ t := by
        by_contra h; push Not at h
        rw [min_eq_right h.le, min_eq_right (h.le.trans hpc_lt_ps.le)] at hlt
        exact lt_irrefl _ hlt
      exact le_min (le_refl _) hpct
    have hpc_eq_zero : P[ft | ℱ.seq (φ.partition i.castSucc)] =ᵐ[P] fun _ => (0 : ℝ) := by
      filter_upwards [hpull, ht_zero] with ω hp hz
      rw [hp]; simp only [Pi.mul_apply]; rw [hz]; ring
    have hm₂pc := ℱ.le' (φ.partition i.castSucc)
    have : SigmaFinite (P.trim hm₂pc) := inferInstance
    have htower := MeasureTheory.condExp_condExp_of_le (μ := P) (f := ft)
      (ℱ.mono hpc_s.le) hm₂pc
    refine htower.symm.trans ((MeasureTheory.condExp_congr_ae hpc_eq_zero).trans ?_)
    exact Filter.EventuallyEq.of_eq (MeasureTheory.condExp_const (ℱ.le' s) (0 : ℝ))

/-- **Martingale property of `simpleIntegral` (compensated Poisson).** For a
simple predictable integrand `φ` adapted to a filtration `ℱ` for which `N` is a
Poisson random measure, the process `t ↦ simpleIntegral N φ t` is a martingale
wrt `ℱ`.

Proof: `simpleIntegral N φ t = ∑_i ξ_i · Ñ(timeRect i t)`. Adaptedness is
`simpleIntegral_stronglyAdapted_compensated`; the cond-exp identity reduces to the
per-term identity `simpleIntegral_term_condExp_compensated` via `condExp_finsetSum`
+ `eventuallyEq_sum`. -/
lemma martingale_simpleIntegral_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => simpleIntegral N φ t)
      ℱ P := by
  refine ⟨simpleIntegral_stronglyAdapted_compensated N ℱ hℱ φ h_adapt, ?_⟩
  intro s t hst
  have h_unfold_pi : ∀ u : ℝ, (fun ω => simpleIntegral N φ u ω) =
      ∑ i : Fin φ.N, (fun ω : Ω => φ.ξ i ω * N.compensated (φ.timeRect i u) ω) := by
    intro u; ext ω; rw [Finset.sum_apply]; rfl
  change P[fun ω => simpleIntegral N φ t ω | ℱ.seq s] =ᵐ[P]
    fun ω => simpleIntegral N φ s ω
  rw [h_unfold_pi t, h_unfold_pi s]
  have h_int : ∀ i ∈ (Finset.univ : Finset (Fin φ.N)),
      MeasureTheory.Integrable
        (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) P :=
    fun i _ => simpleIntegral_term_integrable_compensated N φ i t
  refine (MeasureTheory.condExp_finsetSum h_int (m := ℱ.seq s)).trans ?_
  refine eventuallyEq_sum ?_
  intro i _
  exact simpleIntegral_term_condExp_compensated N ℱ hℱ φ i (h_adapt i) hst

end LevyStochCalc.Poisson.Compensated
