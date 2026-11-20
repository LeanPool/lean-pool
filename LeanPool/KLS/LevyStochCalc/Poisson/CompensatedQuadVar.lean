/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedProcess
public import LeanPool.KLS.LevyStochCalc.Martingale.SquareCompensator

/-!
# The quadratic-variation martingale of the compensated integral

For an adapted mark-step integrand `G`, the compensated square
`t ↦ (∫_0^t ∫_E G dÑ)² − ∫_0^t ∫_E G(u, e)² ν(de) du` is a martingale on the natural
filtration: the increment isometries of `MarkStep` give the set-level identity required by
`LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral`. The compensated square of the
`L²` integral process is then the `L¹`-limit of the stage compensated squares.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g)
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : IsPoissonFiltration N ℱ)

/-- The compensator `∫_0^t ∫_E G(u, e)² ν(de) du` of a mark-step integrand. -/
noncomputable def compensator (t : ℝ) (ω : Ω) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) t, ∫ e, (G.eval u e ω) ^ 2 ∂ν ∂volume

omit [IsProbabilityMeasure P] in
/-- The mark integral of the squared integrand is bounded, uniformly in time and sample. -/
lemma integral_eval_sq_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ u ω, ∫ e, (G.eval u e ω) ^ 2 ∂ν ≤ C := by
  obtain ⟨C, hC⟩ := G.eval_bounded
  refine ⟨C ^ 2 * (ν (⋃ k, G.B k)).toReal, by positivity, fun u ω => ?_⟩
  have hint : IntegrableOn (fun _ : E => C ^ 2) (⋃ k, G.B k) ν :=
    integrableOn_const G.measure_iUnion_B_ne_top
  calc ∫ e, (G.eval u e ω) ^ 2 ∂ν
      = ∫ e in ⋃ k, G.B k, (G.eval u e ω) ^ 2 ∂ν := by
        rw [← integral_indicator G.measurableSet_iUnion_B]
        refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
        by_cases he : e ∈ ⋃ k, G.B k
        · rw [Set.indicator_of_mem he]
        · rw [Set.indicator_of_notMem he]
          change (G.eval u e ω) ^ 2 = 0
          rw [G.eval_support ω u e he]
          ring
    _ ≤ ∫ _ in ⋃ k, G.B k, C ^ 2 ∂ν := by
        refine setIntegral_mono_on ?_ hint G.measurableSet_iUnion_B fun e _ => ?_
        · refine hint.mono' ?_ (Filter.Eventually.of_forall fun e => ?_)
          · exact ((G.eval_measurable.comp (by fun_prop :
                Measurable fun e : E => ((ω, u, e) : Ω × ℝ × E))).pow_const 2).aestronglyMeasurable
          · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hC ω u e, abs_nonneg (G.eval u e ω), sq_abs (G.eval u e ω)]
        · nlinarith [hC ω u e, abs_nonneg (G.eval u e ω), sq_abs (G.eval u e ω)]
    _ = C ^ 2 * (ν (⋃ k, G.B k)).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_comm, measureReal_def]

omit [IsProbabilityMeasure P] in
lemma integral_eval_sq_nonneg (u : ℝ) (ω : Ω) : 0 ≤ ∫ e, (G.eval u e ω) ^ 2 ∂ν :=
  integral_nonneg fun _ => sq_nonneg _

omit [IsProbabilityMeasure P] in
lemma measurable_integral_eval_sq :
    Measurable (fun q : Ω × ℝ => ∫ e, (G.eval q.2 e q.1) ^ 2 ∂ν) := by
  have h : Measurable (fun r : (Ω × ℝ) × E => (G.eval r.1.2 r.2 r.1.1) ^ 2) :=
    (G.eval_measurable.comp (by fun_prop :
      Measurable fun r : (Ω × ℝ) × E => ((r.1.1, r.1.2, r.2) : Ω × ℝ × E))).pow_const 2
  exact h.stronglyMeasurable.integral_prod_right'.measurable

omit [IsProbabilityMeasure P] in
lemma compensator_nonneg (t : ℝ) (ω : Ω) : 0 ≤ G.compensator t ω :=
  integral_nonneg fun u => G.integral_eval_sq_nonneg u ω

omit [IsProbabilityMeasure P] in
/-- The compensator vanishes at nonpositive times. -/
lemma compensator_of_nonpos {t : ℝ} (ht : t ≤ 0) (ω : Ω) : G.compensator t ω = 0 := by
  unfold compensator
  rw [Measure.restrict_eq_zero.2 (by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_of_nonpos (by linarith)), integral_zero_measure]

omit [IsProbabilityMeasure P] in
/-- The mark integral of the squared integrand is integrable in time over any set of finite
Lebesgue measure. -/
lemma integrableOn_integral_eval_sq {S : Set ℝ} (hS : volume S ≠ ⊤) (ω : Ω) :
    IntegrableOn (fun u => ∫ e, (G.eval u e ω) ^ 2 ∂ν) S volume := by
  obtain ⟨_, hC⟩ := Classical.choose_spec G.integral_eval_sq_le
  have hint : IntegrableOn (fun _ : ℝ => Classical.choose G.integral_eval_sq_le) S volume :=
    integrableOn_const hS
  have hmeas : AEStronglyMeasurable (fun u => ∫ e, (G.eval u e ω) ^ 2 ∂ν)
      (volume.restrict S) :=
    ((G.measurable_integral_eval_sq).comp (measurable_prodMk_left (x := ω))).aestronglyMeasurable
  exact hint.mono' hmeas (Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (G.integral_eval_sq_nonneg u ω)]
    exact hC u ω)

omit [IsProbabilityMeasure P] in
lemma compensator_le {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    G.compensator t ω ≤ (Classical.choose G.integral_eval_sq_le) * t := by
  obtain ⟨_, hC⟩ := Classical.choose_spec G.integral_eval_sq_le
  set C := Classical.choose G.integral_eval_sq_le
  have hint : IntegrableOn (fun _ : ℝ => C) (Set.Icc (0 : ℝ) t) volume :=
    integrableOn_const measure_Icc_lt_top.ne
  calc G.compensator t ω ≤ ∫ _ in Set.Icc (0 : ℝ) t, C ∂volume :=
        setIntegral_mono_on (G.integrableOn_integral_eval_sq measure_Icc_lt_top.ne ω) hint
          measurableSet_Icc fun u _ => hC u ω
    _ = C * t := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc, sub_zero,
          ENNReal.toReal_ofReal ht, mul_comm]

omit [IsProbabilityMeasure P] in
/-- The compensator increment between two nonnegative times is the integral of the squared
integrand over the intervening interval. -/
lemma compensator_sub {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ω : Ω) :
    G.compensator t ω - G.compensator s ω
      = ∫ u in Set.Ioc s t, ∫ e, (G.eval u e ω) ^ 2 ∂ν ∂volume := by
  have hdisjoint : Disjoint (Set.Icc (0 : ℝ) s) (Set.Ioc s t) :=
    (Set.Iic_disjoint_Ioc (c := t) (le_refl s)).mono Set.Icc_subset_Iic_self subset_rfl
  unfold compensator
  rw [← Set.Icc_union_Ioc_eq_Icc hs hst, setIntegral_union hdisjoint measurableSet_Ioc
    (G.integrableOn_integral_eval_sq measure_Icc_lt_top.ne ω)
    (G.integrableOn_integral_eval_sq measure_Ioc_lt_top.ne ω)]
  ring

omit [IsProbabilityMeasure P] in
/-- Fubini for the squared integrand over a time set of finite Lebesgue measure. -/
lemma integral_integral_eval_sq_swap {S : Set ℝ} (hSfin : volume S ≠ ⊤) (ω : Ω) :
    ∫ e, ∫ σ in S, (G.eval σ e ω) ^ 2 ∂volume ∂ν
      = ∫ σ in S, ∫ e, (G.eval σ e ω) ^ 2 ∂ν ∂volume := by
  obtain ⟨C, hC⟩ := G.eval_bounded
  refine integral_integral_swap ?_
  have hmeas : Measurable (fun q : E × ℝ => (G.eval q.2 q.1 ω) ^ 2) :=
    (G.eval_measurable.comp (by fun_prop :
      Measurable fun q : E × ℝ => ((ω, q.2, q.1) : Ω × ℝ × E))).pow_const 2
  have hind : Integrable (((⋃ k, G.B k) ×ˢ (Set.univ : Set ℝ)).indicator (fun _ => C ^ 2))
      (ν.prod (volume.restrict S)) := by
    rw [integrable_indicator_iff (G.measurableSet_iUnion_B.prod MeasurableSet.univ)]
    refine integrableOn_const ?_
    rw [Measure.prod_prod, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top G.measure_iUnion_B_ne_top hSfin
  refine hind.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
  change ‖(G.eval q.2 q.1 ω) ^ 2‖ ≤ _
  by_cases hq : q.1 ∈ ⋃ k, G.B k
  · rw [Set.indicator_of_mem (Set.mem_prod.2 ⟨hq, Set.mem_univ _⟩), Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
    nlinarith [hC ω q.2 q.1, abs_nonneg (G.eval q.2 q.1 ω), sq_abs (G.eval q.2 q.1 ω)]
  · have hq' : q ∉ (⋃ k, G.B k) ×ˢ (Set.univ : Set ℝ) :=
      fun h ↦ hq (Set.mem_prod.mp h).1
    rw [Set.indicator_of_notMem hq', G.eval_support ω q.2 q.1 hq]
    simp

lemma measurable_compensator (t : ℝ) : Measurable (G.compensator t) :=
  G.measurable_integral_eval_sq.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) t)) |>.measurable

lemma integrable_compensator (t : ℝ) : Integrable (G.compensator t) P := by
  rcases le_or_gt 0 t with ht | ht
  · refine Integrable.mono' (integrable_const (Classical.choose G.integral_eval_sq_le * t))
      (G.measurable_compensator t).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (G.compensator_nonneg t ω)]
    exact G.compensator_le ht ω
  · have h : G.compensator t = fun _ => 0 := funext fun ω => G.compensator_of_nonpos ht.le ω
    rw [h]
    exact integrable_const 0

/-- The compensator up to time `t` is measurable for the natural filtration at time `t`. -/
lemma compensator_stronglyMeasurable (hG : G.Adapted ℱ) (t : ℝ) :
    @StronglyMeasurable Ω ℝ _ (ℱ t) (G.compensator t) := by
  rcases lt_or_ge t 0 with ht | ht
  · have h : G.compensator t = fun _ => 0 := funext fun ω => G.compensator_of_nonpos ht.le ω
    rw [h]
    exact stronglyMeasurable_const
  · let G' : @MarkStep Ω (ℱ t) E _ ν _ (g.clamp t ht) :=
      @MarkStep.mk Ω (ℱ t) E _ ν _ (g.clamp t ht) G.K G.B
        G.B_measurable G.B_finite
        (fun i k ω => if i < (g.clamp t ht).N₀ then G.ξ i k ω else 0)
        (fun i k => by
          obtain ⟨M, hM⟩ := G.ξ_bounded i k
          refine ⟨|M|, fun ω => ?_⟩
          split_ifs
          · exact (hM ω).trans (le_abs_self M)
          · rw [abs_zero]
            exact abs_nonneg M)
        (fun i k => by
          by_cases hi : i < (g.clamp t ht).N₀
          · simp only [hi, ite_true]
            exact ((hG i (g.lt_of_lt_clampIndex hi).1 k).mono
              (ℱ.mono (g.lt_of_lt_clampIndex hi).2.le)).measurable
          · simp only [hi, ite_false]
            exact measurable_const)
    have hev : ∀ u e ω, @eval Ω (ℱ t) E _ ν _ (g.clamp t ht) G' u e ω
        = (G.clamp t ht).eval u e ω := by
      intro u e ω
      unfold eval
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      change _ * ∑ k : Fin G.K, (if i < (g.clamp t ht).N₀ then G.ξ i k ω else 0)
          * (G.B k).indicator (fun _ => (1 : ℝ)) e
        = _ * ∑ k : Fin G.K, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e
      simp only [hi, ite_true]
    have hcomp : G.compensator t
        = @compensator Ω (ℱ t) E _ ν _ (g.clamp t ht) G' t := by
      funext ω
      unfold compensator
      refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
      beta_reduce
      rw [hev, G.eval_clamp t ht, ite_eq_left hu.2]
    rw [hcomp]
    exact (@measurable_compensator Ω (ℱ t) E _ ν _ (g.clamp t ht) G'
      t).stronglyMeasurable

include hℱ in
/-- The set integral of the squared increment of the integral over a set measurable at the
earlier time equals that of the increment of the compensator. -/
theorem setIntegral_increment_sq_eq (hG : G.Adapted ℱ) {s t : ℝ} (hst : s ≤ t) {B : Set Ω}
    (hB : MeasurableSet[ℱ s] B) :
    ∫ ω in B, (G.integral N t ω - G.integral N s ω) ^ 2 ∂P
      = ∫ ω in B, (G.compensator t ω - G.compensator s ω) ∂P := by
  have hBm : MeasurableSet B := ℱ.le s B hB
  set w : Ω → ℝ := B.indicator (fun _ => (1 : ℝ)) with hwdef
  have hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C := ⟨1, fun ω => abs_indicator_one_le B ω⟩
  have hwm : Measurable w := measurable_const.indicator hBm
  have hwa : @StronglyMeasurable Ω ℝ _ (ℱ s) w :=
    stronglyMeasurable_const.indicator hB
  have hind : ∀ f : Ω → ℝ, ∫ ω, (w ω) ^ 2 * f ω ∂P = ∫ ω in B, f ω ∂P := by
    intro f
    rw [← integral_indicator hBm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ B
    · simp [hwdef, Set.indicator_of_mem hω]
    · simp [hwdef, Set.indicator_of_notMem hω]
  have hsq : ∀ f : Ω → ℝ, ∫ ω, (w ω * f ω) ^ 2 ∂P = ∫ ω in B, (f ω) ^ 2 ∂P := by
    intro f
    rw [← hind]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    ring
  rcases eq_or_lt_of_le hst with rfl | hlt
  · simp
  rcases le_or_gt t 0 with ht | ht
  · have h1 : ∀ ω, G.integral N t ω - G.integral N s ω = 0 := fun ω => by
        rw [G.integral_eq_zero_of_nonpos N ht, G.integral_eq_zero_of_nonpos N (hst.trans ht),
        sub_zero]
    have h2 : ∀ ω, G.compensator t ω - G.compensator s ω = 0 := fun ω => by
      rw [G.compensator_of_nonpos ht, G.compensator_of_nonpos (hst.trans ht), sub_zero]
    simp only [h1, h2]
    simp
  rcases le_or_gt s 0 with hs | hs
  · have h1 : ∀ ω, G.integral N t ω - G.integral N s ω = G.integral N t ω := fun ω => by
      rw [G.integral_eq_zero_of_nonpos N hs, sub_zero]
    have h2 : ∀ ω, G.compensator t ω - G.compensator s ω = G.compensator t ω := fun ω => by
      rw [G.compensator_of_nonpos hs, sub_zero]
    simp only [h1, h2]
    rw [← hsq, G.integral_weight_zero_sq N hℱ hw hwm hG ht.le
      (hwa.mono (ℱ.mono hs)), ← hind]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    beta_reduce
    rw [G.integral_integral_eval_sq_swap measure_Icc_lt_top.ne]
    rfl
  · rw [← hsq, G.integral_weight_incr_sq N hℱ hw hwm hs hlt hG hwa, ← hind]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    beta_reduce
    rw [G.integral_integral_eval_sq_swap measure_Ioc_lt_top.ne,
      G.compensator_sub hs.le hlt.le]

include hℱ in
/-- The compensated square `(∫_0^t ∫_E G dÑ)² − ∫_0^t ∫_E G² dν du` of an adapted mark-step
integrand is a martingale on the natural filtration. -/
theorem martingale_sq_sub_compensator (hG : G.Adapted ℱ) :
    Martingale (fun t ω => (G.integral N t ω) ^ 2 - G.compensator t ω)
      ℱ P :=
  LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral (G.martingale_integral N hℱ hG)
    (fun t => G.memLp_integral N t) (fun t => G.compensator_stronglyMeasurable hG t)
    (fun t => G.integrable_compensator t)
    (fun _ _ hst _ hB => G.setIntegral_increment_sq_eq N hℱ hG hst hB)

end MarkStep

end LevyStochCalc.Poisson.Compensated
