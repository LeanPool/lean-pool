/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral
public import Mathlib.Probability.CondVar

/-! # The time-indexed Itô isometry for the general Itô integral (B1b)

B1b built the general Itô integral `(φ●B)_t = ∫₀ᵗ φ dB` and proved it a continuous
L² martingale, with the contraction `‖(φ●B)_t‖ ≤ ‖φ‖` and the terminal isometry
`‖(φ●B)_T‖ = ‖φ‖`. This file proves the **explicit time-indexed Itô isometry**

`E[(φ●B)_t²] = ∫_{(0,t]×Ω} φ² d(trimMeasure T)`  (= `∫₀ᵗ E[φ_s²] ds`),

the L²-energy law that B1b deferred. On a simple process `V` the LHS is B1a's
`itoSimpleProcess_isometry_time` (the t-capped predictable-rectangle double sum);
the RHS is the same double sum, via a **band-restricted** version of
`ItoIntegralL2.integral_rectTerm_mul` (the time integral picks up an `∩ (0,t]`).
The general case follows by density.

## Main results

* `itoProcessCLM_norm_sq`: for `t ≤ T` and a predictable `φ ∈ L²([0,T])`,
  `E[(φ●B)_t²] = ∫_{(0,t]×Ω} φ² d(trimMeasure T)`.
* `setIntegral_Ioc_prod_add`: the band integral of an integrable space-time function is additive
  over adjacent time bands.
* `clm_band_energy`: for `u ≤ v ≤ T`, `𝔼[((φ●B)_v − (φ●B)_u)²]` is the band energy
  `∫_{(u,v]×Ω} φ² d(trimMeasure T)`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Ch 7

## Tags

time-indexed Itô isometry, Itô isometry, energy identity, stochastic integral, L² martingale,
MSC 60H05, MSC 60G44
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralProcessGeneral

open MeasureTheory ProbabilityTheory ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

omit [IsProbabilityMeasure μ] in
/-- **Band-restricted rectangle cross-integral.** The `ItoIntegralL2.integral_rectTerm_mul`
identity with the time integral restricted to `(0,t]`: the overlap factor gains an
`∩ (0,t]`, capping the right endpoint at `t`. (Fubini over the restricted product
`(timeMeasure.restrict (Ioc 0 t)) ⊗ μ`, then `timeMeasure` of the triple interval
intersection.) -/
private lemma integral_rectTerm_mul_band (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (p q : ℝ≥0 × ℝ≥0) :
    ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)),
        rectTerm hBmeas V p z * rectTerm hBmeas V q z ∂(timeMeasure.prod μ)
      = (∫ ω, V.value p ω * V.value q ω ∂μ)
          * max 0 ((min (min (p.2 : ℝ) q.2) (t : ℝ)) - (max (p.1 : ℝ) q.1)) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hfun : (fun z : ℝ≥0 × Ω ↦ rectTerm hBmeas V p z * rectTerm hBmeas V q z)
      = fun z ↦ ((Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) z.1
                    * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) z.1)
                  * (V.value p z.2 * V.value q z.2) := by
    funext z; simp only [rectTerm, elemIntegrand]; ring
  rw [setIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ)
        (fun z _ ↦ congrFun hfun z),
      ← Measure.restrict_prod_eq_prod_univ,
      integral_prod_mul
        (fun i : ℝ≥0 ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
          * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i)
        (fun ω ↦ V.value p ω * V.value q ω), mul_comm]
  congr 1
  have hpt : ∀ i : ℝ≥0, (Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
        * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i
        = (Set.Ioc p.1 p.2 ∩ Set.Ioc q.1 q.2).indicator (1 : ℝ≥0 → ℝ) i := by
    intro i; rw [Set.inter_indicator_one]; rfl
  simp_rw [hpt]
  rw [integral_indicator_one (measurableSet_Ioc.inter measurableSet_Ioc), Measure.real_def,
      Measure.restrict_apply (measurableSet_Ioc.inter measurableSet_Ioc),
      Set.Ioc_inter_Ioc, Set.Ioc_inter_Ioc, timeMeasure_Ioc, ENNReal.toReal_ofReal']
  push_cast
  rw [max_eq_left (le_max_of_le_left (by positivity))]
  exact max_comm _ _

omit hB in
/-- **Band-overlap reconciliation (pure ℝ).** B1a's time-indexed isometry expresses the
overlap of two predictable rectangles as `max 0 (min(p.2∧t, q.2∧t) − max(p.1∧t, q.1∧t))`
(each endpoint individually truncated at `t`), whereas the band-restricted cross-integral
(`integral_rectTerm_mul_band`) produces `max 0 (min(p.2∧q.2, t) − max(p.1, q.1))` (the joint
overlap intersected with `(0,t]`). These are equal: both measure the length of
`(p.1,p.2] ∩ (q.1,q.2] ∩ (0,t]`. When the joint overlap is nonempty its left endpoint
`max p.1 q.1 < t`, so the individual `∧t`-truncations on the left are inert; when empty,
both clamp to `0`. -/
lemma band_overlap_real (P1 P2 Q1 Q2 T : ℝ) :
    max 0 (min (min P2 T) (min Q2 T) - max (min P1 T) (min Q1 T))
      = max 0 (min (min P2 Q2) T - max P1 Q1) := by
  -- The right endpoints coincide unconditionally: `(P2∧T)∧(Q2∧T) = (P2∧Q2)∧T`.
  have hR : min (min P2 T) (min Q2 T) = min (min P2 Q2) T := by
    rw [min_min_min_comm, min_self]
  rw [hR]
  rcases le_total (max P1 Q1) T with hLT | hLT
  · -- Overlap can be nonempty: the left `∧t`-truncations are inert.
    rw [min_eq_left ((le_max_left P1 Q1).trans hLT),
        min_eq_left ((le_max_right P1 Q1).trans hLT)]
  · -- `max P1 Q1 ≥ T ≥` right endpoint: both differences are `≤ 0`, both clamp to `0`.
    have hRle : min (min P2 Q2) T ≤ T := min_le_right _ _
    have hL : max (min P1 T) (min Q1 T) = T := by
      apply le_antisymm (max_le (min_le_right _ _) (min_le_right _ _))
      rcases le_total P1 Q1 with h | h
      · rw [max_eq_right h] at hLT; exact le_max_of_le_right (le_min hLT le_rfl)
      · rw [max_eq_left h] at hLT; exact le_max_of_le_left (le_min hLT le_rfl)
    rw [hL, max_eq_left (by linarith : min (min P2 Q2) T - T ≤ 0),
        max_eq_left (by linarith : min (min P2 Q2) T - max P1 Q1 ≤ 0)]

omit hB in
/-- **Restricting the horizon-`T` predictable measure to the `(0,t]` band gives the
horizon-`t` measure** (for `t ≤ T`). Both are restrictions of the same full predictable
trim; `band_t ∩ band_T = band_t`. This lets the time-indexed energy
`∫_{(0,t]} · d(trimMeasure T)` collapse to a plain integral against `trimMeasure t`. -/
private lemma trimMeasure_restrict_band {t T : ℝ≥0} (htT : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u)) :
    (trimMeasure (μ := μ) T hBmeas).restrict (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω))
      = trimMeasure (μ := μ) t hBmeas := by
  rw [trimMeasure_eq_restrict T hBmeas,
      Measure.restrict_restrict_of_subset
        (Set.prod_mono (Set.Ioc_subset_Ioc le_rfl htT) subset_rfl),
      trimMeasure_eq_restrict t hBmeas]

omit hB in
/-- **Dropping the horizon-`t` predictable trim** to the untrimmed product over the
`(0,t]` band. `trimMeasure t = ((timeMeasure.restrict (0,t]) ⊗ μ).trim`; `integral_trim`
removes the trim (legal for predictable-strongly-measurable `f`) and
`Measure.restrict_prod_eq_prod_univ` moves the time-restriction out to a band on the
product. -/
private lemma integral_trimMeasure {t : ℝ≥0} (hBmeas : ∀ u, Measurable (B u))
    {f : ℝ≥0 × Ω → ℝ}
    (hf : StronglyMeasurable[(natFiltration hBmeas).predictable] f) :
    ∫ z, f z ∂(trimMeasure (μ := μ) t hBmeas)
      = ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), f z ∂(timeMeasure.prod μ) := by
  rw [show trimMeasure (μ := μ) t hBmeas
        = ((timeMeasureHorizon t).prod μ).trim (natFiltration hBmeas).predictable_le_prod from rfl,
      integral_trim (natFiltration hBmeas).predictable_le_prod hf,
      show ((timeMeasureHorizon t).prod μ : Measure (ℝ≥0 × Ω))
          = (timeMeasure.prod μ).restrict (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)) from by
        rw [timeMeasureHorizon, Measure.restrict_prod_eq_prod_univ]]

omit [IsProbabilityMeasure μ] in
/-- **Time-indexed energy of a simple process (RHS form).** For `t ≤ T`, the
predictable `L²`-energy of `uncurry V` over the `(0,t]` band equals the truncated
predictable-rectangle double sum: collapse band+trim to the horizon-`t` measure
(`trimMeasure_restrict_band`), drop the trim (`integral_trimMeasure`), then expand the
square and Fubini-factorise each cross-term (`integral_rectTerm_mul_band`). Mirrors
`ItoIntegralL2.simpleProcessL2_norm_sq` with the band cap. -/
private lemma band_integral_uncurry_sq {t T : ℝ≥0} (htT : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u)) (V : SimpleProcess ℝ (natFiltration hBmeas)) :
    ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)),
        (Function.uncurry ⇑V z) ^ 2 ∂(trimMeasure (μ := μ) T hBmeas)
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (min (p.2 : ℝ) q.2) (t : ℝ)) - max (p.1 : ℝ) q.1) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  -- (A) collapse band+trim to the horizon-`t` measure, then drop the trim.
  rw [trimMeasure_restrict_band htT]
  simp only [pow_two]
  have hsm : StronglyMeasurable[(natFiltration hBmeas).predictable]
      (fun z ↦ Function.uncurry ⇑V z * Function.uncurry ⇑V z) :=
    V.isStronglyPredictable.mul V.isStronglyPredictable
  rw [integral_trimMeasure hBmeas hsm]
  -- (B) expand the square into the rectangle double sum and integrate termwise.
  have hint : ∀ p ∈ V.value.support, ∀ q ∈ V.value.support,
      Integrable (fun z ↦ rectTerm hBmeas V p z * rectTerm hBmeas V q z) (timeMeasure.prod μ) :=
    fun p _ q _ ↦ (memLp_rectTerm hBmeas V p).integrable_mul (memLp_rectTerm hBmeas V q)
  have hsq : (fun z ↦ Function.uncurry ⇑V z * Function.uncurry ⇑V z)
      =ᵐ[(timeMeasure.prod μ).restrict (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω))]
        fun z ↦ ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          rectTerm hBmeas V p z * rectTerm hBmeas V q z := by
    filter_upwards [ae_restrict_of_ae (uncurry_ae_eq_sum_rectTerm hBmeas V)] with z hz
    rw [hz, Finset.sum_mul_sum]
  rw [integral_congr_ae hsq,
      integral_finsetSum _ (fun p hp ↦
        (integrable_finsetSum _ fun q hq ↦ hint p hp q hq).integrableOn)]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [integral_finsetSum _ fun q hq ↦ (hint p hp q hq).integrableOn]
  exact Finset.sum_congr rfl fun q _ ↦ integral_rectTerm_mul_band hB t hBmeas V p q

omit [IsProbabilityMeasure μ] in
/-- **Time-indexed Itô isometry on a simple process.** `‖(V●B)_t‖² = ∫_{(0,t]×Ω}(uncurry V)²`
for `t ≤ T`: the LHS is B1a's `itoSimpleProcess_isometry_time` (the per-endpoint
`∧t`-truncated predictable-rectangle double sum); the RHS is `band_integral_uncurry_sq`
(the joint-overlap-`∩(0,t]` double sum); the two overlap forms agree pointwise by
`band_overlap_real`. -/
private lemma itoSimpleProcessLp_band_isometry {t T : ℝ≥0} (htT : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u)) (V : SimpleProcess ℝ (natFiltration hBmeas)) :
    ‖itoSimpleProcessLp (μ := μ) hB hBmeas V t‖ ^ 2
      = ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)),
          (Function.uncurry ⇑V z) ^ 2 ∂(trimMeasure (μ := μ) T hBmeas) := by
  rw [band_integral_uncurry_sq hB htT hBmeas V]
  have hLHS : ‖itoSimpleProcessLp (μ := μ) hB hBmeas V t‖ ^ 2
      = ∫ ω, (itoSimpleProcess hBmeas V t ω) ^ 2 ∂μ := by
    rw [lp_two_norm_sq (itoSimpleProcessLp hB hBmeas V t)]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_itoSimpleProcess hB hBmeas V t).coeFn_toLp] with ω hω
    rw [show (itoSimpleProcessLp hB hBmeas V t : Ω → ℝ) ω = itoSimpleProcess hBmeas V t ω from hω]
  rw [hLHS, itoSimpleProcess_isometry_time hB hBmeas V t]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  push_cast
  exact band_overlap_real _ _ _ _ _

omit hB in
/-- `(0,t]×Ω` is measurable for the predictable σ-algebra carried by `trimMeasure`. -/
lemma measurableSet_band (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    MeasurableSet[(natFiltration hBmeas).predictable] (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)) :=
  MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := natFiltration hBmeas) 0 t
    MeasurableSet.univ

omit [IsProbabilityMeasure μ] hB in
/-- Truncation to the `(0,t]`-band keeps `L²`. -/
private lemma memLp_truncBand (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    MemLp ((Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)).indicator (φ : ℝ≥0 × Ω → ℝ)) 2
      (trimMeasure (μ := μ) T hBmeas) :=
  (Lp.memLp φ).indicator (measurableSet_band t hBmeas).nullMeasurableSet

omit [IsProbabilityMeasure μ] hB in
/-- **Band truncation as a norm-`≤1` CLM** on the predictable `L²` space: pointwise
indicator multiplication `φ ↦ 𝟙_{(0,t]×Ω} · φ` (on `L²` this is the orthogonal projection
onto the `(0,t]`-band, but it is formalised here only as a norm-`≤1` CLM — `mkContinuous`
via `eLpNorm_indicator_le`). The general time-indexed isometry reads
`‖itoProcessCLM T t φ‖² = ‖truncCLM T t φ‖²` — both sides continuous in `φ`, equal on the
dense simple processes. -/
private noncomputable def truncCLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) →L[ℝ]
      Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  LinearMap.mkContinuous
    { toFun := fun φ ↦ (memLp_truncBand T t hBmeas φ).toLp
        ((Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)).indicator (φ : ℝ≥0 × Ω → ℝ))
      map_add' := fun φ ψ ↦ by
        refine Lp.ext ?_
        filter_upwards [(memLp_truncBand T t hBmeas (φ + ψ)).coeFn_toLp,
          Lp.coeFn_add ((memLp_truncBand T t hBmeas φ).toLp _)
            ((memLp_truncBand T t hBmeas ψ).toLp _),
          (memLp_truncBand T t hBmeas φ).coeFn_toLp,
          (memLp_truncBand T t hBmeas ψ).coeFn_toLp,
          Lp.coeFn_add φ ψ] with z e_sum e_radd e_φ e_ψ h_φψ
        rw [e_sum, e_radd, Pi.add_apply, e_φ, e_ψ]
        simp only [Set.indicator_apply, h_φψ, Pi.add_apply]
        split_ifs <;> ring
      map_smul' := fun c φ ↦ by
        refine Lp.ext ?_
        filter_upwards [(memLp_truncBand T t hBmeas (c • φ)).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_truncBand T t hBmeas φ).toLp _),
          (memLp_truncBand T t hBmeas φ).coeFn_toLp,
          Lp.coeFn_smul c φ] with z e_sm e_rsmul e_φ h_φ
        rw [e_sm, RingHom.id_apply, e_rsmul, Pi.smul_apply, e_φ]
        simp only [Set.indicator_apply, h_φ, Pi.smul_apply, smul_eq_mul]
        split_ifs <;> ring }
    1 (fun φ ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [one_mul, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.memLp φ).eLpNorm_ne_top
        (eLpNorm_indicator_le _ (measurableSet_band t hBmeas).nullMeasurableSet))

omit [IsProbabilityMeasure μ] hB in
/-- **The truncation CLM realises the band energy.** `‖truncCLM T t φ‖² = ∫_{(0,t]×Ω} φ²`:
its value is `𝟙_{(0,t]} · φ`, whose squared `L²`-norm integrates `φ²` over the band. This is
the continuous RHS the general isometry equalises against. -/
private lemma truncCLM_norm_sq (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ‖truncCLM (μ := μ) T t hBmeas φ‖ ^ 2
      = ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), (φ z) ^ 2
          ∂(trimMeasure (μ := μ) T hBmeas) := by
  rw [lp_two_norm_sq, ← integral_indicator (measurableSet_band t hBmeas)]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_truncBand T t hBmeas φ).coeFn_toLp] with z hz
  rw [show (truncCLM (μ := μ) T t hBmeas φ : ℝ≥0 × Ω → ℝ) z
        = (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)).indicator (φ : ℝ≥0 × Ω → ℝ) z from hz]
  by_cases hzm : z ∈ (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω))
  · rw [Set.indicator_of_mem hzm, Set.indicator_of_mem hzm]
  · rw [Set.indicator_of_notMem hzm, Set.indicator_of_notMem hzm]; norm_num

/-- **The time-indexed Itô isometry (B1b, general integrand).** For `t ≤ T` and any predictable
`φ ∈ L²([0,T])`, `E[(φ●B)_t²] = ∫_{(0,t]×Ω} φ² d(predictable measure)` (`= ∫₀ᵗ E[φ_s²] ds`).
Both `φ ↦ ‖(φ●B)_t‖²` (a CLM norm) and `φ ↦ ∫_{(0,t]} φ²` (`= ‖truncCLM T t φ‖²`) are continuous,
and they agree on the dense simple processes (`itoSimpleProcessLp_band_isometry`), so they agree
everywhere (`DenseRange.equalizer`). This is the deferred L²-energy law completing B1b's isometry
— the per-`t` refinement of the terminal `itoProcessCLM_norm_terminal`. -/
theorem itoProcessCLM_norm_sq {t T : ℝ≥0} (htT : t ≤ T) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ‖itoProcessCLM hB T t hBmeas φ‖ ^ 2
      = ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), (φ z) ^ 2
          ∂(trimMeasure (μ := μ) T hBmeas) := by
  rw [← truncCLM_norm_sq T t hBmeas φ]
  refine congrFun (DenseRange.equalizer (simpleAssemblyHorizon_denseRange (μ := μ) T hBmeas)
    ((continuous_pow 2).comp (itoProcessCLM hB T t hBmeas).continuous.norm)
    ((continuous_pow 2).comp (truncCLM (μ := μ) T t hBmeas).continuous.norm)
    (funext fun V ↦ ?_)) φ
  simp only [Function.comp_apply]
  rw [itoProcessCLM_simpleAssemblyHorizon, truncCLM_norm_sq,
      itoSimpleProcessLp_band_isometry hB htT hBmeas V.val]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (memLp_uncurry_trimMeasure T hBmeas V.val).coeFn_toLp] with z hz
  rw [show (simpleAssemblyHorizon (μ := μ) T hBmeas V : ℝ≥0 × Ω → ℝ) z
        = Function.uncurry ⇑V.val z from hz]


omit hB [IsProbabilityMeasure μ] in
/-- **The band integral is additive in the time band**: for an integrable space-time function the
integral over `(a,c] × Ω` of the predictable trim measure is the sum of the integrals over the
adjacent bands `(a,b] × Ω` and `(b,c] × Ω`. -/
theorem setIntegral_Ioc_prod_add {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {F : ℝ≥0 × Ω → ℝ}
    (hF : Integrable F (trimMeasure (μ := μ) T hBmeas)) {a b c : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) :
    ∫ z in Set.Ioc a c ×ˢ (Set.univ : Set Ω), F z ∂(trimMeasure (μ := μ) T hBmeas)
      = ∫ z in Set.Ioc a b ×ˢ (Set.univ : Set Ω), F z ∂(trimMeasure (μ := μ) T hBmeas)
        + ∫ z in Set.Ioc b c ×ˢ (Set.univ : Set Ω), F z ∂(trimMeasure (μ := μ) T hBmeas) := by
  rw [← Set.Ioc_union_Ioc_eq_Ioc hab hbc, Set.union_prod]
  exact setIntegral_union (Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le le_rfl) _ _)
    (measurableSet_predictable_Ioc_prod b c MeasurableSet.univ) hF.integrableOn hF.integrableOn

/-- **The band-energy law of the Itô integral process**: the `L²` energy of the increment of
`(φ●B)` over a band `(u,v]`, `v ≤ T`, is the band energy of the integrand,

  `𝔼[((φ●B)_v − (φ●B)_u)²] = ∫_{(u,v]×Ω} φ² d(trimMeasure T)`.

Pythagoras for the martingale `itoProcessCLM` (`(φ●B)_u` is the conditional expectation of
`(φ●B)_v`: `condVar_ae_eq_condExp_sq_sub_sq_condExp`), then the time-indexed isometry
`itoProcessCLM_norm_sq` at `v` and at `u` and the band additivity `setIntegral_Ioc_prod_add`. -/
theorem clm_band_energy (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0}
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, ((itoProcessCLM hB T v hBmeas φ : Ω → ℝ) ω
        - (itoProcessCLM hB T u hBmeas φ : Ω → ℝ) ω) ^ 2 ∂μ
      = ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), (φ z) ^ 2
          ∂(trimMeasure (μ := μ) T hBmeas) := by
  set A := itoProcessCLM hB T v hBmeas φ
  set b := itoProcessCLM hB T u hBmeas φ
  have hm := (natFiltration hBmeas).le u
  have hmart : μ[(A : Ω → ℝ) | natFiltration hBmeas u] =ᵐ[μ] (b : Ω → ℝ) :=
    itoIntegralProcessGen_isMartingale hB T hBmeas φ huv
  have hnrm (w : ℝ≥0) (hw : w ≤ T) : ∫ ω, (itoProcessCLM hB T w hBmeas φ : Ω → ℝ) ω ^ 2 ∂μ
      = ∫ z in Set.Ioc 0 w ×ˢ (Set.univ : Set Ω), (φ z) ^ 2 ∂(trimMeasure (μ := μ) T hBmeas) :=
    (lp_two_norm_sq _).symm.trans (itoProcessCLM_norm_sq hB hw hBmeas φ)
  have hpyth : ∫ ω, ((A : Ω → ℝ) ω - μ[(A : Ω → ℝ) | natFiltration hBmeas u] ω) ^ 2 ∂μ
      = ∫ ω, (A : Ω → ℝ) ω ^ 2 ∂μ - ∫ ω, μ[(A : Ω → ℝ) | natFiltration hBmeas u] ω ^ 2 ∂μ := by
    have hA := Lp.memLp A
    have hsq : Integrable (μ[(A : Ω → ℝ) | natFiltration hBmeas u] ^ 2) μ :=
      (hA.condExp one_le_two).integrable_sq
    have h := integral_congr_ae (condVar_ae_eq_condExp_sq_sub_sq_condExp hm hA)
    rw [condVar, integral_condExp hm, integral_sub' integrable_condExp hsq,
      integral_condExp hm] at h
    exact h
  calc _ = ∫ ω, ((A : Ω → ℝ) ω - μ[(A : Ω → ℝ) | natFiltration hBmeas u] ω) ^ 2 ∂μ :=
        integral_congr_ae (by filter_upwards [hmart] with ω hω using by rw [hω])
    _ = ∫ ω, (A : Ω → ℝ) ω ^ 2 ∂μ - ∫ ω, (b : Ω → ℝ) ω ^ 2 ∂μ := by
        rw [hpyth, show ∫ ω, μ[(A : Ω → ℝ) | natFiltration hBmeas u] ω ^ 2 ∂μ
          = ∫ ω, (b : Ω → ℝ) ω ^ 2 ∂μ from
          integral_congr_ae (by filter_upwards [hmart] with ω hω using by rw [hω])]
    _ = _ := by
        rw [hnrm v hvT, hnrm u (huv.trans hvT),
          setIntegral_Ioc_prod_add hBmeas (Lp.memLp φ).integrable_sq zero_le huv]
        ring

end ItoIntegralProcessGeneral
end MathFin
