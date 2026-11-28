/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessContinuousModification
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessIsometry

/-! # Predictability and `L²` assembly of the Itô process (the SDE-existence keystone)

To run a Picard iteration for the SDE `dX = b(X)dt + σ(X)dB` inside the
predictable `L²` space `E := Lp ℝ 2 (trimMeasure T)`, the Itô term
`t ↦ (φ ● B)_t`, assembled as a *space-time* function, must itself be
**predictable** — otherwise the iterate cannot be fed back through the Itô
integral (whose integrand domain is the predictable `L²` space). This is the
one genuinely new regularity fact the construction needs: everything before
`ItoIntegralProcessGeneral` only ever needed the process to be adapted at each
fixed time (into `Lp μ`), never jointly predictable in `(t, ω)`.

Mathlib's `Probability/Process/Predictable.lean` supplies only the easy
direction (predictable ⟹ adapted). The hard direction — a left-continuous
adapted process is predictable — is **Degenne's**
`StronglyAdapted.isStronglyPredictable_of_leftContinuous`, which needs left-continuity on
every path. We apply it not to the continuous modification `itoContinuousMod`
directly, whose paths are continuous only almost surely, but to each *elementary*
Itô integral `itoSimpleProcess V`, which is genuinely continuous for **every** `ω`
(from Brownian path continuity) and genuinely adapted (its martingale property).
Predictability of the general process then lifts through the pointwise `limUnder`
that *defines* `itoContinuousMod` (`StronglyMeasurable.limUnder`), so
`itoContinuousMod` is predictable, and in particular adapted, for the natural
filtration itself; no augmentation is needed.

* path continuity is `ItoIntegralProcess.itoSimpleProcess_pathContinuous`, consumed here.
* `itoSimpleProcess_isStronglyPredictable` — the elementary integral is predictable.
* `itoContinuousMod_isStronglyPredictable` — the general assembled process is predictable.
* `memLp_itoContinuousMod` — the assembled process is `L²` in the predictable trim measure.
* `itoProcessAssembled` — it, packaged as an element of `Lp ℝ 2 (trimMeasure T)` (the space
  a Picard iterate for the SDE lands in).
* `itoProcessAssembled_norm_sq` — the energy identity
  `‖itoProcessAssembled φ‖²_E = ∫₀ᵀ ‖(φ●B)_t‖² dt` (the contraction workhorse for the SDE fixed
  point).
* `itoProcessAssembled_add` / `itoProcessAssembled_sub` — linearity of the assembled process (as an
  `Lp` class), so the contraction difference reduces to the energy identity via `itoProcessCLM`'s
  linearity.

## Main definitions

* `itoProcessAssembled`: the space-time function `(t,ω) ↦ (φ ● B)_t(ω)`, the continuous
  modification, as an element of `Lp ℝ 2 (trimMeasure T)`.

## Main results

* `itoSimpleProcess_isStronglyPredictable`: the elementary Itô integral is predictable as a
  space-time function.
* `itoContinuousMod_isStronglyPredictable`: the assembled Itô process `itoContinuousMod` is
  predictable.
* `memLp_itoContinuousMod`: `itoContinuousMod` is in `L²` for the predictable trim measure.
* `itoProcessAssembled_norm_sq`: `‖itoProcessAssembled φ‖² = ∫₀ᵀ ‖(φ ● B)_t‖² dt`.
* `itoProcessAssembled_norm_le`: `‖itoProcessAssembled φ‖ ≤ √T · ‖φ‖`.
* `itoProcessAssembled_add`, `itoProcessAssembled_sub`: the assembled Itô process is additive and
  subtractive in the integrand.

## Tags

predictable process, Picard iteration, SDE existence, stochastic differential equation,
Itô integral, left-continuous adapted, MSC 60H10, MSC 60H05, MSC 60G07
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcessContinuousModification
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

omit [IsProbabilityMeasure μ] in
/-- **The elementary Itô integral is predictable** as a space-time function. It is
genuinely (every `ω`) continuous — hence left-continuous — and genuinely adapted
(the martingale property `itoSimpleProcess_isMartingale.1`), so Degenne's
`StronglyAdapted.isStronglyPredictable_of_leftContinuous` applies directly. This
is the base case that sidesteps the a.e./everywhere friction which blocks
applying the same lemma to the continuous modification directly. -/
theorem itoSimpleProcess_isStronglyPredictable (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (V : SimpleProcess ℝ (natFiltration hBmeas)) :
    IsStronglyPredictable (natFiltration hBmeas) (itoSimpleProcess hBmeas V) := by
  apply MeasureTheory.StronglyAdapted.isStronglyPredictable_of_leftContinuous
  · exact (itoSimpleProcess_isMartingale hB hBmeas V).1
  · exact fun ω a ↦
      (ItoIntegralProcess.itoSimpleProcess_pathContinuous hBmeas hBcont V ω).continuousWithinAt

/-- **The assembled Itô process is predictable** (general integrand). By
construction `itoContinuousMod` is the pointwise `limUnder` of the elementary
integrals of a fixed approximating sequence `Vₙ`; each is predictable
(`itoSimpleProcess_isStronglyPredictable`), and `StronglyMeasurable.limUnder`
lifts strong predictable-measurability to the limit. (The ambient σ-algebra must
be pinned to the predictable one before invoking the limit lemma, which would
otherwise synthesize the default product σ-algebra.) -/
theorem itoContinuousMod_isStronglyPredictable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    IsStronglyPredictable (natFiltration hBmeas) (itoContinuousMod T hBmeas φ) := by
  rw [IsStronglyPredictable]
  have hrw : (Function.uncurry (itoContinuousMod T hBmeas φ))
      = fun z : ℝ≥0 × Ω ↦ limUnder atTop (fun n ↦
          Function.uncurry (itoSimpleProcess hBmeas
            ((approxSeq T hBmeas φ).choose n).val) z) := by
    funext z; rfl
  rw [hrw]
  let : MeasurableSpace (ℝ≥0 × Ω) := (natFiltration hBmeas).predictable
  exact StronglyMeasurable.limUnder (fun n ↦
    itoSimpleProcess_isStronglyPredictable hB hBmeas hBcont
      ((approxSeq T hBmeas φ).choose n).val)

/-- **The assembled Itô process is `L²`** in the predictable trim measure. It is predictable
(`itoContinuousMod_isStronglyPredictable`); the energy is finite because, slice by slice, the
modification identity and the Itô contraction give `∫₀ᵀ ‖(φ ● B)_t‖² dt ≤ T ‖φ‖²` (`eLpNorm_trim`
drops the trim, then Tonelli splits the product and each time-slice is bounded by
`itoProcessCLM_norm_le`). -/
theorem memLp_itoContinuousMod (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    MemLp (Function.uncurry (itoContinuousMod T hBmeas φ)) 2 (trimMeasure (μ := μ) T hBmeas) := by
  have hpred := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ
  rw [memLp_iff, show trimMeasure (μ := μ) T hBmeas
        = ((timeMeasureHorizon T).prod μ).trim (natFiltration hBmeas).predictable_le_prod from rfl,
      eLpNorm_trim _ hpred,
      eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (by norm_num) (by norm_num)
        (hpred.mono (natFiltration hBmeas).predictable_le_prod).aestronglyMeasurable,
      lintegral_prod _
        ((hpred.mono (natFiltration hBmeas).predictable_le_prod).measurable.eNorm.pow_const _
          |>.aemeasurable)]
  -- per-time energy bound: for `t ≤ T` the slice energy is `≤ ‖φ‖²`
  have key : ∀ t : ℝ≥0, t ≤ T →
      (∫⁻ ω, ‖itoContinuousMod T hBmeas φ t ω‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ)
        ≤ (ENNReal.ofReal ‖φ‖) ^ (2 : ℝ≥0∞).toReal := by
    intro t htT
    have hmod : (∫⁻ ω, ‖itoContinuousMod T hBmeas φ t ω‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ)
        = ∫⁻ ω, ‖(itoProcessCLM hB T t hBmeas φ : Ω → ℝ) ω‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont φ htT] with ω hω
      rw [hω]
    rw [hmod, lintegral_rpow_eNorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    gcongr
    rw [← eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable (itoProcessCLM hB T t hBmeas φ)), ← Lp.eNorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (itoProcessCLM_norm_le hB T t hBmeas φ)
  refine lt_of_le_of_lt
    (lintegral_mono_ae (g := fun _ ↦ (ENNReal.ofReal ‖φ‖) ^ (2 : ℝ≥0∞).toReal) ?_) ?_
  · have hsub : ∀ᵐ t ∂(timeMeasureHorizon T), t ≤ T := by
      rw [timeMeasureHorizon]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
    filter_upwards [hsub] with t htT using key t htT
  · rw [lintegral_const]
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) (measure_lt_top _ _)

/-- **The assembled Itô process as an element of the predictable `L²` space `E`.**
The space-time function `(t,ω) ↦ (φ ● B)_t(ω)` (the continuous modification), packaged as a
class in `Lp ℝ 2 (trimMeasure T)` — the object a Picard iterate for the SDE lands in. -/
noncomputable def itoProcessAssembled (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  (memLp_itoContinuousMod hB T hBmeas hBcont φ).toLp
      (Function.uncurry (itoContinuousMod T hBmeas φ))

/-- **The energy identity.** `‖itoProcessAssembled φ‖²_E = ∫₀ᵀ ‖(φ ● B)_t‖² dt` — the squared
`E`-norm of the assembled process is the time-integral of the per-time Itô `L²`-norms. Slice by
slice the modification identity turns the space-time integral (Tonelli over the trimmed product)
into `∫₀ᵀ ‖itoProcessCLM T t φ‖² dt`. Paired with `itoProcessCLM_norm_sq` (the `[0,t]` energy
`‖itoProcessCLM T t φ‖² = ∫_{(0,t]×Ω} φ²`), this is the Grönwall/Bielecki workhorse the SDE
contraction consumes. -/
theorem itoProcessAssembled_norm_sq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ‖itoProcessAssembled hB T hBmeas hBcont φ‖ ^ 2
      = ∫ t, ‖itoProcessCLM hB T t hBmeas φ‖ ^ 2 ∂(timeMeasureHorizon T) := by
  have hpred := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ
  have hmem := memLp_itoContinuousMod hB T hBmeas hBcont φ
  have hmem_prod : MemLp (Function.uncurry (itoContinuousMod T hBmeas φ)) 2
      ((timeMeasureHorizon T).prod μ) :=
    memLp_of_memLp_trim (natFiltration hBmeas).predictable_le_prod hmem
  have hint : Integrable (fun z ↦ (Function.uncurry (itoContinuousMod T hBmeas φ) z) ^ 2)
      ((timeMeasureHorizon T).prod μ) := by
    refine (hmem_prod.integrable_mul hmem_prod).congr ?_
    filter_upwards with z
    rw [Pi.mul_apply, pow_two]
  have hcoe : ⇑(itoProcessAssembled hB T hBmeas hBcont φ)
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas φ) :=
    hmem.coeFn_toLp
  have htrim : (∫ z, (Function.uncurry (itoContinuousMod T hBmeas φ) z) ^ 2
        ∂(trimMeasure (μ := μ) T hBmeas))
      = ∫ z, (Function.uncurry (itoContinuousMod T hBmeas φ) z) ^ 2
          ∂((timeMeasureHorizon T).prod μ) :=
    (integral_trim (μ := (timeMeasureHorizon T).prod μ)
      (natFiltration hBmeas).predictable_le_prod (hpred.pow 2)).symm
  rw [lp_two_norm_sq,
      integral_congr_ae (g := fun z ↦ (Function.uncurry (itoContinuousMod T hBmeas φ) z) ^ 2)
        (by filter_upwards [hcoe] with z hz; rw [hz]),
      htrim, integral_prod _ hint]
  refine integral_congr_ae ?_
  have hsub : ∀ᵐ t ∂(timeMeasureHorizon T), t ≤ T := by
    rw [timeMeasureHorizon]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
  filter_upwards [hsub] with t htT
  rw [lp_two_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont φ htT] with ω hω
  simp only [Function.uncurry]
  rw [hω]

/-- **The Itô operator bound** `‖itoProcessAssembled φ‖ ≤ √T‖φ‖` — the norm corollary of the energy
identity `itoProcessAssembled_norm_sq`: it turns the square norm into `∫₀ᵀ ‖itoProcessCLM t φ‖² dt`,
and each `[0,t]`-energy is `≤` the full energy `‖φ‖²` (the Itô isometry is flat in `t`), so the
time-integral is `≤ T‖φ‖²`. The `√T` (vs the drift's `T`) is the contraction workhorse. -/
theorem itoProcessAssembled_norm_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ‖itoProcessAssembled hB T hBmeas hBcont φ‖ ≤ Real.sqrt (T : ℝ) * ‖φ‖ := by
  have hφsq : Integrable (fun z ↦ (φ z) ^ 2) (trimMeasure (μ := μ) T hBmeas) :=
    (Lp.memLp φ).integrable_sq
  have hsq : ‖itoProcessAssembled hB T hBmeas hBcont φ‖ ^ 2 ≤ (T : ℝ) * ‖φ‖ ^ 2 := by
    rw [itoProcessAssembled_norm_sq]
    have hpt : ∀ᵐ t ∂(timeMeasureHorizon T),
        ‖itoProcessCLM hB T t hBmeas φ‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
      filter_upwards [ae_restrict_mem (μ := timeMeasure) measurableSet_Ioc] with t ht
      rw [itoProcessCLM_norm_sq hB ht.2 hBmeas φ, lp_two_norm_sq]
      exact setIntegral_le_integral hφsq (ae_of_all _ fun z ↦ sq_nonneg _)
    calc ∫ t, ‖itoProcessCLM hB T t hBmeas φ‖ ^ 2 ∂(timeMeasureHorizon T)
        ≤ ∫ _t, ‖φ‖ ^ 2 ∂(timeMeasureHorizon T) :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) (integrable_const _) hpt
      _ = (T : ℝ) * ‖φ‖ ^ 2 := by
          rw [integral_const, timeMeasureHorizon, measureReal_def, Measure.restrict_apply_univ,
            timeMeasure_Ioc,
            ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact T.coe_nonneg),
            NNReal.coe_zero, sub_zero, smul_eq_mul]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul T.coe_nonneg, Real.sqrt_sq (norm_nonneg _)] at h

/-- **Additivity** of the assembled Itô process (as an `Lp` class). Both sides are modifications
of the linear process `itoProcessCLM T · (φ+ψ)`, so they agree slice by slice (the modification
identity + `itoProcessCLM`'s `map_add`); the per-time a.e. equalities lift to an a.e. equality on
the trimmed product (`Measure.ae_prod_iff_ae_ae` + `ae_eq_trim_of_stronglyMeasurable`). -/
theorem itoProcessAssembled_add (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ ψ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    itoProcessAssembled hB T hBmeas hBcont (φ + ψ)
      = itoProcessAssembled hB T hBmeas hBcont φ + itoProcessAssembled hB T hBmeas hBcont ψ := by
  have hpredφ := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ
  have hpredψ := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont ψ
  have hpredS' : StronglyMeasurable[(natFiltration hBmeas).predictable]
      (Function.uncurry (itoContinuousMod T hBmeas (φ + ψ))) :=
    itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont (φ + ψ)
  have hgSM : StronglyMeasurable[(natFiltration hBmeas).predictable]
      (Function.uncurry (itoContinuousMod T hBmeas φ)
        + Function.uncurry (itoContinuousMod T hBmeas ψ)) :=
    StronglyMeasurable.add hpredφ hpredψ
  have hkey : Function.uncurry (itoContinuousMod T hBmeas (φ + ψ))
      =ᵐ[trimMeasure (μ := μ) T hBmeas]
        (Function.uncurry (itoContinuousMod T hBmeas φ)
          + Function.uncurry (itoContinuousMod T hBmeas ψ)) := by
    refine hpredS'.ae_eq_trim_of_stronglyMeasurable
      (natFiltration hBmeas).predictable_le_prod hgSM ?_
    have hset : MeasurableSet {z : ℝ≥0 × Ω |
        Function.uncurry (itoContinuousMod T hBmeas (φ + ψ)) z
          = (Function.uncurry (itoContinuousMod T hBmeas φ)
              + Function.uncurry (itoContinuousMod T hBmeas ψ)) z} :=
      measurableSet_eq_fun (hpredS'.mono (natFiltration hBmeas).predictable_le_prod).measurable
        (hgSM.mono (natFiltration hBmeas).predictable_le_prod).measurable
    rw [Filter.EventuallyEq, Measure.ae_prod_iff_ae_ae hset]
    have hsub : ∀ᵐ t ∂(timeMeasureHorizon T), t ≤ T := by
      rw [timeMeasureHorizon]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
    filter_upwards [hsub] with t htT
    filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont (φ + ψ) htT,
      itoContinuousMod_modification hB T hBmeas hBcont φ htT,
      itoContinuousMod_modification hB T hBmeas hBcont ψ htT,
      Lp.coeFn_add (itoProcessCLM hB T t hBmeas φ) (itoProcessCLM hB T t hBmeas ψ)]
      with ω hωS hωφ hωψ hωadd
    simp only [Function.uncurry, Pi.add_apply]
    rw [hωS, map_add, hωadd, Pi.add_apply, ← hωφ, ← hωψ]
  have hcoeS : ⇑(itoProcessAssembled hB T hBmeas hBcont (φ + ψ))
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas (φ + ψ)) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont (φ + ψ)).coeFn_toLp
  have hcoeφ : ⇑(itoProcessAssembled hB T hBmeas hBcont φ)
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas φ) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont φ).coeFn_toLp
  have hcoeψ : ⇑(itoProcessAssembled hB T hBmeas hBcont ψ)
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas ψ) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont ψ).coeFn_toLp
  refine Lp.ext ?_
  filter_upwards [hcoeS, hkey, hcoeφ, hcoeψ,
    Lp.coeFn_add (itoProcessAssembled hB T hBmeas hBcont φ)
      (itoProcessAssembled hB T hBmeas hBcont ψ)] with z hzS hzk hzφ hzψ hza
  rw [hzS, hzk, hza]
  simp only [Pi.add_apply, hzφ, hzψ]

/-- **Subtractivity** of the assembled Itô process (the SDE contraction consumes this: it turns
`itoProcessAssembled (σ∘X) − itoProcessAssembled (σ∘Y)` into `itoProcessAssembled (σ∘X − σ∘Y)`,
whose energy is `∫₀ᵀ ‖itoProcessCLM T t (σ∘X − σ∘Y)‖² dt`). -/
theorem itoProcessAssembled_sub (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ ψ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    itoProcessAssembled hB T hBmeas hBcont (φ - ψ)
      = itoProcessAssembled hB T hBmeas hBcont φ - itoProcessAssembled hB T hBmeas hBcont ψ := by
  have hpredφ := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ
  have hpredψ := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont ψ
  have hpredS' : StronglyMeasurable[(natFiltration hBmeas).predictable]
      (Function.uncurry (itoContinuousMod T hBmeas (φ - ψ))) :=
    itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont (φ - ψ)
  have hgSM : StronglyMeasurable[(natFiltration hBmeas).predictable]
      (Function.uncurry (itoContinuousMod T hBmeas φ)
        - Function.uncurry (itoContinuousMod T hBmeas ψ)) :=
    StronglyMeasurable.sub hpredφ hpredψ
  have hkey : Function.uncurry (itoContinuousMod T hBmeas (φ - ψ))
      =ᵐ[trimMeasure (μ := μ) T hBmeas]
        (Function.uncurry (itoContinuousMod T hBmeas φ)
          - Function.uncurry (itoContinuousMod T hBmeas ψ)) := by
    refine hpredS'.ae_eq_trim_of_stronglyMeasurable
      (natFiltration hBmeas).predictable_le_prod hgSM ?_
    have hset : MeasurableSet {z : ℝ≥0 × Ω |
        Function.uncurry (itoContinuousMod T hBmeas (φ - ψ)) z
          = (Function.uncurry (itoContinuousMod T hBmeas φ)
              - Function.uncurry (itoContinuousMod T hBmeas ψ)) z} :=
      measurableSet_eq_fun (hpredS'.mono (natFiltration hBmeas).predictable_le_prod).measurable
        (hgSM.mono (natFiltration hBmeas).predictable_le_prod).measurable
    rw [Filter.EventuallyEq, Measure.ae_prod_iff_ae_ae hset]
    have hsub : ∀ᵐ t ∂(timeMeasureHorizon T), t ≤ T := by
      rw [timeMeasureHorizon]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
    filter_upwards [hsub] with t htT
    filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont (φ - ψ) htT,
      itoContinuousMod_modification hB T hBmeas hBcont φ htT,
      itoContinuousMod_modification hB T hBmeas hBcont ψ htT,
      Lp.coeFn_sub (itoProcessCLM hB T t hBmeas φ) (itoProcessCLM hB T t hBmeas ψ)]
      with ω hωS hωφ hωψ hωsub
    simp only [Function.uncurry, Pi.sub_apply]
    rw [hωS, map_sub, hωsub, Pi.sub_apply, ← hωφ, ← hωψ]
  have hcoeS : ⇑(itoProcessAssembled hB T hBmeas hBcont (φ - ψ))
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas (φ - ψ)) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont (φ - ψ)).coeFn_toLp
  have hcoeφ : ⇑(itoProcessAssembled hB T hBmeas hBcont φ)
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas φ) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont φ).coeFn_toLp
  have hcoeψ : ⇑(itoProcessAssembled hB T hBmeas hBcont ψ)
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas ψ) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont ψ).coeFn_toLp
  refine Lp.ext ?_
  filter_upwards [hcoeS, hkey, hcoeφ, hcoeψ,
    Lp.coeFn_sub (itoProcessAssembled hB T hBmeas hBcont φ)
      (itoProcessAssembled hB T hBmeas hBcont ψ)] with z hzS hzk hzφ hzψ hza
  rw [hzS, hzk, hza]
  simp only [Pi.sub_apply, hzφ, hzψ]

end ItoIntegralProcessContinuousModification
end MathFin
