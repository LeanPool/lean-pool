/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessContinuousModification

/-! # Predictability and `L²` assembly of the drift process (SDE-existence keystone II)

The Picard iterate for the SDE `dX = b(X)dt + σ(X)dB` is
`Φ(X)_t = η + ∫₀ᵗ b(X_s) ds + ∫₀ᵗ σ(X_s) dB_s`. The Itô term was assembled into
the predictable `L²` space `E := Lp ℝ 2 (trimMeasure T)` in
`ItoProcessPredictable`. This file does the same for the **drift** term
`t ↦ ∫₀ᵗ g(s, ω) ds`: it too must land back in `E` (predictable `L²`), because the
*next* iterate is fed through the Itô integral, whose integrand domain is `E`.

The drift is pure Lebesgue integration, so — unlike the Itô side — **none of this
needs the Brownian motion `B` itself** (`IsPreBrownianReal`), only its *filtration*
`natFiltration hBmeas`. Each elementary drift `driftSimpleProcess V` (the Lebesgue
integral of the step process `V`) is genuinely continuous and adapted for **every**
`ω` — a finite sum of `𝓕`-measurable coefficients times deterministic continuous
time-increments — so Degenne's `StronglyAdapted.isStronglyPredictable_of_leftContinuous`
applies to the base case. The contrast with the Itô side is the elegant part: there
the continuous version is only `∀ᵐ ω`-continuous and adapted to the *augmented*
filtration, so the theorem is applied per-elementary-process to dodge that friction;
here there is no friction to dodge — no randomness in the time-regularity means no
exceptional null set — and the theorem applies to the raw `natFiltration` directly.

**Part 1 — predictability.**
* `driftSimpleProcess` — the elementary drift `∑_p V(p)(ω)·((p.2 ∧ t) − (p.1 ∧ t))`.
* `driftSimpleProcess_continuous` / `_stronglyAdapted` / `_isStronglyPredictable`.
* `driftContinuousMod` / `_isStronglyPredictable` — the pointwise-`limUnder` drift-limit
  process (via `StronglyMeasurable.limUnder`) and its predictability. Provided for
  **parity with the Itô side's `itoContinuousMod`**, a genuine everywhere-defined
  pathwise realization for future SDE-path-continuity use; the `L²` keystone below
  does **not** route through it (its predictability comes for free from membership in
  the predictable trim space `E`).

**Part 2 — the drift as a bounded operator on `E`.**
* `driftSimpleProcess_eq_setIntegral` — the honest-integral bridge
  `driftSimpleProcess V t ω = ∫₀ᵗ ⇑V(s,ω) ds` (against `timeMeasure`).
* `driftSimpleProcessLp` — the elementary drift packaged as an element of `E`.
* `driftSimpleProcessLp_norm_le` — the energy bound
  `‖driftSimpleProcessLp V‖ ≤ T·‖simpleAssemblyHorizon V‖` (Tonelli → pointwise Cauchy–Schwarz →
  Fubini → the outer `∫₀ᵀ`).
* `driftProcessAssembled` — **the keystone**: `g ↦ (t ↦ ∫₀ᵗ g(s,·) ds)` as a CLM
  `E →L E`. Because it is a CLM into the predictable trim space `E`, it is linear,
  bounded (`‖·‖ ≤ T‖·‖`), and predictable — all for free. That routing through `E`,
  rather than re-proving each property by hand, is the payoff of this construction.

## Main definitions

* `driftSimpleProcess`: the elementary drift (Lebesgue) integral `∫₀ᵗ V(s, ω) ds` of a simple
  process `V`.
* `driftSimpleProcessLp`: the elementary drift assembled as an element of
  `Lp ℝ 2 (trimMeasure T)`.
* `driftProcessLM`: the elementary drift as a linear map on the `T`-bounded simple processes.
* `driftProcessAssembled`: the continuous linear extension of that map to
  `Lp ℝ 2 (trimMeasure T)`.
* `driftContinuousMod`: the pathwise drift-limit process of an integrand `φ`, defined by a
  pointwise limit.

## Main results

* `driftSimpleProcess_continuous`, `driftSimpleProcess_stronglyAdapted`,
  `driftSimpleProcess_isStronglyPredictable`: the elementary drift has continuous paths, is
  adapted, and is predictable.
* `driftSimpleProcess_eq_setIntegral`: the elementary drift is the Lebesgue integral of the
  process over `(0, t]`.
* `driftSimpleProcessLp_norm_le`: the `L²` energy bound of the elementary drift for `T`-bounded
  simple processes.
* `driftProcessAssembled_norm_le`: `‖driftProcessAssembled φ‖ ≤ T‖φ‖`.
* `driftContinuousMod_isStronglyPredictable`, `driftContinuousMod_stronglyAdapted`: the
  pathwise drift-limit process is predictable and adapted.

## Tags

drift term, Picard iteration, SDE existence, predictable process, Lebesgue integral, L2 operator,
MSC 60H10, MSC 60H05
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcessContinuousModification
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- `timeMeasure` restricted to any bounded time-interval `(a, b]` is finite
(`timeMeasure (a, b] = ofReal (b − a) < ∞`), so the Cauchy–Schwarz / `L²` steps
below on `(0, t]` find their finiteness instance by resolution. -/
private instance isFiniteMeasure_timeMeasure_restrict_Ioc (a b : ℝ≥0) :
    IsFiniteMeasure (timeMeasure.restrict (Set.Ioc a b)) :=
  ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩

/-- **The elementary drift (Lebesgue) integral** of a simple process `V`:
`driftSimpleProcess V t ω = ∑_p V(p)(ω)·((p.2 ∧ t) − (p.1 ∧ t))`. This is exactly
`∫₀ᵗ V_tilde(s, ω) ds` for the step process `V_tilde = ∑_p V(p)·𝟙_{(p.1, p.2]}` — the time
increment `(p.2 ∧ t) − (p.1 ∧ t)` is the Lebesgue length of `(p.1, p.2] ∩ (0, t]`.
(The clamp `min · t` is taken in `ℝ≥0` and then coerced, so the increment matches
`timeMeasure_Ioc_inter`'s `ℝ≥0`-valued endpoints definitionally in the bridge below.) -/
noncomputable def driftSimpleProcess (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  V.value.sum fun p v ↦ v ω * (((min p.2 t : ℝ≥0) : ℝ) - ((min p.1 t : ℝ≥0) : ℝ))

/-- **Path continuity of the elementary drift.** For every `ω`, `t ↦ driftSimpleProcess V t ω`
is continuous: a finite sum of `V(p)(ω)` (constant in `t`) times the continuous
time-increment `(p.2 ∧ t) − (p.1 ∧ t)` (continuous clamp `t ↦ min c t`, then the
coercion `ℝ≥0 → ℝ`). -/
theorem driftSimpleProcess_continuous (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (ω : Ω) :
    Continuous (fun t : ℝ≥0 ↦ driftSimpleProcess hBmeas V t ω) := by
  simp only [driftSimpleProcess, Finsupp.sum]
  fun_prop

/-- **The elementary drift is adapted.** For each `t`, `driftSimpleProcess V t` is
`𝓕_t`-measurable: it is `∑_p V(p)·c_p(t)` with `c_p(t) := (p.2 ∧ t) − (p.1 ∧ t)` a
real constant; for `p.1 ≤ t` the coefficient `V(p)` is `𝓕_{p.1} ⊆ 𝓕_t`-measurable, and
for `p.1 > t` the increment `c_p(t)` collapses to `0` (both endpoints clamp to `t`). -/
theorem driftSimpleProcess_stronglyAdapted (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) :
    StronglyAdapted (natFiltration hBmeas) (driftSimpleProcess hBmeas V) := by
  intro t
  have hsm : ∀ p ∈ V.value.support, StronglyMeasurable[natFiltration hBmeas t]
      (fun ω ↦ V.value p ω * (((min p.2 t : ℝ≥0) : ℝ) - ((min p.1 t : ℝ≥0) : ℝ))) := by
    intro p hp
    by_cases ht : p.1 ≤ t
    · exact
        (((V.measurable_value p).mono ((natFiltration hBmeas).mono ht)
        le_rfl).stronglyMeasurable).mul
        stronglyMeasurable_const
    · rw [not_le] at ht
      have h1 : min p.1 t = t := min_eq_right ht.le
      have h2 : min p.2 t = t := min_eq_right (ht.le.trans (V.le_of_mem_support_value p hp))
      simp only [h1, h2, sub_self, mul_zero]
      exact stronglyMeasurable_const
  exact Finset.stronglyMeasurable_fun_sum _ hsm

/-- **The elementary drift is predictable** as a space-time function — genuinely
(every `ω`) continuous, hence left-continuous, and genuinely adapted, so Degenne's
`StronglyAdapted.isStronglyPredictable_of_leftContinuous` applies (the base case,
sidestepping the a.e./everywhere friction). -/
theorem driftSimpleProcess_isStronglyPredictable (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) :
    IsStronglyPredictable (natFiltration hBmeas) (driftSimpleProcess hBmeas V) := by
  apply MeasureTheory.StronglyAdapted.isStronglyPredictable_of_leftContinuous
  · exact driftSimpleProcess_stronglyAdapted hBmeas V
  · exact fun ω a ↦ (driftSimpleProcess_continuous hBmeas V ω).continuousWithinAt

/-- The pathwise drift-limit process: for each `t, ω` the limit (junk off the
convergence set) of the elementary drifts of a fixed approximating sequence `Vₙ`
(`approxSeq`'s choice for `φ`). -/
noncomputable def driftContinuousMod (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop fun n ↦ driftSimpleProcess hBmeas ((approxSeq T hBmeas φ).choose n).val t ω

/-- **The assembled drift is predictable** (general integrand). By construction
`driftContinuousMod` is the pointwise `limUnder` of the elementary drifts of a fixed
approximating sequence; each is predictable (`driftSimpleProcess_isStronglyPredictable`),
and `StronglyMeasurable.limUnder` lifts predictability to the limit. -/
theorem driftContinuousMod_isStronglyPredictable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    IsStronglyPredictable (natFiltration hBmeas) (driftContinuousMod T hBmeas φ) := by
  rw [IsStronglyPredictable]
  have hrw : (Function.uncurry (driftContinuousMod T hBmeas φ))
      = fun z : ℝ≥0 × Ω ↦ limUnder atTop (fun n ↦
          Function.uncurry (driftSimpleProcess hBmeas
            ((approxSeq T hBmeas φ).choose n).val) z) := by
    funext z; rfl
  rw [hrw]
  let : MeasurableSpace (ℝ≥0 × Ω) := (natFiltration hBmeas).predictable
  exact StronglyMeasurable.limUnder (fun n ↦
    driftSimpleProcess_isStronglyPredictable hBmeas
      ((approxSeq T hBmeas φ).choose n).val)

/-- **The assembled drift is fixed-time `𝓕`-adapted.** At each `t`, `driftContinuousMod T φ t` is
the pointwise `limUnder` of the elementary drifts `driftSimpleProcess (approxSeq φ)ₙ t`, each
`𝓕 t`-strongly-measurable (`driftSimpleProcess_stronglyAdapted`), and `StronglyMeasurable.limUnder`
lifts adaptedness to the limit — the pointwise-in-time companion of
`driftContinuousMod_isStronglyPredictable`, feeding the `IsExpQMartingale.adapted` field of the
predictable-θ Girsanov theorem. -/
theorem driftContinuousMod_stronglyAdapted (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    StronglyAdapted (natFiltration hBmeas) (driftContinuousMod T hBmeas φ) := by
  intro t
  let : MeasurableSpace Ω := (natFiltration hBmeas t : MeasurableSpace Ω)
  exact StronglyMeasurable.limUnder fun n ↦
    driftSimpleProcess_stronglyAdapted hBmeas ((approxSeq T hBmeas φ).choose n).val t

/-! ## Part 2 — the drift assembled into `E` (`L²`, energy bound, linearity) -/

/-- **Bridge to the honest Lebesgue integral.** The elementary drift is literally the
Lebesgue integral `∫₀ᵗ ⇑V(s,ω) ds` (against `timeMeasure`) of the step process `⇑V`: on
`(0,t]` the `⊥`-fibre vanishes and `⇑V(s,ω) = ∑_p 𝟙_{(p.1,p.2]}(s)·V(p)(ω)`, so each interval
contributes `V(p)(ω)·timeMeasure((0,t] ∩ (p.1,p.2])`, whose real value is the time-increment
`(p.2 ∧ t) − (p.1 ∧ t)`. This is the identity the `L²` bound reads through Cauchy–Schwarz. -/
theorem driftSimpleProcess_eq_setIntegral (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) (ω : Ω) :
    driftSimpleProcess hBmeas V t ω = ∫ s in Set.Ioc (0 : ℝ≥0) t, ⇑V s ω ∂timeMeasure := by
  have htoReal : ∀ p : ℝ≥0 × ℝ≥0, p.1 ≤ p.2 →
      (timeMeasure (Set.Ioc (0 : ℝ≥0) t ∩ Set.Ioc p.1 p.2)).toReal
        = ((min p.2 t : ℝ≥0) : ℝ) - ((min p.1 t : ℝ≥0) : ℝ) := by
    intro p hp12
    rw [Set.inter_comm, timeMeasure_Ioc_inter, NNReal.coe_zero, max_eq_left p.1.coe_nonneg,
        NNReal.coe_min, NNReal.coe_min]
    by_cases ht : p.1 ≤ t
    · rw [ENNReal.toReal_ofReal (by
            have : (p.1 : ℝ) ≤ min (p.2 : ℝ) t :=
              le_min (by exact_mod_cast hp12) (by exact_mod_cast ht)
            linarith), min_eq_left (by exact_mod_cast ht : (p.1 : ℝ) ≤ t)]
    · rw [not_le] at ht
      have htp1 : (t : ℝ) ≤ p.1 := le_of_lt (by exact_mod_cast ht)
      have htp2 : (t : ℝ) ≤ p.2 := htp1.trans (by exact_mod_cast hp12)
      rw [min_eq_right htp2, min_eq_right htp1, sub_self,
          ENNReal.ofReal_eq_zero.mpr (by linarith), ENNReal.toReal_zero]
  have hV_eq : Set.EqOn (fun s ↦ ⇑V s ω)
      (fun s ↦ ∑ p ∈ V.value.support, (Set.Ioc p.1 p.2).indicator (fun _ ↦ V.value p ω) s)
      (Set.Ioc (0 : ℝ≥0) t) := by
    intro s hs
    have hs0 : s ∉ ({⊥} : Set ℝ≥0) := by
      simp only [Set.mem_singleton_iff]
      rintro rfl
      exact absurd hs.1 not_lt_bot
    simp only [SimpleProcess.apply_eq, Set.indicator_of_notMem hs0, zero_add, Finsupp.sum]
  have hint : ∀ p ∈ V.value.support,
      Integrable (fun s ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ V.value p ω) s)
        (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)) :=
    fun p _ ↦ (integrable_const (V.value p ω)).indicator measurableSet_Ioc
  rw [driftSimpleProcess, Finsupp.sum, setIntegral_congr_fun measurableSet_Ioc hV_eq,
      integral_finsetSum _ hint]
  refine Finset.sum_congr rfl (fun p hp ↦ ?_)
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul,
      measureReal_def, htoReal p (V.le_of_mem_support_value p hp), mul_comm]

/-- **The elementary drift is `L²`** — indeed bounded. Each term satisfies
`|V(p)(ω)·((p.2 ∧ t) − (p.1 ∧ t))| ≤ valueBound·p.2` (the coefficient is bounded and the
time-increment lies in `[0, p.2]`), so the finite sum is bounded by the constant
`∑_p valueBound·p.2`; being predictable on the finite measure `trimMeasure T`, it is `MemLp`. -/
theorem memLp_uncurry_driftSimpleProcess (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) :
    MemLp (Function.uncurry (driftSimpleProcess hBmeas V)) 2 (trimMeasure (μ := μ) T hBmeas) := by
  refine MemLp.of_bound (driftSimpleProcess_isStronglyPredictable hBmeas V).aestronglyMeasurable
    (∑ p ∈ V.value.support, V.valueBound * (p.2 : ℝ)) (ae_of_all _ fun z ↦ ?_)
  rw [Function.uncurry_apply_pair, driftSimpleProcess, Finsupp.sum, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  rw [abs_mul]
  have hval : |V.value p z.2| ≤ V.valueBound := by
    rw [← Real.norm_eq_abs]; exact V.value_le_valueBound p z.2
  have hc : |((min p.2 z.1 : ℝ≥0) : ℝ) - ((min p.1 z.1 : ℝ≥0) : ℝ)| ≤ (p.2 : ℝ) := by
    rw [abs_of_nonneg (by
      have : ((min p.1 z.1 : ℝ≥0) : ℝ) ≤ ((min p.2 z.1 : ℝ≥0) : ℝ) := by
        exact_mod_cast min_le_min_right z.1 (V.le_of_mem_support_value p hp)
      linarith)]
    have h1 : ((min p.2 z.1 : ℝ≥0) : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast min_le_left p.2 z.1
    have h2 : (0 : ℝ) ≤ ((min p.1 z.1 : ℝ≥0) : ℝ) := (min p.1 z.1).coe_nonneg
    linarith
  exact mul_le_mul hval hc (abs_nonneg _) (le_trans (abs_nonneg _) hval)

/-- **The elementary-drift slice is `L²` in the time variable** (bounded step process on the
finite measure `timeMeasure.restrict (Ioc 0 T)`). -/
theorem memLp_slice (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (ω : Ω) :
    MemLp (fun s ↦ ⇑V s ω) 2 (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) := by
  refine MemLp.of_bound
    (((V.isStronglyPredictable.mono (natFiltration hBmeas).predictable_le_prod).comp_measurable
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (V.valueBotBound + ∑ p ∈ V.value.support, V.valueBound) (ae_of_all _ fun s ↦ ?_)
  rw [SimpleProcess.apply_eq, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [Set.indicator]
    split_ifs with h
    · exact V.valueBot_le_valueBotBound ω
    · rw [abs_zero]; exact V.valueBotBound_nonneg
  · rw [Finsupp.sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ ↦ ?_)
    rw [Set.indicator]
    split_ifs with h
    · rw [← Real.norm_eq_abs]; exact V.value_le_valueBound p ω
    · rw [abs_zero]; exact V.valueBound_nonneg

/-- **Pointwise `L²` bound of the elementary drift** (bridge + Cauchy–Schwarz + interval
extension): for `t ≤ T`, `(driftSimpleProcess V t ω)² ≤ T·∫₀ᵀ (⇑V s ω)² ds`. -/
theorem driftSimpleProcess_sq_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) {t : ℝ≥0} (htT : t ≤ T) (ω : Ω) :
    (driftSimpleProcess hBmeas V t ω) ^ 2
      ≤ (T : ℝ) * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑V s ω) ^ 2 ∂timeMeasure := by
  rw [driftSimpleProcess_eq_setIntegral]
  have hCS := sq_integral_le_measureReal_mul (ν := timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t))
    (f := fun s ↦ ⇑V s ω) ((memLp_slice T hBmeas V ω).mono_measure (Measure.restrict_mono
      (Set.Ioc_subset_Ioc_right htT) le_rfl))
  rw [Measure.restrict_apply_univ, timeMeasure_Ioc,
    ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact t.coe_nonneg),
    NNReal.coe_zero, sub_zero] at hCS
  refine hCS.trans (mul_le_mul (by exact_mod_cast htT) ?_ (integral_nonneg fun s ↦ sq_nonneg _)
    T.coe_nonneg)
  exact setIntegral_mono_set ((memLp_slice T hBmeas V ω).integrable_sq)
    (ae_of_all _ fun s ↦ sq_nonneg _) (ae_of_all _ fun _ h ↦ Set.Ioc_subset_Ioc_right htT h)

/-- **Additivity** of the elementary drift in the simple process (`Finsupp.sum_add_index'`,
the summand being linear in the coefficient). -/
theorem driftSimpleProcess_add (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) :
    driftSimpleProcess hBmeas (V + W) t
      = driftSimpleProcess hBmeas V t + driftSimpleProcess hBmeas W t := by
  funext ω
  simp only [driftSimpleProcess]
  rw [show (V + W).value = V.value + W.value from rfl]
  exact Finsupp.sum_add_index' (fun p ↦ by simp) (fun p a b ↦ by simp [Pi.add_apply, add_mul])

/-- **Homogeneity** of the elementary drift in the simple process (through the honest-integral
bridge + `integral_const_mul`). -/
theorem driftSimpleProcess_smul (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) :
    driftSimpleProcess hBmeas (c • V) t = c • driftSimpleProcess hBmeas V t := by
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [driftSimpleProcess_eq_setIntegral, driftSimpleProcess_eq_setIntegral, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun s _ ↦ ?_)
  rw [SimpleProcess.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]

/-- The elementary drift assembled as an element of `E = Lp ℝ 2 (trimMeasure T)`. -/
noncomputable def driftSimpleProcessLp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  (memLp_uncurry_driftSimpleProcess T hBmeas V).toLp
      (Function.uncurry (driftSimpleProcess hBmeas V))

/-- **The drift energy bound** — the relative `L²` bound that makes the drift a bounded operator on
`E`: `‖driftSimpleProcessLp V‖ ≤ T·‖simpleAssemblyHorizon V‖`. Tonelli turns the `E`-norm into
`∫₀ᵀ∫_Ω (drift)² `; the pointwise Cauchy–Schwarz bound `(drift)² ≤ T·∫₀ᵀ(⇑V)²` and Fubini collapse
the inner double integral to `T·‖simpleAssemblyHorizon V‖²`; the outer `∫₀ᵀ` adds the last `T`. -/
theorem driftSimpleProcessLp_norm_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP T hBmeas) :
    ‖driftSimpleProcessLp (μ := μ) T hBmeas V.val‖ ≤ (T : ℝ) *
        ‖simpleAssemblyHorizon (μ := μ) T hBmeas V‖ := by
  set 𝓕 := natFiltration (mΩ := mΩ) hBmeas
  have hpredD := driftSimpleProcess_isStronglyPredictable hBmeas V.val
  have hmemD := memLp_uncurry_driftSimpleProcess (μ := μ) T hBmeas V.val
  have hmemV := memLp_uncurry_trimMeasure (μ := μ) T hBmeas V.val
  -- both `E`-norms², via `lp_two_norm_sq` + `coeFn_toLp` + `integral_trim`, as product integrals.
  have hnorm : ∀ (g : ℝ≥0 → Ω → ℝ)
      (hg : MemLp (Function.uncurry g) 2 (trimMeasure (μ := μ) T hBmeas)),
      StronglyMeasurable[𝓕.predictable] (Function.uncurry g) →
      ‖hg.toLp (Function.uncurry g)‖ ^ 2
        = ∫ z, (Function.uncurry g z) ^ 2 ∂((timeMeasureHorizon T).prod μ) := by
    intro g hg hgp
    rw [lp_two_norm_sq, integral_congr_ae (g := fun z ↦ (Function.uncurry g z) ^ 2)
      (by filter_upwards [hg.coeFn_toLp] with z hz; rw [hz]),
      show trimMeasure (μ := μ) T hBmeas
          = ((timeMeasureHorizon T).prod μ).trim 𝓕.predictable_le_prod from rfl,
      ← integral_trim 𝓕.predictable_le_prod
        (f := fun z ↦ (Function.uncurry g z) ^ 2) (hgp.pow 2)]
  have hsAsm : simpleAssemblyHorizon (μ := μ) T hBmeas V = hmemV.toLp (Function.uncurry ⇑V.val) :=
      rfl
  have hsq : ‖driftSimpleProcessLp (μ := μ) T hBmeas V.val‖ ^ 2
      ≤ ((T : ℝ) * ‖simpleAssemblyHorizon (μ := μ) T hBmeas V‖) ^ 2 := by
    rw [driftSimpleProcessLp, hnorm _ hmemD hpredD, mul_pow, hsAsm,
      hnorm _ hmemV V.val.isStronglyPredictable]
    -- ∫ (drift)² ∂prod ≤ (T:ℝ)² · ∫ (⇑V)² ∂prod
    have hmemD_prod : MemLp (Function.uncurry (driftSimpleProcess hBmeas V.val)) 2
        ((timeMeasureHorizon T).prod μ) :=
      memLp_of_memLp_trim 𝓕.predictable_le_prod hmemD
    have hmemV_prod : MemLp (Function.uncurry ⇑V.val) 2 ((timeMeasureHorizon T).prod μ) :=
      memLp_of_memLp_trim 𝓕.predictable_le_prod hmemV
    have hintD := hmemD_prod.integrable_sq
    have hintV := hmemV_prod.integrable_sq
    rw [integral_prod _ hintD]
    -- Fubini: `∫_ω ∫_{Ioc 0 T}(⇑V)² dμ = ∫_prod (⇑V)²`.
    have hW : ∫ ω, (∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑V.val s ω) ^ 2 ∂timeMeasure) ∂μ
        = ∫ z, (Function.uncurry ⇑V.val z) ^ 2 ∂((timeMeasureHorizon T).prod μ) := by
      rw [integral_prod _ hintV]
      exact integral_integral_swap hintV.swap
    calc ∫ t, ∫ ω, (driftSimpleProcess hBmeas V.val t ω) ^ 2 ∂μ ∂(timeMeasureHorizon T)
        ≤ ∫ _t : ℝ≥0, (T : ℝ) * ∫ z, (Function.uncurry ⇑V.val z) ^ 2
            ∂((timeMeasureHorizon T).prod μ)
            ∂(timeMeasureHorizon T) := by
          refine integral_mono_ae hintD.integral_prod_left (integrable_const _) ?_
          have hslice : ∀ᵐ t ∂(timeMeasureHorizon T),
              Integrable (fun ω ↦ (driftSimpleProcess hBmeas V.val t ω) ^ 2) μ :=
            hintD.prod_right_ae
          filter_upwards [ae_restrict_mem (μ := timeMeasure) measurableSet_Ioc, hslice]
            with t ht hint_t
          calc ∫ ω, (driftSimpleProcess hBmeas V.val t ω) ^ 2 ∂μ
              ≤ ∫ ω, (T : ℝ) * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑V.val s ω) ^ 2 ∂timeMeasure ∂μ :=
                integral_mono_ae hint_t
                  ((hintV.integral_prod_right).const_mul _)
                  (ae_of_all _ fun ω ↦ driftSimpleProcess_sq_le T hBmeas V.val ht.2 ω)
            _ = (T : ℝ) * ∫ z, (Function.uncurry ⇑V.val z) ^ 2
                  ∂((timeMeasureHorizon T).prod μ) := by
                rw [integral_const_mul, hW]
      _ = (T : ℝ) ^ 2 * ∫ z, (Function.uncurry ⇑V.val z) ^ 2 ∂((timeMeasureHorizon T).prod μ) := by
          rw [integral_const, timeMeasureHorizon, measureReal_def, Measure.restrict_apply_univ,
            timeMeasure_Ioc,
            ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact T.coe_nonneg),
            NNReal.coe_zero, sub_zero, smul_eq_mul]
          ring
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg T.coe_nonneg (norm_nonneg _))] at h

/-- **The elementary drift as a linear map** on the `T`-bounded simple processes,
`V ↦ driftSimpleProcessLp V` (the target of the `extendOfNorm` extension). -/
noncomputable def driftProcessLM (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    TBoundedSP T hBmeas →ₗ[ℝ] Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) where
  toFun V := driftSimpleProcessLp (μ := μ) T hBmeas V.val
  map_add' V W := by
    change driftSimpleProcessLp (μ := μ) T hBmeas ((V + W).val) = _
    rw [Submodule.coe_add, driftSimpleProcessLp, driftSimpleProcessLp, driftSimpleProcessLp,
        ← MemLp.toLp_add (memLp_uncurry_driftSimpleProcess T hBmeas V.val)
          (memLp_uncurry_driftSimpleProcess T hBmeas W.val)]
    congr 1
    funext z
    exact congrFun (driftSimpleProcess_add hBmeas V.val W.val z.1) z.2
  map_smul' c V := by
    change driftSimpleProcessLp (μ := μ) T hBmeas ((c • V).val) = _
    rw [Submodule.coe_smul, driftSimpleProcessLp, driftSimpleProcessLp, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_uncurry_driftSimpleProcess T hBmeas V.val)]
    congr 1
    funext z
    exact congrFun (driftSimpleProcess_smul hBmeas c V.val z.1) z.2

/-- **The assembled drift as a CLM on `E`.** Extends the elementary drift `driftProcessLM`
along the dense embedding `simpleAssemblyHorizon`, via `LinearMap.extendOfNorm` with the energy
bound `driftSimpleProcessLp_norm_le`. For `g ∈ E`, this is `t ↦ ∫₀ᵗ g(s,·) ds` — the drift term of
the Picard iterate — landing back in the predictable `L²` space `E`. Being a CLM it is linear,
bounded (`‖·‖ ≤ T‖·‖`), and predictable-by-construction, all for free. -/
noncomputable def driftProcessAssembled (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) →L[ℝ] Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  (driftProcessLM (μ := μ) T hBmeas).extendOfNorm (simpleAssemblyHorizon (μ := μ) T hBmeas)

/-- **The bridge (definitional).** On the embedding of a `T`-bounded simple process, the
assembled drift reproduces the elementary drift `driftSimpleProcessLp V`. -/
theorem driftProcessAssembled_simpleAssembly (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP T hBmeas) :
    driftProcessAssembled (μ := μ) T hBmeas (simpleAssemblyHorizon (μ := μ) T hBmeas V)
      = driftSimpleProcessLp (μ := μ) T hBmeas V.val := by
  rw [driftProcessAssembled,
      LinearMap.extendOfNorm_eq (simpleAssemblyHorizon_denseRange (μ := μ) T hBmeas)
    ⟨(T : ℝ), fun W ↦ driftSimpleProcessLp_norm_le T hBmeas W⟩]
  rfl

/-- **The drift operator bound** `‖driftProcessAssembled φ‖ ≤ T‖φ‖` for general `φ ∈ E` — the
witness of the `‖·‖ ≤ T‖·‖` the CLM advertises: the `extendOfNorm` operator norm inherited from the
elementary energy bound `driftSimpleProcessLp_norm_le`. -/
theorem driftProcessAssembled_norm_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ‖driftProcessAssembled (μ := μ) T hBmeas φ‖ ≤ (T : ℝ) * ‖φ‖ := by
  rw [driftProcessAssembled]
  exact LinearMap.norm_extendOfNorm_apply_le (simpleAssemblyHorizon_denseRange (μ := μ) T hBmeas)
    (T : ℝ) (fun W ↦ driftSimpleProcessLp_norm_le T hBmeas W) φ

end ItoIntegralProcessContinuousModification
end MathFin
