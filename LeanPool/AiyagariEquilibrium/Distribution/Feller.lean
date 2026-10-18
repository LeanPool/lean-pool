/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuation
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure


/-!
# The agent distribution: state space and Markov operator

Step one towards a stationary agent distribution for the income fluctuation problem.

## The compact state space

The model is posed with state space `ℝ × Z`, but a distribution has to live somewhere
compact -- Prokhorov's theorem, which supplies the compactness of the space of probability
measures, needs a compact underlying space. The household never leaves
`[0, assetCap] × Z`, so that is where the distribution lives, and `State` is that region as
a space in its own right rather than as a subset of a larger one.

Taking it as a subtype is forced. A *subset* of `ℝ × Z` would not be a compact space, and
the earlier concavity work could not use a subtype because it is not a module over `ℝ`.
Both choices are right in their own place: concavity needs the linear structure of the
ambient space, the distribution needs compactness of the region.

## The Markov operator

`markovOp h s` is the expected value of `h` at next period's state, given that the household
is at `s` today and follows its optimal policy. The content of the definition is that it
lands in the *bounded continuous* functions again:

* continuity is the **Feller property**, and comes from continuity of the optimal policy,
  which is what the whole concavity and uniqueness development was for;
* boundedness is immediate from `∑ prob = 1`.

Feller is what will make the induced map on probability measures continuous, and continuity
of that map is what a fixed point argument needs.

## The operator on measures

`push μ` is where the distribution `μ` is a period later. It is assembled from
`Measure.withDensity` and `Measure.map` rather than from `Measure.bind`: Mathlib has
`lintegral_bind` but no Bochner `integral_bind`, whereas both of the former have their
Bochner lemmas, and it is the Bochner integral that the weak topology is stated with.

`integral_push` is the duality `∫ h d(push μ) = ∫ (markovOp h) dμ`, and it is what makes
the whole thing work: weak convergence is tested against bounded continuous functions, so
weak continuity of `push` reduces immediately to `markovOp h` being one.
-/

@[expose] public section

open scoped NNReal ENNReal
open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-- The compact region the agent distribution lives on: assets in `[0, assetCap]` paired
with an income state. -/
abbrev State (_P : IncomeFluctuation Z assetFloor assetCap) : Type _ :=
  ↥(Icc assetFloor assetCap) × Z

instance : CompactSpace P.State :=
  haveI : CompactSpace ↥(Icc assetFloor assetCap) := isCompact_iff_compactSpace.mp isCompact_Icc
  inferInstanceAs (CompactSpace (_ × _))

/-- The region, read back as a state of the original model. -/
def incl (s : P.State) : ℝ × Z := ((s.1 : ℝ), s.2)

theorem continuous_incl : Continuous P.incl :=
  (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd

theorem incl_mem (s : P.State) : (P.incl s).1 ∈ Icc assetFloor assetCap := s.1.2

/-- Next period's assets under the optimal policy, as a point of the region. -/
noncomputable def nextAssets (s : P.State) : ↥(Icc assetFloor assetCap) :=
  ⟨P.policy (P.incl s), P.policy_mem_region _⟩

/-- Next period's state if the income shock `z'` occurs. -/
noncomputable def nextState (s : P.State) (z' : Z) : P.State := (P.nextAssets s, z')

/-- **The policy moves the household continuously within the region.** This is the Feller
input, and it is exactly what the concavity and uniqueness development bought. -/
theorem continuous_nextAssets : Continuous P.nextAssets :=
  (P.continuousOn_policy.comp_continuous P.continuous_incl P.incl_mem).subtype_mk _

theorem continuous_nextState (z' : Z) : Continuous fun s => P.nextState s z' :=
  P.continuous_nextAssets.prodMk continuous_const

/-- The probability of moving to income state `z'`, as a function of today's state. -/
noncomputable def prob (s : P.State) (z' : Z) : ℝ := P.transitionMatrix s.2 z'

theorem prob_nonneg (s : P.State) (z' : Z) : 0 ≤ P.prob s z' := P.transitionMatrix_nonneg _ _

theorem prob_sum (s : P.State) : ∑ z', P.prob s z' = 1 := P.transitionMatrix_sum _

theorem continuous_prob (z' : Z) : Continuous fun s => P.prob s z' :=
  (continuous_of_discreteTopology (f := fun z => P.transitionMatrix z z')).comp continuous_snd

/-- The expected value of `h` next period, as a bare function. -/
noncomputable def markovFn (h : P.State →ᵇ ℝ) (s : P.State) : ℝ :=
  ∑ z', P.prob s z' * h (P.nextState s z')

theorem continuous_markovFn (h : P.State →ᵇ ℝ) : Continuous (P.markovFn h) :=
  continuous_finsetSum _ fun z' _ =>
    (P.continuous_prob z').mul (h.continuous.comp (P.continuous_nextState z'))

theorem abs_markovFn_le (h : P.State →ᵇ ℝ) (s : P.State) : |P.markovFn h s| ≤ ‖h‖ := by
  calc |P.markovFn h s| ≤ ∑ z', |P.prob s z' * h (P.nextState s z')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z', P.prob s z' * |h (P.nextState s z')| := by
        refine Finset.sum_congr rfl fun z' _ => ?_
        rw [abs_mul, abs_of_nonneg (P.prob_nonneg s z')]
    _ ≤ ∑ z', P.prob s z' * ‖h‖ := by
        refine Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left ?_ (P.prob_nonneg s z')
        simpa [Real.norm_eq_abs] using h.norm_coe_le_norm (P.nextState s z')
    _ = ‖h‖ := by rw [← Finset.sum_mul, P.prob_sum, one_mul]

/-- **The Markov operator.** `markovOp h` is the expected value of `h` next period. That it
is again bounded and *continuous* is the Feller property. -/
noncomputable def markovOp (h : P.State →ᵇ ℝ) : P.State →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (P.markovFn h) (P.continuous_markovFn h) ‖h‖
    fun s => by simpa [Real.norm_eq_abs] using P.abs_markovFn_le h s

@[simp]
theorem markovOp_apply (h : P.State →ᵇ ℝ) (s : P.State) :
    P.markovOp h s = ∑ z', P.prob s z' * h (P.nextState s z') := rfl

theorem norm_markovOp_le (h : P.State →ᵇ ℝ) : ‖P.markovOp h‖ ≤ ‖h‖ :=
  (norm_le (norm_nonneg h)).2 fun s => by
    rw [Real.norm_eq_abs]
    exact P.abs_markovFn_le h s

/-- The operator is monotone: a larger payoff tomorrow is worth more today. -/
theorem markovOp_mono {h k : P.State →ᵇ ℝ} (hk : ⇑h ≤ ⇑k) : ⇑(P.markovOp h) ≤ ⇑(P.markovOp k) := by
  intro s
  refine Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left ?_ (P.prob_nonneg s z')
  exact hk _

/-- The operator is unital: a constant payoff is worth its own value. This is `∑ prob = 1`,
and it is what will make the induced map send probability measures to probability
measures. -/
theorem markovOp_const (c : ℝ) : P.markovOp (const P.State c) = const P.State c := by
  ext s
  simp only [markovOp_apply, const_apply, ← Finset.sum_mul, P.prob_sum, one_mul]

/-! ### The operator on measures -/

open MeasureTheory

variable [MeasurableSpace Z] [BorelSpace Z]

/-- The reweighting density for shock `z'`, as an `ℝ≥0`-valued function. -/
noncomputable def dens (z' : Z) (s : P.State) : ℝ≥0 := (P.prob s z').toNNReal

theorem measurable_dens (z' : Z) : Measurable (P.dens z') :=
  (continuous_real_toNNReal.comp (P.continuous_prob z')).measurable

omit [MeasurableSpace Z] [BorelSpace Z] in
@[simp]
theorem coe_dens (z' : Z) (s : P.State) : ((P.dens z' s : ℝ≥0) : ℝ) = P.prob s z' :=
  Real.coe_toNNReal _ (P.prob_nonneg s z')

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem sum_dens (s : P.State) : ∑ z', ((P.dens z' s : ℝ≥0) : ℝ≥0∞) = 1 := by
  have hz : ∀ z' : Z, ((P.dens z' s : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (P.prob s z') :=
    fun _ => rfl
  rw [Finset.sum_congr rfl fun z' _ => hz z',
    ← ENNReal.ofReal_sum_of_nonneg fun z' _ => P.prob_nonneg s z', P.prob_sum s,
    ENNReal.ofReal_one]

/-- **One period of the agent distribution's motion.** Each income state `z'` reweights the
distribution by the probability of moving there and pushes it along the policy. -/
noncomputable def push (μ : Measure P.State) : Measure P.State :=
  Measure.sum fun z' =>
    (μ.withDensity fun s => (P.dens z' s : ℝ≥0∞)).map fun s => P.nextState s z'

theorem measurable_nextState (z' : Z) : Measurable fun s => P.nextState s z' :=
  (P.continuous_nextState z').measurable

/-- `push` preserves total mass, because the transition probabilities sum to one. -/
instance isProbabilityMeasure_push (μ : Measure P.State) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (P.push μ) := by
  constructor
  rw [push, Measure.sum_apply _ MeasurableSet.univ]
  have hterm : ∀ z' : Z,
      ((μ.withDensity fun s => (P.dens z' s : ℝ≥0∞)).map fun s => P.nextState s z') univ
        = ∫⁻ s, (P.dens z' s : ℝ≥0∞) ∂μ := by
    intro z'
    rw [Measure.map_apply (P.measurable_nextState z') MeasurableSet.univ,
      Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [tsum_fintype]
  simp only [hterm]
  rw [← lintegral_finsetSum _ fun z' _ => ((P.measurable_dens z').coe_nnreal_ennreal)]
  simp only [P.sum_dens]
  simp

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- Each transition probability is at most one. -/
theorem prob_le_one (s : P.State) (z' : Z) : P.prob s z' ≤ 1 := by
  rw [← P.prob_sum s]
  exact Finset.single_le_sum (fun i _ => P.prob_nonneg s i) (Finset.mem_univ z')

theorem integrable_term (μ : Measure P.State) [IsProbabilityMeasure μ] (h : P.State →ᵇ ℝ)
    (z' : Z) : Integrable (fun s => P.prob s z' * h (P.nextState s z')) μ := by
  refine (integrable_const ‖h‖).mono' ?_ ?_
  · exact ((P.continuous_prob z').mul
      (h.continuous.comp (P.continuous_nextState z'))).measurable.aestronglyMeasurable
  · filter_upwards with s
    have h1 := P.prob_le_one s z'
    have h2 : |h (P.nextState s z')| ≤ ‖h‖ := by
      simpa [Real.norm_eq_abs] using h.norm_coe_le_norm (P.nextState s z')
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (P.prob_nonneg s z')]
    nlinarith [P.prob_nonneg s z', abs_nonneg (h (P.nextState s z'))]

/-- **Duality.** The integral of `h` against tomorrow's distribution is the integral of the
expected value of `h` against today's. This is the bridge between the two operators, and it
is what turns the Feller property into weak continuity. -/
theorem integral_push (μ : Measure P.State) [IsProbabilityMeasure μ] (h : P.State →ᵇ ℝ) :
    ∫ s, h s ∂(P.push μ) = ∫ s, P.markovOp h s ∂μ := by
  have hterm : ∀ z' : Z,
      ∫ s, h s ∂((μ.withDensity fun s => (P.dens z' s : ℝ≥0∞)).map fun s => P.nextState s z')
        = ∫ s, P.prob s z' * h (P.nextState s z') ∂μ := by
    intro z'
    rw [integral_map (P.measurable_nextState z').aemeasurable
      h.continuous.measurable.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul (P.measurable_dens z')]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    calc (P.dens z' s : ℝ≥0) • h (P.nextState s z')
        = ((P.dens z' s : ℝ≥0) : ℝ) • h (P.nextState s z') := NNReal.smul_def _ _
      _ = P.prob s z' * h (P.nextState s z') := by rw [smul_eq_mul, P.coe_dens z' s]
  have hint : Integrable (fun s => h s) (P.push μ) := h.integrable _
  rw [push]
  rw [integral_sum_measure hint, tsum_fintype]
  simp only [hterm]
  rw [← integral_finsetSum _ fun z' _ => P.integrable_term μ h z']
  rfl

/-- **The agent distribution operator**, on probability measures. -/
noncomputable def pushProb (μ : ProbabilityMeasure P.State) : ProbabilityMeasure P.State :=
  ⟨P.push (μ : Measure P.State), P.isProbabilityMeasure_push _⟩

@[simp]
theorem coe_pushProb (μ : ProbabilityMeasure P.State) :
    ((P.pushProb μ : ProbabilityMeasure P.State) : Measure P.State)
      = P.push (μ : Measure P.State) := rfl

/-- **The distribution operator is weakly continuous.** This is the Feller property in the
form a fixed point argument needs, and it falls straight out of the duality: weak
convergence is tested against bounded continuous functions, and `markovOp h` is one. -/
theorem continuous_pushProb : Continuous P.pushProb := by
  rw [continuous_iff_continuousAt]
  intro μ
  rw [ContinuousAt, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro h
  have hdual : ∀ ν : ProbabilityMeasure P.State,
      ∫ s, h s ∂((P.pushProb ν : ProbabilityMeasure P.State) : Measure P.State)
        = ∫ s, P.markovOp h s ∂(ν : Measure P.State) := fun ν => P.integral_push _ h
  simp only [hdual]
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_id : Filter.Tendsto id (𝓝 μ) (𝓝 μ)) (P.markovOp h)

/-- A **stationary agent distribution** is a fixed point of the operator. -/
def IsStationary (μ : ProbabilityMeasure P.State) : Prop := P.pushProb μ = μ

end IncomeFluctuation

end LeanEconomics
