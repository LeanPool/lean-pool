/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Distribution.Feller
public import LeanPool.AiyagariEquilibrium.Equilibrium.Aiyagari
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationMonotone

/-!
# Aggregate capital is strictly positive

Every equilibrium result so far is conditional on excess demand changing sign, and nothing in
the development says that households save anything at all. This file supplies the missing
economics: under log utility, households rich enough in income save strictly, and the stationary
distribution then carries strictly positive aggregate capital.

## Capital is the mean of the policy

`markovOp_assetCoord` is the identity the whole argument runs on. The expected asset coordinate
next period is the policy today, because the asset the household carries forward does not depend
on which income shock arrives:

  `markovOp assetCoord = policyCoord`.

With stationarity that gives `aggregateCapital μ = ∫ policy dμ` — aggregate capital is the mean
saving, not merely something computed from the distribution. Everything after is a lower bound
on that integral.

## Rich households save, and the argument is the crudest deviation again

Saving `h` rather than nothing costs `u resources - u (resources - h)` and gains
`β (cont h - cont 0)`. For LOG the cost is `log (m / (m - h))`, which SHRINKS as resources grow,
while the gain is a fixed positive number — positive because the value function is strictly
increasing in assets, which `valueFunction_lt_of_lt` proves from strict monotonicity of `u`,
itself recovered from strict concavity. So above an explicit income level the household saves
strictly, with no envelope theorem and no Euler equation.

Since the cost falls with resources, it is enough to check the inequality at the household's
POOREST state in that income, `a = 0`, and it then holds at every asset level.

## Reaching those households

The income coordinate of the stationary distribution is bounded below by the worst transition
probability into that state, and that too is pure duality: the indicator of an income state is
CONTINUOUS here, `Z` being discrete, so it is a legitimate test function and
`markovOp (incomeIndicator z₁) s = transitionMatrix s.2 z₁`. Stationarity turns a uniform lower
bound on the column of the transition matrix into a lower bound on the mass.
-/

@[expose] public section

open scoped NNReal
open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### Strict monotonicity -/

/-- Period utility is STRICTLY increasing: a concave function that is flat on an interval is
affine there, which strict concavity forbids. -/
theorem strictMonoOn_u : StrictMonoOn P.u (Ioi 0) := by
  intro x hx y hy hxy
  rcases lt_or_eq_of_le (P.monotoneOn_u hx hy hxy.le) with h | h
  · exact h
  · exfalso
    have hx0 : (0 : ℝ) < x := hx
    have hy0 : (0 : ℝ) < y := hy
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    have hsum : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
    have hstrict := P.strictConcaveOn_u.2 hx hy (ne_of_lt hxy) hhalf hhalf hsum
    simp only [smul_eq_mul] at hstrict
    have hmid : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
    have hle : P.u ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) ≤ P.u y :=
      P.monotoneOn_u hmid hy (by linarith)
    linarith

/-- **The value function is strictly increasing in assets.** More assets buy strictly more
consumption at the same saving plan. -/
theorem valueFunction_lt_of_lt (hpc : P.PositiveConsumption) {x y : ℝ} {z : Z}
    (hx : x ∈ Icc assetFloor assetCap)
    (hy : y ∈ Icc assetFloor assetCap) (hxy : x < y) :
    P.toExtended.valueFunction (x, z) < P.toExtended.valueFunction (y, z) := by
  have hbm : P.policy (x, z) ∈ P.toExtended.feasible (x, z) := P.policy_mem _
  have hbm' : P.policy (x, z) ∈ P.toExtended.feasible (y, z) := P.feasible_mono hxy.le hbm
  have hcx : 0 < P.consumption (x, z) (P.policy (x, z)) := P.consumption_policy_pos hpc hx
  have hresl : P.resources (x, z) < P.resources (y, z) := by
    simp only [resources, max_eq_right hx.1, max_eq_right hy.1]
    nlinarith [P.interest_gt_neg_one]
  have hcy : 0 < P.consumption (y, z) (P.policy (x, z)) := by
    simp only [consumption] at hcx ⊢; linarith
  have hstep : P.objR (x, z) (P.policy (x, z)) < P.objR (y, z) (P.policy (x, z)) := by
    simp only [objR]
    have := P.strictMonoOn_u (mem_Ioi.mpr hcx) (mem_Ioi.mpr hcy)
      (by simp only [consumption] at hcx ⊢; linarith)
    linarith
  have h1 := P.objR_le_of_mem hy hbm' (P.mem_dom_of_pos hcy)
  have e1 : P.objR (x, z) (P.policy (x, z)) = P.toExtended.valueFunction (x, z) := by
    simp only [objR, cont]; exact (P.valueFunction_eq_policy hx).symm
  have e2 : P.objR (y, z) (P.policy (y, z)) = P.toExtended.valueFunction (y, z) := by
    simp only [objR, cont]; exact (P.valueFunction_eq_policy hy).symm
  rw [← e1, ← e2]
  linarith

/-- **The continuation is strictly increasing**, since some income state has positive
probability. -/
theorem cont_lt_of_lt (hpc : P.PositiveConsumption) (z : Z) {x y : ℝ}
    (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap)
    (hxy : x < y) : P.cont z x < P.cont z y := by
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Z, 0 < P.transitionMatrix z z₀ := by
    by_contra hcon
    push Not at hcon
    have hz : ∑ z', P.transitionMatrix z z' = 0 :=
      Finset.sum_eq_zero fun z' _ =>
        le_antisymm (hcon z') (P.transitionMatrix_nonneg _ _)
    rw [P.transitionMatrix_sum] at hz
    norm_num at hz
  simp only [cont]
  refine Finset.sum_lt_sum (fun z' _ => ?_) ⟨z₀, Finset.mem_univ _, ?_⟩
  · exact mul_le_mul_of_nonneg_left (P.valueFunction_lt_of_lt hpc hx hy hxy).le
      (P.transitionMatrix_nonneg _ _)
  · exact mul_lt_mul_of_pos_left (P.valueFunction_lt_of_lt hpc hx hy hxy) hz₀

/-! ### Capital is the mean of the policy -/

theorem norm_policy_incl_le (s : P.State) :
    ‖P.policy (P.incl s)‖ ≤ |assetFloor| + |assetCap| := by
  have h := P.policy_mem_region (P.incl s)
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [h.1, neg_abs_le assetFloor, abs_nonneg assetCap],
    by linarith [h.2, le_abs_self assetCap, abs_nonneg assetFloor]⟩

/-- Saving carried forward, as a bounded continuous function of the state. -/
noncomputable def policyCoord : P.State →ᵇ ℝ :=
  ofNormedAddCommGroup (fun s => P.policy (P.incl s))
    (P.continuousOn_policy.comp_continuous P.continuous_incl P.incl_mem)
    (|assetFloor| + |assetCap|) P.norm_policy_incl_le

@[simp] theorem policyCoord_apply (s : P.State) : P.policyCoord s = P.policy (P.incl s) := rfl

/-- **The expected asset coordinate next period is today's saving.** The asset carried forward
does not depend on which income shock arrives, so the expectation collapses. -/
theorem markovOp_assetCoord : P.markovOp P.assetCoord = P.policyCoord := by
  ext s
  simp only [markovOp_apply, policyCoord_apply]
  have hz : ∀ z' : Z, P.assetCoord (P.nextState s z') = P.policy (P.incl s) := fun _ => rfl
  simp only [hz]
  rw [← Finset.sum_mul, P.prob_sum, one_mul]

variable [MeasurableSpace Z] [BorelSpace Z]

/-- **Aggregate capital is mean saving.** -/
theorem aggregateCapital_eq_integral_policy {μ : ProbabilityMeasure P.State}
    (hμ : P.IsStationary μ) :
    P.aggregateCapital μ = ∫ s, P.policyCoord s ∂(μ : Measure P.State) := by
  calc P.aggregateCapital μ = P.aggregateCapital (P.pushProb μ) := by rw [hμ]
    _ = ∫ s, P.markovOp P.assetCoord s ∂(μ : Measure P.State) := by
        rw [aggregateCapital, coe_pushProb, P.integral_push]
    _ = ∫ s, P.policyCoord s ∂(μ : Measure P.State) := by rw [P.markovOp_assetCoord]

/-! ### The stationary distribution reaches every income state -/

open Classical in
/-- The indicator of an income state — continuous, because `Z` is discrete. -/
noncomputable def incomeIndicator (z₁ : Z) : P.State →ᵇ ℝ :=
  ofNormedAddCommGroup (fun s => if s.2 = z₁ then 1 else 0)
    ((continuous_of_discreteTopology (f := fun z : Z => if z = z₁ then (1 : ℝ) else 0)).comp
      continuous_snd) 1
    (fun s => by by_cases h : s.2 = z₁ <;> simp [h])

omit [MeasurableSpace Z] [BorelSpace Z] in
open Classical in
@[simp] theorem incomeIndicator_apply (z₁ : Z) (s : P.State) :
    P.incomeIndicator z₁ s = if s.2 = z₁ then 1 else 0 := rfl

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem markovOp_incomeIndicator (z₁ : Z) (s : P.State) :
    P.markovOp (P.incomeIndicator z₁) s = P.transitionMatrix s.2 z₁ := by
  classical
  simp only [markovOp_apply, incomeIndicator_apply, nextState]
  rw [Finset.sum_eq_single z₁ (fun b _ hb => by simp [hb]) (by simp)]
  simp [prob]

/-- **The stationary mass on an income state is at least the worst transition into it.** -/
theorem le_integral_incomeIndicator {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ)
    {z₁ : Z} {p₀ : ℝ} (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁) :
    p₀ ≤ ∫ s, P.incomeIndicator z₁ s ∂(μ : Measure P.State) := by
  have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
  calc p₀ = ∫ _s, p₀ ∂(μ : Measure P.State) := by simp
    _ ≤ ∫ s, P.markovOp (P.incomeIndicator z₁) s ∂(μ : Measure P.State) := by
        refine integral_mono (integrable_const _) ((P.markovOp _).integrable _) fun s => ?_
        rw [P.markovOp_incomeIndicator]
        exact hp s.2
    _ = ∫ s, P.incomeIndicator z₁ s ∂(P.push (μ : Measure P.State)) :=
        (P.integral_push _ _).symm
    _ = ∫ s, P.incomeIndicator z₁ s ∂(μ : Measure P.State) := by
        rw [← coe_pushProb, hμ]

/-! ### Rich households save -/

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **A household with enough income saves strictly.** The cost of saving `h` instead of nothing
is `log (m / (m - h))`, which falls as resources grow, while the gain `β (cont h - cont 0)` is a
fixed positive number. So it is enough to check the comparison at `a = 0`, the poorest state in
that income, and it then holds at every asset level. -/
theorem policy_pos_of_cost (hfl : assetFloor = 0) (z₁ : Z) {h κ : ℝ} (hh0 : 0 < h)
    (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hcost : ∀ R : ℝ, P.income z₁ ≤ R → P.u R - P.u (R - h) ≤ κ)
    (hgain : κ < P.discount * (P.cont z₁ h - P.cont z₁ 0))
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) :
    0 < P.policy (a, z₁) := by
  subst hfl
  rcases lt_or_eq_of_le (P.policy_mem_region (a, z₁)).1 with hpos | hzero
  · exact hpos
  exfalso
  have hm : P.income z₁ ≤ P.resources (a, z₁) := by
    simp only [resources, max_eq_right ha.1]
    nlinarith [P.interest_gt_neg_one, ha.1]
  have hmh : h < P.resources (a, z₁) := lt_of_lt_of_le hhinc hm
  have hfeas : h ∈ P.toExtended.feasible (a, z₁) := by
    rw [P.feasible_eq, P.maxSaving_eq]
    exact ⟨hh0.le, le_min hhcap hmh.le⟩
  have hch : 0 < P.consumption (a, z₁) h := by simp only [consumption]; linarith
  have hopt := P.objR_le_of_mem ha hfeas (P.mem_dom_of_pos hch)
  rw [← hzero] at hopt
  simp only [objR, consumption, sub_zero] at hopt
  linarith [hcost (P.resources (a, z₁)) hm]

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- The log instance of `policy_pos_of_cost`: the cost of saving `h` is `log (m / (m - h))`,
which falls as resources grow, so it is enough to check it at the poorest state in that income. -/
theorem policy_pos_of_income (hfl : assetFloor = 0) (hu : P.u = Real.log) (z₁ : Z) {h : ℝ}
    (hh0 : 0 < h)
    (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hgain : Real.log (P.income z₁ / (P.income z₁ - h))
      < P.discount * (P.cont z₁ h - P.cont z₁ 0))
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) :
    0 < P.policy (a, z₁) := by
  subst hfl
  have hinc0 : 0 < P.income z₁ := lt_trans hh0 hhinc
  refine P.policy_pos_of_cost rfl z₁ hh0 hhcap hhinc (fun R hm => ?_) hgain ha
  rw [hu]
  have hR : 0 < R := lt_of_lt_of_le hinc0 hm
  have hmono : R / (R - h) ≤ P.income z₁ / (P.income z₁ - h) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hm, hh0]
  have hlog := Real.log_le_log (div_pos (by linarith) (by linarith)) hmono
  rw [Real.log_div (by linarith) (by linarith)] at hlog
  linarith

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- A uniform positive lower bound on saving across the asset region, by compactness. -/
theorem exists_policy_lower_bound_of_cost (hfl : assetFloor = 0) (z₁ : Z) {h κ : ℝ} (hh0 : 0 < h)
    (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hcost : ∀ R : ℝ, P.income z₁ ≤ R → P.u R - P.u (R - h) ≤ κ)
    (hgain : κ < P.discount * (P.cont z₁ h - P.cont z₁ 0)) :
    ∃ ε > 0, ∀ a ∈ Icc assetFloor assetCap, ε ≤ P.policy (a, z₁) := by
  subst hfl
  have hne : (Icc (0 : ℝ) assetCap).Nonempty := ⟨0, ⟨le_rfl, P.assetFloor_le_assetCap⟩⟩
  have hcont : ContinuousOn (fun a : ℝ => P.policy (a, z₁)) (Icc (0 : ℝ) assetCap) :=
    P.continuousOn_policy.comp (by fun_prop) fun a ha => ha
  obtain ⟨a₀, ha₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  exact ⟨P.policy (a₀, z₁), P.policy_pos_of_cost rfl z₁ hh0 hhcap hhinc hcost hgain ha₀,
    fun a ha => isMinOn_iff.mp hmin a ha⟩

/-! ### Positive aggregate capital -/

/-- **Aggregate capital is strictly positive.** Households in income state `z₁` save at least
`ε`, the stationary distribution puts at least `p₀` of its mass there, and aggregate capital is
mean saving. -/
theorem aggregateCapital_pos_of_cost (hfl : assetFloor = 0) {μ : ProbabilityMeasure P.State}
    (hμ : P.IsStationary μ) {z₁ : Z} {p₀ : ℝ} (hp0 : 0 < p₀)
    (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    {h κ : ℝ} (hh0 : 0 < h) (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hcost : ∀ R : ℝ, P.income z₁ ≤ R → P.u R - P.u (R - h) ≤ κ)
    (hgain : κ < P.discount * (P.cont z₁ h - P.cont z₁ 0)) :
    0 < P.aggregateCapital μ := by
  subst hfl
  obtain ⟨ε, hε, hεle⟩ :=
    P.exists_policy_lower_bound_of_cost rfl z₁ hh0 hhcap hhinc hcost hgain
  rw [P.aggregateCapital_eq_integral_policy hμ]
  have hbound : ∀ s : P.State, ε * P.incomeIndicator z₁ s ≤ P.policyCoord s := by
    intro s
    by_cases hz : s.2 = z₁
    · have hmem : ((s.1 : ℝ)) ∈ Icc (0 : ℝ) assetCap := s.1.2
      have hge := hεle _ hmem
      have hind : P.incomeIndicator z₁ s = 1 := by simp [hz]
      have hpc : P.policyCoord s = P.policy ((s.1 : ℝ), s.2) := rfl
      rw [hind, mul_one, hpc, hz]
      exact hge
    · have hind : P.incomeIndicator z₁ s = 0 := by simp [hz]
      rw [hind, mul_zero]
      exact (P.policy_mem_region (P.incl s)).1
  calc (0 : ℝ) < ε * p₀ := by positivity
    _ ≤ ε * ∫ s, P.incomeIndicator z₁ s ∂(μ : Measure P.State) :=
        mul_le_mul_of_nonneg_left (P.le_integral_incomeIndicator hμ hp) hε.le
    _ = ∫ s, ε * P.incomeIndicator z₁ s ∂(μ : Measure P.State) := (integral_const_mul _ _).symm
    _ ≤ ∫ s, P.policyCoord s ∂(μ : Measure P.State) :=
        integral_mono (((P.incomeIndicator z₁).integrable _).const_mul ε)
          (P.policyCoord.integrable _) hbound

/-- The log instance of `aggregateCapital_pos_of_cost`. -/
theorem aggregateCapital_pos (hfl : assetFloor = 0) (hu : P.u = Real.log)
    {μ : ProbabilityMeasure P.State}
    (hμ : P.IsStationary μ) {z₁ : Z} {p₀ : ℝ} (hp0 : 0 < p₀)
    (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    {h : ℝ} (hh0 : 0 < h) (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hgain : Real.log (P.income z₁ / (P.income z₁ - h))
      < P.discount * (P.cont z₁ h - P.cont z₁ 0)) :
    0 < P.aggregateCapital μ := by
  subst hfl
  have hinc0 : 0 < P.income z₁ := lt_trans hh0 hhinc
  refine P.aggregateCapital_pos_of_cost rfl hμ hp0 hp hh0 hhcap hhinc (fun R hm => ?_) hgain
  rw [hu]
  have hmono : R / (R - h) ≤ P.income z₁ / (P.income z₁ - h) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hm, hh0]
  have hlog := Real.log_le_log (div_pos (by linarith) (by linarith)) hmono
  rw [Real.log_div (by linarith) (by linarith)] at hlog
  linarith

/-! ### The gain, bounded by primitives

`policy_pos_of_income` asks for a lower bound on `cont z₁ h - cont z₁ 0`, which is an object of
the solved model rather than a primitive. It is bounded below by the same deviation trick applied
one level down, and WHICH TERM OF THE SUM IS KEPT is the economics.

Bounding by the worst state — every `income z'` replaced by `maxIncome` — gives, for small `h`, a
condition amounting to `β (1 + r) > 1`. That is useless here: the natural asset bound wants
`β (1 + r) < 1`, so the two would collide. Keeping the LOW-income term instead gives
`P z z₀ · log (1 + (1+r) h / income z₀)`, and with `income z₀` small that term is large; the
condition becomes roughly `β (1 + r) · P z z₀ > minIncome / maxIncome`, satisfiable under ordinary
impatience provided income is dispersed.

That difference is the precautionary motive. The household saves not because it is patient but
because with probability `P z z₀` it lands where consumption is small and the marginal value of
assets is large. The motive enters through the DISPERSION of income rather than through convexity
of `u'`, which is why it is available without a third derivative. -/

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem valueFunction_le_of_le (hpc : P.PositiveConsumption) {x y : ℝ} {z : Z}
    (hx : x ∈ Icc assetFloor assetCap)
    (hy : y ∈ Icc assetFloor assetCap) (hxy : x ≤ y) :
    P.toExtended.valueFunction (x, z) ≤ P.toExtended.valueFunction (y, z) := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · exact (P.valueFunction_lt_of_lt hpc hx hy hlt).le

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem resources_zero (hfl : assetFloor = 0) (z : Z) : P.resources (0, z) = P.income z := by
  subst hfl
  simp only [resources]; norm_num

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The value of extra assets is at least the one-period utility gain**, got by carrying the
poorer household's own saving plan forward. -/
theorem valueFunction_sub_ge (hpc : P.PositiveConsumption) {x y : ℝ}
    (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap)
    (hxy : x ≤ y) (z : Z) :
    P.u (P.consumption (x, z) (P.policy (x, z)) + (1 + P.interest) * (y - x))
        - P.u (P.consumption (x, z) (P.policy (x, z)))
      ≤ P.toExtended.valueFunction (y, z) - P.toExtended.valueFunction (x, z) := by
  have hbm : P.policy (x, z) ∈ P.toExtended.feasible (x, z) := P.policy_mem _
  have hbm' : P.policy (x, z) ∈ P.toExtended.feasible (y, z) := P.feasible_mono hxy hbm
  have hc0 : 0 < P.consumption (x, z) (P.policy (x, z)) := P.consumption_policy_pos hpc hx
  have hres : P.resources (y, z) = P.resources (x, z) + (1 + P.interest) * (y - x) := by
    simp only [resources, max_eq_right hx.1, max_eq_right hy.1]; ring
  have hch : P.consumption (y, z) (P.policy (x, z))
      = P.consumption (x, z) (P.policy (x, z)) + (1 + P.interest) * (y - x) := by
    simp only [consumption, hres]; ring
  have hchpos : 0 < P.consumption (y, z) (P.policy (x, z)) := by
    rw [hch]
    have : 0 ≤ (1 + P.interest) * (y - x) :=
      mul_nonneg P.interest_gt_neg_one.le (by linarith)
    linarith
  have hopt := P.objR_le_of_mem hy hbm' (P.mem_dom_of_pos hchpos)
  have e0 : P.objR (x, z) (P.policy (x, z)) = P.toExtended.valueFunction (x, z) := by
    simp only [objR, cont]; exact (P.valueFunction_eq_policy hx).symm
  have eh : P.objR (y, z) (P.policy (y, z)) = P.toExtended.valueFunction (y, z) := by
    simp only [objR, cont]; exact (P.valueFunction_eq_policy hy).symm
  simp only [objR, cont, hch] at hopt
  simp only [objR, cont] at e0 eh
  rw [← e0, ← eh]
  linarith

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- The continuation rises with saving. -/
theorem cont_le_of_le (hpc : P.PositiveConsumption) (z : Z) {x y : ℝ}
    (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap)
    (hxy : x ≤ y) : P.cont z x ≤ P.cont z y := by
  simp only [cont]
  refine Finset.sum_le_sum fun z' _ => ?_
  exact mul_le_mul_of_nonneg_left (P.valueFunction_le_of_le hpc hx hy hxy)
    (P.transitionMatrix_nonneg _ _)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- A lower bound on the one-period utility gain in one successor state gives a
probability-weighted lower bound on the continuation gain. -/
theorem cont_sub_ge_of_utility_bound (hpc : P.PositiveConsumption) (z z₀ : Z)
    {x y bound : ℝ} (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap)
    (hxy : x ≤ y)
    (hbound : ∀ c : ℝ, 0 < c → c ≤ P.income z₀ + (1 + P.interest) * x - assetFloor →
      bound ≤ P.u (c + (1 + P.interest) * (y - x)) - P.u c) :
    P.transitionMatrix z z₀ * bound ≤ P.cont z y - P.cont z x := by
  have hterm : P.transitionMatrix z z₀ *
      (P.toExtended.valueFunction (y, z₀) - P.toExtended.valueFunction (x, z₀))
        ≤ P.cont z y - P.cont z x := by
    simp only [cont, ← Finset.sum_sub_distrib, ← mul_sub]
    refine Finset.single_le_sum (f := fun z' : Z => P.transitionMatrix z z' *
      (P.toExtended.valueFunction (y, z') - P.toExtended.valueFunction (x, z')))
      (fun z' _ => ?_) (Finset.mem_univ z₀)
    exact mul_nonneg (P.transitionMatrix_nonneg _ _)
      (sub_nonneg.mpr (P.valueFunction_le_of_le hpc hx hy hxy))
  have hc : 0 < P.consumption (x, z₀) (P.policy (x, z₀)) := P.consumption_policy_pos hpc hx
  have hcle : P.consumption (x, z₀) (P.policy (x, z₀))
      ≤ P.income z₀ + (1 + P.interest) * x - assetFloor := by
    simp only [consumption, resources, max_eq_right hx.1]
    exact sub_le_sub_left (P.policy_mem_region (x, z₀)).1 _
  exact (mul_le_mul_of_nonneg_left
    ((hbound _ hc hcle).trans (P.valueFunction_sub_ge hpc hx hy hxy z₀))
    (P.transitionMatrix_nonneg _ _)).trans hterm

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The continuation's gain between two saving levels, in primitives.** -/
theorem log_cont_sub_ge_gen (hfl : assetFloor = 0) (hpc : P.PositiveConsumption)
    (hu : P.u = Real.log) (z z₀ : Z)
    {x y : ℝ}
    (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap) (hxy : x ≤ y) :
    P.transitionMatrix z z₀ * Real.log (1 + (1 + P.interest) * (y - x)
        / (P.income z₀ + (1 + P.interest) * x))
      ≤ P.cont z y - P.cont z x := by
  subst hfl
  have hRh : 0 ≤ (1 + P.interest) * (y - x) :=
    mul_nonneg P.interest_gt_neg_one.le (sub_nonneg.mpr hxy)
  refine P.cont_sub_ge_of_utility_bound hpc z z₀ hx hy hxy ?_
  intro c hc hcle
  simp only [sub_zero] at hcle
  rw [hu]
  have hden : 0 < P.income z₀ + (1 + P.interest) * x := lt_of_lt_of_le hc hcle
  have hfrac : 0 ≤ (1 + P.interest) * (y - x) / (P.income z₀ + (1 + P.interest) * x) :=
    div_nonneg hRh hden.le
  rw [← Real.log_div (by linarith) hc.ne']
  refine Real.log_le_log (by linarith) ?_
  rw [le_div_iff₀ hc]
  have hkey : (1 + P.interest) * (y - x) / (P.income z₀ + (1 + P.interest) * x) * c
      ≤ (1 + P.interest) * (y - x) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left hcle hRh
  nlinarith only [hkey]

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The continuation's gain from zero, in primitives.** Only the term for income state `z₀` is
kept; the rest are non-negative. For a LOW income `z₀` the logarithm is large, and that is the
precautionary motive. -/
theorem log_cont_sub_ge (hfl : assetFloor = 0) (hpc : P.PositiveConsumption)
    (hu : P.u = Real.log) (z z₀ : Z) {h : ℝ}
    (hh : h ∈ Icc assetFloor assetCap) :
    P.transitionMatrix z z₀ * Real.log (1 + (1 + P.interest) * h / P.income z₀)
      ≤ P.cont z h - P.cont z 0 := by
  subst hfl
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) assetCap := ⟨le_rfl, P.assetFloor_le_assetCap⟩
  have := P.log_cont_sub_ge_gen rfl hpc hu z z₀ h0 hh hh.1
  simpa using this

/-- **Aggregate capital is strictly positive, from primitives alone.** Every hypothesis is stated
in `β`, `r`, the income levels and the transition matrix. -/
theorem aggregateCapital_pos_of_primitives (hfl : assetFloor = 0)
    (hpc : P.PositiveConsumption) (hu : P.u = Real.log)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) {z₁ z₀ : Z} {p₀ : ℝ} (hp0 : 0 < p₀)
    (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    {h : ℝ} (hh0 : 0 < h) (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hgain : Real.log (P.income z₁ / (P.income z₁ - h))
      < P.discount * (P.transitionMatrix z₁ z₀
          * Real.log (1 + (1 + P.interest) * h / P.income z₀))) :
    0 < P.aggregateCapital μ := by
  subst hfl
  refine P.aggregateCapital_pos rfl hu hμ hp0 hp hh0 hhcap hhinc (lt_of_lt_of_le hgain ?_)
  exact mul_le_mul_of_nonneg_left (P.log_cont_sub_ge rfl hpc hu z₁ z₀ ⟨hh0.le, hhcap⟩)
    P.discount.coe_nonneg

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **A quantitative lower bound on saving.** A household with enough income saves at least
`h/2`, not merely something positive — which is what a sign change needs, since the rate at
which demand falls below supply has to be chosen from a number. -/
theorem policy_ge_of_cost (hfl : assetFloor = 0) (hpc : P.PositiveConsumption) (z₁ : Z)
    {h κ : ℝ} (hh0 : 0 < h)
    (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hcost : ∀ R b : ℝ, P.income z₁ ≤ R → 0 ≤ b → b ≤ h → P.u (R - b) - P.u (R - h) ≤ κ)
    (hgain : κ < P.discount * (P.cont z₁ h - P.cont z₁ (h / 2)))
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) :
    h / 2 ≤ P.policy (a, z₁) := by
  subst hfl
  by_contra hcon
  rw [not_le] at hcon
  have hinc0 : 0 < P.income z₁ := lt_trans hh0 hhinc
  have hm : P.income z₁ ≤ P.resources (a, z₁) := by
    simp only [resources, max_eq_right ha.1]
    nlinarith [P.interest_gt_neg_one, ha.1]
  have hmh : h < P.resources (a, z₁) := lt_of_lt_of_le hhinc hm
  have hfeas : h ∈ P.toExtended.feasible (a, z₁) := by
    rw [P.feasible_eq, P.maxSaving_eq]
    exact ⟨hh0.le, le_min hhcap hmh.le⟩
  have hch : 0 < P.consumption (a, z₁) h := by simp only [consumption]; linarith
  have hopt := P.objR_le_of_mem ha hfeas (P.mem_dom_of_pos hch)
  have hbreg : P.policy (a, z₁) ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region _
  have hhalfreg : h / 2 ∈ Icc (0 : ℝ) assetCap := ⟨by linarith, by linarith⟩
  have hmono : P.cont z₁ (P.policy (a, z₁)) ≤ P.cont z₁ (h / 2) :=
    P.cont_le_of_le hpc z₁ hbreg hhalfreg hcon.le
  have hcostle := hcost (P.resources (a, z₁)) (P.policy (a, z₁)) hm hbreg.1 (by linarith)
  simp only [objR, consumption] at hopt
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hmono hβ
  have hdist : (P.discount : ℝ) * (P.cont z₁ h - P.cont z₁ (h / 2))
      = (P.discount : ℝ) * P.cont z₁ h - (P.discount : ℝ) * P.cont z₁ (h / 2) := by ring
  linarith [hopt, hcostle, hgain, hscaled, hdist.le, hdist.ge]

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- The log instance of `policy_ge_of_cost`. -/
theorem policy_ge_of_gain (hfl : assetFloor = 0) (hpc : P.PositiveConsumption)
    (hu : P.u = Real.log) (z₁ : Z)
    {h : ℝ} (hh0 : 0 < h)
    (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hgain : Real.log (P.income z₁ / (P.income z₁ - h))
      < P.discount * (P.cont z₁ h - P.cont z₁ (h / 2)))
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) :
    h / 2 ≤ P.policy (a, z₁) := by
  subst hfl
  have hinc0 : 0 < P.income z₁ := lt_trans hh0 hhinc
  refine P.policy_ge_of_cost rfl hpc z₁ hh0 hhcap hhinc (fun R b hm hb0 hbh => ?_) hgain ha
  rw [hu]
  have hratio : (R - b) / (R - h) ≤ P.income z₁ / (P.income z₁ - h) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hm, hh0, hb0, hhinc]
  rw [← Real.log_div (by linarith) (by linarith)]
  exact Real.log_le_log (div_pos (by linarith) (by linarith)) hratio

end IncomeFluctuation

end LeanEconomics
