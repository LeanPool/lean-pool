/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.DynamicProgramming.Extended
public import LeanPool.AiyagariEquilibrium.Topology.IccCorrespondence
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Consumption and savings with period utility unbounded below

Period utility may fall to `-∞` at zero consumption, which covers `σ ≥ 1` in the CES family
and log utility. Assets are capped.

## This file used to use a floor

It replaced `u` by `max floor u` to keep the reward real-valued and bounded, and then had
to prove the floor never binds: bounds on the value function above and below, then
`floor_lt_rewardFn_optimal`, then `cFloor_le_consumption_optimal`. Four structure fields
(`floor`, `cFloor`, `u_cFloor_le_floor`, `floor_lt`) and about a hundred and fifty lines of
proof existed only to establish that a device introduced for technical reasons was
invisible in the answer.

With `LeanEconomics.DynamicProgramming.Extended` the reward is simply `-∞` there. All of
that machinery is gone. What replaces it is a single hypothesis, `tendsto_atBot_u`, saying
utility falls to `-∞` at zero consumption -- which is not an extra assumption at all, since
it is precisely the situation that forced the floor.

**Positive consumption at the optimum now comes for free.** It used to be the conclusion of
the floor argument. Now it follows from the value function being real: if the optimal
action left zero consumption the reward would be `-∞`, so the value would be `-∞`, and it
is not. That is `exists_optimal_saving`, which returns `0 < consumption` as part of its
conclusion rather than requiring a separate development.

## What is unchanged

Consumption is still clamped *above*, and assets are still capped. Neither has anything to
do with `-∞`; both are the ordinary requirement that the reward be bounded above, which the
weighted theory addresses separately.

Cash on hand is now computed from `max 0 a` rather than `a`. With a floor, a state with
negative cash on hand received the floor value; without one it would receive `-∞`, which
the framework does not allow. Reading assets as nonnegative keeps the value finite
everywhere, and changes nothing on `[0, assetCap]`, which is where the results are stated.
-/

@[expose] public section

open scoped NNReal
open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

/-- `c ↦ -1/c`, that is CES utility at `σ = 2`, is strictly concave on the positives.
Mathlib has no convexity lemma for `x⁻¹`, and its `rpow` convexity results cover only
exponents `≥ 1`, so this is proved by hand: the difference of the two sides is
`a * b * (x - y)² / (x * y * (a * x + b * y))`. -/
theorem strictConcaveOn_neg_inv : StrictConcaveOn ℝ (Ioi 0) (fun c : ℝ => -c⁻¹) := by
  refine ⟨convex_Ioi 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have hs : (0 : ℝ) < a * x + b * y := by positivity
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hpos : 0 < a * b * (x - y) ^ 2 := by positivity
  have key : (a * x + b * y)⁻¹ < a * x⁻¹ + b * y⁻¹ := by
    rw [← sub_pos]
    have hb' : b = 1 - a := by linarith
    subst hb'
    have heq : a * x⁻¹ + (1 - a) * y⁻¹ - (a * x + (1 - a) * y)⁻¹
        = (a * (1 - a) * (x - y) ^ 2) / (x * y * (a * x + (1 - a) * y)) := by
      field_simp
      ring
    rw [heq]
    positivity
  simp only [smul_eq_mul]
  linarith

/-- A consumption-savings problem whose period utility is unbounded below. -/
structure ConsumptionSavingsUnbounded where
  /-- Constant labour income. -/
  income : ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The upper bound imposed on asset holdings. -/
  assetCap : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  /-- Period utility, required to behave only on positive consumption. -/
  u : ℝ → ℝ
  income_pos : 0 < income
  interest_gt_neg_one : 0 < 1 + interest
  assetCap_nonneg : 0 ≤ assetCap
  discount_lt_one : discount < 1
  continuousOn_u : ContinuousOn u (Ioi 0)
  monotoneOn_u : MonotoneOn u (Ioi 0)
  /-- Utility falls to `-∞` as consumption vanishes. This single hypothesis replaces the
  four fields the floored version needed. -/
  tendsto_atBot_u : Tendsto u (𝓝[>] 0) atBot
  /-- Diminishing marginal utility. Needed for a *unique* optimal policy, hence for an
  agent distribution to be a well-defined object. -/
  strictConcaveOn_u : StrictConcaveOn ℝ (Ioi 0) u

namespace ConsumptionSavingsUnbounded

variable (P : ConsumptionSavingsUnbounded)

/-- Cash on hand, with assets read as nonnegative. -/
noncomputable def resources (a : ℝ) : ℝ := P.income + (1 + P.interest) * max 0 a

/-- The largest consumption the capped problem allows. -/
noncomputable def maxConsumption : ℝ := P.income + (1 + P.interest) * P.assetCap

/-- The largest asset holding that can be carried forward. -/
noncomputable def maxSaving (a : ℝ) : ℝ := max 0 (min P.assetCap (P.resources a))

/-- Consumption on the budget line. -/
noncomputable def consumption (a a' : ℝ) : ℝ := P.resources a - a'

/-- The reward: utility of consumption clamped above, and `-∞` where consumption vanishes.
No floor. -/
noncomputable def rewardFn (p : ℝ × ℝ) : EReal :=
  extendBot P.u (min P.maxConsumption (P.consumption p.1 p.2))

theorem income_le_resources (a : ℝ) : P.income ≤ P.resources a := by
  have : 0 ≤ (1 + P.interest) * max 0 a :=
    mul_nonneg P.interest_gt_neg_one.le (le_max_left _ _)
  simp only [resources]; linarith

theorem resources_pos (a : ℝ) : 0 < P.resources a :=
  lt_of_lt_of_le P.income_pos (P.income_le_resources a)

theorem income_le_maxConsumption : P.income ≤ P.maxConsumption := by
  have : 0 ≤ (1 + P.interest) * P.assetCap :=
    mul_nonneg P.interest_gt_neg_one.le P.assetCap_nonneg
  simp only [maxConsumption]; linarith

theorem maxConsumption_pos : 0 < P.maxConsumption :=
  lt_of_lt_of_le P.income_pos P.income_le_maxConsumption

theorem continuous_resources : Continuous P.resources :=
  continuous_const.add (continuous_const.mul (continuous_const.max continuous_id))

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max (continuous_const.min P.continuous_resources)

theorem continuous_rewardFn : Continuous P.rewardFn := by
  refine (continuous_extendBot P.continuousOn_u P.tendsto_atBot_u).comp
    (continuous_const.min ?_)
  exact (P.continuous_resources.comp continuous_fst).sub continuous_snd

/-- The problem as a dynamic program with an extended-real reward. -/
noncomputable def toExtended : ExtendedProgram ℝ ℝ where
  feasible a := Icc 0 (P.maxSaving a)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  reward := ⟨P.rewardFn, P.continuous_rewardFn⟩
  rewardMax := P.u P.maxConsumption
  reward_le := by
    intro s a _
    rcases le_or_gt (min P.maxConsumption (P.consumption s a)) 0 with h | h
    · simp only [ContinuousMap.coe_mk, rewardFn]
      rw [extendBot_of_nonpos h]
      exact bot_le
    · simp only [ContinuousMap.coe_mk, rewardFn]
      rw [extendBot_of_pos h, EReal.coe_le_coe_iff]
      exact P.monotoneOn_u h P.maxConsumption_pos (min_le_left _ _)
  select := ⟨fun _ => 0, continuous_const⟩
  select_mem := fun _ => ⟨le_rfl, le_max_left _ _⟩
  rewardMin := P.u P.income
  le_reward_select := by
    intro s
    have h : P.income ≤ min P.maxConsumption (P.consumption s 0) := by
      refine le_min P.income_le_maxConsumption ?_
      simp only [consumption, sub_zero]
      exact P.income_le_resources s
    simp only [ContinuousMap.coe_mk, rewardFn]
    rw [extendBot_of_pos (lt_of_lt_of_le P.income_pos h), EReal.coe_le_coe_iff]
    exact P.monotoneOn_u P.income_pos (lt_of_lt_of_le P.income_pos h) h
  transition := ⟨fun p => p.2, continuous_snd⟩
  discount := P.discount
  discount_lt_one := P.discount_lt_one

@[simp]
theorem feasible_eq (a : ℝ) : P.toExtended.feasible a = Icc 0 (P.maxSaving a) := rfl

theorem consumption_le_maxConsumption {a a' : ℝ} (ha : a ∈ Icc 0 P.assetCap) (ha' : 0 ≤ a') :
    P.consumption a a' ≤ P.maxConsumption := by
  have hmax : max 0 a = a := max_eq_right ha.1
  have : (1 + P.interest) * a ≤ (1 + P.interest) * P.assetCap :=
    mul_le_mul_of_nonneg_left ha.2 P.interest_gt_neg_one.le
  simp only [consumption, resources, maxConsumption, hmax]
  linarith

/-- **The Bellman equation, with honest utility and positive consumption.** That
consumption is positive at the optimum is not assumed and not separately proved: a zero
would make the reward `-∞` and hence the value `-∞`, and the value is real. -/
theorem exists_optimal_saving {a : ℝ} (ha : a ∈ Icc 0 P.assetCap) :
    ∃ a' ∈ Icc 0 (P.maxSaving a), 0 < P.consumption a a' ∧
      P.toExtended.valueFunction a
        = P.u (P.consumption a a') + P.discount * P.toExtended.valueFunction a' := by
  obtain ⟨a', ha', heq⟩ := P.toExtended.exists_optimal_policy a
  -- the reward at the optimum cannot be `⊥`, or the value would not be real
  have hne : P.rewardFn (a, a') ≠ ⊥ := by
    intro hb
    rw [show P.toExtended.reward (a, a') = P.rewardFn (a, a') from rfl, hb,
      EReal.bot_add _] at heq
    exact EReal.coe_ne_bot _ heq
  have hpos : 0 < min P.maxConsumption (P.consumption a a') := by
    by_contra hle
    push Not at hle
    exact hne (extendBot_of_nonpos hle)
  have hc : 0 < P.consumption a a' := lt_of_lt_of_le hpos (min_le_right _ _)
  have hclamp : min P.maxConsumption (P.consumption a a') = P.consumption a a' :=
    min_eq_right (P.consumption_le_maxConsumption ha ha'.1)
  refine ⟨a', ha', hc, ?_⟩
  have hrw : P.toExtended.reward (a, a') = ((P.u (P.consumption a a') : ℝ) : EReal) :=
    calc P.toExtended.reward (a, a')
        = extendBot P.u (min P.maxConsumption (P.consumption a a')) := rfl
      _ = extendBot P.u (P.consumption a a') := by rw [hclamp]
      _ = _ := extendBot_of_pos hc
  rw [hrw, ← EReal.coe_add, EReal.coe_eq_coe_iff] at heq
  exact heq

/-! ### Concavity and the optimal policy

The `σ < 1` model gets concavity from the general criterion in
`LeanEconomics.DynamicProgramming.Bellman`. That criterion is stated for a real-valued
reward and does not apply here, because `ConcaveOn` over `EReal` would need an ordered
module structure that does not sit well. The way round is that the `-∞` never appears where
it matters: at an optimum consumption is strictly positive, so every value the argument
touches is finite, and the reasoning can be carried out in the reals. -/

theorem resources_eq_affine {x : ℝ} (hx : 0 ≤ x) :
    P.resources x = P.income + (1 + P.interest) * x := by
  simp only [resources, max_eq_right hx]

theorem resources_affine_comb {x y θ φ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hθ : 0 ≤ θ)
    (hφ : 0 ≤ φ) (hθφ : θ + φ = 1) :
    P.resources (θ * x + φ * y) = θ * P.resources x + φ * P.resources y := by
  have hmix : 0 ≤ θ * x + φ * y := by positivity
  rw [P.resources_eq_affine hmix, P.resources_eq_affine hx, P.resources_eq_affine hy]
  linear_combination (-P.income) * hθφ

theorem maxSaving_le_assetCap (a : ℝ) : P.maxSaving a ≤ P.assetCap :=
  max_le P.assetCap_nonneg (min_le_left _ _)

theorem feasible_subset_region {x a : ℝ} (ha : a ∈ P.toExtended.feasible x) :
    a ∈ Icc 0 P.assetCap :=
  ⟨ha.1, ha.2.trans (P.maxSaving_le_assetCap x)⟩

theorem maxSaving_eq (x : ℝ) : P.maxSaving x = min P.assetCap (P.resources x) :=
  max_eq_right (le_min P.assetCap_nonneg (P.resources_pos x).le)

theorem feasible_convex {x y : ℝ} (hx : x ∈ Icc 0 P.assetCap) (hy : y ∈ Icc 0 P.assetCap)
    {ax ay θ φ : ℝ} (hax : ax ∈ P.toExtended.feasible x) (hay : ay ∈ P.toExtended.feasible y)
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hθφ : θ + φ = 1) :
    θ * ax + φ * ay ∈ P.toExtended.feasible (θ * x + φ * y) := by
  obtain ⟨hax0, haxm⟩ := hax
  obtain ⟨hay0, haym⟩ := hay
  rw [P.maxSaving_eq x] at haxm
  rw [P.maxSaving_eq y] at haym
  have hmix : (0 : ℝ) ≤ θ * x + φ * y :=
    add_nonneg (mul_nonneg hθ hx.1) (mul_nonneg hφ hy.1)
  refine ⟨add_nonneg (mul_nonneg hθ hax0) (mul_nonneg hφ hay0), ?_⟩
  rw [P.maxSaving_eq (θ * x + φ * y)]
  refine le_min ?_ ?_
  · have h1 : ax ≤ P.assetCap := haxm.trans (min_le_left _ _)
    have h2 : ay ≤ P.assetCap := haym.trans (min_le_left _ _)
    nlinarith
  · have h1 : ax ≤ P.resources x := haxm.trans (min_le_right _ _)
    have h2 : ay ≤ P.resources y := haym.trans (min_le_right _ _)
    rw [P.resources_affine_comb hx.1 hy.1 hθ hφ hθφ]
    nlinarith

/-- A finite reward means strictly positive consumption. -/
theorem consumption_pos_of_ne_bot {x a : ℝ} (h : P.toExtended.reward (x, a) ≠ ⊥) :
    0 < P.consumption x a := by
  by_contra hle
  push Not at hle
  refine h ?_
  calc P.toExtended.reward (x, a)
      = extendBot P.u (min P.maxConsumption (P.consumption x a)) := rfl
    _ = ⊥ := extendBot_of_nonpos ((min_le_right _ _).trans hle)

/-- Where consumption is positive the reward is an ordinary real utility. -/
theorem reward_eq_coe {x a : ℝ} (hx : x ∈ Icc 0 P.assetCap) (ha : a ∈ P.toExtended.feasible x)
    (hc : 0 < P.consumption x a) :
    P.toExtended.reward (x, a) = ((P.u (P.consumption x a) : ℝ) : EReal) :=
  calc P.toExtended.reward (x, a)
      = extendBot P.u (min P.maxConsumption (P.consumption x a)) := rfl
    _ = extendBot P.u (P.consumption x a) := by
        rw [min_eq_right (P.consumption_le_maxConsumption hx ha.1)]
    _ = _ := extendBot_of_pos hc

/-- At an optimum consumption is positive and the value is an ordinary real expression. -/
theorem bellmanFn_eq_of_optimal {v : ℝ →ᵇ ℝ} {x a : ℝ} (hx : x ∈ Icc 0 P.assetCap)
    (ha : a ∈ P.toExtended.feasible x)
    (heq : P.toExtended.objectiveE v x a = ((P.toExtended.bellmanFn v x : ℝ) : EReal)) :
    0 < P.consumption x a ∧
      P.toExtended.bellmanFn v x = P.u (P.consumption x a) + P.discount * v a := by
  have hne : P.toExtended.reward (x, a) ≠ ⊥ := by
    intro hb
    rw [ExtendedProgram.objectiveE, hb, EReal.bot_add _] at heq
    exact EReal.coe_ne_bot _ heq.symm
  have hc := P.consumption_pos_of_ne_bot hne
  refine ⟨hc, ?_⟩
  rw [ExtendedProgram.objectiveE, P.reward_eq_coe hx ha hc, ← EReal.coe_add,
    EReal.coe_eq_coe_iff] at heq
  exact heq.symm

/-- **The Bellman operator preserves concavity on the region.** -/
theorem concaveOn_bellman (v : ℝ →ᵇ ℝ) (hv : ConcaveOn ℝ (Icc 0 P.assetCap) ⇑v) :
    ConcaveOn ℝ (Icc 0 P.assetCap) ⇑(P.toExtended.bellman v) := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  obtain ⟨ax, hax, heqx⟩ := P.toExtended.exists_optimal_action v x
  obtain ⟨ay, hay, heqy⟩ := P.toExtended.exists_optimal_action v y
  obtain ⟨hcx, hbx⟩ := P.bellmanFn_eq_of_optimal hx hax heqx
  obtain ⟨hcy, hby⟩ := P.bellmanFn_eq_of_optimal hy hay heqy
  have hxy : θ * x + φ * y ∈ Icc 0 P.assetCap := by
    simpa using convex_Icc (0 : ℝ) P.assetCap hx hy hθ hφ hθφ
  have hmix := P.feasible_convex hx hy hax hay hθ hφ hθφ
  have hcmix : P.consumption (θ * x + φ * y) (θ * ax + φ * ay)
      = θ * P.consumption x ax + φ * P.consumption y ay := by
    simp only [consumption]
    rw [P.resources_affine_comb hx.1 hy.1 hθ hφ hθφ]
    ring
  have hcm : 0 < P.consumption (θ * x + φ * y) (θ * ax + φ * ay) := by
    rw [hcmix]
    rcases lt_or_eq_of_le hθ with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos h hcx) (mul_nonneg hφ hcy.le)
    · have hφ1 : φ = 1 := by linarith
      rw [← h, hφ1]
      simpa using hcy
  -- the mixed action is available, so it bounds the mixed value from below
  have hle := P.toExtended.le_bellmanFn v hmix
  have hobj : P.toExtended.objectiveE v (θ * x + φ * y) (θ * ax + φ * ay)
      = ((P.u (P.consumption (θ * x + φ * y) (θ * ax + φ * ay))
          + P.discount * v (θ * ax + φ * ay) : ℝ) : EReal) := by
    rw [ExtendedProgram.objectiveE, P.reward_eq_coe hxy hmix hcm, ← EReal.coe_add]
    rfl
  rw [hobj] at hle
  have hle' : P.u (P.consumption (θ * x + φ * y) (θ * ax + φ * ay))
      + P.discount * v (θ * ax + φ * ay) ≤ P.toExtended.bellmanFn v (θ * x + φ * y) := by
    exact_mod_cast hle
  -- concavity of utility and of the continuation value
  have hu := P.strictConcaveOn_u.concaveOn.2 hcx hcy hθ hφ hθφ
  have hvv := hv.2 (P.feasible_subset_region hax) (P.feasible_subset_region hay) hθ hφ hθφ
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hvv hβ
  simp only [smul_eq_mul] at hu hvv hscaled
  rw [hcmix] at hle'
  simp only [smul_eq_mul, ExtendedProgram.bellman_apply]
  rw [hbx, hby]
  linarith

/-- **The value function is concave on `[0, assetCap]`**, for utility unbounded below. -/
theorem concaveOn_valueFunction :
    ConcaveOn ℝ (Icc 0 P.assetCap) ⇑P.toExtended.valueFunction :=
  Blackwell.concaveOn_valueFunction (convex_Icc _ _) P.toExtended.blackwell
    P.toExtended.discount_lt_one fun v hv => P.concaveOn_bellman v hv

/-- **The optimal action is unique.** Two distinct optimal actions would be beaten by their
midpoint, since utility is strictly concave and the continuation value concave. -/
theorem optimal_action_unique {x : ℝ} (hx : x ∈ Icc 0 P.assetCap) {a₀ a₁ : ℝ}
    (h₀ : a₀ ∈ P.toExtended.feasible x) (h₁ : a₁ ∈ P.toExtended.feasible x)
    (hm₀ : P.toExtended.objectiveE P.toExtended.valueFunction x a₀
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction x : ℝ) : EReal))
    (hm₁ : P.toExtended.objectiveE P.toExtended.valueFunction x a₁
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction x : ℝ) : EReal)) :
    a₀ = a₁ := by
  by_contra hne
  obtain ⟨hc₀, hb₀⟩ := P.bellmanFn_eq_of_optimal hx h₀ hm₀
  obtain ⟨hc₁, hb₁⟩ := P.bellmanFn_eq_of_optimal hx h₁ hm₁
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hsum : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
  have hmem : (1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁ ∈ P.toExtended.feasible x := by
    simpa using convex_Icc (0 : ℝ) (P.maxSaving x) h₀ h₁ hhalf.le hhalf.le hsum
  have hcmid : P.consumption x ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁)
      = (1 / 2 : ℝ) * P.consumption x a₀ + (1 / 2 : ℝ) * P.consumption x a₁ := by
    simp only [consumption]; ring
  have hcm : 0 < P.consumption x ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁) := by
    rw [hcmid]; linarith
  have hcne : P.consumption x a₀ ≠ P.consumption x a₁ := by
    simp only [consumption]
    intro h
    exact hne (by linarith)
  -- strict gain at the midpoint
  have hu := P.strictConcaveOn_u.2 hc₀ hc₁ hcne hhalf hhalf hsum
  have hvv := P.concaveOn_valueFunction.2 (P.feasible_subset_region h₀)
    (P.feasible_subset_region h₁) hhalf.le hhalf.le hsum
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hvv hβ
  simp only [smul_eq_mul] at hu hvv hscaled
  have hle := P.toExtended.le_bellmanFn P.toExtended.valueFunction hmem
  have hobj : P.toExtended.objectiveE P.toExtended.valueFunction x
        ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁)
      = ((P.u (P.consumption x ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁))
          + P.discount * P.toExtended.valueFunction ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁)
            : ℝ) : EReal) := by
    rw [ExtendedProgram.objectiveE, P.reward_eq_coe hx hmem hcm, ← EReal.coe_add]
    rfl
  rw [hobj] at hle
  have hle' : P.u (P.consumption x ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁))
      + P.discount * P.toExtended.valueFunction ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁)
      ≤ P.toExtended.bellmanFn P.toExtended.valueFunction x := by exact_mod_cast hle
  rw [hcmid] at hle'
  linarith

/-- The optimal saving choice. By `optimal_action_unique` this is *the* optimal choice on
the region, not merely *an* optimal choice. -/
noncomputable def policy (x : ℝ) : ℝ :=
  Classical.choose (P.toExtended.exists_optimal_action P.toExtended.valueFunction x)

theorem policy_mem (x : ℝ) : P.policy x ∈ P.toExtended.feasible x :=
  (Classical.choose_spec
    (P.toExtended.exists_optimal_action P.toExtended.valueFunction x)).1

theorem policy_optimal (x : ℝ) :
    P.toExtended.objectiveE P.toExtended.valueFunction x (P.policy x)
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction x : ℝ) : EReal) :=
  (Classical.choose_spec
    (P.toExtended.exists_optimal_action P.toExtended.valueFunction x)).2

theorem policy_mem_region (x : ℝ) : P.policy x ∈ Icc 0 P.assetCap :=
  P.feasible_subset_region (P.policy_mem x)

/-- Consumption under the optimal policy is strictly positive: the household never starves
itself. With a floor this had to be proved; here it follows from the value being real. -/
theorem consumption_policy_pos {x : ℝ} (hx : x ∈ Icc 0 P.assetCap) :
    0 < P.consumption x (P.policy x) :=
  (P.bellmanFn_eq_of_optimal hx (P.policy_mem x) (P.policy_optimal x)).1

/-- **Any optimal action is the policy.** -/
theorem eq_policy_of_optimal {x : ℝ} (hx : x ∈ Icc 0 P.assetCap) {a : ℝ}
    (ha : a ∈ P.toExtended.feasible x)
    (hopt : P.toExtended.objectiveE P.toExtended.valueFunction x a
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction x : ℝ) : EReal)) :
    a = P.policy x :=
  P.optimal_action_unique hx ha (P.policy_mem x) hopt (P.policy_optimal x)

/-- **The Bellman equation at the policy**, with honest utility and positive consumption. -/
theorem valueFunction_eq_policy {x : ℝ} (hx : x ∈ Icc 0 P.assetCap) :
    P.toExtended.valueFunction x
      = P.u (P.consumption x (P.policy x))
        + P.discount * P.toExtended.valueFunction (P.policy x) := by
  have h := (P.bellmanFn_eq_of_optimal hx (P.policy_mem x) (P.policy_optimal x)).2
  have hfix : P.toExtended.bellmanFn P.toExtended.valueFunction x
      = P.toExtended.valueFunction x := by
    conv_rhs => rw [← P.toExtended.bellman_valueFunction]
    rfl
  rw [← hfix, h]

/-- **The maximiser set is exactly the policy.** -/
theorem argmax_eq_singleton {x : ℝ} (hx : x ∈ Icc 0 P.assetCap) :
    argmax (P.toExtended.objectiveE P.toExtended.valueFunction) P.toExtended.feasible x
      = {P.policy x} := by
  ext a
  simp only [argmax, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ha, hmax⟩
    refine P.eq_policy_of_optimal hx ha (le_antisymm (P.toExtended.le_bellmanFn _ ha) ?_)
    rw [← P.policy_optimal x]
    exact isMaxOn_iff.mp hmax _ (P.policy_mem x)
  · rintro rfl
    refine ⟨P.policy_mem x, isMaxOn_iff.mpr fun b hb => ?_⟩
    rw [P.policy_optimal x]
    exact P.toExtended.le_bellmanFn _ hb

/-- **The optimal policy is continuous on the region**, for utility unbounded below. -/
theorem continuousOn_policy : ContinuousOn P.policy (Icc 0 P.assetCap) :=
  continuousOn_of_upperHemicontinuous_singleton
    (P.toExtended.upperHemicontinuous_argmax P.toExtended.valueFunction)
    fun _ hx => P.argmax_eq_singleton hx

/-! ### Utilities that qualify -/

/-- CES period utility. -/
noncomputable def crra (σ c : ℝ) : ℝ := c ^ (1 - σ) / (1 - σ)

theorem continuousOn_crra {σ : ℝ} : ContinuousOn (crra σ) (Ioi 0) := fun c hc =>
  (((Real.continuousAt_rpow_const c (1 - σ) (Or.inl (ne_of_gt hc))).div_const _)).continuousWithinAt

theorem monotoneOn_crra {σ : ℝ} (hσ : 1 < σ) : MonotoneOn (crra σ) (Ioi 0) := by
  intro x hx y _ hxy
  have hneg : (1 : ℝ) - σ < 0 := by linarith
  simp only [crra]
  rw [div_le_div_right_of_neg hneg]
  exact Real.rpow_le_rpow_of_nonpos hx hxy hneg.le

theorem continuousOn_log : ContinuousOn Real.log (Ioi 0) :=
  Real.continuousOn_log.mono fun _ hx => ne_of_gt hx

theorem monotoneOn_log : MonotoneOn Real.log (Ioi 0) := Real.strictMonoOn_log.monotoneOn

/-- A calibration with `σ = 2`, where CES utility is `-1 / c`. -/
noncomputable def calibrated : ConsumptionSavingsUnbounded where
  income := 1
  interest := 1 / 20
  assetCap := 10
  discount := 24 / 25
  u := fun c => -c⁻¹
  income_pos := by norm_num
  interest_gt_neg_one := by norm_num
  assetCap_nonneg := by norm_num
  discount_lt_one := by norm_num
  continuousOn_u := (continuousOn_id.inv₀ fun x hx => ne_of_gt hx).neg
  monotoneOn_u := by
    intro x hx y _ hxy
    have : (0 : ℝ) < x := hx
    simp only [neg_le_neg_iff]
    gcongr
  tendsto_atBot_u := tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero
  strictConcaveOn_u := strictConcaveOn_neg_inv

/-- A log calibration (`σ = 1`). -/
noncomputable def calibratedLog : ConsumptionSavingsUnbounded where
  income := 1
  interest := 1 / 20
  assetCap := 10
  discount := 24 / 25
  u := Real.log
  income_pos := by norm_num
  interest_gt_neg_one := by norm_num
  assetCap_nonneg := by norm_num
  discount_lt_one := by norm_num
  continuousOn_u := continuousOn_log
  monotoneOn_u := monotoneOn_log
  tendsto_atBot_u := Real.tendsto_log_nhdsGT_zero
  strictConcaveOn_u := strictConcaveOn_log_Ioi

end ConsumptionSavingsUnbounded

end LeanEconomics
