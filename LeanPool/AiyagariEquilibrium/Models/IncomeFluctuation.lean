/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.DynamicProgramming.ExtendedStochastic
public import LeanPool.AiyagariEquilibrium.Topology.IccCorrespondence
public import LeanPool.AiyagariEquilibrium.Models.ConsumptionSavingsUnbounded

/-!
# The income fluctuation problem

The canonical incomplete-markets household: income follows a finite Markov chain, assets
earn interest, borrowing is ruled out, and the household chooses savings. The state is the
pair `(a, z)` of assets and income state, and

  `V (a, z) = max { u c + β * ∑ z', P z z' * V (a', z') }`.

Period utility may fall to `-∞` at zero consumption, so this covers log and CRRA with
`σ ≥ 1` -- and, since the utility DOMAIN is a field, CES with `γ < 1` as well.

## The domain field

`u` is required to behave on a set `dom` with `Ioi 0 ⊆ dom ⊆ Ici 0`, so there are exactly two
choices: `Ioi 0`, where utility is unbounded below, and `Ici 0`, where it is bounded there. The
old `tendsto_atBot_u` is replaced by `continuousOn_extendDom`, which says that `u` extended by
`⊥` off `dom` is continuous where consumption lives. That is what Berge actually consumes, and
it is exactly `tendsto_atBot_u` when `dom = Ioi 0` (see `continuousOn_extendDom_Ioi`) and merely
continuity of `u` on `Ici 0` in the other case, where the `⊥` branch is unreachable.

Nothing is lost by the swap: `tendsto_atBot_u` comes BACK as a theorem from `Unbounded`.

The one real consequence is that positive consumption at the optimum is no longer free. With
`dom = Ioi 0` the reward is `⊥` there and the value being real settles it; with `dom = Ici 0`
it has to be earned from a MARGINAL Inada condition instead — see `ConsumptionFloor`. Results
that need it take `PositiveConsumption` as a hypothesis, which both routes supply. Results that
only need `u` to behave take membership in `dom`, and carry over untouched.

## Retrofitted onto extended-real rewards

This file used a floor, with the same apparatus as the deterministic models: `floor`,
`cFloor`, and a chain of results establishing that the floor never binds. All of it is
gone. The reward is `-∞` where consumption vanishes, and positive consumption at the
optimum follows from the value function being real rather than from an argument.

The stochastic case needed `LeanEconomics.DynamicProgramming.ExtendedStochastic`, since the
continuation here is an expectation over shocks rather than `v` at a single point. That
turned out to be routine: the expectation is a sum of reals, so the objective is again an
extended real plus a finite coercion, and the reward's `-∞` never meets the expectation's
arithmetic.

## Unchanged

Discreteness of the income state is still what makes every function of `z` continuous, so
the budget correspondence is continuous in the pair. Consumption is still clamped above and
assets still capped -- the ordinary boundedness requirement, unrelated to the floor. Cash on
hand is computed from `max 0 a`, as in the deterministic retrofits, so that the value stays
finite at every state.
-/

@[expose] public section

open scoped NNReal
open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

/-- Utility extended by `⊥` outside the domain on which it is required to behave. With
`D = Ioi 0` this is `extendBot`; with `D = Ici 0` the `⊥` branch is unreachable on `Ici 0`. -/
noncomputable def extendDom (D : Set ℝ) (u : ℝ → ℝ) (c : ℝ) : EReal :=
  open Classical in if c ∈ D then ((u c : ℝ) : EReal) else ⊥

theorem extendDom_of_mem {D : Set ℝ} {u : ℝ → ℝ} {c : ℝ} (h : c ∈ D) :
    extendDom D u c = ((u c : ℝ) : EReal) := by
  simp only [extendDom, h, reduceIte]

theorem extendDom_of_not_mem {D : Set ℝ} {u : ℝ → ℝ} {c : ℝ} (h : c ∉ D) :
    extendDom D u c = ⊥ := by
  simp only [extendDom, h, reduceIte]

theorem extendDom_ne_bot_iff {D : Set ℝ} {u : ℝ → ℝ} {c : ℝ} :
    extendDom D u c ≠ ⊥ ↔ c ∈ D := by
  by_cases h : c ∈ D
  · simp [extendDom_of_mem h, h]
  · simp [extendDom_of_not_mem h, h]

/-- With `D = Ioi 0` the extension is `extendBot`, so the divergence condition supplies the
continuity requirement. -/
theorem extendDom_Ioi (u : ℝ → ℝ) : extendDom (Ioi 0) u = extendBot u := by
  funext c
  rcases le_or_gt c 0 with h | h
  · rw [extendDom_of_not_mem (by simpa using h), extendBot_of_nonpos h]
  · rw [extendDom_of_mem (mem_Ioi.mpr h), extendBot_of_pos h]

/-- The unbounded case: divergence at zero supplies the continuity requirement. -/
theorem continuousOn_extendDom_Ioi {u : ℝ → ℝ} (hc : ContinuousOn u (Ioi 0))
    (ht : Tendsto u (𝓝[>] 0) atBot) : ContinuousOn (extendDom (Ioi 0) u) (Ici 0) := by
  rw [extendDom_Ioi]
  exact (continuous_extendBot hc ht).continuousOn

/-- The income fluctuation problem, with period utility unbounded below. -/
structure IncomeFluctuation (Z : Type*) [Fintype Z] [Nonempty Z] [TopologicalSpace Z]
    [DiscreteTopology Z] (assetFloor assetCap : ℝ) where
  /-- Income in each state. -/
  income : Z → ℝ
  /-- The Markov transition matrix on income states. -/
  transitionMatrix : Z → Z → ℝ
  /-- The interest rate on assets. -/
  interest : ℝ
  /-- The discount factor. -/
  discount : ℝ≥0
  /-- Period utility, required to behave only on positive consumption. -/
  u : ℝ → ℝ
  /-- A lower bound on income. -/
  minIncome : ℝ
  /-- An upper bound on income. -/
  maxIncome : ℝ
  minIncome_pos : 0 < minIncome
  minIncome_le : ∀ z, minIncome ≤ income z
  le_maxIncome : ∀ z, income z ≤ maxIncome
  transitionMatrix_nonneg : ∀ z z', 0 ≤ transitionMatrix z z'
  transitionMatrix_sum : ∀ z, ∑ z', transitionMatrix z z' = 1
  interest_gt_neg_one : 0 < 1 + interest
  /-- The borrowing limit is below the asset cap, so the household always has somewhere to be. -/
  assetFloor_le_assetCap : assetFloor ≤ assetCap
  /-- The asset cap is a large positive number; nothing in the development needs it to be small,
  but several bounds need it to have a sign. -/
  assetCap_nonneg : 0 ≤ assetCap
  /-- **A declared floor on consumption**, at most what a household pinned at the borrowing limit
  can afford. Carrying it as data rather than computing it from the rate is what lets the same
  household problem be re-run at a different interest rate without moving the reward's lower
  bound: `minConsumption` is the rate-free part of the natural-borrowing-limit condition. -/
  minConsumption : ℝ := minIncome + interest * assetFloor
  /-- **The borrowing limit is sustainable**: at the limit, income covers the interest on the debt
  with something left to eat. With `assetFloor = 0` this is `0 < minIncome`; with a negative limit
  it is Aiyagari's natural-borrowing-limit condition, and it is what replaces positivity of cash
  on hand -- resources can be negative when the household is in debt, while consumption cannot. -/
  minConsumption_pos : 0 < minConsumption
  minConsumption_le_floor : minConsumption ≤ minIncome + interest * assetFloor
  discount_lt_one : discount < 1
  /-- The consumption levels at which utility is required to behave. `Ioi 0` when utility is
  unbounded below, `Ici 0` when it is bounded there. -/
  dom : Set ℝ
  Ioi_subset_dom : Ioi 0 ⊆ dom
  dom_subset_Ici : dom ⊆ Ici 0
  continuousOn_u_dom : ContinuousOn u dom
  monotoneOn_u_dom : MonotoneOn u dom
  /-- Diminishing marginal utility, which makes the optimal policy unique. -/
  strictConcaveOn_u_dom : StrictConcaveOn ℝ dom u
  /-- **What replaces the Inada condition.** Utility, extended by `⊥` off its domain, must be
  continuous where consumption lives. For `dom = Ioi 0` this is exactly `Tendsto u (𝓝[>] 0) atBot`
  via `continuous_extendBot`; for `dom = Ici 0` the `⊥` branch is never taken and it is just
  continuity of `u` on `Ici 0`. -/
  continuousOn_extendDom : ContinuousOn (extendDom dom u) (Ici 0)

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-- Cash on hand, with assets read as nonnegative. -/
noncomputable def resources (s : ℝ × Z) : ℝ :=
  P.income s.2 + (1 + P.interest) * max assetFloor s.1

/-- The largest consumption the capped problem allows. -/
noncomputable def maxConsumption : ℝ :=
  P.maxIncome + (1 + P.interest) * assetCap - assetFloor

/-- The largest asset holding that can be carried forward. -/
noncomputable def maxSaving (s : ℝ × Z) : ℝ := max assetFloor (min assetCap (P.resources s))

/-- Consumption on the budget line. -/
noncomputable def consumption (s : ℝ × Z) (a' : ℝ) : ℝ := P.resources s - a'

/-- Consumption clamped into `[0, maxConsumption]`. On the feasible set the lower clamp is
inactive, so this is consumption itself; off it, it keeps the reward's argument in `Ici 0`, which
is where `continuousOn_extendDom` applies. -/
noncomputable def clampedConsumption (p : (ℝ × Z) × ℝ) : ℝ :=
  min P.maxConsumption (max 0 (P.consumption p.1 p.2))

/-- The reward: utility of consumption clamped above, and `⊥` where consumption falls outside
the domain on which utility behaves. No floor. -/
noncomputable def rewardFn (p : (ℝ × Z) × ℝ) : EReal :=
  extendDom P.dom P.u (P.clampedConsumption p)

/-- **The rates at which the borrowing limit is sustainable.** Raising the interest rate raises
the debt service on a negative floor, so a floor that supports positive consumption at one rate
need not support it at another: sustainability is part of what it means for a rate to be
admissible, not a consequence of `-1 < r`. With `assetFloor = 0` the second conjunct is free. -/
def RateOK (P : IncomeFluctuation Z assetFloor assetCap) (r : ℝ) : Prop :=
  0 < 1 + r ∧ P.minConsumption ≤ P.minIncome + r * assetFloor

theorem RateOK.one_add_pos {P : IncomeFluctuation Z assetFloor assetCap} {r : ℝ}
    (h : P.RateOK r) : 0 < 1 + r := h.1

theorem RateOK.sustainable {P : IncomeFluctuation Z assetFloor assetCap} {r : ℝ}
    (h : P.RateOK r) : P.minConsumption ≤ P.minIncome + r * assetFloor := h.2

/-- At a zero borrowing limit every admissible rate is sustainable. -/
theorem rateOK_of_floor_zero {P : IncomeFluctuation Z 0 assetCap} {r : ℝ} (hr : 0 < 1 + r) :
    P.RateOK r := ⟨hr, by simpa using P.minConsumption_le_floor⟩

/-- Sustainability is linear in the rate, so it is inherited from the endpoints of an interval. -/
theorem rateOK_of_mem_Icc {rlo rhi r : ℝ} (hlo : P.RateOK rlo) (hhi : P.RateOK rhi)
    (hr : r ∈ Set.Icc rlo rhi) : P.RateOK r := by
  refine ⟨by linarith [hr.1, hlo.1], ?_⟩
  rcases le_total (0 : ℝ) assetFloor with hf | hf
  · nlinarith [hlo.2, hr.1, hr.2]
  · nlinarith [hhi.2, hr.1, hr.2]

theorem rateOK_self : P.RateOK P.interest := ⟨P.interest_gt_neg_one, P.minConsumption_le_floor⟩

theorem minConsumption_le_consumption_floor (s : ℝ × Z) :
    P.minConsumption ≤ P.resources s - assetFloor := by
  have h1 : assetFloor ≤ max assetFloor s.1 := le_max_left _ _
  have h2 : (1 + P.interest) * assetFloor ≤ (1 + P.interest) * max assetFloor s.1 :=
    mul_le_mul_of_nonneg_left h1 P.interest_gt_neg_one.le
  have := P.minIncome_le s.2
  have := P.minConsumption_le_floor
  simp only [resources]; linarith

/-- **Cash on hand always exceeds the borrowing limit**, so something can always be eaten. This
replaces positivity of cash on hand: in debt, resources can be negative while consumption cannot.
-/
theorem assetFloor_lt_resources (s : ℝ × Z) : assetFloor < P.resources s := by
  have h1 := P.minConsumption_le_consumption_floor s
  have h2 := P.minConsumption_pos
  linarith

theorem minIncome_le_maxIncome : P.minIncome ≤ P.maxIncome :=
  (P.minIncome_le Classical.ofNonempty).trans (P.le_maxIncome _)

theorem minConsumption_le_maxConsumption : P.minConsumption ≤ P.maxConsumption := by
  have h : (1 + P.interest) * assetFloor ≤ (1 + P.interest) * assetCap :=
    mul_le_mul_of_nonneg_left P.assetFloor_le_assetCap P.interest_gt_neg_one.le
  simp only [maxConsumption]
  linarith [P.minIncome_le_maxIncome, P.minConsumption_le_floor]

theorem maxConsumption_pos : 0 < P.maxConsumption :=
  lt_of_lt_of_le P.minConsumption_pos P.minConsumption_le_maxConsumption

theorem mem_dom_of_pos {c : ℝ} (hc : 0 < c) : c ∈ P.dom := P.Ioi_subset_dom hc

theorem nonneg_of_mem_dom {c : ℝ} (hc : c ∈ P.dom) : 0 ≤ c := P.dom_subset_Ici hc

theorem maxConsumption_mem_dom : P.maxConsumption ∈ P.dom := P.mem_dom_of_pos P.maxConsumption_pos

theorem convex_dom : Convex ℝ P.dom := P.strictConcaveOn_u_dom.1

/-- The domain is an up-set: if utility behaves at `c` it behaves at anything larger. Both
`Ioi 0` and `Ici 0` are, and it follows from the two bracketing inclusions alone. -/
theorem dom_upward {c c' : ℝ} (hc : c ∈ P.dom) (h : c ≤ c') : c' ∈ P.dom := by
  rcases lt_or_ge 0 c' with h' | h'
  · exact P.mem_dom_of_pos h'
  · rwa [le_antisymm h (h'.trans (P.nonneg_of_mem_dom hc))] at hc

/-- Utility behaves on the positives whatever the domain is, so every existing argument that
supplies `0 < c` keeps working. -/
theorem continuousOn_u : ContinuousOn P.u (Ioi 0) := P.continuousOn_u_dom.mono P.Ioi_subset_dom

theorem monotoneOn_u : MonotoneOn P.u (Ioi 0) := P.monotoneOn_u_dom.mono P.Ioi_subset_dom

theorem strictConcaveOn_u : StrictConcaveOn ℝ (Ioi 0) P.u :=
  P.strictConcaveOn_u_dom.subset P.Ioi_subset_dom (convex_Ioi 0)

theorem clampedConsumption_nonneg (p : (ℝ × Z) × ℝ) : 0 ≤ P.clampedConsumption p :=
  le_min P.maxConsumption_pos.le (le_max_left _ _)

theorem clampedConsumption_le (p : (ℝ × Z) × ℝ) :
    P.clampedConsumption p ≤ P.maxConsumption := min_le_left _ _

/-- Discreteness of `Z` is what makes this continuous. -/
theorem continuous_resources : Continuous P.resources :=
  (continuous_of_discreteTopology.comp continuous_snd).add
    (continuous_const.mul (continuous_const.max continuous_fst))

theorem continuous_maxSaving : Continuous P.maxSaving :=
  continuous_const.max (continuous_const.min P.continuous_resources)

theorem continuous_clampedConsumption : Continuous P.clampedConsumption := by
  refine continuous_const.min (continuous_const.max ?_)
  exact (P.continuous_resources.comp continuous_fst).sub continuous_snd

theorem continuous_rewardFn : Continuous P.rewardFn :=
  P.continuousOn_extendDom.comp_continuous P.continuous_clampedConsumption
    fun p => mem_Ici.mpr (P.clampedConsumption_nonneg p)

/-- The problem as a stochastic dynamic program with an extended-real reward. -/
noncomputable def toExtended : ExtendedStochasticProgram (ℝ × Z) ℝ Z where
  feasible s := Icc assetFloor (P.maxSaving s)
  isCompact_feasible _ := isCompact_Icc
  feasible_nonempty _ := nonempty_Icc.mpr (le_max_left _ _)
  upperHemicontinuous_feasible := upperHemicontinuous_Icc continuous_const P.continuous_maxSaving
  lowerHemicontinuous_feasible :=
    lowerHemicontinuous_Icc continuous_const P.continuous_maxSaving fun _ => le_max_left _ _
  reward := ⟨P.rewardFn, P.continuous_rewardFn⟩
  rewardMax := P.u P.maxConsumption
  reward_le := by
    intro s a _
    simp only [ContinuousMap.coe_mk, rewardFn]
    by_cases h : P.clampedConsumption (s, a) ∈ P.dom
    · rw [extendDom_of_mem h, EReal.coe_le_coe_iff]
      exact P.monotoneOn_u_dom h P.maxConsumption_mem_dom (P.clampedConsumption_le _)
    · rw [extendDom_of_not_mem h]
      exact bot_le
  select := ⟨fun _ => assetFloor, continuous_const⟩
  select_mem := fun _ => ⟨le_rfl, le_max_left _ _⟩
  rewardMin := P.u P.minConsumption
  le_reward_select := by
    intro s
    simp only [ContinuousMap.coe_mk, rewardFn]
    have h : P.minConsumption ≤ P.clampedConsumption (s, assetFloor) := by
      refine le_min P.minConsumption_le_maxConsumption (le_max_of_le_right ?_)
      simp only [consumption]
      exact P.minConsumption_le_consumption_floor s
    have hpos : 0 < P.clampedConsumption (s, assetFloor) :=
      lt_of_lt_of_le P.minConsumption_pos h
    rw [extendDom_of_mem (P.mem_dom_of_pos hpos), EReal.coe_le_coe_iff]
    exact P.monotoneOn_u_dom (P.mem_dom_of_pos P.minConsumption_pos)
      (P.mem_dom_of_pos hpos) h
  transition z' := ⟨fun p => (p.2, z'), continuous_snd.prodMk continuous_const⟩
  prob z' := ⟨fun p => P.transitionMatrix p.1.2 z',
    (continuous_of_discreteTopology (f := fun z => P.transitionMatrix z z')).comp
      (continuous_snd.comp continuous_fst)⟩
  prob_nonneg _ _ := P.transitionMatrix_nonneg _ _
  prob_sum p := P.transitionMatrix_sum _
  discount := P.discount
  discount_lt_one := P.discount_lt_one

@[simp]
theorem feasible_eq (s : ℝ × Z) : P.toExtended.feasible s = Icc assetFloor (P.maxSaving s) := rfl

theorem maxSaving_le_resources (s : ℝ × Z) : P.maxSaving s ≤ P.resources s :=
  max_le (P.assetFloor_lt_resources s).le (min_le_right _ _)

theorem consumption_nonneg {s : ℝ × Z} {a : ℝ} (ha : a ∈ P.toExtended.feasible s) :
    0 ≤ P.consumption s a := by
  simp only [consumption]
  linarith [le_trans ha.2 (P.maxSaving_le_resources s)]

theorem consumption_le_maxConsumption {s : ℝ × Z} {a' : ℝ} (hs : s.1 ∈ Icc assetFloor assetCap)
    (ha' : assetFloor ≤ a') : P.consumption s a' ≤ P.maxConsumption := by
  have hmax : max assetFloor s.1 = s.1 := max_eq_right hs.1
  have : (1 + P.interest) * s.1 ≤ (1 + P.interest) * assetCap :=
    mul_le_mul_of_nonneg_left hs.2 P.interest_gt_neg_one.le
  simp only [consumption, resources, maxConsumption, hmax]
  linarith [P.le_maxIncome s.2]

/-- **Utility is unbounded below**: the domain is the open half-line, so the reward is `⊥` at
zero consumption. This is the hypothesis under which positive consumption comes free. -/
def Unbounded : Prop := P.dom = Ioi 0

theorem clampedConsumption_mem_dom_of_ne_bot {s : ℝ × Z} {a : ℝ}
    (h : P.toExtended.reward (s, a) ≠ ⊥) : P.clampedConsumption (s, a) ∈ P.dom :=
  extendDom_ne_bot_iff.mp h

theorem consumption_pos_of_ne_bot (hd : P.Unbounded) {s : ℝ × Z} {a : ℝ}
    (h : P.toExtended.reward (s, a) ≠ ⊥) : 0 < P.consumption s a := by
  have hmem := P.clampedConsumption_mem_dom_of_ne_bot h
  rw [hd] at hmem
  have : 0 < max 0 (P.consumption s a) := lt_of_lt_of_le hmem (min_le_right _ _)
  rcases max_cases 0 (P.consumption s a) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at this; exact absurd this (lt_irrefl 0)
  · rwa [he] at this

/-- On the feasible set the clamps are both inactive, so the reward's argument is consumption
itself. -/
theorem clampedConsumption_eq {s : ℝ × Z} {a : ℝ} (hs : s.1 ∈ Icc assetFloor assetCap)
    (ha : a ∈ P.toExtended.feasible s) : P.clampedConsumption (s, a) = P.consumption s a := by
  have h0 : 0 ≤ P.consumption s a := P.consumption_nonneg ha
  simp only [clampedConsumption, max_eq_right h0,
    min_eq_right (P.consumption_le_maxConsumption hs ha.1)]

theorem consumption_mem_dom_of_ne_bot {s : ℝ × Z} {a : ℝ} (hs : s.1 ∈ Icc assetFloor assetCap)
    (ha : a ∈ P.toExtended.feasible s) (h : P.toExtended.reward (s, a) ≠ ⊥) :
    P.consumption s a ∈ P.dom := by
  have := P.clampedConsumption_mem_dom_of_ne_bot h
  rwa [P.clampedConsumption_eq hs ha] at this

/-- **The reward is the utility of consumption**, wherever consumption lies in the domain on
which utility is required to behave. -/
theorem reward_eq_coe_dom {s : ℝ × Z} {a : ℝ} (hs : s.1 ∈ Icc assetFloor assetCap)
    (ha : a ∈ P.toExtended.feasible s) (hc : P.consumption s a ∈ P.dom) :
    P.toExtended.reward (s, a) = ((P.u (P.consumption s a) : ℝ) : EReal) :=
  calc P.toExtended.reward (s, a)
      = extendDom P.dom P.u (P.clampedConsumption (s, a)) := rfl
    _ = extendDom P.dom P.u (P.consumption s a) := by rw [P.clampedConsumption_eq hs ha]
    _ = _ := extendDom_of_mem hc

theorem reward_eq_coe {s : ℝ × Z} {a : ℝ} (hs : s.1 ∈ Icc assetFloor assetCap)
    (ha : a ∈ P.toExtended.feasible s) (hc : 0 < P.consumption s a) :
    P.toExtended.reward (s, a) = ((P.u (P.consumption s a) : ℝ) : EReal) :=
  P.reward_eq_coe_dom hs ha (P.mem_dom_of_pos hc)

/-- **The stochastic Bellman equation, with honest utility and positive consumption.** That
consumption is positive at the optimum is a consequence of the value being real, not a
separate development. -/
theorem exists_optimal_saving {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) :
    ∃ a' ∈ Icc assetFloor (P.maxSaving s), P.consumption s a' ∈ P.dom ∧
      P.toExtended.valueFunction s
        = P.u (P.consumption s a')
          + P.discount * ∑ z', P.transitionMatrix s.2 z'
              * P.toExtended.valueFunction (a', z') := by
  obtain ⟨a', ha', heq⟩ := P.toExtended.exists_optimal_policy s
  have hne : P.rewardFn (s, a') ≠ ⊥ := by
    intro hb
    rw [show P.toExtended.reward (s, a') = P.rewardFn (s, a') from rfl, hb,
      EReal.bot_add _] at heq
    exact EReal.coe_ne_bot _ heq
  have hc : P.consumption s a' ∈ P.dom := P.consumption_mem_dom_of_ne_bot hs ha' hne
  refine ⟨a', ha', hc, ?_⟩
  rw [P.reward_eq_coe_dom hs ha' hc, ← EReal.coe_add, EReal.coe_eq_coe_iff] at heq
  exact heq

/-! ### Concavity and the optimal policy

The state is a pair `(assets, income state)`, which is not a module over `ℝ`, so concavity
is stated along the asset slice for each income state -- see
`LeanEconomics.Blackwell.forall_concaveOn_valueFunction`. Everything else follows the
deterministic argument, with the continuation value now an expectation: it is concave in
next period's assets because each `V (·, z')` is, and the transition probabilities are
nonnegative. -/

/-- A convex combination stays above a common lower bound. Used wherever the borrowing limit
has to survive an averaging argument, which with a floor of zero was `add_nonneg`. -/
theorem le_convex_comb {c x y θ φ : ℝ} (hx : c ≤ x) (hy : c ≤ y) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ)
    (hθφ : θ + φ = 1) : c ≤ θ * x + φ * y := by
  have key : θ * x + φ * y - c = θ * (x - c) + φ * (y - c) := by linear_combination c * hθφ
  linarith [key, mul_nonneg hθ (sub_nonneg.mpr hx), mul_nonneg hφ (sub_nonneg.mpr hy)]

theorem convex_comb_le {c x y θ φ : ℝ} (hx : x ≤ c) (hy : y ≤ c) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ)
    (hθφ : θ + φ = 1) : θ * x + φ * y ≤ c := by
  have key : c - (θ * x + φ * y) = θ * (c - x) + φ * (c - y) := by
    linear_combination (-c) * hθφ
  linarith [key, mul_nonneg hθ (sub_nonneg.mpr hx), mul_nonneg hφ (sub_nonneg.mpr hy)]

theorem resources_eq_affine {s : ℝ × Z} (hs : assetFloor ≤ s.1) :
    P.resources s = P.income s.2 + (1 + P.interest) * s.1 := by
  simp only [resources, max_eq_right hs]

theorem resources_affine_comb {x y θ φ : ℝ} {z : Z} (hx : assetFloor ≤ x)
    (hy : assetFloor ≤ y)
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hθφ : θ + φ = 1) :
    P.resources (θ * x + φ * y, z) = θ * P.resources (x, z) + φ * P.resources (y, z) := by
  have hmix : assetFloor ≤ θ * x + φ * y := le_convex_comb hx hy hθ hφ hθφ
  rw [P.resources_eq_affine hmix, P.resources_eq_affine hx, P.resources_eq_affine hy]
  linear_combination (-(P.income z)) * hθφ

theorem maxSaving_le_assetCap (s : ℝ × Z) : P.maxSaving s ≤ assetCap :=
  max_le P.assetFloor_le_assetCap (min_le_left _ _)

theorem feasible_subset_region {s : ℝ × Z} {a : ℝ} (ha : a ∈ P.toExtended.feasible s) :
    a ∈ Icc assetFloor assetCap :=
  ⟨ha.1, ha.2.trans (P.maxSaving_le_assetCap s)⟩

theorem maxSaving_eq (s : ℝ × Z) : P.maxSaving s = min assetCap (P.resources s) :=
  max_eq_right (le_min P.assetFloor_le_assetCap (P.assetFloor_lt_resources s).le)

theorem feasible_convex {x y : ℝ} {z : Z} (hx : x ∈ Icc assetFloor assetCap)
    (hy : y ∈ Icc assetFloor assetCap) {ax ay θ φ : ℝ}
    (hax : ax ∈ P.toExtended.feasible (x, z)) (hay : ay ∈ P.toExtended.feasible (y, z))
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hθφ : θ + φ = 1) :
    θ * ax + φ * ay ∈ P.toExtended.feasible (θ * x + φ * y, z) := by
  obtain ⟨hax0, haxm⟩ := hax
  obtain ⟨hay0, haym⟩ := hay
  rw [P.maxSaving_eq (x, z)] at haxm
  rw [P.maxSaving_eq (y, z)] at haym
  refine ⟨le_convex_comb hax0 hay0 hθ hφ hθφ, ?_⟩
  rw [P.maxSaving_eq (θ * x + φ * y, z)]
  refine le_min ?_ ?_
  · have h1 : ax ≤ assetCap := haxm.trans (min_le_left _ _)
    have h2 : ay ≤ assetCap := haym.trans (min_le_left _ _)
    exact convex_comb_le h1 h2 hθ hφ hθφ
  · have h1 : ax ≤ P.resources (x, z) := haxm.trans (min_le_right _ _)
    have h2 : ay ≤ P.resources (y, z) := haym.trans (min_le_right _ _)
    rw [P.resources_affine_comb hx.1 hy.1 hθ hφ hθφ]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hθ) (mul_le_mul_of_nonneg_left h2 hφ)

theorem bellmanFn_eq_of_optimal {v : (ℝ × Z) →ᵇ ℝ} {s : ℝ × Z} {a : ℝ}
    (hs : s.1 ∈ Icc assetFloor assetCap) (ha : a ∈ P.toExtended.feasible s)
    (heq : P.toExtended.objectiveE v s a
      = ((P.toExtended.bellmanFn v s : ℝ) : EReal)) :
    P.consumption s a ∈ P.dom ∧
      P.toExtended.bellmanFn v s
        = P.u (P.consumption s a) + P.discount * ∑ z', P.transitionMatrix s.2 z' * v (a, z') := by
  have hne : P.toExtended.reward (s, a) ≠ ⊥ := by
    intro hb
    rw [ExtendedStochasticProgram.objectiveE, hb, EReal.bot_add _] at heq
    exact EReal.coe_ne_bot _ heq.symm
  have hc := P.consumption_mem_dom_of_ne_bot hs ha hne
  refine ⟨hc, ?_⟩
  rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_coe_dom hs ha hc, ← EReal.coe_add,
    EReal.coe_eq_coe_iff] at heq
  exact heq.symm

/-- **The Bellman operator preserves concavity along each asset slice.** -/
theorem concaveOn_bellman (v : (ℝ × Z) →ᵇ ℝ)
    (hv : ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap) fun a => v (a, z)) (z : Z) :
    ConcaveOn ℝ (Icc assetFloor assetCap) fun a => (P.toExtended.bellman v) (a, z) := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  obtain ⟨ax, hax, heqx⟩ := P.toExtended.exists_optimal_action v (x, z)
  obtain ⟨ay, hay, heqy⟩ := P.toExtended.exists_optimal_action v (y, z)
  obtain ⟨hcx, hbx⟩ := P.bellmanFn_eq_of_optimal hx hax heqx
  obtain ⟨hcy, hby⟩ := P.bellmanFn_eq_of_optimal hy hay heqy
  have hxy : θ * x + φ * y ∈ Icc assetFloor assetCap := by
    simpa using convex_Icc assetFloor assetCap hx hy hθ hφ hθφ
  have hmix := P.feasible_convex hx hy hax hay hθ hφ hθφ
  have hcmix : P.consumption (θ * x + φ * y, z) (θ * ax + φ * ay)
      = θ * P.consumption (x, z) ax + φ * P.consumption (y, z) ay := by
    simp only [consumption]
    rw [P.resources_affine_comb hx.1 hy.1 hθ hφ hθφ]
    ring
  have hcm : P.consumption (θ * x + φ * y, z) (θ * ax + φ * ay) ∈ P.dom := by
    rw [hcmix]
    simpa only [smul_eq_mul] using P.convex_dom hcx hcy hθ hφ hθφ
  have hle := P.toExtended.le_bellmanFn v hmix
  have hobj : P.toExtended.objectiveE v (θ * x + φ * y, z) (θ * ax + φ * ay)
      = ((P.u (P.consumption (θ * x + φ * y, z) (θ * ax + φ * ay))
          + P.discount * ∑ z', P.transitionMatrix z z' * v (θ * ax + φ * ay, z') : ℝ) : EReal) := by
    rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_coe_dom hxy hmix hcm, ← EReal.coe_add]
    rfl
  rw [hobj] at hle
  have hle' : P.u (P.consumption (θ * x + φ * y, z) (θ * ax + φ * ay))
      + P.discount * ∑ z', P.transitionMatrix z z' * v (θ * ax + φ * ay, z')
      ≤ P.toExtended.bellmanFn v (θ * x + φ * y, z) := by exact_mod_cast hle
  -- utility is concave, and so is the expectation, termwise
  have hu := P.strictConcaveOn_u_dom.concaveOn.2 hcx hcy hθ hφ hθφ
  have hexp : θ * (∑ z', P.transitionMatrix z z' * v (ax, z'))
      + φ * (∑ z', P.transitionMatrix z z' * v (ay, z'))
      ≤ ∑ z', P.transitionMatrix z z' * v (θ * ax + φ * ay, z') := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z' _ => ?_
    have hvz := (hv z').2 (P.feasible_subset_region hax) (P.feasible_subset_region hay) hθ hφ hθφ
    simp only [smul_eq_mul] at hvz
    nlinarith [P.transitionMatrix_nonneg z z']
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hexp hβ
  simp only [smul_eq_mul] at hu
  simp only [smul_eq_mul, ExtendedStochasticProgram.bellman_apply]
  rw [hbx, hby]
  rw [hcmix] at hle'
  linarith

/-- **The value function is concave in assets, for each income state.** -/
theorem concaveOn_valueFunction (z : Z) :
    ConcaveOn ℝ (Icc assetFloor assetCap) fun a => P.toExtended.valueFunction (a, z) :=
  Blackwell.forall_concaveOn_valueFunction (convex_Icc _ _) (fun (z : Z) (a : ℝ) => (a, z))
    P.toExtended.blackwell P.toExtended.discount_lt_one
    (fun v hv => P.concaveOn_bellman v hv) z

/-- **The optimal action is unique.** -/
theorem optimal_action_unique {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) {a₀ a₁ : ℝ}
    (h₀ : a₀ ∈ P.toExtended.feasible s) (h₁ : a₁ ∈ P.toExtended.feasible s)
    (hm₀ : P.toExtended.objectiveE P.toExtended.valueFunction s a₀
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction s : ℝ) : EReal))
    (hm₁ : P.toExtended.objectiveE P.toExtended.valueFunction s a₁
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction s : ℝ) : EReal)) :
    a₀ = a₁ := by
  by_contra hne
  obtain ⟨hc₀, hb₀⟩ := P.bellmanFn_eq_of_optimal hs h₀ hm₀
  obtain ⟨hc₁, hb₁⟩ := P.bellmanFn_eq_of_optimal hs h₁ hm₁
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hsum : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
  have hmem : (1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁ ∈ P.toExtended.feasible s := by
    simpa using convex_Icc assetFloor (P.maxSaving s) h₀ h₁ hhalf.le hhalf.le hsum
  have hcmid : P.consumption s ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁)
      = (1 / 2 : ℝ) * P.consumption s a₀ + (1 / 2 : ℝ) * P.consumption s a₁ := by
    simp only [consumption]; ring
  have hcm : P.consumption s ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁) ∈ P.dom := by
    rw [hcmid]
    simpa only [smul_eq_mul] using P.convex_dom hc₀ hc₁ hhalf.le hhalf.le hsum
  have hcne : P.consumption s a₀ ≠ P.consumption s a₁ := by
    simp only [consumption]
    intro h
    exact hne (by linarith)
  have hu := P.strictConcaveOn_u_dom.2 hc₀ hc₁ hcne hhalf hhalf hsum
  have hexp : (1 / 2 : ℝ) * (∑ z', P.transitionMatrix s.2 z' * P.toExtended.valueFunction (a₀, z'))
      + (1 / 2 : ℝ) * (∑ z', P.transitionMatrix s.2 z' * P.toExtended.valueFunction (a₁, z'))
      ≤ ∑ z', P.transitionMatrix s.2 z'
          * P.toExtended.valueFunction ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁, z') := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z' _ => ?_
    have hvz := (P.concaveOn_valueFunction z').2 (P.feasible_subset_region h₀)
      (P.feasible_subset_region h₁) hhalf.le hhalf.le hsum
    simp only [smul_eq_mul] at hvz
    nlinarith [P.transitionMatrix_nonneg s.2 z']
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hexp hβ
  simp only [smul_eq_mul] at hu
  have hle := P.toExtended.le_bellmanFn P.toExtended.valueFunction hmem
  have hobj : P.toExtended.objectiveE P.toExtended.valueFunction s
        ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁)
      = ((P.u (P.consumption s ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁))
          + P.discount * ∑ z', P.transitionMatrix s.2 z'
              * P.toExtended.valueFunction ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁, z')
            : ℝ) : EReal) := by
    rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_coe_dom hs hmem hcm, ← EReal.coe_add]
    rfl
  rw [hobj] at hle
  have hle' : P.u (P.consumption s ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁))
      + P.discount * ∑ z', P.transitionMatrix s.2 z'
          * P.toExtended.valueFunction ((1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * a₁, z')
      ≤ P.toExtended.bellmanFn P.toExtended.valueFunction s := by exact_mod_cast hle
  rw [hcmid] at hle'
  linarith

/-- The optimal saving choice. -/
noncomputable def policy (s : ℝ × Z) : ℝ :=
  Classical.choose (P.toExtended.exists_optimal_action P.toExtended.valueFunction s)

theorem policy_mem (s : ℝ × Z) : P.policy s ∈ P.toExtended.feasible s :=
  (Classical.choose_spec
    (P.toExtended.exists_optimal_action P.toExtended.valueFunction s)).1

theorem policy_optimal (s : ℝ × Z) :
    P.toExtended.objectiveE P.toExtended.valueFunction s (P.policy s)
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction s : ℝ) : EReal) :=
  (Classical.choose_spec
    (P.toExtended.exists_optimal_action P.toExtended.valueFunction s)).2

theorem policy_mem_region (s : ℝ × Z) : P.policy s ∈ Icc assetFloor assetCap :=
  P.feasible_subset_region (P.policy_mem s)

theorem consumption_policy_mem_dom {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) :
    P.consumption s (P.policy s) ∈ P.dom :=
  (P.bellmanFn_eq_of_optimal hs (P.policy_mem s) (P.policy_optimal s)).1

/-- **Consumption never vanishes at the optimum.** Automatic when utility is unbounded below
(`positiveConsumption_of_unbounded`); when it is bounded, it has to be earned from a marginal
Inada condition, which is what `ConsumptionFloor` does. -/
def PositiveConsumption : Prop :=
  ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → 0 < P.consumption s (P.policy s)

/-- **Utility really does diverge when the domain is the open half-line.** The structure no
longer carries `tendsto_atBot_u`, but it has not lost it: `continuousOn_extendDom` says the
extension is continuous at zero consumption, and with `dom = Ioi 0` the value there is `⊥`. -/
theorem tendsto_atBot_u (hd : P.Unbounded) : Tendsto P.u (𝓝[>] 0) atBot := by
  have hcont : ContinuousWithinAt (extendDom P.dom P.u) (Ici 0) 0 :=
    P.continuousOn_extendDom 0 (mem_Ici.mpr le_rfl)
  have hbot : extendDom P.dom P.u 0 = ⊥ := extendDom_of_not_mem (by rw [hd]; simp)
  rw [ContinuousWithinAt, hbot] at hcont
  have h2 : Tendsto (extendDom P.dom P.u) (𝓝[>] (0 : ℝ)) (𝓝 ⊥) :=
    hcont.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  refine tendsto_atBot.2 fun R => ?_
  filter_upwards [h2 (Iio_mem_nhds (EReal.bot_lt_coe R)), self_mem_nhdsWithin] with c hc hcpos
  simp only [mem_preimage, mem_Iio, extendDom_of_mem (P.mem_dom_of_pos hcpos),
    EReal.coe_lt_coe_iff] at hc
  exact hc.le

theorem positiveConsumption_of_unbounded (hd : P.Unbounded) : P.PositiveConsumption := by
  intro s hs
  have := P.consumption_policy_mem_dom hs
  rwa [hd] at this

theorem consumption_policy_pos (hpc : P.PositiveConsumption) {s : ℝ × Z}
    (hs : s.1 ∈ Icc assetFloor assetCap) : 0 < P.consumption s (P.policy s) := hpc s hs

theorem eq_policy_of_optimal {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) {a : ℝ}
    (ha : a ∈ P.toExtended.feasible s)
    (hopt : P.toExtended.objectiveE P.toExtended.valueFunction s a
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction s : ℝ) : EReal)) :
    a = P.policy s :=
  P.optimal_action_unique hs ha (P.policy_mem s) hopt (P.policy_optimal s)

theorem argmax_eq_singleton {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) :
    argmax (P.toExtended.objectiveE P.toExtended.valueFunction) P.toExtended.feasible s
      = {P.policy s} := by
  ext a
  simp only [argmax, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ha, hmax⟩
    refine P.eq_policy_of_optimal hs ha (le_antisymm (P.toExtended.le_bellmanFn _ ha) ?_)
    rw [← P.policy_optimal s]
    exact isMaxOn_iff.mp hmax _ (P.policy_mem s)
  · rintro rfl
    refine ⟨P.policy_mem s, isMaxOn_iff.mpr fun b hb => ?_⟩
    rw [P.policy_optimal s]
    exact P.toExtended.le_bellmanFn _ hb

/-- **The optimal policy is continuous** on the region of states with assets in
`[0, assetCap]`. -/
theorem continuousOn_policy :
    ContinuousOn P.policy {s : ℝ × Z | s.1 ∈ Icc assetFloor assetCap} :=
  continuousOn_of_upperHemicontinuous_singleton
    (P.toExtended.upperHemicontinuous_argmax P.toExtended.valueFunction)
    fun _ hs => P.argmax_eq_singleton hs

/-- **The Bellman equation at the policy.** -/
theorem valueFunction_eq_policy {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) :
    P.toExtended.valueFunction s
      = P.u (P.consumption s (P.policy s))
        + P.discount * ∑ z', P.transitionMatrix s.2 z'
            * P.toExtended.valueFunction (P.policy s, z') := by
  have h := (P.bellmanFn_eq_of_optimal hs (P.policy_mem s) (P.policy_optimal s)).2
  have hfix : P.toExtended.bellmanFn P.toExtended.valueFunction s
      = P.toExtended.valueFunction s := by
    conv_rhs => rw [← P.toExtended.bellman_valueFunction]
    rfl
  rw [← hfix, h]

/-- A two-state calibration with `σ = 2`, where CES utility is `-1 / c`. -/
noncomputable def calibrated : IncomeFluctuation (Fin 2) 0 10 where
  income z := if z = 0 then 1 / 2 else 3 / 2
  transitionMatrix _ _ := 1 / 2
  interest := 1 / 20
  discount := 24 / 25
  u := fun c => -c⁻¹
  minIncome := 1 / 2
  maxIncome := 3 / 2
  minIncome_pos := by norm_num
  minIncome_le z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  assetFloor_le_assetCap := by norm_num
  assetCap_nonneg := by norm_num
  minConsumption_pos := by norm_num
  minConsumption_le_floor := le_rfl
  discount_lt_one := by norm_num
  dom := Ioi 0
  Ioi_subset_dom := subset_rfl
  dom_subset_Ici := Ioi_subset_Ici_self
  continuousOn_u_dom := (continuousOn_id.inv₀ fun x hx => ne_of_gt hx).neg
  monotoneOn_u_dom := by
    intro x hx y _ hxy
    have : (0 : ℝ) < x := hx
    simp only [neg_le_neg_iff]
    gcongr
  strictConcaveOn_u_dom := strictConcaveOn_neg_inv
  continuousOn_extendDom :=
    continuousOn_extendDom_Ioi ((continuousOn_id.inv₀ fun x hx => ne_of_gt hx).neg)
      (tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero)

end IncomeFluctuation

end LeanEconomics
