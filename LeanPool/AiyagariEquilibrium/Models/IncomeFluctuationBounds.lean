/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuation

/-!
# Consumption at the optimum is bounded away from zero

Positivity of optimal consumption is already known pointwise: a zero would make the reward
`⊥` and the value could not be real. What is needed for comparative statics is a UNIFORM
bound, a single `δ > 0` working at every state.

The bound proved here is explicit rather than compactness-based, and that is the whole point.
A compactness argument would say that optimal consumption is continuous and positive on a
compact state space, hence has a positive minimum — true, and recorded below as a sanity
check, but useless for the parametric problem. There the bound has to be uniform over an
interval of interest rates as well, and the corresponding compactness argument would need
joint continuity in `(r, s)`, which is precisely what the bound is wanted to prove. It would
be circular.

The explicit route avoids that. At the optimum the Bellman equation reads

  V s = u c* + β · E[V]

so `u c* ≥ -(1 + β)‖V‖`, a lower bound on the UTILITY of optimal consumption depending only
on the sup norm of the value function. Since `u` falls to `-∞` at zero, that pins consumption
away from zero. Nothing in the argument refers to the state, so the bound is automatically
uniform in the state; and when `r` varies, `‖V‖` is controlled by the reward bounds, which are
themselves uniform over a compact interval of rates.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-- The expected continuation value is bounded by the sup norm of the value function. -/
theorem abs_expectation_le (a : ℝ) (z : Z) :
    |∑ z', P.transitionMatrix z z' * P.toExtended.valueFunction (a, z')|
      ≤ ‖P.toExtended.valueFunction‖ := by
  exact P.toExtended.abs_expect_le P.toExtended.valueFunction ((assetFloor, z), a)

/-- **The utility of optimal consumption is bounded below**, by a quantity depending only on
the sup norm of the value function — not on the state. -/
theorem le_utility_consumption_policy {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) :
    -(1 + P.discount) * ‖P.toExtended.valueFunction‖
      ≤ P.u (P.consumption s (P.policy s)) := by
  have hbell := P.valueFunction_eq_policy hs
  have hexp := P.abs_expectation_le (P.policy s) s.2
  have hV : |P.toExtended.valueFunction s| ≤ ‖P.toExtended.valueFunction‖ :=
    P.toExtended.valueFunction.norm_coe_le_norm _
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  rw [abs_le] at hexp hV
  nlinarith [hexp.1, hexp.2, hV.1, hV.2, hbell]

/-- **The utility bound in terms of the reward bounds alone** — no fixed point on the right.

This is the form that survives into a parametric statement. A family of programs sharing a
utility function and a common bound on `max |u minConsumption| |u maxConsumption| / (1 - β)` has
a common `L`, and then `exists_lower_bound_of_utility_ge` hands it a single `δ`. -/
theorem le_utility_consumption_policy_of_bounds {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) :
    -(1 + P.discount) * (max |P.u P.minConsumption| |P.u P.maxConsumption| / (1 - P.discount))
      ≤ P.u (P.consumption s (P.policy s)) := by
  refine le_trans ?_ (P.le_utility_consumption_policy hs)
  have hnorm := P.toExtended.norm_valueFunction_le
  have hmin : P.toExtended.rewardMin = P.u P.minConsumption := rfl
  have hmax : P.toExtended.rewardMax = P.u P.maxConsumption := rfl
  have hdisc : P.toExtended.discount = P.discount := rfl
  rw [hmin, hmax, hdisc] at hnorm
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  nlinarith [hnorm]

/-- **From a lower bound on utility to a lower bound on consumption.** The resulting `δ`
depends only on `u` and on `L` — NOT on the state, and not on anything that moves with the
interest rate. That is the property the parametric argument needs. -/
theorem exists_lower_bound_of_utility_ge (hd : P.Unbounded) (L : ℝ)
    (hL : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → L ≤ P.u (P.consumption s (P.policy s))) :
    ∃ δ > 0, ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → δ ≤ P.consumption s (P.policy s) := by
  have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), P.u c < L - 1 :=
    P.tendsto_atBot_u hd (eventually_lt_atBot (L - 1))
  obtain ⟨ε, hε, hsub⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  refine ⟨ε, hε, fun s hs => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < P.consumption s (P.policy s) :=
    P.consumption_policy_pos (P.positiveConsumption_of_unbounded hd) hs
  have hbad : P.u (P.consumption s (P.policy s)) < L - 1 := hsub ⟨hpos, hlt⟩
  linarith [hL s hs]

/-- **Consumption at the optimum is bounded away from zero, uniformly in the state.**

No compactness and no continuity of the policy are used, which is exactly what lets the same
argument run uniformly in the interest rate: a compactness proof would need joint continuity
in `(r, s)`, which is what such a bound is wanted to prove in the first place. -/
theorem exists_consumption_policy_lower_bound (hd : P.Unbounded) :
    ∃ δ > 0, ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → δ ≤ P.consumption s (P.policy s) :=
  P.exists_lower_bound_of_utility_ge hd _ fun _ hs =>
    P.le_utility_consumption_policy_of_bounds hs

/-! ### A choice set that does not move

The Bellman operator maximises over `Icc 0 (maxSaving s)`, an interval whose RIGHT ENDPOINT
moves with the interest rate. Comparing the operator at two rates therefore means comparing
suprema over two different sets, which is the awkward part of any such estimate.

Writing the choice as a fraction `θ ∈ [0,1]` of the maximum feasible saving removes the
problem: the choice set becomes `[0,1]` for every rate and every state, and all the rate
dependence moves into the objective, where it can be estimated pointwise. `|sSup f - sSup g|`
over a COMMON set is bounded by the pointwise gap; over two different sets it is not. -/

theorem assetFloor_le_maxSaving (s : ℝ × Z) : assetFloor ≤ P.maxSaving s := le_max_left _ _

/-- How much saving room the household has above the borrowing limit. -/
noncomputable def savingRoom (s : ℝ × Z) : ℝ := P.maxSaving s - assetFloor

theorem savingRoom_nonneg (s : ℝ × Z) : 0 ≤ P.savingRoom s := by
  simp only [savingRoom]; linarith [P.assetFloor_le_maxSaving s]

/-- The feasible set is the image of the FIXED interval `[0,1]` under the affine map that takes
`θ` to the borrowing limit plus a fraction `θ` of the saving room. With `assetFloor = 0` this is
just scaling by the maximum feasible saving. -/
theorem feasible_eq_image (s : ℝ × Z) :
    P.toExtended.feasible s = (fun θ => assetFloor + θ * P.savingRoom s) '' Icc 0 1 := by
  have hcomp : (fun θ : ℝ => assetFloor + θ * P.savingRoom s)
      = (fun y : ℝ => assetFloor + y) ∘ (fun θ : ℝ => θ * P.savingRoom s) := rfl
  rw [P.feasible_eq, hcomp, Set.image_comp,
    image_mul_right_Icc (by norm_num) (P.savingRoom_nonneg s), image_const_add_Icc]
  simp only [zero_mul, one_mul, add_zero]
  congr 1
  simp only [savingRoom]; ring

/-- **The one-period value as a supremum over a fixed interval.** -/
theorem maxE_eq_sSup_unit (v : (ℝ × Z) →ᵇ ℝ) (s : ℝ × Z) :
    P.toExtended.maxE v s
      = sSup ((fun θ => P.toExtended.objectiveE v s (assetFloor + θ * P.savingRoom s))
          '' Icc 0 1) := by
  rw [ExtendedStochasticProgram.maxE, maxValueE, P.feasible_eq_image, Set.image_image]

/-- **Consumption is bounded below by a quantity free of the state and the interest rate.**

Along the reparametrised choice, consumption is at least `minConsumption * (1 - θ)`. The bound
holds because the saving room never exceeds what is left after servicing the debt, so taking a
fraction `θ` of it leaves at least a fraction `1 - θ`.

This is the uniformity that makes the parametric estimate possible: it does not mention the
state, and the only model data it mentions -- `minConsumption` -- does not move with the interest
rate. Away from `θ = 1` the reward is therefore real and bounded, so the `-∞` cannot
interfere. -/
theorem minConsumption_mul_le_consumption {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (s : ℝ × Z) :
    P.minConsumption * (1 - θ) ≤ P.consumption s (assetFloor + θ * P.savingRoom s) := by
  have hms := P.maxSaving_le_resources s
  have hroom := P.savingRoom_nonneg s
  have hR := P.minConsumption_le_consumption_floor s
  have hle : P.savingRoom s ≤ P.resources s - assetFloor := by
    simp only [savingRoom]; linarith
  have h1 : θ * P.savingRoom s ≤ θ * (P.resources s - assetFloor) :=
    mul_le_mul_of_nonneg_left hle hθ.1
  simp only [consumption]
  nlinarith [hθ.1, hθ.2, hR, h1]

end IncomeFluctuation

end LeanEconomics
