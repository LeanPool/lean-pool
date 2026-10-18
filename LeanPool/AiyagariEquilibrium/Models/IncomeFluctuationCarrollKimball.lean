/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationConsumption
public import LeanPool.AiyagariEquilibrium.Analysis.PowerMean

/-!
# Concavity of the consumption function as a closed class

`IncomeFluctuationConsumption` showed that concavity of the consumption function cannot follow
from concavity of `u` and of the value function, and that it is a statement about the FIXED
POINT. This file supplies the machinery that statements about the fixed point need, and reduces
Carroll and Kimball (1996) to its single inductive step.

The pattern is the one used four times already — monotonicity, concavity, Lipschitz bounds and
increasing differences — but with one new difficulty. Those four are properties OF the value
function, closed in sup norm by `isClosed_concaveOn` and its relatives. Concavity of the
consumption function is a property of the value function's ARGMAX, and nothing says offhand
that an argmax survives a uniform limit. So the closure step has to be proved rather than
quoted, and that is what `tendsto_policyOf` does: along a uniformly convergent sequence of
continuation values the optimal actions converge, because a cluster point of the maximisers is
a maximiser of the limit and the maximiser of the limit is unique.

That gives `concaveOn_consumptionFn_of_preserves`: if the Bellman operator carries a concave
consumption function to a concave consumption function, the fixed point's consumption function
is concave. The iteration starts from `0`, whose consumption function is `resources`, affine on
the asset region — `policyOf_zero`, an agent with no future eats everything.

## What is proved, and what is left

The hypothesis `hT` is the whole of Carroll and Kimball. Two thirds of it are now discharged.

**The analysis.** On paper the argument runs through second derivatives: risk tolerances ADD
across the optimisation, `T_V(m) = T_u(c) + T_W(m - c)`, and Kimball's risk-tolerance
aggregation theorem propagates `T_V' ≥ T_u'` from the continuation to the value. `PowerMean`
supplies the integrated form of exactly that, with no derivative: for CRRA marginal utility the
consumption paired with a given stock of end-of-period assets is a positive multiple of the
weighted power mean, exponent `-γ`, of next period's consumptions, and a power mean with a
NEGATIVE exponent is concave and nondecreasing. Homogeneity turns that into the convexity of a
sublevel set, which is elementary.

**The transfer.** Turning concavity of that map into concavity of the consumption function is
usually done by differentiating an inverse function. `concaveOn_of_egm` does it from the budget
identity alone: write the choice against end-of-period assets, and the two concavities are the
same statement.

**The Euler equation** `hEuler` is proved in `IncomeFluctuationEuler`, and so is the step with
the BORROWING LIMIT allowed to bind. Saving more is feasible unless the household already saves
the maximum, so the inequality half of the first-order condition survives the corner; and at a
constrained state the saving is `assetFloor`, which lies below any average of savings, which is
the only thing `concaveOn_of_egm` ever needed. `concaveOn_of_egm_corner` and
`concaveOn_consumptionFnOf_bellman` are the results.

**The induction's bookkeeping** is done in `IncomeFluctuationIterate`: positivity and
monotonicity of the consumption function, proved at the fixed point in this development, restated
for an arbitrary continuation, and a uniform bound on saving that covers every iterate at once.

**So Carroll and Kimball is proved** -- `concaveOn_consumptionFn_of_marginal` for CRRA,
`concaveOn_consumptionFn_of_bounded_crra` for the bounded CES family `0 < γ < 1`, where positive
consumption comes from the marginal Inada condition run against an arbitrary continuation.

One input is left explicit: a calibration inequality putting the asset cap above the bound on
saving. `crra_policyOf_le_mul` makes that bound the multiplicative one -- deviate to a FRACTION
of the saving and price the extra consumption where it lands -- so it involves the continuation's
OSCILLATION rather than its level, and the hypothesis is character for character the one
`crra_policy_lt_assetCap` carries. The witnesses that discharge that one discharge this one:
`nearLog_concaveOn_consumptionFn` is Carroll and Kimball for a concrete CES economy, at every
rate the equilibrium argument uses.

**Toda (2021) still bounds what can be hoped for.** Under regularity conditions HARA is
NECESSARY for the consumption function to be concave, and the structure assumes of `u` only
strict concavity, so `hT` at that generality is FALSE and no proof of it can exist. That is why
the step above is stated for CRRA, which is what Light's published version (2020) assumes.

## OWED: this is deferred, not abandoned

The obstruction has moved four times.

* HARA was the first answer: Toda (2021) makes it NECESSARY, and `Analysis/HARA.lean` supplies
  it. The utility class is no longer the blocker.
* The asset cap was the second, and worse, because it made the conclusion outright FALSE --
  `not_concaveOn_consumptionFn_of_cap_binds` below. `crra_policy_lt_assetCap` removes it by
  calibration, and `nearLog` is recalibrated so that saving provably never reaches the cap.
* Differentiability was the third, and it is now GONE: `hasDerivAt_bellman` is the Clausen and
  Strub sandwich run along the iteration, and `PowerMean` removes second derivatives altogether.
* The Euler equation was the fourth, and it is proved -- `euler_eq`, and without the envelope
  theorem at that.
* The borrowing-constraint kink was the fifth, and `concaveOn_of_egm_corner` absorbs it.
* The induction's bookkeeping was the sixth, and `IncomeFluctuationIterate` does it.

* Positive consumption for the bounded CES family was the seventh, and
  `positiveConsumptionAll_of_marginalInada` does it.
* The cap calibration was the eighth, and `crra_policyOf_le_mul` makes it the one the witnesses
  already prove.

Nothing remains: `nearLog_concaveOn_consumptionFn` is the theorem at a concrete calibration.

This file holds the analysis and the closure step; `IncomeFluctuationEuler` the first-order
condition and the corner; `IncomeFluctuationIterate` the bookkeeping and the theorem.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-- Continuation values that are concave along each asset slice. This is what makes the optimal
action unique, and it is preserved by the Bellman operator. -/
def ConcaveSlices (assetFloor assetCap : ℝ) (v : (ℝ × Z) →ᵇ ℝ) : Prop :=
  ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap) fun a => v (a, z)

omit [Fintype Z] [Nonempty Z] [DiscreteTopology Z] in
theorem concaveSlices_zero : ConcaveSlices assetFloor assetCap (0 : (ℝ × Z) →ᵇ ℝ) :=
  fun _ => ⟨convex_Icc _ _, fun _ _ _ _ _ _ _ _ _ => by simp⟩

theorem concaveSlices_bellman {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetFloor assetCap v) :
    ConcaveSlices assetFloor assetCap (P.toExtended.bellman v) :=
  fun z => P.concaveOn_bellman v hv z

theorem concaveSlices_valueFunction :
    ConcaveSlices assetFloor assetCap P.toExtended.valueFunction :=
  P.concaveOn_valueFunction

/-! ### The optimal action of an arbitrary continuation

`IncomeFluctuation` proves uniqueness for every continuation whose asset slices are concave.
The closure argument applies that shared theorem along the whole approximating sequence; the
wrapper below gives its hypothesis the name `ConcaveSlices`. -/

/-- **The optimal action is unique** for any continuation with concave slices. -/
theorem optimal_action_unique_of_concaveSlices {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices assetFloor assetCap v)
    {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) {a₀ a₁ : ℝ}
    (h₀ : a₀ ∈ P.toExtended.feasible s) (h₁ : a₁ ∈ P.toExtended.feasible s)
    (hm₀ : P.toExtended.objectiveE v s a₀ = ((P.toExtended.bellmanFn v s : ℝ) : EReal))
    (hm₁ : P.toExtended.objectiveE v s a₁ = ((P.toExtended.bellmanFn v s : ℝ) : EReal)) :
    a₀ = a₁ := by
  exact P.optimal_action_unique_of_concave hv hs h₀ h₁ hm₀ hm₁

/-! ### The agent with no future eats everything

The iteration starts at the zero continuation, where saving buys nothing and the optimal plan
is to consume all cash on hand. Its consumption function is `resources`, affine on the asset
region, so the induction has a base. -/

/-- Saving more cannot raise the reward: consumption falls, and utility rises with it. -/
theorem reward_antitone {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) {x y : ℝ}
    (hx : x ∈ P.toExtended.feasible s) (hy : y ∈ P.toExtended.feasible s) (hxy : x ≤ y) :
    P.toExtended.reward (s, y) ≤ P.toExtended.reward (s, x) := by
  by_cases h : P.consumption s y ∈ P.dom
  · have hcx : P.consumption s x ∈ P.dom :=
      P.dom_upward h (by simp only [consumption]; linarith)
    rw [P.reward_eq_coe_dom hs hx hcx, P.reward_eq_coe_dom hs hy h, EReal.coe_le_coe_iff]
    exact P.monotoneOn_u_dom h hcx (by simp only [consumption]; linarith)
  · have hb : P.toExtended.reward (s, y) = ⊥ := by
      by_contra hne
      exact h (P.consumption_mem_dom_of_ne_bot hs hy hne)
    rw [hb]; exact bot_le

/-- **With nothing to gain from saving, the household saves nothing.** -/
theorem policyOf_zero {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) :
    P.policyOf 0 s = assetFloor := by
  have hmem0 : assetFloor ∈ P.toExtended.feasible s := ⟨le_rfl, le_max_left _ _⟩
  have hc0 : 0 < P.consumption s assetFloor := by
    have h1 := P.minConsumption_le_consumption_floor s
    have h2 := P.minConsumption_pos
    simp only [consumption]; linarith
  have hobj : ∀ a : ℝ, P.toExtended.objectiveE (0 : (ℝ × Z) →ᵇ ℝ) s a
      = P.toExtended.reward (s, a) := by
    intro a
    simp [ExtendedStochasticProgram.objectiveE, ExtendedStochasticProgram.expect]
  have hle : ∀ a ∈ P.toExtended.feasible s,
      P.toExtended.objectiveE (0 : (ℝ × Z) →ᵇ ℝ) s a
        ≤ ((P.u (P.consumption s assetFloor) : ℝ) : EReal) := by
    intro a ha
    rw [hobj a, ← P.reward_eq_coe hs hmem0 hc0]
    exact P.reward_antitone hs hmem0 ha ha.1
  have hb := P.toExtended.bellmanFn_le (0 : (ℝ × Z) →ᵇ ℝ) hle
  have hopt : P.toExtended.objectiveE (0 : (ℝ × Z) →ᵇ ℝ) s assetFloor
      = ((P.toExtended.bellmanFn (0 : (ℝ × Z) →ᵇ ℝ) s : ℝ) : EReal) := by
    refine le_antisymm (P.toExtended.le_bellmanFn _ hmem0) ?_
    rw [hobj assetFloor, P.reward_eq_coe hs hmem0 hc0, EReal.coe_le_coe_iff]
    exact hb
  exact optimal_action_unique_of_concaveSlices P concaveSlices_zero hs (P.policyOf_mem _ _) hmem0
    (P.policyOf_optimal _ _) hopt

theorem consumptionFnOf_zero {z : Z} {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) :
    P.consumptionFnOf 0 z a = P.income z + (1 + P.interest) * a - assetFloor := by
  rw [consumptionFnOf, P.policyOf_zero (s := (a, z)) ha]
  simp only [consumption, resources, max_eq_right ha.1]

theorem concaveOn_consumptionFnOf_zero (z : Z) :
    ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf 0 z) := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  have hm : θ • x + φ • y ∈ Icc assetFloor assetCap := convex_Icc _ _ hx hy hθ hφ hθφ
  simp only [smul_eq_mul] at hm ⊢
  rw [P.consumptionFnOf_zero hx, P.consumptionFnOf_zero hy, P.consumptionFnOf_zero hm]
  have hφ' : φ = 1 - θ := by linarith
  subst hφ'
  exact le_of_eq (by ring)

/-! ### The closure step: optimal actions survive a uniform limit

This is what the four earlier closed-class arguments got for free from `isClosed_concaveOn`.
Concavity of the consumption function is a property of the ARGMAX, so closure has to be proved:
a cluster point of maximisers of `vₙ` is a maximiser of the limit, and the maximiser of the
limit is unique. -/

theorem abs_expect_sub_le_norm (v w : (ℝ × Z) →ᵇ ℝ) (p : (ℝ × Z) × ℝ) :
    |P.toExtended.expect v p - P.toExtended.expect w p| ≤ ‖v - w‖ := by
  have h : P.toExtended.expect v p - P.toExtended.expect w p
      = P.toExtended.expect (v - w) p := by
    simp only [ExtendedStochasticProgram.expect, ← Finset.sum_sub_distrib,
      BoundedContinuousFunction.coe_sub, Pi.sub_apply, mul_sub]
  rw [h]
  exact P.toExtended.abs_expect_le _ _

theorem tendsto_expect {v : ℕ → (ℝ × Z) →ᵇ ℝ} {w : (ℝ × Z) →ᵇ ℝ} (hv : Tendsto v atTop (𝓝 w))
    {x : ℕ → ℝ} {y : ℝ} (hx : Tendsto x atTop (𝓝 y)) (s : ℝ × Z) :
    Tendsto (fun n => P.toExtended.expect (v n) (s, x n)) atTop
      (𝓝 (P.toExtended.expect w (s, y))) := by
  have hnorm : Tendsto (fun n => ‖v n - w‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hv
  have hcont : Tendsto (fun n => P.toExtended.expect w (s, x n)) atTop
      (𝓝 (P.toExtended.expect w (s, y))) :=
    ((P.toExtended.continuous_expect w).tendsto _).comp (tendsto_const_nhds.prodMk_nhds hx)
  have hdiff : Tendsto (fun n => P.toExtended.expect (v n) (s, x n)
      - P.toExtended.expect w (s, x n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hnorm
    simpa only [Real.norm_eq_abs] using P.abs_expect_sub_le_norm (v n) w (s, x n)
  simpa using hdiff.add hcont

theorem tendsto_objectiveE {v : ℕ → (ℝ × Z) →ᵇ ℝ} {w : (ℝ × Z) →ᵇ ℝ} (hv : Tendsto v atTop (𝓝 w))
    {x : ℕ → ℝ} {y : ℝ} (hx : Tendsto x atTop (𝓝 y)) (s : ℝ × Z) :
    Tendsto (fun n => P.toExtended.objectiveE (v n) s (x n)) atTop
      (𝓝 (P.toExtended.objectiveE w s y)) := by
  have hr : Tendsto (fun n => P.toExtended.reward (s, x n)) atTop
      (𝓝 (P.toExtended.reward (s, y))) :=
    (P.toExtended.reward.continuous.tendsto _).comp (tendsto_const_nhds.prodMk_nhds hx)
  have he : Tendsto (fun n =>
      ((P.toExtended.discount * P.toExtended.expect (v n) (s, x n) : ℝ) : EReal)) atTop
      (𝓝 ((P.toExtended.discount * P.toExtended.expect w (s, y) : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp
      (tendsto_const_nhds.mul (P.tendsto_expect hv hx s))
  exact Filter.Tendsto.comp
    (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))
    (hr.prodMk_nhds he)

/-- **Optimal actions survive a uniform limit.** -/
theorem tendsto_policyOf {v : ℕ → (ℝ × Z) →ᵇ ℝ} {w : (ℝ × Z) →ᵇ ℝ}
    (hv : Tendsto v atTop (𝓝 w)) (hw : ConcaveSlices assetFloor assetCap w)
    {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) :
    Tendsto (fun n => P.policyOf (v n) s) atTop (𝓝 (P.policyOf w s)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨L, hLK, φ, hφ, hφlim⟩ := (P.toExtended.isCompact_feasible s).tendsto_subseq
    (x := fun i => P.policyOf (v (ns i)) s) (fun i => P.policyOf_mem _ _)
  have hv' : Tendsto (fun i => v (ns (φ i))) atTop (𝓝 w) :=
    hv.comp (hns.comp hφ.tendsto_atTop)
  have hlim' : Tendsto (fun i => P.policyOf (v (ns (φ i))) s) atTop (𝓝 L) := hφlim
  -- every feasible action is beaten by the limit of the maximisers
  have key : ∀ x ∈ P.toExtended.feasible s,
      P.toExtended.objectiveE w s x ≤ P.toExtended.objectiveE w s L := by
    intro x hx
    refine le_of_tendsto_of_tendsto (P.tendsto_objectiveE hv' tendsto_const_nhds s)
      (P.tendsto_objectiveE hv' hlim' s) (Eventually.of_forall fun i => ?_)
    have hle := P.toExtended.le_bellmanFn (v (ns (φ i))) hx
    rwa [← P.policyOf_optimal (v (ns (φ i))) s] at hle
  have hLopt : P.toExtended.objectiveE w s L = ((P.toExtended.bellmanFn w s : ℝ) : EReal) := by
    refine le_antisymm (P.toExtended.le_bellmanFn w hLK) ?_
    rw [← P.policyOf_optimal w s]
    exact key _ (P.policyOf_mem w s)
  have hLeq : L = P.policyOf w s :=
    optimal_action_unique_of_concaveSlices P hw hs hLK (P.policyOf_mem w s) hLopt
      (P.policyOf_optimal w s)
  exact ⟨φ, by rw [← hLeq]; exact hlim'⟩

/-- The limit step, split off from `concaveOn_consumptionFn_of_preserves`: concavity of the
consumption functions of the iterates passes to the fixed point, because optimal actions survive
a uniform limit. -/
theorem concaveOn_consumptionFn_of_iterates
    (hcons : ∀ n : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z)) (z : Z) :
    ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) := by
  set T := P.toExtended.bellman with hTdef
  have hlim : Tendsto (fun n => T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) atTop
      (𝓝 P.toExtended.valueFunction) := P.toExtended.tendsto_iterate_valueFunction 0
  have hpt : ∀ a ∈ Icc assetFloor assetCap,
      Tendsto (fun n => P.consumptionFnOf (T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a) atTop
        (𝓝 (P.consumptionFn z a)) := by
    intro a ha
    have hp := P.tendsto_policyOf hlim P.concaveSlices_valueFunction (s := (a, z)) ha
    have he : P.consumptionFn z a
        = P.resources (a, z) - P.policyOf P.toExtended.valueFunction (a, z) := rfl
    rw [he]
    simpa only [consumptionFnOf, consumption] using tendsto_const_nhds.sub hp
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  have hm : θ • x + φ • y ∈ Icc assetFloor assetCap := convex_Icc _ _ hx hy hθ hφ hθφ
  refine le_of_tendsto_of_tendsto
    (((hpt x hx).const_smul θ).add ((hpt y hy).const_smul φ)) (hpt _ hm)
    (Eventually.of_forall fun n => (hcons n z).2 hx hy hθ hφ hθφ)

/-! ### Carroll and Kimball, reduced to one step -/

/-- **The consumption function of the fixed point is concave whenever the Bellman operator
preserves concavity of the consumption function.** Everything except the hypothesis `hT` is
discharged: the base case, the induction, the limit.

`hT` is Carroll and Kimball (1996) — see the module docstring for what proving it would take. -/
theorem concaveOn_consumptionFn_of_preserves
    (hT : ∀ v : (ℝ × Z) →ᵇ ℝ, ConcaveSlices assetFloor assetCap v →
      (∀ z, ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z)) →
      ∀ z, ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf (P.toExtended.bellman v) z))
    (z : Z) : ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) := by
  set T := P.toExtended.bellman with hTdef
  have hslices : ∀ n : ℕ, ConcaveSlices assetFloor assetCap (T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact P.concaveSlices_bellman ih
  have hcons : ∀ n : ℕ, ∀ z, ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z) := by
    intro n
    induction n with
    | zero => exact P.concaveOn_consumptionFnOf_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact hT _ (hslices k) ih
  exact P.concaveOn_consumptionFn_of_iterates hcons z

/-! ### The endogenous-gridpoint transfer

The step that carries concavity forward is not about the Bellman operator at all. Write the
household's choice against END-OF-PERIOD assets rather than against cash on hand: let `C A` be
the consumption it pairs with saving `A`, so that the budget reads `y + R a = A + C A`. The
graph of the consumption function is then the curve `A ↦ (A + C A, C A)`, and concavity of the
consumption function is exactly concavity of `C`.

That equivalence is elementary — it is proved below with no derivative and no inverse function,
from the budget identity and the fact that `A + C A` is strictly increasing. What it buys is
that the hard step moves to `C`, where the first-order condition makes it a POWER MEAN of next
period's consumptions, and `Analysis/PowerMean` settles those. -/

/-- If `C` is nondecreasing then cash on hand is strictly increasing in end-of-period assets. -/
theorem strictMonoOn_add_egm {S : Set ℝ} {C : ℝ → ℝ} (hC : MonotoneOn C S) :
    StrictMonoOn (fun A => A + C A) S := fun _ ha _ hb hab => by
  have := hC ha hb hab.le
  simp only
  linarith

/-- **The endogenous-gridpoint transfer.** With the budget written against end-of-period assets,
concavity of the consumption function is concavity of `C`. Derivative-free. -/
theorem concaveOn_of_egm {z : Z} {g C h : ℝ → ℝ}
    (hC : ConcaveOn ℝ (Icc assetFloor assetCap) C)
    (hM : StrictMonoOn (fun A => A + C A) (Icc assetFloor assetCap))
    (hg : ∀ a ∈ Icc assetFloor assetCap, g a ∈ Icc assetFloor assetCap)
    (hbud : ∀ a ∈ Icc assetFloor assetCap,
      P.income z + (1 + P.interest) * a = g a + C (g a))
    (hh : ∀ a ∈ Icc assetFloor assetCap, h a = C (g a)) :
    ConcaveOn ℝ (Icc assetFloor assetCap) h := by
  refine ⟨convex_Icc _ _, fun a ha b hb θ φ hθ hφ hθφ => ?_⟩
  simp only [smul_eq_mul]
  have hm : θ * a + φ * b ∈ Icc assetFloor assetCap := by
    simpa only [smul_eq_mul] using convex_Icc assetFloor assetCap ha hb hθ hφ hθφ
  have hA₁ := hg a ha
  have hA₂ := hg b hb
  have hAθ := hg _ hm
  have hAm : θ * g a + φ * g b ∈ Icc assetFloor assetCap := by
    simpa only [smul_eq_mul] using convex_Icc assetFloor assetCap hA₁ hA₂ hθ hφ hθφ
  have h1 := hbud a ha
  have h2 := hbud b hb
  have h3 := hbud _ hm
  -- the budget at the midpoint, split two ways
  have hcomb : P.income z + (1 + P.interest) * (θ * a + φ * b)
      = (θ * g a + φ * g b) + (θ * C (g a) + φ * C (g b)) := by
    linear_combination θ * h1 + φ * h2 - P.income z * hθφ
  -- concavity of `C` puts the midpoint's saving below the average
  have hCc : θ * C (g a) + φ * C (g b) ≤ C (θ * g a + φ * g b) := by
    simpa only [smul_eq_mul] using hC.2 hA₁ hA₂ hθ hφ hθφ
  have hle : g (θ * a + φ * b) + C (g (θ * a + φ * b))
      ≤ (θ * g a + φ * g b) + C (θ * g a + φ * g b) := by
    rw [← h3, hcomb]; linarith
  have hAle : g (θ * a + φ * b) ≤ θ * g a + φ * g b := by
    by_contra hcon
    exact absurd (hM hAm hAθ (not_le.mp hcon)) (not_lt.mpr hle)
  -- and the budget converts that into the concavity of the consumption function
  rw [hh a ha, hh b hb, hh _ hm]
  have hval : C (g (θ * a + φ * b))
      = (θ * g a + φ * g b) + (θ * C (g a) + φ * C (g b)) - g (θ * a + φ * b) := by
    rw [← hcomb, h3]; ring
  rw [hval]
  linarith

/-! ### Carroll and Kimball for CRRA, from the first-order condition

With CRRA marginal utility `u' c = c ^ (-γ)` the first-order condition says exactly that the
consumption paired with saving `A` is a positive multiple of the weighted power mean, exponent
`-γ`, of next period's consumptions at `A`. `Analysis/PowerMean` makes that map concave and
nondecreasing, and the transfer above does the rest. -/

/-- **The endogenous-gridpoint map for CRRA.** The consumption a household with continuation `v`
pairs with end-of-period assets `A`, read off the Euler equation. -/
noncomputable def egmMap (v : (ℝ × Z) →ᵇ ℝ) (γ : ℝ) (z : Z) (A : ℝ) : ℝ :=
  ((P.discount : ℝ) * (1 + P.interest)) ^ (-(1 / γ))
    * powerMean (P.transitionMatrix z) (-γ) fun z' => P.consumptionFnOf v z' A

theorem concaveOn_egmMap {γ : ℝ} (hγ : 0 < γ) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z')) :
    ConcaveOn ℝ (Icc assetFloor assetCap) (P.egmMap v γ z) := by
  have hmean := concaveOn_powerMean_comp (convex_Icc assetFloor assetCap)
    (neg_neg_of_pos hγ) (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hpos hconc
  have hk : (0 : ℝ) ≤ ((P.discount : ℝ) * (1 + P.interest)) ^ (-(1 / γ)) :=
    Real.rpow_nonneg (mul_nonneg P.discount.coe_nonneg P.interest_gt_neg_one.le) _
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  have hstep := hmean.2 hx hy hθ hφ hθφ
  simp only [smul_eq_mul] at hstep ⊢
  simp only [egmMap]
  linarith [mul_le_mul_of_nonneg_left hstep hk]

theorem monotoneOn_egmMap {γ : ℝ} (hγ : 0 < γ) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap)) :
    MonotoneOn (P.egmMap v γ z) (Icc assetFloor assetCap) := by
  have hmean := monotoneOn_powerMean_comp (D := Icc assetFloor assetCap)
    (neg_neg_of_pos hγ) (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hpos hmono
  intro x hx y hy hxy
  exact mul_le_mul_of_nonneg_left (hmean hx hy hxy)
    (Real.rpow_nonneg (mul_nonneg P.discount.coe_nonneg P.interest_gt_neg_one.le) _)

/-- **Carroll and Kimball (1996), the induction step, for CRRA.** Given the Euler equation, the
Bellman operator carries a concave consumption function to a concave consumption function.

Everything except `hEuler` is now proved: the power-mean concavity that Carroll and Kimball
obtain from Kimball's risk-tolerance aggregation, and the endogenous-gridpoint transfer that
turns it into concavity of the consumption function. `hEuler` is the first-order condition of
the maximisation, which holds wherever the choice is interior — see the module docstring. -/
theorem concaveOn_consumptionFnOf_bellman_of_euler {γ : ℝ} (hγ : 0 < γ) {v : (ℝ × Z) →ᵇ ℝ}
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap)) (z : Z)
    (hEuler : ∀ a ∈ Icc assetFloor assetCap,
      P.consumptionFnOf (P.toExtended.bellman v) z a
        = P.egmMap v γ z (P.policyOf (P.toExtended.bellman v) (a, z))) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_of_egm (z := z) (g := fun a => P.policyOf (P.toExtended.bellman v) (a, z))
    (C := P.egmMap v γ z) (P.concaveOn_egmMap hγ z hpos hconc)
    (strictMonoOn_add_egm (P.monotoneOn_egmMap hγ z hpos hmono))
    (fun a _ => P.feasible_subset_region (P.policyOf_mem _ (a, z))) (fun a ha => ?_)
    (fun a ha => hEuler a ha)
  rw [← hEuler a ha]
  have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
    simp only [resources, max_eq_right ha.1]
  simp only [consumptionFnOf, consumption, hres]
  ring

/-! ### The asset cap obstructs concavity, and `hT` is stated too strongly

Attempting `hT` for log utility — the one CRRA specification this structure admits with Light's
condition, by `crra_pinch` — turns up an obstruction that has nothing to do with Carroll and
Kimball and everything to do with the cap.

Where the cap binds the household cannot save more, so every extra unit of resources is consumed
and the consumption function has slope exactly `1 + r`. Below, wherever it saves strictly more,
the slope is strictly less. Increments therefore RISE across the kink, which concavity forbids.
`not_concaveOn_consumptionFn_of_cap_binds` proves it.

So `hT` as stated is not merely hard, it is FALSE for any calibration whose cap binds, quite
apart from the HARA question. Concavity of the consumption function on the asset region needs the
cap to be SLACK — above the natural asset bound, so that the household never wants to save that
much. That is exactly what `exists_decline_of_consumption_lower_bound` is about, and by
`one_sub_mpc_mul_of_asymptotic` the condition behind it is `β (1 + r) < 1`.

Which ties the two halves of the development together: the imposed `assetCap`, so far a
bookkeeping device for compactness, has to be justified economically before the Carroll–Kimball
hypothesis can even be true. -/

/-- Once the cap binds it binds for ever after, since the policy is monotone and capped. -/
theorem policy_eq_assetCap_of_le {y w : ℝ} {z : Z} (hy : y ∈ Icc assetFloor assetCap)
    (hw : w ∈ Icc assetFloor assetCap) (hyw : y ≤ w) (h : P.policy (y, z) = assetCap) :
    P.policy (w, z) = assetCap := by
  exact le_antisymm (P.policy_mem_region _).2
    (le_trans (le_of_eq h.symm) (P.policy_mono hy hw hyw))

/-- **A binding asset cap rules out a concave consumption function.** -/
theorem not_concaveOn_consumptionFn_of_cap_binds {x y w : ℝ} {z : Z}
    (hx : x ∈ Icc assetFloor assetCap) (hw : w ∈ Icc assetFloor assetCap)
    (hxy : x < y) (hyw : y < w)
    (hrise : P.policy (x, z) < P.policy (y, z))
    (hflat : P.policy (y, z) = P.policy (w, z)) :
    ¬ ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) := by
  intro hconc
  have hy : y ∈ Icc assetFloor assetCap := ⟨le_trans hx.1 hxy.le, le_trans hyw.le hw.2⟩
  have h := hconc.slope_anti_adjacent hx hw hxy hyw
  have hres : ∀ a ∈ Icc assetFloor assetCap,
      P.resources (a, z) = P.income z + (1 + P.interest) * a :=
    fun a ha => by simp only [resources, max_eq_right ha.1]
  simp only [consumptionFn, consumption, hres x hx, hres y hy, hres w hw] at h
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at h
  nlinarith [h, hrise, hflat, sub_pos.mpr hxy, sub_pos.mpr hyw]

end IncomeFluctuation

end LeanEconomics
