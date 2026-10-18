/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuation
public import LeanPool.AiyagariEquilibrium.Analysis.DifferentiableSandwich
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# The lazy agent's value, and the envelope condition

Clausen and Strub's construction: to show the value function is differentiable in assets,
exhibit a differentiable LOWER bound touching it. Freeze the optimal saving and vary the
state — the "lazy" agent, who meets an unfamiliar state by making the choice that was optimal
at a familiar one.

The point is structural. Once the saving is frozen, current assets enter the objective ONLY
through the reward, because the continuation value depends on the saving chosen and on the
current income state, never on current assets. So the lazy value is `u` composed with an
affine map plus a constant, and is differentiable wherever `u` is.

Concavity of the value function, already proved, then supplies the upper half of the sandwich
via `ConcaveOn.hasDerivAt_of_lowerBound`, and the derivative is the envelope condition

  V'(a) = (1 + r) · u'(c),

which is the expression Light (2018) Theorem 1 is built on.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **The lazy agent's value.** The saving `a'` is frozen; only current assets vary. -/
noncomputable def lazyValue (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (a' a : ℝ) : ℝ :=
  P.u (P.resources (a, z) - a')
    + P.discount * ∑ z' : Z, P.transitionMatrix z z' * v (a', z')

/-- Resources are affine in assets above the borrowing constraint. -/
theorem hasDerivAt_resources {z : Z} {a : ℝ} (ha : assetFloor < a) :
    HasDerivAt (fun x => P.resources (x, z)) (1 + P.interest) a := by
  have heq : (fun x => P.resources (x, z)) =ᶠ[𝓝 a] fun x => P.income z + (1 + P.interest) * x := by
    filter_upwards [lt_mem_nhds ha] with x hx
    simp only [resources, max_eq_right hx.le]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  simpa using ((hasDerivAt_id a).const_mul (1 + P.interest)).const_add (P.income z)

/-- **The lazy value is differentiable**, because current assets enter only through the
reward once the saving is frozen. -/
theorem hasDerivAt_lazyValue (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (a' : ℝ) {a du : ℝ}
    (ha : assetFloor < a)
    (hu : HasDerivAt P.u du (P.resources (a, z) - a')) :
    HasDerivAt (P.lazyValue v z a') ((1 + P.interest) * du) a := by
  have hinner : HasDerivAt (fun x => P.resources (x, z) - a') (1 + P.interest) a :=
    (P.hasDerivAt_resources ha).sub_const a'
  have hcomp : HasDerivAt (fun x => P.u (P.resources (x, z) - a'))
      (du * (1 + P.interest)) a := hu.comp a hinner
  have hsum := hcomp.add_const
    ((P.discount : ℝ) * ∑ z' : Z, P.transitionMatrix z z' * v (a', z'))
  rw [mul_comm du (1 + P.interest)] at hsum
  exact hsum

/-- **The lazy value is a lower bound**: freezing a feasible saving can only do worse than
optimising. Stated on the utility DOMAIN, so that it survives the bounded family, where zero
consumption is admissible and positivity has to be earned. -/
theorem lazyValue_le_dom (v : (ℝ × Z) →ᵇ ℝ) (z : Z) {a' a : ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hmem : a' ∈ P.toExtended.feasible (a, z)) (hc : P.consumption (a, z) a' ∈ P.dom) :
    P.lazyValue v z a' a ≤ P.toExtended.bellmanFn v (a, z) := by
  have hobj := P.toExtended.le_bellmanFn v hmem
  have hrw := P.reward_eq_coe_dom (s := (a, z)) ha hmem hc
  have hdx : (P.toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  rw [ExtendedStochasticProgram.objectiveE, hrw, hdx, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at hobj
  exact hobj

theorem lazyValue_le (v : (ℝ × Z) →ᵇ ℝ) (z : Z) {a' a : ℝ} (ha : a ∈ Icc assetFloor assetCap)
    (hmem : a' ∈ P.toExtended.feasible (a, z)) (hc : 0 < P.consumption (a, z) a') :
    P.lazyValue v z a' a ≤ P.toExtended.bellmanFn v (a, z) :=
  P.lazyValue_le_dom v z ha hmem (P.mem_dom_of_pos hc)

/-- At the optimum the lazy value touches the Bellman value. -/
theorem lazyValue_eq_dom (v : (ℝ × Z) →ᵇ ℝ) (z : Z) {a' a : ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hmem : a' ∈ P.toExtended.feasible (a, z)) (hc : P.consumption (a, z) a' ∈ P.dom)
    (hopt : P.toExtended.objectiveE v (a, z) a'
      = ((P.toExtended.bellmanFn v (a, z) : ℝ) : EReal)) :
    P.lazyValue v z a' a = P.toExtended.bellmanFn v (a, z) := by
  have hrw := P.reward_eq_coe_dom (s := (a, z)) ha hmem hc
  have hdx : (P.toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  rw [ExtendedStochasticProgram.objectiveE, hrw, hdx, ← EReal.coe_add,
    EReal.coe_eq_coe_iff] at hopt
  exact hopt

theorem lazyValue_eq (v : (ℝ × Z) →ᵇ ℝ) (z : Z) {a' a : ℝ} (ha : a ∈ Icc assetFloor assetCap)
    (hmem : a' ∈ P.toExtended.feasible (a, z)) (hc : 0 < P.consumption (a, z) a')
    (hopt : P.toExtended.objectiveE v (a, z) a'
      = ((P.toExtended.bellmanFn v (a, z) : ℝ) : EReal)) :
    P.lazyValue v z a' a = P.toExtended.bellmanFn v (a, z) :=
  P.lazyValue_eq_dom v z ha hmem (P.mem_dom_of_pos hc) hopt

/-! ### The envelope theorem

Concavity supplies the upper half of the sandwich, the lazy agent the lower half. The only
work is the neighbourhood: the frozen saving is feasible at the state it came from, but at
poorer states it need not be, so the lower bound is only local. Continuity of the feasible
boundary gives an interval on which it survives, provided the saving is interior there. -/

/-- **The envelope condition for `bellman v`.** The marginal value of assets is the gross
interest rate times the marginal utility of the consumption the household actually chooses.
Clausen and Strub's sandwich, run one step of the iteration at a time rather than at the fixed
point. -/
theorem hasDerivAt_bellman_of_optimal {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a a' du : ℝ}
    (ha : assetFloor < a) (hacap : a < assetCap)
    (hconc : ConcaveOn ℝ (Icc assetFloor assetCap) fun x => (P.toExtended.bellman v) (x, z))
    (ha'mem : a' ∈ P.toExtended.feasible (a, z))
    (hopt : P.toExtended.objectiveE v (a, z) a'
      = ((P.toExtended.bellmanFn v (a, z) : ℝ) : EReal))
    (hint : a' < P.maxSaving (a, z))
    (hc : 0 < P.consumption (a, z) a')
    (hu : HasDerivAt P.u du (P.consumption (a, z) a')) :
    HasDerivAt (fun x => (P.toExtended.bellman v) (x, z)) ((1 + P.interest) * du) a := by
  have hamem : ((a, z) : ℝ × Z).1 ∈ Icc assetFloor assetCap := ⟨ha.le, hacap.le⟩
  have ha'0 : assetFloor ≤ a' := ha'mem.1
  have hba : ∀ x : ℝ, P.toExtended.bellmanFn v (x, z) = (P.toExtended.bellman v) (x, z) :=
    fun x => by rw [← P.toExtended.bellman_apply]
  -- the frozen saving stays feasible, and consumption stays positive, near `a`
  have hcms : ContinuousAt (fun x => P.maxSaving (x, z)) a :=
    (P.continuous_maxSaving.comp (continuous_id.prodMk continuous_const)).continuousAt
  have hccon : ContinuousAt (fun x => P.consumption (x, z) a') a :=
    ((P.continuous_resources.comp (continuous_id.prodMk continuous_const)).sub
      continuous_const).continuousAt
  have hev : {x : ℝ | assetFloor < x ∧ x < assetCap ∧ a' < P.maxSaving (x, z)
      ∧ 0 < P.consumption (x, z) a'} ∈ 𝓝 a := by
    have h1 : ∀ᶠ x in 𝓝 a, assetFloor < x := lt_mem_nhds ha
    have h2 : ∀ᶠ x in 𝓝 a, x < assetCap := gt_mem_nhds hacap
    have h3 : ∀ᶠ x in 𝓝 a, a' < P.maxSaving (x, z) := hcms.eventually_const_lt hint
    have h4 : ∀ᶠ x in 𝓝 a, 0 < P.consumption (x, z) a' := hccon.eventually_const_lt hc
    filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4 using ⟨hx1, hx2, hx3, hx4⟩
  obtain ⟨l, r, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  have hIsub : Ioo l r ⊆ Icc assetFloor assetCap := fun x hx =>
    ⟨(hsub hx).1.le, (hsub hx).2.1.le⟩
  have hlow : ∀ x ∈ Ioo l r, P.lazyValue v z a' x ≤ (P.toExtended.bellman v) (x, z) := by
    intro x hx
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hsub hx
    have hfe : a' ∈ P.toExtended.feasible (x, z) := ⟨ha'0, hx3.le⟩
    have := P.lazyValue_le v z ⟨hx1.le, hx2.le⟩ hfe hx4
    rwa [hba x] at this
  have htouch : P.lazyValue v z a' a = (P.toExtended.bellman v) (a, z) := by
    have hfe : a' ∈ P.toExtended.feasible (a, z) := ha'mem
    have := P.lazyValue_eq v z hamem hfe hc hopt
    rwa [hba a] at this
  refine (hconc.subset hIsub (convex_Ioo l r)).hasDerivAt_of_lowerBound hmem
    (Ioo_mem_nhds hmem.1 hmem.2)
    ⟨(l + a) / 2, ⟨by linarith [hmem.1, hmem.2], by linarith [hmem.1, hmem.2]⟩,
      by linarith [hmem.1, hmem.2]⟩
    ⟨(a + r) / 2, ⟨by linarith [hmem.1, hmem.2], by linarith [hmem.1, hmem.2]⟩,
      by linarith [hmem.1, hmem.2]⟩
    hlow htouch (P.hasDerivAt_lazyValue v z a' ha hu)

theorem hasDerivAt_valueFunction (hpc : P.PositiveConsumption) {z : Z} {a du : ℝ}
    (ha : assetFloor < a) (hacap : a < assetCap)
    (hconc : ConcaveOn ℝ (Icc assetFloor assetCap)
      fun x => P.toExtended.valueFunction (x, z))
    (hint : P.policy (a, z) < P.maxSaving (a, z))
    (hu : HasDerivAt P.u du (P.resources (a, z) - P.policy (a, z))) :
    HasDerivAt (fun x => P.toExtended.valueFunction (x, z)) ((1 + P.interest) * du) a := by
  simpa only [P.toExtended.bellman_valueFunction] using
    P.hasDerivAt_bellman_of_optimal ha hacap
      (by simpa only [P.toExtended.bellman_valueFunction] using hconc)
      (P.policy_mem (a, z)) (P.policy_optimal (a, z)) hint
      (P.consumption_policy_pos hpc ⟨ha.le, hacap.le⟩) hu

/-! ### At the borrowing constraint

The sandwich does NOT extend to the left endpoint, and the failure is not technical. Its first
step is that `U - L` has a local minimum where the bounds touch, forcing the two derivatives to
agree; at an endpoint a minimum gives only `d' ≥ 0`, so the upper bound may be strictly
steeper and the derivative is not pinned.

The right-derivative at the constraint is instead obtained as a LIMIT of the interior
derivatives, using that a derivative extends continuously to an endpoint
(`hasDerivWithinAt_Ici_of_tendsto_deriv`). This matters because `a = 0` is precisely the atom
the whole ergodic argument runs on, so a statement that stops short of it would stop short of
the states that carry the stationary distribution. -/

theorem hasDerivWithinAt_valueFunction_Ici {z : Z} {g : ℝ → ℝ} {e b : ℝ} (hb : 0 < b)
    (hderiv : ∀ x ∈ Ioo (0 : ℝ) b,
      HasDerivAt (fun y => P.toExtended.valueFunction (y, z)) (g x) x)
    (hlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 e)) :
    HasDerivWithinAt (fun y => P.toExtended.valueFunction (y, z)) e (Ici 0) 0 := by
  have hmem : Ioo (0 : ℝ) b ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hb
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 b) ?_ ?_ hmem ?_
  · exact fun x hx => ((hderiv x hx).differentiableAt).differentiableWithinAt
  · exact (P.toExtended.valueFunction.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousWithinAt
  · refine hlim.congr' ?_
    filter_upwards [hmem] with x hx
    exact ((hderiv x hx).deriv).symm

end IncomeFluctuation

end LeanEconomics
