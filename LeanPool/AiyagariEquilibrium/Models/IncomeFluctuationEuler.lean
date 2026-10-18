/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationEnvelope
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationCarrollKimball
public import LeanPool.AiyagariEquilibrium.Models.CRRA

/-!
# The Euler equation along the iteration, and the borrowing limit

Carroll and Kimball's induction runs along the ITERATES `Tⁿ 0`, so everything it needs must hold
one step of the iteration at a time, and at states where the borrowing limit BINDS.

## The envelope condition

`hasDerivAt_bellman` is Clausen and Strub's theorem for `bellman v` rather than for the fixed
point. Nothing in the lazy-agent argument used the fixed point: freezing a feasible saving and
varying current assets gives a differentiable lower bound touching `bellman v` at the optimum,
and concavity of the slice supplies the upper half of the sandwich. `euler_of_interior` reads
the first-order condition off it.

## But the Euler equation does not need it

The same freezing trick gives BOTH one-sided bounds on the marginal value of assets — carry the
poorer household's plan forward (`bellman_sub_ge`), or the richer household's plan back
(`bellman_sub_le`) — and those are enough. Comparing the optimum with a deviation of size `ε`
and letting `ε` shrink gives

* `euler_le`, from saving MORE, which is feasible unless the household already saves the
  maximum, and
* `euler_ge`, from saving LESS, which is feasible unless the household is at the borrowing
  limit;

and `euler_eq` is the two together. No envelope theorem, no second derivative: only that `u` is
differentiable at the consumptions concerned.

## The borrowing limit

That asymmetry is the whole point. At the limit `euler_ge` fails and the first-order condition
degenerates to the inequality `euler_le`, which in endogenous-gridpoint form says consumption is
at most `egmMap` (`egmMap_ge`). `concaveOn_of_egm_corner` shows that is enough: at a constrained
state the saving is `assetFloor`, which lies below ANY average of savings, and that is the only
thing the transfer of `IncomeFluctuationCarrollKimball` ever needed. So the kink costs nothing,
and `concaveOn_consumptionFnOf_bellman` is Carroll and Kimball's induction step with the
borrowing limit allowed to bind anywhere.

What it still assumes is that the asset CAP is slack — a different condition, discharged by
calibration in `crra_policy_lt_assetCap` — and the induction hypotheses on the continuation's
consumption function.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### The envelope condition for an iterate -/

/-- **The envelope condition for `bellman v`.** The marginal value of assets is the gross
interest rate times the marginal utility of the consumption the household actually chooses.
Clausen and Strub's sandwich, run one step of the iteration at a time rather than at the fixed
point. -/
theorem hasDerivAt_bellman {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a du : ℝ}
    (ha : assetFloor < a) (hacap : a < assetCap)
    (hconc : ConcaveOn ℝ (Icc assetFloor assetCap) fun x => (P.toExtended.bellman v) (x, z))
    (hint : P.policyOf v (a, z) < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf v z a)
    (hu : HasDerivAt P.u du (P.consumptionFnOf v z a)) :
    HasDerivAt (fun x => (P.toExtended.bellman v) (x, z)) ((1 + P.interest) * du) a := by
  set a' := P.policyOf v (a, z) with ha'
  have hamem : ((a, z) : ℝ × Z).1 ∈ Icc assetFloor assetCap := ⟨ha.le, hacap.le⟩
  have ha'0 : assetFloor ≤ a' := (P.policyOf_mem v (a, z)).1
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
    have hfe : a' ∈ P.toExtended.feasible (a, z) := P.policyOf_mem v (a, z)
    have := P.lazyValue_eq v z hamem hfe hc (P.policyOf_optimal v (a, z))
    rwa [hba a] at this
  refine (hconc.subset hIsub (convex_Ioo l r)).hasDerivAt_of_lowerBound hmem
    (Ioo_mem_nhds hmem.1 hmem.2)
    ⟨(l + a) / 2, ⟨by linarith [hmem.1, hmem.2], by linarith [hmem.1, hmem.2]⟩,
      by linarith [hmem.1, hmem.2]⟩
    ⟨(a + r) / 2, ⟨by linarith [hmem.1, hmem.2], by linarith [hmem.1, hmem.2]⟩,
      by linarith [hmem.1, hmem.2]⟩
    hlow htouch (P.hasDerivAt_lazyValue v z a' ha hu)

/-! ### The two lazy bounds on the marginal value of assets

Both directions come from the same trick: carry a plan that was optimal at one asset level over
to another. Neither needs the envelope theorem, and neither needs the borrowing limit to be
slack. -/

/-- **The poorer household's plan, carried forward.** The generalisation of
`valueFunction_sub_ge` to one step of the iteration. -/
theorem bellman_sub_ge {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {x y : ℝ}
    (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap) (hxy : x ≤ y)
    (hc : 0 < P.consumptionFnOf v z x) :
    P.u (P.consumptionFnOf v z x + (1 + P.interest) * (y - x)) - P.u (P.consumptionFnOf v z x)
      ≤ (P.toExtended.bellman v) (y, z) - (P.toExtended.bellman v) (x, z) := by
  set b := P.policyOf v (x, z) with hb
  have hbm : b ∈ P.toExtended.feasible (x, z) := P.policyOf_mem v (x, z)
  have hbm' : b ∈ P.toExtended.feasible (y, z) := P.feasible_mono hxy hbm
  have hres : P.resources (y, z) = P.resources (x, z) + (1 + P.interest) * (y - x) := by
    simp only [resources, max_eq_right hx.1, max_eq_right hy.1]; ring
  have hch : P.consumption (y, z) b
      = P.consumptionFnOf v z x + (1 + P.interest) * (1 * (y - x)) := by
    simp only [consumptionFnOf, consumption, hres, ← hb]; ring
  have hchpos : 0 < P.consumption (y, z) b := by
    rw [hch]
    have : (0 : ℝ) ≤ (1 + P.interest) * (1 * (y - x)) :=
      mul_nonneg P.interest_gt_neg_one.le (by linarith)
    linarith
  have hle := P.lazyValue_le v z hy hbm' hchpos
  have heq := P.lazyValue_eq v z hx hbm hc (P.policyOf_optimal v (x, z))
  have hba : ∀ t : ℝ, P.toExtended.bellmanFn v (t, z) = (P.toExtended.bellman v) (t, z) :=
    fun t => by rw [← P.toExtended.bellman_apply]
  rw [hba y] at hle
  rw [hba x] at heq
  simp only [lazyValue] at hle heq
  have hcx : P.resources (x, z) - b = P.consumptionFnOf v z x := rfl
  have hcy : P.resources (y, z) - b
      = P.consumptionFnOf v z x + (1 + P.interest) * (y - x) := by
    simp only [← hcx, hres]; ring
  rw [hcy] at hle
  rw [hcx] at heq
  linarith

/-- **The richer household's plan, carried back.** Feasible only if the richer plan is still
affordable at the poorer state, which is what `hfe` says. -/
theorem bellman_sub_le {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {x y : ℝ}
    (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap)
    (hfe : P.policyOf v (y, z) ≤ P.maxSaving (x, z))
    (hcx : 0 < P.consumptionFnOf v z y - (1 + P.interest) * (y - x))
    (hc : 0 < P.consumptionFnOf v z y) :
    (P.toExtended.bellman v) (y, z) - (P.toExtended.bellman v) (x, z)
      ≤ P.u (P.consumptionFnOf v z y)
        - P.u (P.consumptionFnOf v z y - (1 + P.interest) * (y - x)) := by
  set b := P.policyOf v (y, z) with hb
  have hbm : b ∈ P.toExtended.feasible (y, z) := P.policyOf_mem v (y, z)
  have hbm' : b ∈ P.toExtended.feasible (x, z) := ⟨hbm.1, hfe⟩
  have hres : P.resources (y, z) = P.resources (x, z) + (1 + P.interest) * (y - x) := by
    simp only [resources, max_eq_right hx.1, max_eq_right hy.1]; ring
  have hcy : P.resources (y, z) - b = P.consumptionFnOf v z y := rfl
  have hcxv : P.resources (x, z) - b
      = P.consumptionFnOf v z y - (1 + P.interest) * (y - x) := by
    simp only [← hcy, hres]; ring
  have hcpos : 0 < P.consumption (x, z) b := by
    simp only [consumption, hcxv]; exact hcx
  have hle := P.lazyValue_le v z hx hbm' hcpos
  have heq := P.lazyValue_eq v z hy hbm hc (P.policyOf_optimal v (y, z))
  have hba : ∀ t : ℝ, P.toExtended.bellmanFn v (t, z) = (P.toExtended.bellman v) (t, z) :=
    fun t => by rw [← P.toExtended.bellman_apply]
  rw [hba x] at hle
  rw [hba y] at heq
  simp only [lazyValue] at hle heq
  rw [hcxv] at hle
  rw [hcy] at heq
  linarith

/-! ### The Euler inequality, which survives the borrowing limit

Saving MORE is feasible whenever the household is not already saving the maximum, and that has
nothing to do with the borrowing limit. So this half of the first-order condition holds at the
corner too, and it is the half the concavity argument needs there. -/

/-- **The Euler inequality.** Marginal utility today is at least the discounted, interest-
augmented expected marginal utility tomorrow. The only interiority is `hAmax`: the household
could save a little more. -/
theorem euler_le {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A du : ℝ} {du' : Z → ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hAmax : A < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hu : HasDerivAt P.u du (P.consumptionFnOf (P.toExtended.bellman v) z a))
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A)
    (hu' : ∀ z' : Z, HasDerivAt P.u (du' z') (P.consumptionFnOf v z' A)) :
    (P.discount : ℝ) * ((1 + P.interest) * ∑ z' : Z, P.transitionMatrix z z' * du' z')
      ≤ du := by
  subst hA
  set W := P.toExtended.bellman v with hWdef
  set A := P.policyOf W (a, z) with hAdef
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hAmem : A ∈ Icc assetFloor assetCap :=
    P.feasible_subset_region (P.policyOf_mem W (a, z))
  set c := P.consumptionFnOf W z a with hcdef
  have hcA : c = P.resources (a, z) - A := rfl
  set D : ℝ := du - (P.discount : ℝ)
    * ((1 + P.interest) * ∑ z' : Z, P.transitionMatrix z z' * du' z') with hDdef
  set F : ℝ → ℝ := fun ε => (P.u c - P.u (c - ε))
    - (P.discount : ℝ) * ∑ z' : Z, P.transitionMatrix z z'
        * (P.u (P.consumptionFnOf v z' A + (1 + P.interest) * ε)
            - P.u (P.consumptionFnOf v z' A)) with hFdef
  have hF0 : F 0 = 0 := by simp [hFdef]
  -- `F` is differentiable at zero, with derivative the Euler gap
  have hd1 : HasDerivAt (fun ε : ℝ => P.u c - P.u (c - ε)) du 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => c - ε) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub c
    have h2 : HasDerivAt (fun ε : ℝ => P.u (c - ε)) (du * (-1)) 0 :=
      HasDerivAt.comp (0 : ℝ) (by simpa using hu) h1
    simpa using h2.const_sub (P.u c)
  have hd2 : ∀ z' : Z, HasDerivAt
      (fun ε : ℝ => P.u (P.consumptionFnOf v z' A + (1 + P.interest) * ε)
        - P.u (P.consumptionFnOf v z' A)) (du' z' * (1 + P.interest)) 0 := by
    intro z'
    have h1 : HasDerivAt (fun ε : ℝ => P.consumptionFnOf v z' A + (1 + P.interest) * ε)
        (1 + P.interest) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + P.interest)).const_add
        (P.consumptionFnOf v z' A)
    have h2 := HasDerivAt.comp (0 : ℝ) (by simpa using hu' z') h1
    simpa using h2.sub_const (P.u (P.consumptionFnOf v z' A))
  have hFd : HasDerivAt F D 0 := by
    have hsum : HasDerivAt (fun ε : ℝ => ∑ z' : Z, P.transitionMatrix z z'
        * (P.u (P.consumptionFnOf v z' A + (1 + P.interest) * ε)
            - P.u (P.consumptionFnOf v z' A)))
        (∑ z' : Z, P.transitionMatrix z z' * (du' z' * (1 + P.interest))) 0 :=
      HasDerivAt.fun_sum fun z' _ => (hd2 z').const_mul _
    have hcomm : (1 + P.interest) * ∑ z' : Z, P.transitionMatrix z z' * du' z'
        = ∑ z' : Z, P.transitionMatrix z z' * (du' z' * (1 + P.interest)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z' _ => by ring
    rw [hDdef, hcomm]
    exact hd1.sub (hsum.const_mul (P.discount : ℝ))
  -- and it is non-negative to the right of zero, because saving more is not profitable
  have hFnn : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ F ε := by
    have hδ : 0 < min (P.maxSaving (a, z) - A) c := lt_min (by linarith) hc
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    have hε0 : 0 < ε := hε.1
    have hε1 : ε < P.maxSaving (a, z) - A := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hε2 : ε < c := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hAe : A + ε ∈ Icc assetFloor assetCap :=
      ⟨by linarith [hAmem.1], by linarith [P.maxSaving_le_assetCap (a, z)]⟩
    have hfeas : A + ε ∈ P.toExtended.feasible (a, z) :=
      ⟨by linarith [hAmem.1], by linarith⟩
    have hcpos : 0 < P.consumption (a, z) (A + ε) := by
      simp only [consumption]; rw [hcA] at hε2; linarith
    have hle := P.lazyValue_le W z ha hfeas hcpos
    have heq := P.lazyValue_eq W z ha (P.policyOf_mem W (a, z)) hc
      (P.policyOf_optimal W (a, z))
    have hstep : P.lazyValue W z (A + ε) a ≤ P.lazyValue W z A a := by rw [heq]; exact hle
    simp only [lazyValue] at hstep
    rw [show P.resources (a, z) - (A + ε) = c - ε from by rw [hcA]; ring,
      show P.resources (a, z) - A = c from hcA.symm] at hstep
    have hgain : ∀ z' : Z,
        P.u (P.consumptionFnOf v z' A + (1 + P.interest) * ε)
          - P.u (P.consumptionFnOf v z' A) ≤ W (A + ε, z') - W (A, z') := by
      intro z'
      have hg := P.bellman_sub_ge (z := z') hAmem hAe (by linarith) (hc' z')
      rwa [show A + ε - A = ε from by ring] at hg
    have hsum := Finset.sum_le_sum fun z' (_ : z' ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hgain z') (P.transitionMatrix_nonneg z z')
    have hsplit : ∑ z' : Z, P.transitionMatrix z z' * (W (A + ε, z') - W (A, z'))
        = (∑ z' : Z, P.transitionMatrix z z' * W (A + ε, z'))
          - ∑ z' : Z, P.transitionMatrix z z' * W (A, z') := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun z' _ => by ring
    have hb1 := mul_le_mul_of_nonneg_left hsum hβ
    rw [hsplit] at hb1
    simp only [hFdef]
    linarith
  -- a differentiable function that is zero at zero and non-negative to the right of it has a
  -- non-negative derivative
  have hmono : Tendsto (slope F 0) (𝓝[>] (0 : ℝ)) (𝓝 D) :=
    (hasDerivAt_iff_tendsto_slope.mp hFd).mono_left
      (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have hnn : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ slope F 0 ε := by
    filter_upwards [hFnn, self_mem_nhdsWithin] with ε hFe hε0
    rw [slope_def_field, hF0, sub_zero, sub_zero]
    exact div_nonneg hFe (le_of_lt hε0)
  have hD : 0 ≤ D := ge_of_tendsto hmono hnn
  rw [hDdef] at hD
  linarith

/-! ### The first-order condition

With the envelope available at the saving actually chosen, the objective is differentiable in
the saving, the choice is a local maximum, and the derivative vanishes. That is the Euler
equation: the marginal utility of consuming now equals the discounted, interest-augmented
expected marginal utility of consuming next period. -/

/-- **The Euler equation along the iteration.** Every hypothesis is an interiority or
differentiability condition at the single state `(a, z)` and at the saving it chooses; nothing
is assumed globally. -/
theorem euler_of_interior {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A du : ℝ} {du' : Z → ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hA0 : assetFloor < A) (hAcap : A < assetCap) (hAmax : A < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hu : HasDerivAt P.u du (P.consumptionFnOf (P.toExtended.bellman v) z a))
    (hconc : ∀ z' : Z, ConcaveOn ℝ (Icc assetFloor assetCap)
      fun x => (P.toExtended.bellman v) (x, z'))
    (hint' : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z'))
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A)
    (hu' : ∀ z' : Z, HasDerivAt P.u (du' z') (P.consumptionFnOf v z' A)) :
    du = (P.discount : ℝ) * ((1 + P.interest) * ∑ z', P.transitionMatrix z z' * du' z') := by
  subst hA
  set W := P.toExtended.bellman v with hWdef
  set A := P.policyOf W (a, z) with hAdef
  have hcA : P.consumptionFnOf W z a = P.resources (a, z) - A := rfl
  -- the continuation is differentiable in the saving, by the envelope one step on
  have hWderiv : ∀ z' : Z, HasDerivAt (fun x => W (x, z')) ((1 + P.interest) * du' z') A :=
    fun z' => P.hasDerivAt_bellman hA0 hAcap (hconc z') (hint' z') (hc' z') (hu' z')
  have hsum : HasDerivAt (fun x => ∑ z' : Z, P.transitionMatrix z z' * W (x, z'))
      (∑ z' : Z, P.transitionMatrix z z' * ((1 + P.interest) * du' z')) A :=
    HasDerivAt.fun_sum fun z' _ => (hWderiv z').const_mul _
  -- and so is the reward
  have hres : HasDerivAt (fun x : ℝ => P.resources (a, z) - x) (-1) A := by
    simpa using (hasDerivAt_id A).const_sub (P.resources (a, z))
  have hrew : HasDerivAt (fun x => P.u (P.resources (a, z) - x)) (du * (-1)) A :=
    HasDerivAt.comp A (hcA ▸ hu) hres
  have hΦ : HasDerivAt (fun x => P.lazyValue W z x a)
      (du * (-1) + (P.discount : ℝ)
        * ∑ z' : Z, P.transitionMatrix z z' * ((1 + P.interest) * du' z')) A :=
    hrew.add (hsum.const_mul (P.discount : ℝ))
  -- the chosen saving is a local maximum of the objective
  have hlm : IsLocalMax (fun x => P.lazyValue W z x a) A := by
    have hcont : ContinuousAt (fun x : ℝ => P.resources (a, z) - x) A :=
      (continuous_const.sub continuous_id).continuousAt
    have h1 : ∀ᶠ x in 𝓝 A, assetFloor < x := lt_mem_nhds hA0
    have h2 : ∀ᶠ x in 𝓝 A, x < P.maxSaving (a, z) := gt_mem_nhds hAmax
    have hcpos : (0 : ℝ) < P.resources (a, z) - A := by rw [← hcA]; exact hc
    have h3 : ∀ᶠ x in 𝓝 A, 0 < P.resources (a, z) - x := hcont.eventually_const_lt hcpos
    have hAopt : P.lazyValue W z A a = P.toExtended.bellmanFn W (a, z) :=
      P.lazyValue_eq W z ha (P.policyOf_mem W (a, z)) hc (P.policyOf_optimal W (a, z))
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [hAopt]
    exact P.lazyValue_le W z ha ⟨hx1.le, hx2.le⟩ hx3
  -- so the derivative vanishes, which is the Euler equation
  have hzero := hlm.hasDerivAt_eq_zero hΦ
  have hfac : ∑ z' : Z, P.transitionMatrix z z' * ((1 + P.interest) * du' z')
      = (1 + P.interest) * ∑ z' : Z, P.transitionMatrix z z' * du' z' := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z' _ => by ring
  rw [hfac] at hzero
  linarith

/-- **The reverse Euler inequality.** Saving LESS is feasible only away from the borrowing
limit, which is why this half fails at the corner. Like `euler_le` it uses only the two lazy
bounds: the envelope theorem is not needed for the Euler equation. -/
theorem euler_ge {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A du : ℝ} {du' : Z → ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hA0 : assetFloor < A)
    (hslack : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z'))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hu : HasDerivAt P.u du (P.consumptionFnOf (P.toExtended.bellman v) z a))
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A)
    (hu' : ∀ z' : Z, HasDerivAt P.u (du' z') (P.consumptionFnOf v z' A)) :
    du ≤ (P.discount : ℝ)
      * ((1 + P.interest) * ∑ z' : Z, P.transitionMatrix z z' * du' z') := by
  subst hA
  set W := P.toExtended.bellman v with hWdef
  set A := P.policyOf W (a, z) with hAdef
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hAmem : A ∈ Icc assetFloor assetCap :=
    P.feasible_subset_region (P.policyOf_mem W (a, z))
  set c := P.consumptionFnOf W z a with hcdef
  have hcA : c = P.resources (a, z) - A := rfl
  set D : ℝ := (P.discount : ℝ)
    * ((1 + P.interest) * ∑ z' : Z, P.transitionMatrix z z' * du' z') - du with hDdef
  set G : ℝ → ℝ := fun ε => (P.discount : ℝ) * ∑ z' : Z, P.transitionMatrix z z'
      * (P.u (P.consumptionFnOf v z' A)
          - P.u (P.consumptionFnOf v z' A - (1 + P.interest) * ε))
    - (P.u (c + ε) - P.u c) with hGdef
  have hG0 : G 0 = 0 := by simp [hGdef]
  -- the derivative at zero is the Euler gap, with the sign reversed
  have hd1 : HasDerivAt (fun ε : ℝ => P.u (c + ε) - P.u c) du 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => c + ε) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add c
    have h2 : HasDerivAt (fun ε : ℝ => P.u (c + ε)) (du * 1) 0 :=
      HasDerivAt.comp (0 : ℝ) (by simpa using hu) h1
    simpa using h2.sub_const (P.u c)
  have hd2 : ∀ z' : Z, HasDerivAt
      (fun ε : ℝ => P.u (P.consumptionFnOf v z' A)
        - P.u (P.consumptionFnOf v z' A - (1 + P.interest) * ε))
      (du' z' * (1 + P.interest)) 0 := by
    intro z'
    have h1 : HasDerivAt (fun ε : ℝ => P.consumptionFnOf v z' A - (1 + P.interest) * ε)
        (-(1 + P.interest)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + P.interest)).const_sub
        (P.consumptionFnOf v z' A)
    have h2 := HasDerivAt.comp (0 : ℝ) (by simpa using hu' z') h1
    have h3 := h2.const_sub (P.u (P.consumptionFnOf v z' A))
    have hrw : -(du' z' * -(1 + P.interest)) = du' z' * (1 + P.interest) := by ring
    rwa [hrw] at h3
  have hGd : HasDerivAt G D 0 := by
    have hsum : HasDerivAt (fun ε : ℝ => ∑ z' : Z, P.transitionMatrix z z'
        * (P.u (P.consumptionFnOf v z' A)
            - P.u (P.consumptionFnOf v z' A - (1 + P.interest) * ε)))
        (∑ z' : Z, P.transitionMatrix z z' * (du' z' * (1 + P.interest))) 0 :=
      HasDerivAt.fun_sum fun z' _ => (hd2 z').const_mul _
    have hcomm : (1 + P.interest) * ∑ z' : Z, P.transitionMatrix z z' * du' z'
        = ∑ z' : Z, P.transitionMatrix z z' * (du' z' * (1 + P.interest)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z' _ => by ring
    rw [hDdef, hcomm]
    exact (hsum.const_mul (P.discount : ℝ)).sub hd1
  -- and it is non-negative to the right of zero, because saving less is not profitable
  have hGnn : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ G ε := by
    have hloc : ∀ z' : Z, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        P.policyOf v (A, z') ≤ P.maxSaving (A - ε, z')
          ∧ 0 < P.consumptionFnOf v z' A - (1 + P.interest) * ε := by
      intro z'
      have hcont : ContinuousAt (fun ε : ℝ => P.maxSaving (A - ε, z')) 0 :=
        (P.continuous_maxSaving.comp
          ((continuous_const.sub continuous_id).prodMk continuous_const)).continuousAt
      have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), P.policyOf v (A, z') < P.maxSaving (A - ε, z') :=
        hcont.eventually_const_lt (by simpa using hslack z')
      have hcont2 : ContinuousAt
          (fun ε : ℝ => P.consumptionFnOf v z' A - (1 + P.interest) * ε) 0 :=
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
      have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ),
          0 < P.consumptionFnOf v z' A - (1 + P.interest) * ε :=
        hcont2.eventually_const_lt (by simpa using hc' z')
      filter_upwards [(h1.filter_mono nhdsWithin_le_nhds),
        (h2.filter_mono nhdsWithin_le_nhds)] with ε he1 he2 using ⟨he1.le, he2⟩
    have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z' : Z,
        P.policyOf v (A, z') ≤ P.maxSaving (A - ε, z')
          ∧ 0 < P.consumptionFnOf v z' A - (1 + P.interest) * ε :=
      Filter.eventually_all.mpr hloc
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < A - assetFloor by linarith), hall]
      with ε hε hz'
    have hε0 : 0 < ε := hε.1
    have hε1 : ε < A - assetFloor := hε.2
    have hAe : A - ε ∈ Icc assetFloor assetCap :=
      ⟨by linarith, by linarith [hAmem.2]⟩
    have hfeas : A - ε ∈ P.toExtended.feasible (a, z) :=
      ⟨by linarith, by linarith [(P.policyOf_mem W (a, z)).2]⟩
    have hcpos : 0 < P.consumption (a, z) (A - ε) := by
      simp only [consumption]; rw [hcA] at hc; linarith
    have hle := P.lazyValue_le W z ha hfeas hcpos
    have heq := P.lazyValue_eq W z ha (P.policyOf_mem W (a, z)) hc
      (P.policyOf_optimal W (a, z))
    have hstep : P.lazyValue W z (A - ε) a ≤ P.lazyValue W z A a := by rw [heq]; exact hle
    simp only [lazyValue] at hstep
    rw [show P.resources (a, z) - (A - ε) = c + ε from by rw [hcA]; ring,
      show P.resources (a, z) - A = c from hcA.symm] at hstep
    have hloss : ∀ z' : Z, W (A, z') - W (A - ε, z')
        ≤ P.u (P.consumptionFnOf v z' A)
          - P.u (P.consumptionFnOf v z' A - (1 + P.interest) * ε) := by
      intro z'
      have hg := P.bellman_sub_le (z := z') hAe hAmem (hz' z').1
        (by have := (hz' z').2; rw [show A - (A - ε) = ε from by ring]; linarith)
        (hc' z')
      rwa [show A - (A - ε) = ε from by ring] at hg
    have hsum := Finset.sum_le_sum fun z' (_ : z' ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hloss z') (P.transitionMatrix_nonneg z z')
    have hsplit : ∑ z' : Z, P.transitionMatrix z z' * (W (A, z') - W (A - ε, z'))
        = (∑ z' : Z, P.transitionMatrix z z' * W (A, z'))
          - ∑ z' : Z, P.transitionMatrix z z' * W (A - ε, z') := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun z' _ => by ring
    have hb1 := mul_le_mul_of_nonneg_left hsum hβ
    rw [hsplit] at hb1
    simp only [hGdef]
    linarith
  have hmono : Tendsto (slope G 0) (𝓝[>] (0 : ℝ)) (𝓝 D) :=
    (hasDerivAt_iff_tendsto_slope.mp hGd).mono_left
      (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have hnn : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ slope G 0 ε := by
    filter_upwards [hGnn, self_mem_nhdsWithin] with ε hGe hε0
    rw [slope_def_field, hG0, sub_zero, sub_zero]
    exact div_nonneg hGe (le_of_lt hε0)
  have hD : 0 ≤ D := ge_of_tendsto hmono hnn
  rw [hDdef] at hD
  linarith

/-- **The Euler equation**, from the two deviations. No envelope theorem, no second
derivatives: only that `u` is differentiable at the consumptions concerned. -/
theorem euler_eq {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A du : ℝ} {du' : Z → ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hA0 : assetFloor < A) (hAmax : A < P.maxSaving (a, z))
    (hslack : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z'))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hu : HasDerivAt P.u du (P.consumptionFnOf (P.toExtended.bellman v) z a))
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A)
    (hu' : ∀ z' : Z, HasDerivAt P.u (du' z') (P.consumptionFnOf v z' A)) :
    du = (P.discount : ℝ)
      * ((1 + P.interest) * ∑ z' : Z, P.transitionMatrix z z' * du' z') :=
  le_antisymm (P.euler_ge ha hA hA0 hslack hc hu hc' hu')
    (P.euler_le ha hA hAmax hc hu hc' hu')

/-! ### CRRA: the Euler equation in endogenous-gridpoint form

With `u' c = c ^ (-γ)` the Euler equation says that consumption is a positive multiple of the
weighted power mean, exponent `-γ`, of next period's consumptions — which is exactly `egmMap`,
and exactly what `concaveOn_consumptionFnOf_bellman_of_euler` asks for. -/

theorem egm_of_euler {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A)
    (heuler : P.consumptionFnOf (P.toExtended.bellman v) z a ^ (-γ)
      = (P.discount : ℝ) * ((1 + P.interest)
        * ∑ z' : Z, P.transitionMatrix z z' * P.consumptionFnOf v z' A ^ (-γ))) :
    P.consumptionFnOf (P.toExtended.bellman v) z a = P.egmMap v γ z A := by
  have hγn : γ ≠ 0 := ne_of_gt hγ0
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hK : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hS : (0 : ℝ) < ∑ z' : Z, P.transitionMatrix z z' * P.consumptionFnOf v z' A ^ (-γ) :=
    sum_rpow_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hc'
  have hprod : P.consumptionFnOf (P.toExtended.bellman v) z a ^ (-γ)
      = ((P.discount : ℝ) * (1 + P.interest))
        * ∑ z' : Z, P.transitionMatrix z z' * P.consumptionFnOf v z' A ^ (-γ) := by
    rw [heuler]; ring
  have hexp : (-γ) * (-(1 / γ)) = 1 := by field_simp
  have hinv : (P.consumptionFnOf (P.toExtended.bellman v) z a ^ (-γ)) ^ (-(1 / γ))
      = P.consumptionFnOf (P.toExtended.bellman v) z a := by
    rw [← Real.rpow_mul hc.le, hexp, Real.rpow_one]
  rw [← hinv, hprod, Real.mul_rpow hK.le hS.le]
  simp only [egmMap, powerMean]
  congr 1
  rw [show -(1 / γ) = 1 / (-γ) by field_simp]

/-- **The hypothesis `hEuler` of `concaveOn_consumptionFnOf_bellman_of_euler`, discharged.**
Everything that remains is interiority: the saving chosen must be strictly inside the asset
region and strictly below the feasible maximum, this period and next. -/
theorem egmMap_consumptionFnOf {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hu : P.u = crraUtility γ) {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hA0 : assetFloor < A) (hAmax : A < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hint' : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z'))
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A) :
    P.consumptionFnOf (P.toExtended.bellman v) z a = P.egmMap v γ z A := by
  have hd : HasDerivAt P.u (P.consumptionFnOf (P.toExtended.bellman v) z a ^ (-γ))
      (P.consumptionFnOf (P.toExtended.bellman v) z a) := by
    rw [hu]; exact hasDerivAt_crraUtility γ hc
  have hd' : ∀ z' : Z, HasDerivAt P.u (P.consumptionFnOf v z' A ^ (-γ))
      (P.consumptionFnOf v z' A) := fun z' => by
    rw [hu]; exact hasDerivAt_crraUtility γ (hc' z')
  exact P.egm_of_euler hγ0 hβ hc hc' (P.euler_eq ha hA hA0 hAmax hint' hc hd hc' hd')

/-- The endogenous-gridpoint map, written as a single power of the Euler right-hand side. -/
theorem egmMap_eq_rpow {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {A : ℝ} (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A) :
    P.egmMap v γ z A = ((P.discount : ℝ) * (1 + P.interest)
      * ∑ z' : Z, P.transitionMatrix z z' * P.consumptionFnOf v z' A ^ (-γ)) ^ (-(1 / γ)) := by
  have hγn : γ ≠ 0 := ne_of_gt hγ0
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hK : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hS : (0 : ℝ) < ∑ z' : Z, P.transitionMatrix z z' * P.consumptionFnOf v z' A ^ (-γ) :=
    sum_rpow_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hc'
  rw [Real.mul_rpow hK.le hS.le]
  simp only [egmMap, powerMean]
  congr 1
  rw [show -(1 / γ) = 1 / (-γ) by field_simp]

/-- **The Euler inequality in endogenous-gridpoint form.** Consumption never exceeds the value
the endogenous grid assigns to the saving actually chosen — and this holds AT the borrowing
limit, where the equality fails. -/
theorem egmMap_ge {γ : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hu : P.u = crraUtility γ) {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hAmax : A < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A) :
    P.consumptionFnOf (P.toExtended.bellman v) z a ≤ P.egmMap v γ z A := by
  have hγn : γ ≠ 0 := ne_of_gt hγ0
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hK : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hS : (0 : ℝ) < ∑ z' : Z, P.transitionMatrix z z' * P.consumptionFnOf v z' A ^ (-γ) :=
    sum_rpow_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hc'
  have hd : HasDerivAt P.u (P.consumptionFnOf (P.toExtended.bellman v) z a ^ (-γ))
      (P.consumptionFnOf (P.toExtended.bellman v) z a) := by
    rw [hu]; exact hasDerivAt_crraUtility γ hc
  have hd' : ∀ z' : Z, HasDerivAt P.u (P.consumptionFnOf v z' A ^ (-γ))
      (P.consumptionFnOf v z' A) := fun z' => by
    rw [hu]; exact hasDerivAt_crraUtility γ (hc' z')
  have heuler := P.euler_le ha hA hAmax hc hd hc' hd'
  rw [P.egmMap_eq_rpow hγ0 hβ hc']
  have hKS : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest)
      * ∑ z' : Z, P.transitionMatrix z z' * P.consumptionFnOf v z' A ^ (-γ) := mul_pos hK hS
  have hstep := Real.rpow_le_rpow_of_nonpos hKS (by linarith [heuler])
    (show -(1 / γ) ≤ 0 by rw [neg_nonpos]; positivity)
  have hexp : (-γ) * (-(1 / γ)) = 1 := by field_simp
  rwa [← Real.rpow_mul hc.le, hexp, Real.rpow_one] at hstep

/-! ### The borrowing limit, and the kink it makes

Where the constraint binds the Euler equation is only an inequality, and the endogenous-gridpoint
transfer has to absorb that. It does, and the reason is short: at a constrained state the saving
is `assetFloor`, which is below ANY average of savings, so the step the transfer needs is free
there. -/

/-- **The endogenous-gridpoint transfer, with the corner.** Concavity of the consumption
function needs the Euler equation only where the borrowing limit is slack; at the limit the
inequality `hle` suffices, because the saving is then at its minimum. -/
theorem concaveOn_of_egm_corner {z : Z} {g C h : ℝ → ℝ}
    (hC : ConcaveOn ℝ (Icc assetFloor assetCap) C)
    (hM : StrictMonoOn (fun A => A + C A) (Icc assetFloor assetCap))
    (hg : ∀ a ∈ Icc assetFloor assetCap, g a ∈ Icc assetFloor assetCap)
    (hbud : ∀ a ∈ Icc assetFloor assetCap,
      P.income z + (1 + P.interest) * a = g a + h a)
    (hle : ∀ a ∈ Icc assetFloor assetCap, h a ≤ C (g a))
    (heq : ∀ a ∈ Icc assetFloor assetCap, assetFloor < g a → h a = C (g a)) :
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
  have hcomb : P.income z + (1 + P.interest) * (θ * a + φ * b)
      = (θ * g a + φ * g b) + (θ * h a + φ * h b) := by
    linear_combination θ * h1 + φ * h2 - P.income z * hθφ
  have hAle : g (θ * a + φ * b) ≤ θ * g a + φ * g b := by
    rcases eq_or_lt_of_le hAθ.1 with hcorner | hinterior
    · rw [← hcorner]
      have hsum : θ * assetFloor + φ * assetFloor = assetFloor := by
        rw [← add_mul, hθφ, one_mul]
      linarith [mul_nonneg hθ (sub_nonneg.mpr hA₁.1), mul_nonneg hφ (sub_nonneg.mpr hA₂.1)]
    · have hCc : θ * h a + φ * h b ≤ C (θ * g a + φ * g b) := by
        have hca := hle a ha
        have hcb := hle b hb
        have hmid := hC.2 hA₁ hA₂ hθ hφ hθφ
        simp only [smul_eq_mul] at hmid
        nlinarith [mul_le_mul_of_nonneg_left hca hθ, mul_le_mul_of_nonneg_left hcb hφ]
      have hstep : g (θ * a + φ * b) + C (g (θ * a + φ * b))
          ≤ (θ * g a + φ * g b) + C (θ * g a + φ * g b) := by
        rw [← heq _ hm hinterior, ← h3, hcomb]; linarith
      by_contra hcon
      exact absurd (hM hAm hAθ (not_le.mp hcon)) (not_lt.mpr hstep)
  have hval : h (θ * a + φ * b)
      = (θ * g a + φ * g b) + (θ * h a + φ * h b) - g (θ * a + φ * b) := by
    rw [← hcomb, h3]; ring
  rw [hval]
  linarith

/-! ### Carroll and Kimball's induction step, with the Euler equation discharged -/

/-- **The interiority the first-order condition needs.** At `(a, z)` the household saves
strictly inside the asset region and strictly below its feasible maximum, and does so again next
period in every income state. This is exactly what fails at the borrowing limit, where
`policy_eq_zero_of_corner_at` shows the constraint binds. -/
def EulerInterior (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (a : ℝ) : Prop :=
  assetFloor < P.policyOf (P.toExtended.bellman v) (a, z)
    ∧ P.policyOf (P.toExtended.bellman v) (a, z) < P.maxSaving (a, z)
    ∧ ∀ z' : Z, P.policyOf v (P.policyOf (P.toExtended.bellman v) (a, z), z')
        < P.maxSaving (P.policyOf (P.toExtended.bellman v) (a, z), z')

/-- **Carroll and Kimball (1996), the induction step for CRRA, with no Euler hypothesis.**

`concaveOn_consumptionFnOf_bellman_of_euler` assumed the first-order condition; here it is
proved, from the Clausen–Strub envelope run along the iteration. What is assumed instead is
interiority, which is a property of the state rather than of the model, and the reason the
statement is not yet unconditional. -/
theorem concaveOn_consumptionFnOf_bellman_of_interior {γ : ℝ} (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z' : Z, ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconcv : ∀ z' : Z, ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmonov : ∀ z' : Z, MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap))
    (hcW : ∀ a ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hin : ∀ a ∈ Icc assetFloor assetCap, P.EulerInterior v z a) :
    ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_consumptionFnOf_bellman_of_euler hγ0 hpos hconcv hmonov z fun a ha => ?_
  obtain ⟨h1, h2, h3⟩ := hin a ha
  exact P.egmMap_consumptionFnOf hγ0 hβ hu ha rfl h1 h2 (hcW a ha) h3
    fun z' => hpos z' _ (P.feasible_subset_region (P.policyOf_mem _ (a, z)))

/-- **Carroll and Kimball (1996), the induction step for CRRA, with the borrowing limit allowed
to BIND.** No interiority at the limit is assumed; the only slackness required is of the asset
CAP, which `crra_policy_lt_assetCap` discharges by calibration and which is a different
condition entirely.

Where the limit binds the Euler equation degenerates to an inequality, and `concaveOn_of_egm_corner`
absorbs that: the saving is then at its minimum, so it sits below any average of savings, which
is the only thing the transfer needs. -/
theorem concaveOn_consumptionFnOf_bellman {γ : ℝ} (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z' : Z, ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconcv : ∀ z' : Z, ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmonov : ∀ z' : Z, MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap))
    (hcW : ∀ a ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hslackW : ∀ a ∈ Icc assetFloor assetCap,
      P.policyOf (P.toExtended.bellman v) (a, z) < P.maxSaving (a, z))
    (hslackv : ∀ A ∈ Icc assetFloor assetCap, ∀ z' : Z,
      P.policyOf v (A, z') < P.maxSaving (A, z')) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_of_egm_corner (z := z)
    (g := fun a => P.policyOf (P.toExtended.bellman v) (a, z)) (C := P.egmMap v γ z)
    (P.concaveOn_egmMap hγ0 z hpos hconcv)
    (strictMonoOn_add_egm (P.monotoneOn_egmMap hγ0 z hpos hmonov))
    (fun a _ => P.feasible_subset_region (P.policyOf_mem _ (a, z))) (fun a ha => ?_)
    (fun a ha => ?_) fun a ha hfloor => ?_
  · have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
      simp only [resources, max_eq_right ha.1]
    simp only [consumptionFnOf, consumption, hres]; ring
  · exact P.egmMap_ge hγ0 hβ hu ha rfl (hslackW a ha) (hcW a ha)
      fun z' => hpos z' _ (P.feasible_subset_region (P.policyOf_mem _ (a, z)))
  · exact P.egmMap_consumptionFnOf hγ0 hβ hu ha rfl hfloor (hslackW a ha) (hcW a ha)
      (hslackv _ (P.feasible_subset_region (P.policyOf_mem _ (a, z))))
      fun z' => hpos z' _ (P.feasible_subset_region (P.policyOf_mem _ (a, z)))

end IncomeFluctuation

end LeanEconomics
