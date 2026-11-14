/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationBounds
public import LeanPool.AiyagariEquilibrium.Analysis.DecreasingIncrements

/-!
# The Bellman operator preserves Lipschitz continuity in assets

The economics half of the Lipschitz argument. With `isClosed_forall_lipschitzOn` this makes
the value function Lipschitz in assets, which bounds the marginal value of wealth uniformly
and so lets a corner condition be checked without differentiating anything.

## The action swap

Comparing a richer state `x` with a poorer state `y ≤ x`, the resource shortfall is
`Δ = (1+r)(x-y)`. Given any action `a'` feasible at `x`, the action `max 0 (a' - Δ)` is
feasible at `y` and — away from the truncation — leaves consumption EXACTLY unchanged. So the
whole difference passes to the continuation value, where the hypothesis on `v` bounds it by
`L·Δ`, and the utility term contributes nothing.

Where the truncation bites, the poorer household saves nothing and therefore consumes all its
resources. That is what keeps the utility term controllable: both consumptions are then at
least `minIncome`, where a concave `u` is Lipschitz with the explicit constant of
`slopeBound`. No appeal to the cutoff lemma is needed, and no derivative.

Those two cases are where the constant `(K + βL)(1+r)` comes from, and solving
`(K + βL)(1+r) ≤ L` for `L` is exactly where impatience `β(1+r) < 1` is required.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- The Lipschitz constant of `u` above the lowest possible consumption. -/
noncomputable def slopeBoundU : ℝ := slopeBound P.u P.minConsumption

theorem slopeBoundU_nonneg : 0 ≤ P.slopeBoundU :=
  slopeBound_nonneg P.monotoneOn_u P.minConsumption_pos

theorem abs_u_sub_le {c d : ℝ} (hc : P.minConsumption ≤ c) (hd : P.minConsumption ≤ d) :
    |P.u c - P.u d| ≤ P.slopeBoundU * |c - d| :=
  P.strictConcaveOn_u.concaveOn.abs_sub_le_slopeBound_mul P.monotoneOn_u P.minConsumption_pos hc hd

/-- The expectation inherits a Lipschitz bound from the continuation value, since the two
states share the income draw and hence the transition weights. -/
theorem abs_expect_sub_le_lipschitz {v : (ℝ × Z) →ᵇ ℝ} {L : ℝ}
    (hv : ∀ z : Z, ∀ p ∈ Icc assetFloor assetCap, ∀ q ∈ Icc assetFloor assetCap,
      |v (p, z) - v (q, z)| ≤ L * |p - q|)
    (z : Z) {a b : ℝ} (ha : a ∈ Icc assetFloor assetCap) (hb : b ∈ Icc assetFloor assetCap)
    (x y : ℝ) :
    |P.toExtended.expect v ((x, z), a) - P.toExtended.expect v ((y, z), b)| ≤ L * |a - b| := by
  have hp : ∀ (w : ℝ) (c : ℝ), P.toExtended.expect v ((w, z), c)
      = ∑ z' : Z, P.transitionMatrix z z' * v (c, z') := fun _ _ => rfl
  rw [hp, hp, ← Finset.sum_sub_distrib]
  calc |∑ z' : Z, (P.transitionMatrix z z' * v (a, z') - P.transitionMatrix z z' * v (b, z'))|
      ≤ ∑ z' : Z, |P.transitionMatrix z z' * v (a, z') - P.transitionMatrix z z' * v (b, z')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z' : Z, P.transitionMatrix z z' * (L * |a - b|) := by
        refine Finset.sum_le_sum fun z' _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (P.transitionMatrix_nonneg z z')]
        exact mul_le_mul_of_nonneg_left (hv z' a ha b hb) (P.transitionMatrix_nonneg z z')
    _ = L * |a - b| := by rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]

/-- **The richer state's value exceeds the poorer's by at most the swap cost.** -/
theorem bellmanFn_sub_le_of_lipschitz {v : (ℝ × Z) →ᵇ ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hv : ∀ z : Z, ∀ p ∈ Icc assetFloor assetCap, ∀ q ∈ Icc assetFloor assetCap,
      |v (p, z) - v (q, z)| ≤ L * |p - q|)
    (z : Z) {x y : ℝ} (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap)
    (hxy : y ≤ x) :
    P.toExtended.bellmanFn v (x, z) - P.toExtended.bellmanFn v (y, z)
      ≤ (P.slopeBoundU + P.discount * L) * ((1 + P.interest) * (x - y)) := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hK := P.slopeBoundU_nonneg
  set Δ : ℝ := (1 + P.interest) * (x - y) with hΔdef
  have hΔ0 : 0 ≤ Δ := mul_nonneg P.interest_gt_neg_one.le (by linarith)
  have hres : P.resources (x, z) = P.resources (y, z) + Δ := by
    simp only [resources, hΔdef]
    rw [max_eq_right hx.1, max_eq_right hy.1]; ring
  rw [sub_le_iff_le_add']
  refine P.toExtended.bellmanFn_le v fun a ha => ?_
  rcases eq_or_ne (P.toExtended.reward ((x, z), a)) ⊥ with hbot | hne
  · rw [ExtendedStochasticProgram.objectiveE, hbot, EReal.bot_add]; exact bot_le
  -- consumption is positive at the richer state, so the objective is real there
  have hc : P.consumption (x, z) a ∈ P.dom := P.consumption_mem_dom_of_ne_bot hx ha hne
  have ha0 : assetFloor ≤ a := ha.1
  have hacap : a ≤ assetCap := le_trans ha.2 (P.maxSaving_le_assetCap _)
  have haR : a ≤ P.resources (x, z) := le_trans ha.2 (P.maxSaving_le_resources _)
  set b : ℝ := max assetFloor (a - Δ) with hbdef
  have hb0 : assetFloor ≤ b := le_max_left _ _
  have hba : b ≤ a := by rw [hbdef]; exact max_le ha0 (by linarith)
  have hbmem : b ∈ P.toExtended.feasible (y, z) := by
    rw [P.feasible_eq, P.maxSaving_eq]
    refine ⟨hb0, le_min (le_trans hba hacap) ?_⟩
    rw [hbdef]
    exact max_le (P.assetFloor_lt_resources _).le (by linarith [hres])
  -- consumption at the poorer state under the swapped action
  have hcy : P.consumption (y, z) b = P.resources (y, z) - b := rfl
  have hcymem : P.consumption (y, z) b ∈ P.dom := by
    rcases le_total (a - assetFloor) Δ with h | h
    · refine P.mem_dom_of_pos ?_
      rw [hcy, hbdef, max_eq_left (by linarith)]
      linarith [P.minConsumption_le_consumption_floor (y, z), P.minConsumption_pos]
    · refine P.dom_upward hc (le_of_eq ?_)
      rw [hcy, hbdef, max_eq_right (by linarith)]
      simp only [consumption]; linarith [hres]
  -- both objectives are real; compare them
  have hrx := P.reward_eq_coe_dom hx ha hc
  have hry := P.reward_eq_coe_dom hy hbmem hcymem
  have hexp := P.abs_expect_sub_le_lipschitz hv z (a := a) (b := b)
    ⟨ha0, hacap⟩ ⟨hb0, le_trans hba hacap⟩ x y
  have hgapa : |a - b| ≤ Δ := by
    rw [hbdef]
    rcases le_total (a - assetFloor) Δ with h | h
    · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith)]; exact h
    · rw [max_eq_right (by linarith)]
      rw [show a - (a - Δ) = Δ by ring, abs_of_nonneg hΔ0]
  -- the utility term: equal consumptions off the truncation, both above `minIncome` on it
  have hutil : P.u (P.consumption (x, z) a) - P.u (P.consumption (y, z) b)
      ≤ P.slopeBoundU * Δ := by
    rcases le_total Δ (a - assetFloor) with h | h
    · -- no truncation: consumption is unchanged
      have : P.consumption (y, z) b = P.consumption (x, z) a := by
        rw [hcy, hbdef, max_eq_right (by linarith)]
        simp only [consumption]; linarith [hres]
      rw [this, sub_self]
      positivity
    · -- truncation: the poorer household borrows to the limit and eats the rest
      have hb0' : b = assetFloor := by rw [hbdef, max_eq_left (by linarith)]
      have hcyval : P.consumption (y, z) b = P.resources (y, z) - assetFloor := by
        rw [hcy, hb0']
      have h1 : P.minConsumption ≤ P.consumption (y, z) b := by
        rw [hcyval]; exact P.minConsumption_le_consumption_floor _
      have h2 : P.minConsumption ≤ P.consumption (x, z) a := by
        simp only [consumption]
        rw [hcyval] at h1
        linarith [hres]
      have := P.abs_u_sub_le h2 h1
      rw [abs_le] at this
      refine le_trans this.2 ?_
      refine mul_le_mul_of_nonneg_left ?_ hK
      rw [abs_le]
      constructor
      · simp only [consumption, hb0']; linarith
      · simp only [consumption, hb0']; linarith
  -- assemble
  have hdx : (P.toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  have hstep : P.toExtended.objectiveE v (x, z) a
      ≤ P.toExtended.objectiveE v (y, z) b
        + (((P.slopeBoundU + P.discount * L) * Δ : ℝ) : EReal) := by
    simp only [ExtendedStochasticProgram.objectiveE, hrx, hry, hdx]
    rw [← EReal.coe_add, add_assoc, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    rw [abs_le] at hexp
    have h1 : (P.discount : ℝ)
        * (P.toExtended.expect v ((x, z), a) - P.toExtended.expect v ((y, z), b))
        ≤ P.discount * (L * |a - b|) := mul_le_mul_of_nonneg_left hexp.2 hβ
    have h2 : (P.discount : ℝ) * (L * |a - b|) ≤ P.discount * (L * Δ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgapa hL) hβ
    nlinarith [hutil, h1, h2]
  refine le_trans hstep ?_
  rw [EReal.coe_add]
  exact add_le_add (P.toExtended.le_bellmanFn v hbmem) (le_refl _)

/-- **The poorer state's value falls short by at most the swap cost.** The reverse swap needs
no utility bound at all: where it truncates, the richer household consumes strictly more, so
the utility term has the helpful sign. -/
theorem bellmanFn_sub_le_of_lipschitz' {v : (ℝ × Z) →ᵇ ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hv : ∀ z : Z, ∀ p ∈ Icc assetFloor assetCap, ∀ q ∈ Icc assetFloor assetCap,
      |v (p, z) - v (q, z)| ≤ L * |p - q|)
    (z : Z) {x y : ℝ} (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap)
    (hxy : y ≤ x) :
    P.toExtended.bellmanFn v (y, z) - P.toExtended.bellmanFn v (x, z)
      ≤ P.discount * L * ((1 + P.interest) * (x - y)) := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  set Δ : ℝ := (1 + P.interest) * (x - y) with hΔdef
  have hΔ0 : 0 ≤ Δ := mul_nonneg P.interest_gt_neg_one.le (by linarith)
  have hres : P.resources (x, z) = P.resources (y, z) + Δ := by
    simp only [resources, hΔdef]
    rw [max_eq_right hx.1, max_eq_right hy.1]; ring
  rw [sub_le_iff_le_add']
  refine P.toExtended.bellmanFn_le v fun b hb => ?_
  rcases eq_or_ne (P.toExtended.reward ((y, z), b)) ⊥ with hbot | hne
  · rw [ExtendedStochasticProgram.objectiveE, hbot, EReal.bot_add]; exact bot_le
  have hcy : P.consumption (y, z) b ∈ P.dom := P.consumption_mem_dom_of_ne_bot hy hb hne
  have hb0 : assetFloor ≤ b := hb.1
  have hbcap : b ≤ assetCap := le_trans hb.2 (P.maxSaving_le_assetCap _)
  have hbR : b ≤ P.resources (y, z) := le_trans hb.2 (P.maxSaving_le_resources _)
  set a : ℝ := min (b + Δ) (P.maxSaving (x, z)) with hadef
  have ha0 : assetFloor ≤ a := le_min (by linarith) (P.assetFloor_le_maxSaving _)
  have hamem : a ∈ P.toExtended.feasible (x, z) := ⟨ha0, min_le_right _ _⟩
  have hacap : a ≤ assetCap := le_trans (min_le_right _ _) (P.maxSaving_le_assetCap _)
  -- consumption at the richer state is at least what the poorer household had
  have hcx : P.consumption (y, z) b ≤ P.consumption (x, z) a := by
    simp only [consumption, hadef]
    rcases le_total (b + Δ) (P.maxSaving (x, z)) with h | h
    · rw [min_eq_left h]; linarith [hres]
    · rw [min_eq_right h]
      have hms : P.maxSaving (x, z) = min assetCap (P.resources (x, z)) := P.maxSaving_eq _
      rcases le_total (P.resources (x, z)) assetCap with hcap | hcap
      · -- no truncation is possible here
        rw [hms, min_eq_right hcap] at h ⊢
        linarith [hres]
      · rw [hms, min_eq_left hcap] at h ⊢
        linarith [hres]
  have hcxmem : P.consumption (x, z) a ∈ P.dom := P.dom_upward hcy hcx
  have hgapa : |b - a| ≤ Δ := by
    have hlow : b - Δ ≤ a := by
      rw [hadef]
      refine le_min (by linarith) ?_
      have hmono : P.maxSaving (y, z) ≤ P.maxSaving (x, z) := by
        rw [P.maxSaving_eq, P.maxSaving_eq]
        exact min_le_min le_rfl (by linarith [hres])
      linarith [hb.2]
    have hhigh : a ≤ b + Δ := min_le_left _ _
    rw [abs_le]
    constructor <;> linarith
  have hrx := P.reward_eq_coe_dom hx hamem hcxmem
  have hry := P.reward_eq_coe_dom hy hb hcy
  have hexp := P.abs_expect_sub_le_lipschitz hv z (a := b) (b := a)
    ⟨hb0, hbcap⟩ ⟨ha0, hacap⟩ y x
  have hdx : (P.toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  have hstep : P.toExtended.objectiveE v (y, z) b
      ≤ P.toExtended.objectiveE v (x, z) a + (((P.discount * L) * Δ : ℝ) : EReal) := by
    simp only [ExtendedStochasticProgram.objectiveE, hrx, hry, hdx]
    rw [← EReal.coe_add, add_assoc, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    rw [abs_le] at hexp
    have hu' : P.u (P.consumption (y, z) b) ≤ P.u (P.consumption (x, z) a) :=
      P.monotoneOn_u_dom hcy hcxmem hcx
    have h1 : (P.discount : ℝ)
        * (P.toExtended.expect v ((y, z), b) - P.toExtended.expect v ((x, z), a))
        ≤ P.discount * (L * |b - a|) := mul_le_mul_of_nonneg_left hexp.2 hβ
    have h2 : (P.discount : ℝ) * (L * |b - a|) ≤ P.discount * (L * Δ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgapa hL) hβ
    nlinarith [hu', h1, h2]
  refine le_trans hstep ?_
  rw [EReal.coe_add]
  exact add_le_add (P.toExtended.le_bellmanFn v hamem) (le_refl _)

/-- **The Bellman operator preserves Lipschitz continuity in assets.** -/
theorem abs_bellmanFn_sub_le_of_lipschitz {v : (ℝ × Z) →ᵇ ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hv : ∀ z : Z, ∀ p ∈ Icc assetFloor assetCap, ∀ q ∈ Icc assetFloor assetCap,
      |v (p, z) - v (q, z)| ≤ L * |p - q|)
    (hbig : (P.slopeBoundU + P.discount * L) * (1 + P.interest) ≤ L)
    (z : Z) {x y : ℝ} (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap) :
    |P.toExtended.bellmanFn v (x, z) - P.toExtended.bellmanFn v (y, z)| ≤ L * |x - y| := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hK := P.slopeBoundU_nonneg
  have hone : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have key : ∀ p q : ℝ, p ∈ Icc assetFloor assetCap → q ∈ Icc assetFloor assetCap → q ≤ p →
      |P.toExtended.bellmanFn v (p, z) - P.toExtended.bellmanFn v (q, z)| ≤ L * |p - q| := by
    intro p q hp hq hqp
    have h1 := P.bellmanFn_sub_le_of_lipschitz hL hv z hp hq hqp
    have h2 := P.bellmanFn_sub_le_of_lipschitz' hL hv z hp hq hqp
    have hgap : (P.discount : ℝ) * L * ((1 + P.interest) * (p - q))
        ≤ (P.slopeBoundU + P.discount * L) * ((1 + P.interest) * (p - q)) := by
      refine mul_le_mul_of_nonneg_right (by linarith) (by nlinarith)
    have hfinal : (P.slopeBoundU + P.discount * L) * ((1 + P.interest) * (p - q))
        ≤ L * (p - q) := by
      have := mul_le_mul_of_nonneg_right hbig (by linarith : (0 : ℝ) ≤ p - q)
      nlinarith
    rw [abs_le, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p - q)]
    constructor <;> linarith
  rcases le_total y x with h | h
  · exact key x y hx hy h
  · rw [abs_sub_comm, abs_sub_comm x y]; exact key y x hy hx h

/-- **The value function is Lipschitz in assets**, with an explicit constant. Combining the
preservation proof with the closed class. Any `L` with `(K + βL)(1+r) ≤ L` works, and such an
`L` exists exactly when `β(1+r) < 1`. -/
theorem valueFunction_lipschitz {L : ℝ} (hL : 0 ≤ L)
    (hbig : (P.slopeBoundU + P.discount * L) * (1 + P.interest) ≤ L) :
    ∀ z : Z, ∀ x ∈ Icc assetFloor assetCap, ∀ y ∈ Icc assetFloor assetCap,
      |P.toExtended.valueFunction (x, z) - P.toExtended.valueFunction (y, z)| ≤ L * |x - y| :=
  P.toExtended.blackwell.forall_lipschitzOn_valueFunction P.toExtended.discount_lt_one hL
    (g := fun (z : Z) (a : ℝ) => (a, z))
    (fun v hvv z x hx y hy => by
      simpa only [ExtendedStochasticProgram.bellman_apply] using
        P.abs_bellmanFn_sub_le_of_lipschitz hL (fun z' p hp q hq => hvv z' p hp q hq) hbig z hx hy)

/-! ### The corner

With the marginal value of wealth bounded above by `L`, saving nothing beats saving anything
as soon as `β L` falls below a lower bound on the marginal utility of consumption. Both sides
of that comparison are now explicit constants, and no derivative appears in either. -/

/-- **The corner condition, state by state.** The marginal-utility bound is required only up
to THIS state's resources, so the threshold is local: a state with few resources has high
marginal utility and the constraint binds there, while a richer state may fail the test.

That is what lets the borrowing constraint bind at a bad income draw without binding
everywhere, which the global version could not express. -/
theorem policy_eq_zero_of_corner_at {L m : ℝ}
    (hlip : ∀ z : Z, ∀ x ∈ Icc assetFloor assetCap, ∀ y ∈ Icc assetFloor assetCap,
      |P.toExtended.valueFunction (x, z) - P.toExtended.valueFunction (y, z)| ≤ L * |x - y|)
    {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap)
    (hmarg : ∀ c d : ℝ, d ∈ P.dom → d ≤ c → c ≤ P.resources s - assetFloor →
      m * (c - d) ≤ P.u c - P.u d)
    (hcond : P.discount * L < m) :
    P.policy s = assetFloor := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  set V := P.toExtended.valueFunction with hV
  have hmem0 : assetFloor ∈ P.toExtended.feasible s := ⟨le_rfl, le_max_left _ _⟩
  have hc0 : 0 < P.consumption s assetFloor := by
    have := P.minConsumption_le_consumption_floor s
    have := P.minConsumption_pos
    simp only [consumption]; linarith
  have hrw0 := P.reward_eq_coe hs hmem0 hc0
  have hRmax : P.resources s - assetFloor ≤ P.maxConsumption :=
    P.consumption_le_maxConsumption hs (le_refl assetFloor)
  -- nothing feasible beats borrowing to the limit
  have hdom : ∀ a ∈ P.toExtended.feasible s,
      P.toExtended.objectiveE V s a
        ≤ ((P.u (P.consumption s assetFloor)
            + P.discount * P.toExtended.expect V (s, assetFloor) : ℝ) : EReal) := by
    intro a ha
    rcases eq_or_ne (P.toExtended.reward (s, a)) ⊥ with hbot | hne
    · rw [ExtendedStochasticProgram.objectiveE, hbot, EReal.bot_add]; exact bot_le
    have hca : P.consumption s a ∈ P.dom := P.consumption_mem_dom_of_ne_bot hs ha hne
    have ha0 : assetFloor ≤ a := ha.1
    have hacap : a ≤ assetCap := le_trans ha.2 (P.maxSaving_le_assetCap _)
    have hrwa := P.reward_eq_coe_dom hs ha hca
    have hdx : (P.toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
    -- the utility gain from consuming instead of saving
    have hu : m * (a - assetFloor)
        ≤ P.u (P.consumption s assetFloor) - P.u (P.consumption s a) := by
      have hcc : P.consumption s a ≤ P.consumption s assetFloor := by
        simp only [consumption]; linarith
      have := hmarg (P.consumption s assetFloor) (P.consumption s a) hca hcc
        (by simp only [consumption]; exact le_rfl)
      have hdiff : P.consumption s assetFloor - P.consumption s a = a - assetFloor := by
        simp only [consumption]; ring
      rwa [hdiff] at this
    -- the continuation loss from not saving
    have hexp := P.abs_expect_sub_le_lipschitz hlip s.2 (a := a) (b := assetFloor)
      ⟨ha0, hacap⟩ ⟨le_rfl, P.assetFloor_le_assetCap⟩ s.1 s.1
    rw [abs_le] at hexp
    simp only [ExtendedStochasticProgram.objectiveE, hrwa, hdx, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    have hprod : (P.discount : ℝ) * (P.toExtended.expect V ((s.1, s.2), a)
        - P.toExtended.expect V ((s.1, s.2), assetFloor))
        ≤ P.discount * (L * |a - assetFloor|) :=
      mul_le_mul_of_nonneg_left hexp.2 hβ
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - assetFloor)] at hprod
    have hpp : (P.discount : ℝ) * (L * (a - assetFloor)) ≤ m * (a - assetFloor) := by
      rcases eq_or_lt_of_le ha0 with h | h
      · rw [← h]; simp
      · nlinarith
    have hfix : ∀ c : ℝ, P.toExtended.expect V ((s.1, s.2), c)
        = P.toExtended.expect V (s, c) := fun _ => rfl
    rw [hfix, hfix] at hprod
    linarith
  -- so borrowing to the limit attains the maximum, and the maximiser is unique
  have hle : P.toExtended.bellmanFn V s
      ≤ P.u (P.consumption s assetFloor)
        + P.discount * P.toExtended.expect V (s, assetFloor) :=
    P.toExtended.bellmanFn_le V hdom
  have hdx : (P.toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  have hge : ((P.u (P.consumption s assetFloor)
      + P.discount * P.toExtended.expect V (s, assetFloor) : ℝ) : EReal)
      ≤ ((P.toExtended.bellmanFn V s : ℝ) : EReal) := by
    have h := P.toExtended.le_bellmanFn V hmem0
    rwa [ExtendedStochasticProgram.objectiveE, hrw0, hdx, ← EReal.coe_add] at h
  rw [EReal.coe_le_coe_iff] at hge
  refine (P.eq_policy_of_optimal hs hmem0 ?_).symm
  rw [ExtendedStochasticProgram.objectiveE, hrw0, hdx, ← EReal.coe_add, EReal.coe_eq_coe_iff]
  linarith

/-- The global corner condition, as a corollary. -/
theorem policy_eq_zero_of_corner {L m : ℝ}
    (hlip : ∀ z : Z, ∀ x ∈ Icc assetFloor assetCap, ∀ y ∈ Icc assetFloor assetCap,
      |P.toExtended.valueFunction (x, z) - P.toExtended.valueFunction (y, z)| ≤ L * |x - y|)
    (hmarg : ∀ c d : ℝ, d ∈ P.dom → d ≤ c → c ≤ P.maxConsumption → m * (c - d) ≤ P.u c - P.u d)
    (hcond : P.discount * L < m) {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap) :
    P.policy s = assetFloor :=
  P.policy_eq_zero_of_corner_at hlip hs
    (fun c d hd hdc hc => hmarg c d hd hdc
      (le_trans hc (P.consumption_le_maxConsumption hs (le_refl assetFloor))))
    hcond

/-- For `u c = -1/c`, the marginal-utility bound up to `R` is `1/R²`. So the state-dependent
threshold reads `β L < 1 / resources²`: the constraint binds exactly where resources are small
enough, and `resources = income + (1+r)·assets` rises with BOTH the income draw and the asset
position. -/
theorem crra_marginal {R : ℝ} (hR : 0 < R) (c d : ℝ) (hd : 0 < d) (hdc : d ≤ c) (hcR : c ≤ R) :
    (1 / R ^ 2) * (c - d) ≤ (-c⁻¹) - (-d⁻¹) := by
  have hc : 0 < c := lt_of_lt_of_le hd hdc
  have hkey : -c⁻¹ - -d⁻¹ = (c - d) / (c * d) := by field_simp; ring
  rw [show (1 : ℝ) / R ^ 2 * (c - d) = (c - d) / R ^ 2 by ring, hkey,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hdc) (sub_nonneg.mpr (show c * d ≤ R ^ 2 by nlinarith))]

end IncomeFluctuation

end LeanEconomics
