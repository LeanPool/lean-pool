/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationEuler
public import LeanPool.AiyagariEquilibrium.Models.CRRAConstants

/-!
# Positivity and monotonicity along the iteration

Carroll and Kimball's induction step needs the continuation's consumption function to be
positive, concave and nondecreasing. Concavity is the induction hypothesis. This file proves
positivity and consumption monotonicity against arbitrary continuations, together with saving
bounds uniform over the iteration. Saving-policy monotonicity is shared with the fixed-point
case in `IncomeFluctuationMonotone`.

The exchange arguments use `objROf`, the real objective against an arbitrary continuation.
Continuation value depends on chosen saving and the income state, never on current assets,
so shifting household plans between asset levels cancels the continuation terms.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### Positivity -/

/-- **Consumption never vanishes at the optimum, whatever the continuation.** With utility
unbounded below the reward at zero consumption is `⊥`, and the optimum is a real number. -/
theorem consumptionFnOf_pos (hd : P.Unbounded) (v : (ℝ × Z) →ᵇ ℝ) {z : Z} {a : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) : 0 < P.consumptionFnOf v z a := by
  have hopt := P.policyOf_optimal v (a, z)
  have hne : P.toExtended.reward ((a, z), P.policyOf v (a, z)) ≠ ⊥ := by
    intro hbot
    rw [ExtendedStochasticProgram.objectiveE, hbot, EReal.bot_add] at hopt
    exact (EReal.bot_ne_coe _) hopt
  have hmem := P.consumption_mem_dom_of_ne_bot (s := (a, z)) ha (P.policyOf_mem v (a, z)) hne
  rw [hd] at hmem
  exact hmem

/-- **Consumption is positive at the optimum against every continuation with concave slices.**
The induction sees the iterates, not the value function, so this is what it needs. With utility
unbounded below it is automatic; for the bounded CES family it is earned from a marginal Inada
condition,
exactly as `PositiveConsumption` is. -/
def PositiveConsumptionAll : Prop :=
  ∀ (v : (ℝ × Z) →ᵇ ℝ), ConcaveSlices assetFloor assetCap v →
    ∀ (z : Z), ∀ a ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z a

theorem positiveConsumptionAll_of_unbounded (hd : P.Unbounded) : P.PositiveConsumptionAll :=
  fun v _ _ _ ha => P.consumptionFnOf_pos hd v ha

/-- **Positive consumption for free, when the cap is narrow relative to income.** If the whole
asset range is worth less than one period's minimum consumption, no feasible saving can exhaust
resources, so consumption is positive whatever the continuation. Utilities with FINITE marginal
value at zero — CARA, shifted CRRA — have no Inada condition to appeal to, and this is the
alternative: keep the household away from zero consumption by the budget rather than by the
preferences. -/
theorem positiveConsumptionAll_of_rich (hrich : assetCap - assetFloor < P.minConsumption) :
    P.PositiveConsumptionAll := by
  intro v hv z a ha
  have h1 : P.minConsumption ≤ P.resources (a, z) - assetFloor :=
    P.minConsumption_le_consumption_floor (a, z)
  have h2 : P.policyOf v (a, z) ≤ assetCap :=
    (P.feasible_subset_region (P.policyOf_mem v (a, z))).2
  simp only [consumptionFnOf, consumption]
  linarith

/-! ### Monotonicity of the consumption function -/

/-! ### Saving stays strictly inside the feasible set

Positive consumption already keeps the saving below resources; what is left is the asset CAP,
and that is the single quantitative input the induction still needs. -/

theorem policyOf_lt_maxSaving (hpc : P.PositiveConsumptionAll) {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices assetFloor assetCap v) {a : ℝ} {z : Z}
    (ha : a ∈ Icc assetFloor assetCap) (hcap : P.policyOf v (a, z) < assetCap) :
    P.policyOf v (a, z) < P.maxSaving (a, z) := by
  rw [P.maxSaving_eq]
  refine lt_min hcap ?_
  have hc := hpc v hv z a ha
  simp only [consumptionFnOf, consumption] at hc
  linarith

/-- The same, with positivity supplied only at the continuation in hand. Utilities with finite
marginal value at zero have no `PositiveConsumptionAll`, but they do have positivity against the
continuations the iteration produces. -/
theorem policyOf_lt_maxSaving_of_pos {v : (ℝ × Z) →ᵇ ℝ} {a : ℝ} {z : Z}
    (hc : 0 < P.consumptionFnOf v z a) (hcap : P.policyOf v (a, z) < assetCap) :
    P.policyOf v (a, z) < P.maxSaving (a, z) := by
  rw [P.maxSaving_eq]
  refine lt_min hcap ?_
  simp only [consumptionFnOf, consumption] at hc
  linarith

/-! ### The oscillation of a continuation

`2 ‖v‖` is the wrong bound on the continuation's spread: it is not translation-invariant, and
for CES — where utility is bounded and the level of `v` is large compared with its variation —
it is far too crude. `oscGap` is the right one, and what it bounds is the OSCILLATION. This
section carries that along the iteration. -/

/-- At a zero borrowing limit the spread is `CRRAConstants.oscGap`. -/
theorem oscSpread_eq_oscGap {assetCap : ℝ} (Q : IncomeFluctuation Z 0 assetCap) :
    Q.oscSpread = Q.oscGap := rfl

theorem oscOn_zero : P.OscOn (0 : (ℝ × Z) →ᵇ ℝ) 0 := fun _ _ _ _ _ _ => by simp

/-- **The Bellman operator adds the reward's spread and contracts the continuation's.** -/
theorem oscOn_bellman {v : (ℝ × Z) →ᵇ ℝ} {G : ℝ} (h : P.OscOn v G) :
    P.OscOn (P.toExtended.bellman v)
      (P.u P.maxConsumption - P.u P.minConsumption + P.discount * G) := by
  intro x hx y hy z z'
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hba : ∀ (t : ℝ) (w : Z), (P.toExtended.bellman v) (t, w)
      = P.toExtended.bellmanFn v (t, w) := fun t w => rfl
  -- the optimum at `(x, z)`, priced above
  obtain ⟨-, hup⟩ := P.bellmanFn_eq_of_optimal (v := v) (s := (x, z)) hx
    (P.policyOf_mem v (x, z)) (P.policyOf_optimal v (x, z))
  have hAmem : P.policyOf v (x, z) ∈ Icc assetFloor assetCap :=
    P.feasible_subset_region (P.policyOf_mem v (x, z))
  have hcle : P.u (P.consumptionFnOf v z x) ≤ P.u P.maxConsumption :=
    P.monotoneOn_u_dom (P.consumption_policyOf_mem_dom v hx) P.maxConsumption_mem_dom
      (P.consumption_le_maxConsumption (s := (x, z)) hx (P.policyOf_mem v (x, z)).1)
  -- saving the minimum at `(y, z')`, priced below
  have hfl : assetFloor ∈ P.toExtended.feasible (y, z') := ⟨le_rfl, le_max_left _ _⟩
  have hmin : P.minConsumption ≤ P.consumption (y, z') assetFloor :=
    P.minConsumption_le_consumption_floor (y, z')
  have hminpos : 0 < P.consumption (y, z') assetFloor :=
    lt_of_lt_of_le P.minConsumption_pos hmin
  have hlow := P.lazyValue_le_dom v z' hy hfl (P.mem_dom_of_pos hminpos)
  have hulow : P.u P.minConsumption ≤ P.u (P.consumption (y, z') assetFloor) :=
    P.monotoneOn_u_dom (P.mem_dom_of_pos P.minConsumption_pos)
      (P.mem_dom_of_pos hminpos) hmin
  simp only [lazyValue] at hlow
  have hcont : P.contOf v z (P.policyOf v (x, z)) - P.contOf v z' assetFloor ≤ G :=
    P.contOf_sub_le_osc h hAmem ⟨le_rfl, P.assetFloor_le_assetCap⟩ z z'
  have hscaled := mul_le_mul_of_nonneg_left hcont hβ
  rw [hba x z, hba y z', hup]
  simp only [contOf] at hscaled hlow ⊢
  have hcx : P.consumptionFnOf v z x = P.consumption (x, z) (P.policyOf v (x, z)) := rfl
  rw [hcx] at hcle
  have hres : P.resources (y, z') - assetFloor = P.consumption (y, z') assetFloor := rfl
  rw [hres] at hlow
  linarith

/-- Every iterate from zero oscillates by at most `oscGap`. -/
theorem oscOn_iterate (n : ℕ) :
    P.OscOn ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) P.oscSpread := by
  have hβ1 : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
  have hfix : P.u P.maxConsumption - P.u P.minConsumption + (P.discount : ℝ) * P.oscSpread
      = P.oscSpread := by
    have hne : (1 : ℝ) - (P.discount : ℝ) ≠ 0 := by linarith
    simp only [oscSpread]
    field_simp
    ring
  induction n with
  | zero =>
      intro x hx y hy z z'
      simpa using P.oscSpread_nonneg
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := P.oscOn_bellman ih
      rwa [hfix] at this

/-! ### A uniform bound on saving, and hence on the cap

The last input is quantitative: the household must not want to save all the way to the imposed
ceiling. `policy_le_of_marginal_bound` does this at the fixed point; the same deviation — save
half as far above the borrowing limit — works against any continuation, with `‖v‖` in place of
`‖V‖`. The iterates are uniformly bounded because the Bellman operator adds at most the reward
and contracts what it inherits, so one calibration inequality covers the whole iteration. -/

/-- The Bellman operator adds at most the reward and contracts what it inherits. -/
theorem norm_bellman_le (v : (ℝ × Z) →ᵇ ℝ) :
    ‖P.toExtended.bellman v‖
      ≤ max |P.toExtended.rewardMin| |P.toExtended.rewardMax| + (P.discount : ℝ) * ‖v‖ := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hM : (0 : ℝ) ≤ max |P.toExtended.rewardMin| |P.toExtended.rewardMax| :=
    le_max_of_le_left (abs_nonneg _)
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun s => ?_
  have hb := P.toExtended.bellmanFn_bounds v s
  have hval : (P.toExtended.bellman v) s = P.toExtended.bellmanFn v s := rfl
  rw [hval, Real.norm_eq_abs, abs_le]
  simp only [ExtendedStochasticProgram.loBound, ExtendedStochasticProgram.hiBound] at hb
  have h1 : -|P.toExtended.rewardMin| ≤ P.toExtended.rewardMin := neg_abs_le _
  have h2 : P.toExtended.rewardMax ≤ |P.toExtended.rewardMax| := le_abs_self _
  have h3 : -max |P.toExtended.rewardMin| |P.toExtended.rewardMax|
      ≤ -|P.toExtended.rewardMin| := by
    simp only [neg_le_neg_iff]; exact le_max_left _ _
  have h4 : |P.toExtended.rewardMax|
      ≤ max |P.toExtended.rewardMin| |P.toExtended.rewardMax| := le_max_right _ _
  have hdx : (P.toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  rw [hdx] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- **The iterates are uniformly bounded**, so one calibration covers them all. -/
theorem norm_iterate_le (n : ℕ) :
    ‖(P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)‖
      ≤ max |P.toExtended.rewardMin| |P.toExtended.rewardMax| / (1 - P.discount) := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hβ1 : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
  have hM : (0 : ℝ) ≤ max |P.toExtended.rewardMin| |P.toExtended.rewardMax| :=
    le_max_of_le_left (abs_nonneg _)
  have hfix : max |P.toExtended.rewardMin| |P.toExtended.rewardMax|
      + (P.discount : ℝ) * (max |P.toExtended.rewardMin| |P.toExtended.rewardMax|
        / (1 - P.discount))
      = max |P.toExtended.rewardMin| |P.toExtended.rewardMax| / (1 - P.discount) := by
    have hne : (1 : ℝ) - (P.discount : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  induction n with
  | zero => simpa using by positivity
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine le_trans (P.norm_bellman_le _) ?_
      rw [← hfix]
      have := mul_le_mul_of_nonneg_left ih hβ
      linarith

/-! ### Carroll and Kimball, assembled along the iteration -/

/-- **Carroll and Kimball (1996) for CRRA.** The consumption function is concave.

Everything is now proved except the asset cap: `hslack` says the household never wants to save
all the way to the imposed ceiling, at any stage of the iteration. That is the artefact the cap
always was — `crra_policy_lt_assetCap` discharges it at the fixed point by calibration, and
`policy_assetCap_of_patient` shows it is exactly `β (1 + r) < 1` that makes it true. -/
theorem concaveOn_consumptionFnOf_iterates_of_crra {γ : ℝ} (hpc : P.PositiveConsumptionAll)
    (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ)
    (hslack : ∀ n : ℕ, ∀ a ∈ Icc assetFloor assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap) :
    ∀ n : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z) := by
  set T := P.toExtended.bellman with hTdef
  have hslices : ∀ n : ℕ, ConcaveSlices assetFloor assetCap (T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) :=
    P.concaveSlices_iterate_bellman concaveSlices_zero
  · intro n
    induction n with
    | zero => exact P.concaveOn_consumptionFnOf_zero
    | succ k ih =>
        intro z
        have hnext : ∀ a ∈ Icc assetFloor assetCap,
            P.policyOf (T (T^[k] (0 : (ℝ × Z) →ᵇ ℝ))) (a, z) < P.maxSaving (a, z) := by
          intro a ha
          have hs := hslack (k + 1) a ha z
          rw [Function.iterate_succ_apply'] at hs
          exact P.policyOf_lt_maxSaving hpc (P.concaveSlices_bellman (hslices k)) ha hs
        rw [Function.iterate_succ_apply']
        exact P.concaveOn_consumptionFnOf_bellman hγ0 hβ hu z
          (fun z' A hA => hpc _ (hslices k) z' A hA) ih
          (fun z' x hx y hy hxy => P.consumptionFnOf_mono (hslices k) hx hy hxy)
          (fun a ha => hpc _ (P.concaveSlices_bellman (hslices k)) z a ha) hnext
          fun A hA z' => P.policyOf_lt_maxSaving hpc (hslices k) hA (hslack k A hA z')

/-- **Carroll and Kimball for CRRA**, at the fixed point. -/
theorem concaveOn_consumptionFn_of_crra {γ : ℝ} (hpc : P.PositiveConsumptionAll) (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ)
    (hslack : ∀ n : ℕ, ∀ a ∈ Icc assetFloor assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (z : Z) : ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) :=
  P.concaveOn_consumptionFn_of_iterates
    (P.concaveOn_consumptionFnOf_iterates_of_crra hpc hγ0 hβ hu hslack) z

/-- **Carroll and Kimball (1996) for CRRA, from a calibration.** Beyond CRRA utility and
marginal utility unbounded at zero, the only hypothesis left is one inequality: the asset cap
must sit above the uniform bound on saving that the marginal bound `m` produces. Nothing about
the borrowing limit, and nothing about interiority.

That inequality is the cap being an artefact, which is what it was always meant to be: by
`policy_assetCap_of_patient` it is exactly impatience that makes it true. -/
theorem concaveOn_consumptionFn_of_marginal {γ m : ℝ} (hpc : P.PositiveConsumptionAll)
    (hγ0 : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ) (hm : 0 < m)
    (hmarg : ∀ c d : ℝ, d ∈ P.dom → d ≤ c → c ≤ P.maxConsumption → m * (c - d) ≤ P.u c - P.u d)
    (hcap : assetFloor + 4 * (P.discount : ℝ)
        * (max |P.toExtended.rewardMin| |P.toExtended.rewardMax| / (1 - P.discount)) / m
      < assetCap)
    (z : Z) : ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) := by
  have hslices : ∀ n : ℕ, ConcaveSlices assetFloor assetCap
      ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) :=
    P.concaveSlices_iterate_bellman concaveSlices_zero
  refine P.concaveOn_consumptionFn_of_crra hpc hγ0 hβ hu (fun n a ha z' => ?_) z
  have hb := P.policyOf_le_of_marginal_bound (hslices n) hm hmarg ha z'
  have hn := P.norm_iterate_le n
  have h4 : (0 : ℝ) ≤ 4 * (P.discount : ℝ) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hn h4
  have hmono : 4 * (P.discount : ℝ) * ‖(P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)‖ / m
      ≤ 4 * (P.discount : ℝ) * (max |P.toExtended.rewardMin| |P.toExtended.rewardMax|
        / (1 - P.discount)) / m := by
    rw [div_le_div_iff₀ hm hm]; nlinarith [hstep, hm]
  linarith

/-! ### Positive consumption for the bounded family

With utility unbounded below, consumption is positive because zero consumption is worth `⊥`.
With CES and `γ < 1` it is not: zero consumption is admissible and the floor has to be earned
from the MARGIN, which is what `ConsumptionFloor` does at the fixed point. The induction sees
the iterates, so the same argument is run against an arbitrary continuation — and it goes
through unchanged, because it only ever used concavity and boundedness of the continuation. -/

/-- **Positive consumption against every continuation, for the bounded family.** -/
theorem positiveConsumptionAll_of_marginalInada (hu : MarginalInadaOn P.dom P.u) :
    P.PositiveConsumptionAll := by
  intro v hv z a ha
  obtain ⟨δ, hδ, hspec⟩ := P.exists_consumptionFnOf_floor_of_marginalInada hu hv
  exact lt_of_lt_of_le hδ (hspec z a ha)

/-- **Carroll and Kimball for the BOUNDED CES family**, `0 < γ < 1`, where utility does not fall
to `-∞` and positivity of consumption has to be earned. -/
theorem concaveOn_consumptionFn_of_bounded_crra {γ m : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hβ : 0 < (P.discount : ℝ)) (hb : P.Bounded) (hu : P.u = crraUtility γ) (hm : 0 < m)
    (hmarg : ∀ c d : ℝ, d ∈ P.dom → d ≤ c → c ≤ P.maxConsumption → m * (c - d) ≤ P.u c - P.u d)
    (hcap : assetFloor + 4 * (P.discount : ℝ)
        * (max |P.toExtended.rewardMin| |P.toExtended.rewardMax| / (1 - P.discount)) / m
      < assetCap)
    (z : Z) : ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) := by
  refine P.concaveOn_consumptionFn_of_marginal (P.positiveConsumptionAll_of_marginalInada ?_)
    hγ0 hβ hu hm hmarg hcap z
  rw [hb, hu]
  exact marginalInadaOn_Ici_crraUtility hγ0 hγ1

/-! ### The multiplicative CES bound on saving

`policyOf_le_of_marginal_bound` prices the deviation against the LEVEL of the continuation, and
for CES that is hopeless: at the `cesWitness` parameters it gives a bound about six times the
asset cap. The fix is the one `crra_policy_le_mul` makes at the fixed point — deviate to a
FRACTION `θ` of the saving rather than half of it, and price the extra consumption at the margin
where it lands. The bound then involves the continuation's OSCILLATION, not its level, and it is
proportional to consumption rather than constant. -/

/-- **The proportional CES bound on saving, against an arbitrary continuation.** -/
theorem crra_policyOf_le_mul {γ θ G : ℝ} (hγ0 : 0 < γ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumptionAll) {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices assetFloor assetCap v) (hG : 0 ≤ G) (hosc : P.OscOn v G)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    P.policyOf v (a, z) - assetFloor
      ≤ ((P.discount : ℝ) * G / θ)
        * (P.consumptionFnOf v z a
            + (1 - θ) * (P.policyOf v (a, z) - assetFloor)) ^ γ := by
  simpa only [zero_add] using P.policyOf_le_mul_of_power_marginal (γ := γ) (η := 0)
    hθ0 hθ1 hv hG hosc (fun c d _ hcd hpositive => by
      simpa only [zero_add, hu] using
        crra_marginal_bound hγ0 (by simpa only [zero_add] using hpositive) hcd (le_refl d)) ha z
    (by simpa only [zero_add] using hpc v hv z a ha)

/-- **Saving never reaches the asset cap, against an arbitrary continuation.** The hypothesis is
the one `crra_policy_lt_assetCap` carries at the fixed point, so the calibrations already proved
for the CES witnesses discharge it. -/
theorem crra_policyOf_lt_assetCap {γ θ G : ℝ} (hγ0 : 0 < γ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumptionAll)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetFloor assetCap v) (hG : 0 ≤ G)
    (hosc : P.OscOn v G)
    (hlt : ((P.discount : ℝ) * G / θ)
        * (P.maxIncome + (1 + P.interest - θ) * assetCap - (1 - θ) * assetFloor) ^ γ
      < assetCap - assetFloor)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    P.policyOf v (a, z) < assetCap := by
  refine P.policyOf_lt_cap_of_power_bound (η := 0) hγ0.le hθ0.le hθ1.le
    (show 0 ≤ (P.discount : ℝ) * G / θ from
      div_nonneg (mul_nonneg P.discount.coe_nonneg hG) hθ0.le) ha z
    (by simpa only [zero_add] using (hpc v hv z a ha).le) ?_ ?_
  · simpa only [zero_add] using P.crra_policyOf_le_mul hγ0 hθ0 hθ1 hu hpc hv hG hosc ha z
  · simpa only [zero_add] using hlt

/-- **Carroll and Kimball for the bounded CES family, at the witnesses' own calibration.** The
cap hypothesis is exactly `crra_policy_lt_assetCap`'s, with `oscSpread` for `oscGap` — the same
number at a zero borrowing limit. -/
theorem concaveOn_consumptionFn_of_oscSpread {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ : 0 < (P.discount : ℝ)) (hb : P.Bounded)
    (hu : P.u = crraUtility γ)
    (hlt : ((P.discount : ℝ) * P.oscSpread / θ)
        * (P.maxIncome + (1 + P.interest - θ) * assetCap - (1 - θ) * assetFloor) ^ γ
      < assetCap - assetFloor)
    (z : Z) : ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) := by
  have hpc : P.PositiveConsumptionAll := by
    refine P.positiveConsumptionAll_of_marginalInada ?_
    rw [hb, hu]
    exact marginalInadaOn_Ici_crraUtility hγ0 hγ1
  have hslices : ∀ n : ℕ, ConcaveSlices assetFloor assetCap
      ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) :=
    P.concaveSlices_iterate_bellman concaveSlices_zero
  exact P.concaveOn_consumptionFn_of_iterates
    (P.concaveOn_consumptionFnOf_iterates_of_crra hpc hγ0 hβ hu
      (fun n a ha z' => P.crra_policyOf_lt_assetCap hγ0 hθ0 hθ1 hu hpc (hslices n)
        P.oscSpread_nonneg (P.oscOn_iterate n) hlt ha z')) z

/-! ### A slope bound from the OSCILLATION rather than the level

`contSlopeConstOf` prices the continuation's slope by `‖v‖`, which is what the CRRA arguments
had to hand. For utilities whose marginal value at zero is FINITE — CARA, and shifted CRRA with
a subsistence level — the consumption floor has to beat that slope, and the level is far too
crude a bound to beat. The oscillation is the right measure and it is the one the iterates
control (`oscOn_iterate`). The shared slope and consumption-floor arguments in
`ConsumptionFloor` use this oscillation directly; norm bounds are specializations. -/

/-! ### A consumption floor from a FINITE marginal bound

`exists_consumptionFnOf_floor_of_marginalInada` needs marginal utility to explode at zero, which
excludes every HARA member except pure CRRA. What the argument actually uses is that the
marginal value of consumption near zero beats the discounted slope of the continuation, and for
a finite marginal bound `M` that is an inequality to check rather than a triviality. -/

/-- **Positive consumption from a finite marginal bound**, against every continuation with
concave slices and oscillation at most `G`. -/
theorem consumptionFnOf_pos_of_marginal {M G : ℝ}
    (hM : MarginalBoundOn P.dom P.u M) (hG : 0 ≤ G)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetFloor assetCap v) (hosc : P.OscOn v G)
    (hlt : (P.discount : ℝ) * P.oscSlopeConst G < M)
    (z : Z) {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) : 0 < P.consumptionFnOf v z a := by
  obtain ⟨δ, hδ, hfloor⟩ := P.exists_consumptionFnOf_floor_of_marginal hM hG hv hosc hlt
  exact lt_of_lt_of_le hδ (hfloor z a ha)

/-! ### Single crossing in the continuation

Two continuations at the SAME state, ordered by increasing differences. This is
`policy_le_of_cont_increasingDifferences` of `IncomeFluctuationRateMonotone` read against
arbitrary continuations rather than at the fixed point, and it is what carries Light's step 5
along the iteration: the induction hypothesis is exactly increasing differences of the two
iterates. -/

/-- **Increasing differences between two continuations**, in the same economy. -/
def ContOfIncreasingDifferences (v w : (ℝ × Z) →ᵇ ℝ) : Prop :=
  ∀ (z : Z) (x y : ℝ), x ∈ Icc assetFloor assetCap → y ∈ Icc assetFloor assetCap → x ≤ y →
    P.contOf v z y - P.contOf v z x ≤ P.contOf w z y - P.contOf w z x

/-- **Increasing differences slice by slice**, between two bounded continuous functions on the
state space. This is the property the induction of Light's step 5 carries along the iteration:
it mentions no economy, so it makes sense between the iterates of two DIFFERENT economies, and
it is closed under pointwise limits. -/
def IncDiffSlices (assetFloor assetCap : ℝ) (v w : (ℝ × Z) →ᵇ ℝ) : Prop :=
  ∀ (z : Z) (x y : ℝ), x ∈ Icc assetFloor assetCap → y ∈ Icc assetFloor assetCap → x ≤ y →
    v (y, z) - v (x, z) ≤ w (y, z) - w (x, z)

omit [Fintype Z] [Nonempty Z] [DiscreteTopology Z] in
theorem incDiffSlices_zero (assetFloor assetCap : ℝ) :
    IncDiffSlices (Z := Z) assetFloor assetCap 0 0 := by
  intro z x y _ _ _
  simp

/-- It suffices to have increasing differences slice by slice in the continuations themselves. -/
theorem contOfIncreasingDifferences_of_slices {v w : (ℝ × Z) →ᵇ ℝ}
    (h : IncDiffSlices assetFloor assetCap v w) :
    P.ContOfIncreasingDifferences v w := by
  intro z x y hx hy hxy
  simp only [contOf, ← Finset.sum_sub_distrib, ← mul_sub]
  exact Finset.sum_le_sum fun z' _ =>
    mul_le_mul_of_nonneg_left (h z' x y hx hy hxy) (P.transitionMatrix_nonneg z z')

/-- **Single crossing in the continuation.** A household whose continuation has increasing
differences over another's saves at least as much, at every state. No derivative: the exchange
argument turns the two optimality comparisons into a sandwich that increasing differences
closes. -/
theorem policyOf_le_of_contOf_increasingDifferences {v w : (ℝ × Z) →ᵇ ℝ}
    (hw : ConcaveSlices assetFloor assetCap w) (hid : P.ContOfIncreasingDifferences v w)
    {a : ℝ} {z : Z} (ha : a ∈ Icc assetFloor assetCap) :
    P.policyOf v (a, z) ≤ P.policyOf w (a, z) := by
  by_contra hcon
  rw [not_le] at hcon
  set bV : ℝ := P.policyOf v (a, z) with hbV
  set bW : ℝ := P.policyOf w (a, z) with hbW
  have hbVm : bV ∈ P.toExtended.feasible (a, z) := P.policyOf_mem v (a, z)
  have hbWm : bW ∈ P.toExtended.feasible (a, z) := P.policyOf_mem w (a, z)
  have hcV : P.consumption (a, z) bV ∈ P.dom := P.consumption_policyOf_mem_dom v ha
  have hcW : P.consumption (a, z) bW ∈ P.dom := P.consumption_policyOf_mem_dom w ha
  have hoptV := P.objROf_le_of_mem v ha hbWm hcW
  have hoptW := P.objROf_le_of_mem w ha hbVm hcV
  have hidd := hid z bW bV (P.feasible_subset_region hbWm) (P.feasible_subset_region hbVm) hcon.le
  have hβ0 : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  simp only [objROf] at hoptV hoptW
  have hWeq : P.objROf w (a, z) bV = P.objROf w (a, z) bW := by
    simp only [objROf]
    nlinarith [hoptV, hoptW, mul_le_mul_of_nonneg_left hidd hβ0]
  have hbell : P.toExtended.objectiveE w (a, z) bV
      = ((P.toExtended.bellmanFn w (a, z) : ℝ) : EReal) := by
    rw [P.objectiveE_eq_coe_of w ha hbVm hcV, hWeq, ← P.objectiveE_eq_coe_of w ha hbWm hcW]
    exact P.policyOf_optimal w (a, z)
  exact absurd (P.optimal_action_unique_of_concaveSlices hw ha hbVm hbWm hbell
    (P.policyOf_optimal w (a, z))) (by intro h; rw [h] at hcon; exact lt_irrefl _ hcon)

/-- Consumption is correspondingly ordered the other way. -/
theorem consumptionFnOf_le_of_contOf_increasingDifferences {v w : (ℝ × Z) →ᵇ ℝ}
    (hw : ConcaveSlices assetFloor assetCap w) (hid : P.ContOfIncreasingDifferences v w)
    {a : ℝ} {z : Z} (ha : a ∈ Icc assetFloor assetCap) :
    P.consumptionFnOf w z a ≤ P.consumptionFnOf v z a := by
  simp only [consumptionFnOf, consumption]
  have := P.policyOf_le_of_contOf_increasingDifferences hw hid (z := z) ha
  linarith

end IncomeFluctuation

end LeanEconomics
