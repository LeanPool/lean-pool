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

Carroll and Kimball's induction step needs the CONTINUATION's consumption function to be
positive, concave and nondecreasing. Concavity is the induction hypothesis; the other two are
facts, but they are proved in this development only at the FIXED POINT
(`positiveConsumption_of_unbounded`, `consumptionFn_mono`). This file restates them for an
arbitrary continuation, which is what the induction sees.

Both proofs are the fixed-point proofs with `objR` replaced by `objROf`: the objective read
against an arbitrary continuation. The one structural fact they use is that the continuation
value depends on the saving chosen and the income state, never on current assets, so shifting
both households' plans by their resource gap leaves consumption alone and moves only the
continuation. That is true of `objROf` for exactly the same reason it is true of `objR`.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### The objective against an arbitrary continuation -/

/-- The continuation value of saving `x`, read against `v`. -/
noncomputable def contOf (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (x : ℝ) : ℝ :=
  ∑ z' : Z, P.transitionMatrix z z' * v (x, z')

/-- The objective, as a real number, read against `v`. -/
noncomputable def objROf (v : (ℝ × Z) →ᵇ ℝ) (s : ℝ × Z) (x : ℝ) : ℝ :=
  P.u (P.consumption s x) + P.discount * P.contOf v s.2 x

theorem concaveOn_contOf {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetFloor assetCap v) (z : Z) :
    ConcaveOn ℝ (Icc assetFloor assetCap) (P.contOf v z) := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  simp only [contOf, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z' _ => ?_
  have hz' := (hv z').2 hx hy hθ hφ hθφ
  simp only [smul_eq_mul] at hz'
  nlinarith [mul_le_mul_of_nonneg_left hz' (P.transitionMatrix_nonneg z z')]

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

/-- **Consumption at the optimum lies in the utility domain**, whatever the continuation. This
needs no positivity: the optimum's objective is a real number, so the reward is not `⊥`. -/
theorem consumption_policyOf_mem_dom (v : (ℝ × Z) →ᵇ ℝ) {z : Z} {a : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) : P.consumptionFnOf v z a ∈ P.dom :=
  (P.bellmanFn_eq_of_optimal (s := (a, z)) ha (P.policyOf_mem v (a, z))
    (P.policyOf_optimal v (a, z))).1

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

/-- The objective in the reals agrees with the extended objective where consumption is
positive. -/
theorem objectiveE_eq_coe_of (v : (ℝ × Z) →ᵇ ℝ) {a : ℝ} {z : Z} {x : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) (hx : x ∈ P.toExtended.feasible (a, z))
    (hcx : P.consumption (a, z) x ∈ P.dom) :
    P.toExtended.objectiveE v (a, z) x = ((P.objROf v (a, z) x : ℝ) : EReal) := by
  rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_coe_dom (s := (a, z)) ha hx hcx,
    ← EReal.coe_add]
  rfl

/-- **Any feasible action with positive consumption is worth at most the optimum**, whatever
the continuation. -/
theorem objROf_le_of_mem (v : (ℝ × Z) →ᵇ ℝ) {a : ℝ} {z : Z} {x : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) (hx : x ∈ P.toExtended.feasible (a, z))
    (hcx : P.consumption (a, z) x ∈ P.dom) :
    P.objROf v (a, z) x ≤ P.objROf v (a, z) (P.policyOf v (a, z)) := by
  have hc : P.consumptionFnOf v z a ∈ P.dom := P.consumption_policyOf_mem_dom v ha
  have h1 := P.lazyValue_le_dom v z ha hx hcx
  have h2 := P.lazyValue_eq_dom v z ha (P.policyOf_mem v (a, z)) hc
    (P.policyOf_optimal v (a, z))
  simp only [lazyValue] at h1 h2
  simp only [objROf, contOf, consumption]
  linarith

/-! ### Monotonicity of the saving policy -/

/-- **The optimal policy is increasing in assets, whatever the continuation.** The exchange
argument of `policy_mono`, run against `v`. -/
theorem policyOf_mono {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices assetFloor assetCap v) {a a' : ℝ} {z : Z}
    (ha : a ∈ Icc assetFloor assetCap) (ha' : a' ∈ Icc assetFloor assetCap) (hle : a ≤ a') :
    P.policyOf v (a, z) ≤ P.policyOf v (a', z) := by
  by_contra hcon
  rw [not_le] at hcon
  have hR : P.resources (a, z) ≤ P.resources (a', z) := P.resources_mono hle
  have hys : P.policyOf v (a, z) ∈ P.toExtended.feasible (a, z) := P.policyOf_mem v _
  have hys' : P.policyOf v (a, z) ∈ P.toExtended.feasible (a', z) := P.feasible_mono hle hys
  have hy's' : P.policyOf v (a', z) ∈ P.toExtended.feasible (a', z) := P.policyOf_mem v _
  have hy's : P.policyOf v (a', z) ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq] at hys ⊢
    rw [P.feasible_eq] at hy's'
    exact ⟨hy's'.1, le_trans hcon.le hys.2⟩
  have hcsy : P.consumption (a, z) (P.policyOf v (a, z)) ∈ P.dom :=
    P.consumption_policyOf_mem_dom v ha
  have hcs'y' : P.consumption (a', z) (P.policyOf v (a', z)) ∈ P.dom :=
    P.consumption_policyOf_mem_dom v ha'
  have hcsy' : P.consumption (a, z) (P.policyOf v (a', z)) ∈ P.dom := by
    refine P.dom_upward hcsy ?_
    simp only [consumption]; linarith
  have hcs'y : P.consumption (a', z) (P.policyOf v (a, z)) ∈ P.dom := by
    refine P.dom_upward hcsy ?_
    simp only [consumption]; linarith
  -- increasing differences, from concavity of `u` alone
  have hshift := P.strictConcaveOn_u_dom.concaveOn.sub_le_sub_of_shift
    (c₁ := P.resources (a, z) - P.policyOf v (a, z))
    (c₂ := P.resources (a, z) - P.policyOf v (a', z))
    (Δ := P.resources (a', z) - P.resources (a, z))
    (by simpa only [consumption] using hcsy)
    (by
      have he : P.resources (a, z) - P.policyOf v (a', z)
          + (P.resources (a', z) - P.resources (a, z))
          = P.consumption (a', z) (P.policyOf v (a', z)) := by simp only [consumption]; ring
      rw [he]; exact hcs'y')
    (by linarith) (by linarith)
  have hopt_s := P.objROf_le_of_mem v ha hy's hcsy'
  have hge : P.objROf v (a', z) (P.policyOf v (a', z))
      ≤ P.objROf v (a', z) (P.policyOf v (a, z)) := by
    simp only [objROf, consumption] at hopt_s ⊢
    have e₁ : P.resources (a, z) - P.policyOf v (a', z)
        + (P.resources (a', z) - P.resources (a, z))
        = P.resources (a', z) - P.policyOf v (a', z) := by ring
    have e₂ : P.resources (a, z) - P.policyOf v (a, z)
        + (P.resources (a', z) - P.resources (a, z))
        = P.resources (a', z) - P.policyOf v (a, z) := by ring
    rw [e₁, e₂] at hshift
    linarith
  have hopt' : P.objROf v (a', z) (P.policyOf v (a, z))
      = P.objROf v (a', z) (P.policyOf v (a', z)) :=
    le_antisymm (P.objROf_le_of_mem v ha' hys' hcs'y) hge
  have hbell : P.toExtended.objectiveE v (a', z) (P.policyOf v (a, z))
      = ((P.toExtended.bellmanFn v (a', z) : ℝ) : EReal) := by
    rw [P.objectiveE_eq_coe_of v ha' hys' hcs'y, hopt',
      ← P.objectiveE_eq_coe_of v ha' hy's' hcs'y']
    exact P.policyOf_optimal v _
  exact absurd (P.optimal_action_unique_of_concaveSlices hv (s := (a', z)) ha' hys' hy's'
    hbell (P.policyOf_optimal v _)) (by linarith)

/-! ### Monotonicity of the consumption function -/

/-- **Consumption rises with assets, whatever the continuation.** The exchange argument of
`consumptionFn_mono`, run against `v`. -/
theorem consumptionFnOf_mono {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices assetFloor assetCap v) {a a' : ℝ} {z : Z}
    (ha : a ∈ Icc assetFloor assetCap) (ha' : a' ∈ Icc assetFloor assetCap) (hle : a ≤ a') :
    P.consumptionFnOf v z a ≤ P.consumptionFnOf v z a' := by
  set Δ : ℝ := P.resources (a', z) - P.resources (a, z) with hΔdef
  have hΔ : 0 ≤ Δ := by rw [hΔdef]; linarith [P.resources_mono (z := z) hle]
  set b : ℝ := P.policyOf v (a, z) with hbdef
  set b' : ℝ := P.policyOf v (a', z) with hb'def
  by_contra hcon
  rw [not_le] at hcon
  have hgap : b + Δ < b' := by
    simp only [consumptionFnOf, consumption] at hcon
    rw [hΔdef]; linarith
  have hbmem : b ∈ P.toExtended.feasible (a, z) := P.policyOf_mem v _
  have hb'mem : b' ∈ P.toExtended.feasible (a', z) := P.policyOf_mem v _
  rw [P.feasible_eq] at hbmem hb'mem
  have hshiftup : b + Δ ∈ P.toExtended.feasible (a', z) := by
    rw [P.feasible_eq]
    exact ⟨by linarith [hbmem.1], by linarith [hb'mem.2]⟩
  have hshiftdown : b' - Δ ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq]
    refine ⟨by linarith [hbmem.1], ?_⟩
    have hms := P.maxSaving_le_add_sub (z := z) hle
    rw [← hΔdef] at hms
    linarith [hb'mem.2]
  have hc1 : P.consumption (a, z) b ∈ P.dom := P.consumption_policyOf_mem_dom v ha
  have hc2 : P.consumption (a', z) b' ∈ P.dom := P.consumption_policyOf_mem_dom v ha'
  have he1 : P.consumption (a', z) (b + Δ) = P.consumption (a, z) b := by
    simp only [consumption, hΔdef]; ring
  have he2 : P.consumption (a, z) (b' - Δ) = P.consumption (a', z) b' := by
    simp only [consumption, hΔdef]; ring
  have hI := P.objROf_le_of_mem v ha hshiftdown (by rw [he2]; exact hc2)
  have hII := P.objROf_le_of_mem v ha' hshiftup (by rw [he1]; exact hc1)
  have hbreg : b ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policyOf_mem v _)
  have hb'reg : b' ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policyOf_mem v _)
  have hshift := (P.concaveOn_contOf hv z).sub_le_sub_of_shift (c₁ := b) (c₂ := b' - Δ) (Δ := Δ)
    hbreg (by simpa using hb'reg) (by linarith) hΔ
  rw [sub_add_cancel] at hshift
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hshift hβ
  simp only [objROf, he1, he2] at hI hII
  have hIIeq : P.objROf v (a', z) (b + Δ) = P.objROf v (a', z) b' := by
    simp only [objROf, he1]
    nlinarith [hI, hII, hscaled]
  have hbell : P.toExtended.objectiveE v (a', z) (b + Δ)
      = ((P.toExtended.bellmanFn v (a', z) : ℝ) : EReal) := by
    rw [P.objectiveE_eq_coe_of v ha' hshiftup (by rw [he1]; exact hc1), hIIeq,
      ← P.objectiveE_eq_coe_of v ha' (P.policyOf_mem v _) hc2]
    exact P.policyOf_optimal v _
  exact absurd (P.optimal_action_unique_of_concaveSlices hv (s := (a', z)) ha' hshiftup
    (P.policyOf_mem v _) hbell (P.policyOf_optimal v _)) (by rw [← hb'def]; linarith)

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

/-- `v` varies by at most `G` over the asset region. -/
def OscOn (_P : IncomeFluctuation Z assetFloor assetCap) (v : (ℝ × Z) →ᵇ ℝ) (G : ℝ) : Prop :=
  ∀ x ∈ Icc assetFloor assetCap, ∀ y ∈ Icc assetFloor assetCap, ∀ z z' : Z,
    v (x, z) - v (y, z') ≤ G

theorem OscOn.mono {v : (ℝ × Z) →ᵇ ℝ} {G G' : ℝ} (h : P.OscOn v G) (hG : G ≤ G') :
    P.OscOn v G' := fun x hx y hy z z' => (h x hx y hy z z').trans hG

/-- The spread the iteration can produce: the reward's spread, amplified by `(1 - β)⁻¹`. At a
zero borrowing limit this is definitionally `CRRAConstants.oscGap`, so the witnesses' bounds on
that transfer unchanged. -/
noncomputable def oscSpread : ℝ :=
  (P.u P.maxConsumption - P.u P.minConsumption) / (1 - P.discount)

/-- At a zero borrowing limit the spread is `CRRAConstants.oscGap`. -/
theorem oscSpread_eq_oscGap {assetCap : ℝ} (Q : IncomeFluctuation Z 0 assetCap) :
    Q.oscSpread = Q.oscGap := rfl

theorem oscSpread_nonneg : 0 ≤ P.oscSpread := by
  have hβ : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
  refine div_nonneg (sub_nonneg.mpr ?_) (by linarith)
  exact P.monotoneOn_u_dom (P.mem_dom_of_pos P.minConsumption_pos)
    (P.mem_dom_of_pos P.maxConsumption_pos) P.minConsumption_le_maxConsumption

/-- The continuation inherits the bound, even across different income states. -/
theorem contOf_sub_le_osc {v : (ℝ × Z) →ᵇ ℝ} {G : ℝ} (h : P.OscOn v G) {x y : ℝ}
    (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap) (z z' : Z) :
    P.contOf v z x - P.contOf v z' y ≤ G := by
  classical
  obtain ⟨z₁, -, hz₁⟩ := Finset.exists_max_image Finset.univ (fun w : Z => v (x, w))
    ⟨Classical.ofNonempty, Finset.mem_univ _⟩
  obtain ⟨z₂, -, hz₂⟩ := Finset.exists_min_image Finset.univ (fun w : Z => v (y, w))
    ⟨Classical.ofNonempty, Finset.mem_univ _⟩
  have h1 : P.contOf v z x ≤ v (x, z₁) := by
    have hle : ∑ w : Z, P.transitionMatrix z w * v (x, w)
        ≤ ∑ w : Z, P.transitionMatrix z w * v (x, z₁) :=
      Finset.sum_le_sum fun w _ =>
        mul_le_mul_of_nonneg_left (hz₁ w (Finset.mem_univ _)) (P.transitionMatrix_nonneg z w)
    rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul] at hle
    exact hle
  have h2 : v (y, z₂) ≤ P.contOf v z' y := by
    have hle : ∑ w : Z, P.transitionMatrix z' w * v (y, z₂)
        ≤ ∑ w : Z, P.transitionMatrix z' w * v (y, w) :=
      Finset.sum_le_sum fun w _ =>
        mul_le_mul_of_nonneg_left (hz₂ w (Finset.mem_univ _)) (P.transitionMatrix_nonneg z' w)
    rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul] at hle
    exact hle
  linarith [h x hx y hy z₁ z₂]

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

/-- **The fixed point oscillates by no more than the iterates do**, being their uniform limit. -/
theorem oscOn_valueFunction : P.OscOn P.toExtended.valueFunction P.oscSpread := by
  intro x hx y hy z z'
  have hpt : ∀ p : ℝ × Z, Tendsto
      (fun n => ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) p) atTop
        (𝓝 (P.toExtended.valueFunction p)) := fun p =>
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (P.toExtended.tendsto_iterate_valueFunction 0)).tendsto_at p
  exact le_of_tendsto_of_tendsto ((hpt (x, z)).sub (hpt (y, z'))) tendsto_const_nhds
    (Eventually.of_forall fun n => P.oscOn_iterate n x hx y hy z z')

theorem abs_contOf_le (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (x : ℝ) : |P.contOf v z x| ≤ ‖v‖ := by
  have h1 : |∑ z' : Z, P.transitionMatrix z z' * v (x, z')|
      ≤ ∑ z' : Z, |P.transitionMatrix z z' * v (x, z')| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ z' : Z, |P.transitionMatrix z z' * v (x, z')|
      ≤ ∑ z' : Z, P.transitionMatrix z z' * ‖v‖ := by
    refine Finset.sum_le_sum fun z' _ => ?_
    rw [abs_mul, abs_of_nonneg (P.transitionMatrix_nonneg z z')]
    exact mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm (x, z'))
      (P.transitionMatrix_nonneg z z')
  rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul] at h2
  simp only [contOf]
  linarith

/-- **A uniform bound on saving from a uniform marginal bound**, against any continuation. -/
theorem policyOf_le_of_marginal_bound {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices assetFloor assetCap v) {m : ℝ} (hm : 0 < m)
    (hmarg : ∀ c d : ℝ, d ∈ P.dom → d ≤ c → c ≤ P.maxConsumption → m * (c - d) ≤ P.u c - P.u d)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    P.policyOf v (a, z) ≤ assetFloor + 4 * (P.discount : ℝ) * ‖v‖ / m := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hbound : (0 : ℝ) ≤ 4 * (P.discount : ℝ) * ‖v‖ / m := by positivity
  set b : ℝ := P.policyOf v (a, z) with hbdef
  have hbreg : b ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policyOf_mem v _)
  rcases eq_or_lt_of_le hbreg.1 with hzero | hbpos
  · rw [← hzero]; linarith
  set c : ℝ := P.consumptionFnOf v z a with hcdef
  have hcdom : c ∈ P.dom := P.consumption_policyOf_mem_dom v ha
  have hcpos : 0 ≤ c := P.nonneg_of_mem_dom hcdom
  have hres : P.resources (a, z) = c + b := by
    simp only [hcdef, consumptionFnOf, consumption]; ring
  set w : ℝ := (b + assetFloor) / 2 with hwdef
  have hw0 : assetFloor < w := by rw [hwdef]; linarith
  have hwb : w < b := by rw [hwdef]; linarith
  have heq : b - w = w - assetFloor := by rw [hwdef]; ring
  have hfeas : w ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq]
    exact ⟨hw0.le, by linarith [(P.policyOf_mem v (a, z)).2]⟩
  have hcons : P.consumption (a, z) w = c + (b - assetFloor) / 2 := by
    simp only [consumption, hres, hwdef]; ring
  have hdev : 0 < P.consumption (a, z) w := by rw [hcons]; linarith
  have hopt := P.objROf_le_of_mem v ha hfeas (P.mem_dom_of_pos hdev)
  simp only [objROf, hcons] at hopt
  rw [show P.consumption (a, z) (P.policyOf v (a, z)) = c from rfl,
    show P.policyOf v (a, z) = b from rfl] at hopt
  -- concavity of the continuation caps what the forgone saving could have repaid
  have hfloormem : assetFloor ∈ Icc assetFloor assetCap := ⟨le_rfl, P.assetFloor_le_assetCap⟩
  have hslope := (P.concaveOn_contOf hv z).slope_anti_adjacent hfloormem hbreg hw0 hwb
  have hb1 := abs_le.mp (P.abs_contOf_le v z w)
  have hb0 := abs_le.mp (P.abs_contOf_le v z assetFloor)
  have hloss : P.contOf v z b - P.contOf v z w ≤ 2 * ‖v‖ := by
    rw [div_le_div_iff₀ (by linarith) (by linarith), ← heq] at hslope
    have := le_of_mul_le_mul_right hslope (by linarith : (0 : ℝ) < b - w)
    linarith [hb1.2, hb0.1]
  have hcmax : c + (b - assetFloor) / 2 ≤ P.maxConsumption := by
    have hcm := P.consumption_le_maxConsumption (s := (a, z)) ha hw0.le
    rwa [hcons] at hcm
  have hmg := hmarg (c + (b - assetFloor) / 2) c hcdom (by linarith) hcmax
  rw [show c + (b - assetFloor) / 2 - c = (b - assetFloor) / 2 from by ring] at hmg
  rw [← sub_le_iff_le_add', le_div_iff₀ hm]
  nlinarith [hopt, hmg, mul_le_mul_of_nonneg_left hloss hβ]

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
  have hslices : ∀ n : ℕ, ConcaveSlices assetFloor assetCap (T^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact P.concaveSlices_bellman ih
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
      ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact P.concaveSlices_bellman ih
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

/-- The state-independent bound on the continuation's slope, read against `v`. -/
noncomputable def contSlopeConstOf (v : (ℝ × Z) →ᵇ ℝ) : ℝ := 4 * ‖v‖ / P.minConsumption

theorem contSlopeConstOf_nonneg (v : (ℝ × Z) →ᵇ ℝ) : 0 ≤ P.contSlopeConstOf v :=
  div_nonneg (by positivity) P.minConsumption_pos.le

/-- **The continuation's slope is bounded by a state-independent constant**, above
`assetFloor + minConsumption / 2`, whatever the continuation. -/
theorem contOf_sub_le {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetFloor assetCap v) (z : Z)
    {x y : ℝ} (hx : assetFloor + P.minConsumption / 2 ≤ x) (hxy : x < y)
    (hy : y ∈ Icc assetFloor assetCap) :
    P.contOf v z y - P.contOf v z x ≤ P.contSlopeConstOf v * (y - x) := by
  have hmin := P.minConsumption_pos
  have hx0 : assetFloor < x := by linarith
  have hslope := (P.concaveOn_contOf hv z).slope_anti_adjacent
    (mem_Icc.mpr ⟨le_rfl, P.assetFloor_le_assetCap⟩) hy hx0 hxy
  have hb1 := abs_le.mp (P.abs_contOf_le v z x)
  have hb2 := abs_le.mp (P.abs_contOf_le v z assetFloor)
  have hhalf : P.contSlopeConstOf v * (P.minConsumption / 2) = 2 * ‖v‖ := by
    rw [contSlopeConstOf]; field_simp; ring
  have hbig : P.contOf v z x - P.contOf v z assetFloor
      ≤ P.contSlopeConstOf v * (x - assetFloor) := by
    have hstep : P.contSlopeConstOf v * (P.minConsumption / 2)
        ≤ P.contSlopeConstOf v * (x - assetFloor) :=
      mul_le_mul_of_nonneg_left (by linarith) (P.contSlopeConstOf_nonneg v)
    rw [hhalf] at hstep
    linarith [hb1.2, hb2.1]
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at hslope
  have hprod : (P.contOf v z y - P.contOf v z x) * (x - assetFloor)
      ≤ (P.contSlopeConstOf v * (x - assetFloor)) * (y - x) := by
    nlinarith [hslope, hbig, (show (0 : ℝ) < y - x by linarith)]
  nlinarith [hprod, hx0]

/-- **A consumption floor from the margin, against an arbitrary continuation.** -/
theorem exists_consumptionFnOf_floor_of_marginalInada (hu : MarginalInadaOn P.dom P.u)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetFloor assetCap v) :
    ∃ δ > 0, ∀ (z : Z), ∀ a ∈ Icc assetFloor assetCap, δ ≤ P.consumptionFnOf v z a := by
  have hmin := P.minConsumption_pos
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  obtain ⟨δ₀, hδ₀, hδ⟩ := hu ((P.discount : ℝ) * P.contSlopeConstOf v + 1)
  refine ⟨min δ₀ (P.minConsumption / 4), lt_min hδ₀ (by linarith), fun z a ha => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  set d : ℝ := min δ₀ (P.minConsumption / 4) with hd
  set b : ℝ := P.policyOf v (a, z) with hbdef
  set c : ℝ := P.consumption (a, z) b with hcdef
  have hltc : c < d := hlt
  have hdδ : d ≤ δ₀ := min_le_left _ _
  have hd4 : d ≤ P.minConsumption / 4 := min_le_right _ _
  have hcmem : c ∈ P.dom := P.consumption_policyOf_mem_dom v ha
  have hc0 : 0 ≤ c := P.nonneg_of_mem_dom hcmem
  have hres : P.minConsumption ≤ P.resources (a, z) - assetFloor :=
    P.minConsumption_le_consumption_floor (a, z)
  have hcb : c = P.resources (a, z) - b := rfl
  have hbig : assetFloor + 3 * P.minConsumption / 4 ≤ b := by rw [hcb] at hltc; linarith
  set h : ℝ := d - c with hhdef
  have hh0 : 0 < h := by rw [hhdef]; linarith
  have hhle : h ≤ P.minConsumption / 4 := by rw [hhdef]; linarith
  have hlow : assetFloor + P.minConsumption / 2 ≤ b - h := by linarith
  have hbmem : b ∈ Icc assetFloor assetCap :=
    P.feasible_subset_region (P.policyOf_mem v (a, z))
  have hfeas : b - h ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq]
    exact ⟨by linarith [hbmem.1], by linarith [(P.policyOf_mem v (a, z)).2]⟩
  have hcd : P.consumption (a, z) (b - h) = d := by
    simp only [consumption] at hcb ⊢; linarith
  have hdpos : 0 < P.consumption (a, z) (b - h) := by rw [hcd]; linarith
  have hopt := P.objROf_le_of_mem v ha hfeas (P.mem_dom_of_pos hdpos)
  simp only [objROf, hcd] at hopt
  have hslope := P.contOf_sub_le hv z hlow (by linarith) hbmem
  rw [show b - (b - h) = h from by ring] at hslope
  have hscaled := mul_le_mul_of_nonneg_left hslope hβ
  have hutil : P.u d - P.u c
      ≤ ((P.discount : ℝ) * P.contSlopeConstOf v) * (d - c) := by
    have e : (P.discount : ℝ) * (P.contSlopeConstOf v * h)
        = ((P.discount : ℝ) * P.contSlopeConstOf v) * (d - c) := by rw [hhdef]; ring
    linarith [hopt, hscaled, e.le, e.ge]
  have hmarg := hδ c d hcmem (by linarith) hdδ
  rw [show ((P.discount : ℝ) * P.contSlopeConstOf v + 1) * (d - c)
      = ((P.discount : ℝ) * P.contSlopeConstOf v) * (d - c) + (d - c) from by ring] at hmarg
  rw [hhdef] at hh0
  linarith [hmarg, hutil, hh0]

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
theorem crra_policyOf_le_mul {γ θ G : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumptionAll) {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices assetFloor assetCap v) (hG : 0 ≤ G) (hosc : P.OscOn v G)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    P.policyOf v (a, z) - assetFloor
      ≤ ((P.discount : ℝ) * G / θ)
        * (P.consumptionFnOf v z a
            + (1 - θ) * (P.policyOf v (a, z) - assetFloor)) ^ γ := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  set b : ℝ := P.policyOf v (a, z) with hbdef
  set c : ℝ := P.consumptionFnOf v z a with hcdef
  have hbreg : b ∈ Icc assetFloor assetCap :=
    P.feasible_subset_region (P.policyOf_mem v (a, z))
  have hcpos : 0 < c := hpc v hv z a ha
  have hbase : (0 : ℝ) < c + (1 - θ) * (b - assetFloor) := by
    have h := mul_nonneg (show (0 : ℝ) ≤ 1 - θ by linarith)
      (show (0 : ℝ) ≤ b - assetFloor by linarith [hbreg.1])
    linarith
  have hrpow : (0 : ℝ) < (c + (1 - θ) * (b - assetFloor)) ^ γ := Real.rpow_pos_of_pos hbase _
  rcases eq_or_lt_of_le hbreg.1 with hzero | hbpos
  · rw [← hzero, sub_self]
    positivity
  have hbf : (0 : ℝ) < b - assetFloor := by linarith
  set w : ℝ := assetFloor + θ * (b - assetFloor) with hwdef
  have hw0 : assetFloor < w := by rw [hwdef]; nlinarith
  have hwb : w < b := by rw [hwdef]; nlinarith
  have hwmem : w ∈ Icc assetFloor assetCap := ⟨hw0.le, by linarith [hbreg.2]⟩
  have hfeas : w ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq]
    exact ⟨hw0.le, by linarith [(P.policyOf_mem v (a, z)).2]⟩
  have hcb : c = P.resources (a, z) - b := rfl
  have hcons : P.consumption (a, z) w = c + (1 - θ) * (b - assetFloor) := by
    simp only [consumption, hwdef]; rw [hcb]; ring
  have hdev : 0 < P.consumption (a, z) w := by rw [hcons]; linarith
  have hopt := P.objROf_le_of_mem v ha hfeas (P.mem_dom_of_pos hdev)
  simp only [objROf, hcons] at hopt
  rw [show P.consumption (a, z) (P.policyOf v (a, z)) = c from rfl,
    show P.policyOf v (a, z) = b from rfl] at hopt
  -- concavity of the continuation, priced against its oscillation
  have hslope := (P.concaveOn_contOf hv z).slope_anti_adjacent
    (mem_Icc.mpr ⟨le_rfl, P.assetFloor_le_assetCap⟩) hbreg hw0 hwb
  have hgap := P.contOf_sub_le_osc hosc hwmem
    (show assetFloor ∈ Icc assetFloor assetCap from ⟨le_rfl, P.assetFloor_le_assetCap⟩) z z
  have hbw : b - w = (1 - θ) * (b - assetFloor) := by rw [hwdef]; ring
  have hwf : w - assetFloor = θ * (b - assetFloor) := by rw [hwdef]; ring
  have hloss : P.contOf v z b - P.contOf v z w ≤ (1 - θ) / θ * G := by
    rw [div_le_div_iff₀ (show (0 : ℝ) < b - w by linarith)
      (show (0 : ℝ) < w - assetFloor by linarith), hbw, hwf] at hslope
    have h2 : (P.contOf v z b - P.contOf v z w) * (θ * (b - assetFloor))
        ≤ G * ((1 - θ) * (b - assetFloor)) := by
      nlinarith [hslope, hgap, mul_pos (show (0:ℝ) < 1 - θ by linarith) hbf]
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ0]
    nlinarith [h2, hbf]
  -- the marginal gain, priced where it lands
  have hmg : (c + (1 - θ) * (b - assetFloor)) ^ (-γ) * ((1 - θ) * (b - assetFloor))
      ≤ P.u (c + (1 - θ) * (b - assetFloor)) - P.u c := by
    rw [hu]
    have hbound := crra_marginal_bound_Ici hγ0 hγ1 (mem_Ici.mpr hcpos.le)
      (le_add_of_nonneg_right (mul_nonneg (by linarith) hbf.le))
      (le_refl (c + (1 - θ) * (b - assetFloor)))
    simpa using hbound
  have hmid : P.u (c + (1 - θ) * (b - assetFloor)) - P.u c
      ≤ (P.discount : ℝ) * (P.contOf v z b - P.contOf v z w) := by
    have hd : (P.discount : ℝ) * (P.contOf v z b - P.contOf v z w)
        = (P.discount : ℝ) * P.contOf v z b - (P.discount : ℝ) * P.contOf v z w := by ring
    linarith [hopt, hd.le, hd.ge]
  have hkey := le_trans hmg (le_trans hmid (mul_le_mul_of_nonneg_left hloss hβ))
  rw [Real.rpow_neg hbase.le γ] at hkey
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hexp : ((c + (1 - θ) * (b - assetFloor)) ^ γ)⁻¹ * ((1 - θ) * (b - assetFloor))
      = (1 - θ) * ((b - assetFloor) / (c + (1 - θ) * (b - assetFloor)) ^ γ) := by field_simp
  rw [hexp, show (P.discount : ℝ) * ((1 - θ) / θ * G)
      = (1 - θ) * ((P.discount : ℝ) * G / θ) from by ring] at hkey
  have hdiv := le_of_mul_le_mul_left hkey h1θ
  rw [div_le_iff₀ hrpow] at hdiv
  linarith

/-- **Saving never reaches the asset cap, against an arbitrary continuation.** The hypothesis is
the one `crra_policy_lt_assetCap` carries at the fixed point, so the calibrations already proved
for the CES witnesses discharge it. -/
theorem crra_policyOf_lt_assetCap {γ θ G : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hu : P.u = crraUtility γ) (hpc : P.PositiveConsumptionAll)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetFloor assetCap v) (hG : 0 ≤ G)
    (hosc : P.OscOn v G)
    (hlt : ((P.discount : ℝ) * G / θ)
        * (P.maxIncome + (1 + P.interest - θ) * assetCap - (1 - θ) * assetFloor) ^ γ
      < assetCap - assetFloor)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    P.policyOf v (a, z) < assetCap := by
  by_contra hcon
  rw [not_lt] at hcon
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  set b : ℝ := P.policyOf v (a, z) with hbdef
  set c : ℝ := P.consumptionFnOf v z a with hcdef
  have hbreg : b ∈ Icc assetFloor assetCap :=
    P.feasible_subset_region (P.policyOf_mem v (a, z))
  have hkey := P.crra_policyOf_le_mul hγ0 hγ1 hθ0 hθ1 hu hpc hv hG hosc ha z
  rw [← hbdef, ← hcdef] at hkey
  have hcpos : 0 < c := hpc v hv z a ha
  have hres : P.resources (a, z) - assetFloor ≤ P.maxConsumption :=
    P.consumption_le_maxConsumption (s := (a, z)) ha le_rfl
  have hsum : c + (1 - θ) * (b - assetFloor)
      = (P.resources (a, z) - assetFloor) - θ * (b - assetFloor) := by
    simp only [hcdef, consumptionFnOf, consumption, ← hbdef]; ring
  have hle : c + (1 - θ) * (b - assetFloor)
      ≤ P.maxIncome + (1 + P.interest - θ) * assetCap - (1 - θ) * assetFloor := by
    rw [hsum]
    have hθb : θ * (assetCap - assetFloor) ≤ θ * (b - assetFloor) :=
      mul_le_mul_of_nonneg_left (by linarith) hθ0.le
    simp only [maxConsumption] at hres
    nlinarith [hres, hθb]
  have hnn : (0 : ℝ) ≤ c + (1 - θ) * (b - assetFloor) := by
    have h := mul_nonneg (show (0 : ℝ) ≤ 1 - θ by linarith)
      (show (0 : ℝ) ≤ b - assetFloor by linarith [hbreg.1])
    linarith
  have hmono : (c + (1 - θ) * (b - assetFloor)) ^ γ
      ≤ (P.maxIncome + (1 + P.interest - θ) * assetCap - (1 - θ) * assetFloor) ^ γ :=
    Real.rpow_le_rpow hnn hle hγ0.le
  have hcoef : (0 : ℝ) ≤ (P.discount : ℝ) * G / θ := by positivity
  nlinarith [hkey, mul_le_mul_of_nonneg_left hmono hcoef, hlt]

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
      ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact P.concaveSlices_bellman ih
  exact P.concaveOn_consumptionFn_of_iterates
    (P.concaveOn_consumptionFnOf_iterates_of_crra hpc hγ0 hβ hu
      (fun n a ha z' => P.crra_policyOf_lt_assetCap hγ0 hγ1 hθ0 hθ1 hu hpc (hslices n)
        P.oscSpread_nonneg (P.oscOn_iterate n) hlt ha z')) z



/-! ### A slope bound from the OSCILLATION rather than the level

`contSlopeConstOf` prices the continuation's slope by `‖v‖`, which is what the CRRA arguments
had to hand. For utilities whose marginal value at zero is FINITE — CARA, and shifted CRRA with
a subsistence level — the consumption floor has to beat that slope, and the level is far too
crude a bound to beat. The oscillation is the right measure and it is the one the iterates
control (`oscOn_iterate`), so the same geometry is redone with `G` in place of `2‖v‖`. -/

/-- The slope constant an oscillation bound `G` gives. -/
noncomputable def oscSlopeConst (G : ℝ) : ℝ := 2 * G / P.minConsumption

theorem oscSlopeConst_nonneg {G : ℝ} (hG : 0 ≤ G) : 0 ≤ P.oscSlopeConst G :=
  div_nonneg (by linarith) P.minConsumption_pos.le

/-- **The continuation's slope, priced by its oscillation**, above
`assetFloor + minConsumption / 2`. -/
theorem contOf_sub_le_of_osc {v : (ℝ × Z) →ᵇ ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hv : ConcaveSlices assetFloor assetCap v) (hosc : P.OscOn v G) (z : Z) {x y : ℝ}
    (hx : assetFloor + P.minConsumption / 2 ≤ x) (hxy : x < y)
    (hy : y ∈ Icc assetFloor assetCap) :
    P.contOf v z y - P.contOf v z x ≤ P.oscSlopeConst G * (y - x) := by
  have hmin := P.minConsumption_pos
  have hx0 : assetFloor < x := by linarith
  have hxmem : x ∈ Icc assetFloor assetCap := ⟨hx0.le, by linarith [hy.2]⟩
  have hslope := (P.concaveOn_contOf hv z).slope_anti_adjacent
    (mem_Icc.mpr ⟨le_rfl, P.assetFloor_le_assetCap⟩) hy hx0 hxy
  have hgap := P.contOf_sub_le_osc hosc hxmem
    (show assetFloor ∈ Icc assetFloor assetCap from ⟨le_rfl, P.assetFloor_le_assetCap⟩) z z
  have hhalf : P.oscSlopeConst G * (P.minConsumption / 2) = G := by
    rw [oscSlopeConst]; field_simp
  have hbig : P.contOf v z x - P.contOf v z assetFloor
      ≤ P.oscSlopeConst G * (x - assetFloor) := by
    have hstep : P.oscSlopeConst G * (P.minConsumption / 2)
        ≤ P.oscSlopeConst G * (x - assetFloor) :=
      mul_le_mul_of_nonneg_left (by linarith) (P.oscSlopeConst_nonneg hG)
    rw [hhalf] at hstep
    linarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at hslope
  have hprod : (P.contOf v z y - P.contOf v z x) * (x - assetFloor)
      ≤ (P.oscSlopeConst G * (x - assetFloor)) * (y - x) := by
    nlinarith [hslope, hbig, (show (0 : ℝ) < y - x by linarith)]
  nlinarith [hprod, hx0]

/-! ### A consumption floor from a FINITE marginal bound

`exists_consumptionFnOf_floor_of_marginalInada` needs marginal utility to explode at zero, which
excludes every HARA member except pure CRRA. What the argument actually uses is that the
marginal value of consumption near zero beats the discounted slope of the continuation, and for
a finite marginal bound `M` that is an inequality to check rather than a triviality. -/

/-- **The consumption floor, from a finite marginal bound.** -/
theorem exists_consumptionFnOf_floor_of_marginal {M G : ℝ}
    (hM : MarginalBoundOn P.dom P.u M) (hG : 0 ≤ G)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetFloor assetCap v) (hosc : P.OscOn v G)
    (hlt : (P.discount : ℝ) * P.oscSlopeConst G < M) :
    ∃ δ > 0, ∀ (z : Z), ∀ a ∈ Icc assetFloor assetCap, δ ≤ P.consumptionFnOf v z a := by
  have hmin := P.minConsumption_pos
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  obtain ⟨δ₀, hδ₀, hδ⟩ := hM
  refine ⟨min δ₀ (P.minConsumption / 4), lt_min hδ₀ (by linarith), fun z a ha => ?_⟩
  by_contra hlt'
  rw [not_le] at hlt'
  set d : ℝ := min δ₀ (P.minConsumption / 4) with hd
  set b : ℝ := P.policyOf v (a, z) with hbdef
  set c : ℝ := P.consumption (a, z) b with hcdef
  have hltc : c < d := hlt'
  have hdδ : d ≤ δ₀ := min_le_left _ _
  have hd4 : d ≤ P.minConsumption / 4 := min_le_right _ _
  have hcmem : c ∈ P.dom := P.consumption_policyOf_mem_dom v ha
  have hc0 : 0 ≤ c := P.nonneg_of_mem_dom hcmem
  have hres : P.minConsumption ≤ P.resources (a, z) - assetFloor :=
    P.minConsumption_le_consumption_floor (a, z)
  have hcb : c = P.resources (a, z) - b := rfl
  have hbig : assetFloor + 3 * P.minConsumption / 4 ≤ b := by rw [hcb] at hltc; linarith
  set hgap : ℝ := d - c with hhdef
  have hh0 : 0 < hgap := by rw [hhdef]; linarith
  have hhle : hgap ≤ P.minConsumption / 4 := by rw [hhdef]; linarith
  have hlow : assetFloor + P.minConsumption / 2 ≤ b - hgap := by linarith
  have hbmem : b ∈ Icc assetFloor assetCap :=
    P.feasible_subset_region (P.policyOf_mem v (a, z))
  have hfeas : b - hgap ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq]
    exact ⟨by linarith [hbmem.1], by linarith [(P.policyOf_mem v (a, z)).2]⟩
  have hcd : P.consumption (a, z) (b - hgap) = d := by
    simp only [consumption] at hcb ⊢; linarith
  have hdpos : 0 < P.consumption (a, z) (b - hgap) := by rw [hcd]; linarith
  have hopt := P.objROf_le_of_mem v ha hfeas (P.mem_dom_of_pos hdpos)
  simp only [objROf, hcd] at hopt
  have hslope := P.contOf_sub_le_of_osc hG hv hosc z hlow (by linarith) hbmem
  rw [show b - (b - hgap) = hgap from by ring] at hslope
  have hscaled := mul_le_mul_of_nonneg_left hslope hβ
  have hutil : P.u d - P.u c ≤ ((P.discount : ℝ) * P.oscSlopeConst G) * (d - c) := by
    have e : (P.discount : ℝ) * (P.oscSlopeConst G * hgap)
        = ((P.discount : ℝ) * P.oscSlopeConst G) * (d - c) := by rw [hhdef]; ring
    linarith [hopt, hscaled, e.le, e.ge]
  have hmarg := hδ c d hcmem (by linarith) hdδ
  rw [hhdef] at hh0
  nlinarith [hmarg, hutil, hh0, hlt]

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
