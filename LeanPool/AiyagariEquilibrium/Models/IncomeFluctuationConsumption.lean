/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationMonotone
public import LeanPool.AiyagariEquilibrium.Analysis.RelativeRiskAversion

/-!
# The consumption function

`consumptionFn z a` is what the household actually eats at assets `a`: cash on hand less the
optimal saving. Light (2018) Theorem 1 needs three things from it — positivity, monotonicity,
and CONCAVITY in assets (his Lemma 4). The first two are proved here. The third is not, and
this file says exactly why.

## Consumption rises with assets

`consumptionFn_mono` is the theorem of this file, and it is the mirror image of `policy_mono`.
That one swapped the two households' savings and used increasing differences of `u`; this one
swaps them by the SAME resource gap, `b ↦ b + Δ` and `b' ↦ b' - Δ`, which leaves every
consumption level untouched and moves only the continuation. So the roles are exchanged: the
argument runs on increasing differences of the CONTINUATION, and it is again
`ConcaveOn.sub_le_sub_of_shift` — applied to `cont` rather than to `u`.

Together the two say the marginal propensities are both non-negative:

  `0 ≤ c(a') - c(a) ≤ resources(a') - resources(a)`   for `a ≤ a'`,

which is `sub_le_sub_of_le_resources`. Neither half needs a derivative.

## Concavity is NOT free, and this file does not prove it

It would be pleasant if concavity of `c` followed from concavity of `u` and of the value
function, the way monotonicity does. It does not. With CRRA `u` and a continuation of constant
absolute risk tolerance, the marginal propensity to consume is `T_u(c) / (T_u(c) + T_W(b))`
with `T_u(c) = c/γ` and `T_W` constant, which RISES with consumption — so the consumption
function is CONVEX. Concavity therefore cannot follow from concavity of the two primitives; it
needs the continuation to inherit the curvature of `u`, which is what makes it a statement
about the FIXED POINT rather than about one application of the operator.

That is the Carroll and Kimball (1996) theorem — the Bellman operator preserves concavity of
the consumption function when utility is HARA — and it is the shape of the closed-class
arguments already used here for monotonicity, concavity, Lipschitz bounds and increasing
differences. Light states it as his Lemma 4 and cites Jensen (2017) rather than proving it.
It is left as a hypothesis: `mul_marginal_le_of_scale` takes it as an argument, and everything
else that theorem needs about the consumption function is discharged here.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-- **The continuation value is concave in savings**, being a non-negative combination of the
value function's concave slices. -/
theorem concaveOn_cont (z : Z) : ConcaveOn ℝ (Icc assetFloor assetCap) (P.cont z) := by
  exact P.concaveOn_contOf P.concaveOn_valueFunction z

/-- Consumption at the optimum, as a function of assets. -/
noncomputable def consumptionFn (z : Z) (a : ℝ) : ℝ :=
  P.consumption (a, z) (P.policy (a, z))

/-- The consumption function implied by an arbitrary continuation. -/
noncomputable def consumptionFnOf (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (a : ℝ) : ℝ :=
  P.consumption (a, z) (P.policyOf v (a, z))

theorem consumptionFnOf_valueFunction :
    P.consumptionFnOf P.toExtended.valueFunction = P.consumptionFn := rfl

/-- **Consumption at the optimum lies in the utility domain**, whatever the continuation. This
needs no positivity: the optimum's objective is a real number, so the reward is not `⊥`. -/
theorem consumption_policyOf_mem_dom (v : (ℝ × Z) →ᵇ ℝ) {z : Z} {a : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) : P.consumptionFnOf v z a ∈ P.dom :=
  (P.bellmanFn_eq_of_optimal (s := (a, z)) ha (P.policyOf_mem v (a, z))
    (P.policyOf_optimal v (a, z))).1

theorem consumptionFn_pos (hpc : P.PositiveConsumption) {a : ℝ} (ha : a ∈ Icc assetFloor assetCap)
    (z : Z) :
    0 < P.consumptionFn z a :=
  P.consumption_policy_pos hpc (s := (a, z)) ha

/-- The saving cap cannot grow by more than resources do. -/
theorem maxSaving_le_add_sub {a a' : ℝ} {z : Z} (hle : a ≤ a') :
    P.maxSaving (a', z)
      ≤ P.maxSaving (a, z) + (P.resources (a', z) - P.resources (a, z)) := by
  have hΔ : 0 ≤ P.resources (a', z) - P.resources (a, z) := by
    linarith [P.resources_mono (z := z) hle]
  have hmin : min assetCap (P.resources (a', z))
      ≤ min assetCap (P.resources (a, z)) + (P.resources (a', z) - P.resources (a, z)) := by
    rcases le_total assetCap (P.resources (a, z)) with h | h
    · rw [min_eq_left h]
      exact le_trans (min_le_left _ _) (by linarith)
    · rw [min_eq_right h]
      exact le_trans (min_le_right _ _) (by linarith)
  rw [P.maxSaving_eq, P.maxSaving_eq]
  linarith

/-- **Consumption is ordered across states** against a continuation whose increments are
antitone in income. -/
theorem consumptionFnOf_le_across_states {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap) fun a => v (a, z)) {z₁ z₂ : Z}
    (hid : ∀ x y : ℝ, x ∈ Icc assetFloor assetCap → y ∈ Icc assetFloor assetCap → x ≤ y →
      P.contOf v z₂ y - P.contOf v z₂ x ≤ P.contOf v z₁ y - P.contOf v z₁ x)
    {a a' : ℝ} (ha : a ∈ Icc assetFloor assetCap) (ha' : a' ∈ Icc assetFloor assetCap)
    (hres : P.resources (a, z₁) ≤ P.resources (a', z₂)) :
    P.consumptionFnOf v z₁ a ≤ P.consumptionFnOf v z₂ a' := by
  set Δ : ℝ := P.resources (a', z₂) - P.resources (a, z₁) with hΔdef
  have hΔ : 0 ≤ Δ := by rw [hΔdef]; linarith
  set b : ℝ := P.policyOf v (a, z₁) with hbdef
  set b' : ℝ := P.policyOf v (a', z₂) with hb'def
  by_contra hcon
  rw [not_le] at hcon
  have hgap : b + Δ < b' := by
    simp only [consumptionFnOf, consumption] at hcon
    rw [hΔdef]; linarith
  have hbmem : b ∈ P.toExtended.feasible (a, z₁) := P.policyOf_mem v (a, z₁)
  have hb'mem : b' ∈ P.toExtended.feasible (a', z₂) := P.policyOf_mem v (a', z₂)
  rw [P.feasible_eq] at hbmem hb'mem
  have hms : P.maxSaving (a', z₂) ≤ P.maxSaving (a, z₁) + Δ := by
    have hmin : min assetCap (P.resources (a', z₂))
        ≤ min assetCap (P.resources (a, z₁)) + Δ := by
      rcases le_total assetCap (P.resources (a, z₁)) with h | h
      · rw [min_eq_left h]
        exact le_trans (min_le_left _ _) (by linarith)
      · rw [min_eq_right h]
        exact le_trans (min_le_right _ _) (by rw [hΔdef]; linarith)
    rw [P.maxSaving_eq, P.maxSaving_eq]
    linarith
  have hshiftup : b + Δ ∈ P.toExtended.feasible (a', z₂) := by
    rw [P.feasible_eq]
    exact ⟨by linarith [hbmem.1], by linarith [hb'mem.2]⟩
  have hshiftdown : b' - Δ ∈ P.toExtended.feasible (a, z₁) := by
    rw [P.feasible_eq]
    exact ⟨by linarith [hbmem.1], by linarith [hb'mem.2]⟩
  have hc1 : P.consumption (a, z₁) b ∈ P.dom := P.consumption_policyOf_mem_dom v ha
  have hc2 : P.consumption (a', z₂) b' ∈ P.dom := P.consumption_policyOf_mem_dom v ha'
  have he1 : P.consumption (a', z₂) (b + Δ) = P.consumption (a, z₁) b := by
    simp only [consumption, hΔdef]; ring
  have he2 : P.consumption (a, z₁) (b' - Δ) = P.consumption (a', z₂) b' := by
    simp only [consumption, hΔdef]; ring
  have hI := P.objROf_le_of_mem v ha hshiftdown (by rw [he2]; exact hc2)
  have hII := P.objROf_le_of_mem v ha' hshiftup (by rw [he1]; exact hc1)
  have hbreg : b ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policyOf_mem v _)
  have hb'reg : b' ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policyOf_mem v _)
  -- concavity of the poorer continuation, shifted by `Δ`
  have hshift := (P.concaveOn_contOf hv z₁).sub_le_sub_of_shift (c₁ := b) (c₂ := b' - Δ) (Δ := Δ)
    hbreg (by simpa using hb'reg) (by linarith) hΔ
  rw [sub_add_cancel] at hshift
  -- and the richer continuation is flatter still
  have hacross := hid (b + Δ) b' ⟨by linarith [hbreg.1], by linarith [hb'reg.2]⟩ hb'reg hgap.le
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hchain := mul_le_mul_of_nonneg_left (le_trans hacross hshift) hβ
  simp only [objROf, he1, he2] at hI hII
  have hIIeq : P.objROf v (a', z₂) (b + Δ) = P.objROf v (a', z₂) b' := by
    simp only [objROf, he1]
    linarith [hI, hII, hchain]
  have hbell : P.toExtended.objectiveE v (a', z₂) (b + Δ)
      = ((P.toExtended.bellmanFn v (a', z₂) : ℝ) : EReal) := by
    rw [P.objectiveE_eq_coe_of v ha' hshiftup (by rw [he1]; exact hc1), hIIeq,
      ← P.objectiveE_eq_coe_of v ha' (P.policyOf_mem v _) hc2]
    exact P.policyOf_optimal v _
  exact absurd (P.optimal_action_unique_of_concave hv ha' hshiftup (P.policyOf_mem v _)
    hbell (P.policyOf_optimal v _)) (by rw [← hb'def]; linarith)

/-- **Consumption rises with assets, whatever the continuation.** The exchange argument of
`consumptionFn_mono`, run against `v`. -/
theorem consumptionFnOf_mono {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap) fun a => v (a, z)) {a a' : ℝ} {z : Z}
    (ha : a ∈ Icc assetFloor assetCap) (ha' : a' ∈ Icc assetFloor assetCap) (hle : a ≤ a') :
    P.consumptionFnOf v z a ≤ P.consumptionFnOf v z a' := by
  exact P.consumptionFnOf_le_across_states hv (fun _ _ _ _ _ => le_rfl) ha ha'
    (P.resources_mono hle)

/-- **Consumption rises with assets.** The two households swap savings plans shifted by their
resource gap, which leaves consumption alone and moves only the continuation — so the
comparison is increasing differences of the continuation, exactly as `policy_mono` is
increasing differences of `u`. -/
theorem consumptionFn_mono {a a' : ℝ} {z : Z}
    (ha : a ∈ Icc assetFloor assetCap)
    (ha' : a' ∈ Icc assetFloor assetCap) (hle : a ≤ a') :
    P.consumptionFn z a ≤ P.consumptionFn z a' := by
  simpa only [P.consumptionFnOf_valueFunction] using
    P.consumptionFnOf_mono P.concaveOn_valueFunction ha ha' hle

/-- **The marginal propensities are both non-negative.** Consumption rises with assets, and by
no more than resources do — the second half is `policy_mono`. -/
theorem sub_le_sub_of_le_resources {a a' : ℝ} {z : Z}
    (ha : a ∈ Icc assetFloor assetCap)
    (ha' : a' ∈ Icc assetFloor assetCap) (hle : a ≤ a') :
    0 ≤ P.consumptionFn z a' - P.consumptionFn z a ∧
      P.consumptionFn z a' - P.consumptionFn z a
        ≤ P.resources (a', z) - P.resources (a, z) := by
  refine ⟨by linarith [P.consumptionFn_mono (z := z) ha ha' hle], ?_⟩
  have := P.policy_mono (z := z) ha ha' hle
  simp only [consumptionFn, consumption]
  linarith

theorem monotoneOn_consumptionFn (z : Z) :
    MonotoneOn (P.consumptionFn z) (Icc assetFloor assetCap) :=
  fun _ ha _ ha' h => P.consumptionFn_mono ha ha' h

/-! ### A linear lower bound on consumption makes assets decline

Ma and Toda (2022) prove that the consumption function is asymptotically LINEAR whenever
marginal utility is regularly varying, and characterise the slope. Their Corollary 2.10 covers
this model — constant discount factor and return, bounded relative risk aversion, `R ≥ 1` — and
gives the asymptotic marginal propensity to consume in closed form,

  `c_bar = 1 - (β R^(1-γ))^(1/γ)`.

That result is about the UNCAPPED problem and is not proved here. What is proved here is the
consequence, which is what this development actually wants: a linear lower bound on consumption
forces assets to fall, above an explicit threshold. That is precisely the hypothesis `hdecl` of
`exists_exhaust_of_decline`, on which the whole Doeblin uniqueness and convergence argument
rests, and which has been a raw assumption until now.

The two fit together exactly. With Ma and Toda's slope the asymptotic growth factor of assets is
`(1 - c_bar) R = (β R)^(1/γ)` — `one_sub_mpc_mul_of_asymptotic`, below — so the condition
`(1 - ε) (1 + r) < 1` demanded by `policy_lt_self_of_consumption_lower_bound` is exactly `β R < 1`.
Impatience, and nothing else, is what bounds assets. -/

/-- **The asymptotic growth factor of assets is `(β R)^(1/γ)`.** With Ma and Toda's asymptotic
MPC `c_bar = 1 - (β R^(1-γ))^(1/γ)`, the factor `(1 - c_bar) R` by which assets grow collapses to
`(β R)^(1/γ)`, so assets are eventually contracted exactly when `β R < 1`. -/
theorem one_sub_mpc_mul_of_asymptotic {β R γ : ℝ} (hβ : 0 ≤ β) (hR : 0 < R) (hγ : 0 < γ) :
    (β * R ^ (1 - γ)) ^ (1 / γ) * R = (β * R) ^ (1 / γ) := by
  have h1 : (R ^ (1 - γ)) ^ (1 / γ) * R = R ^ (1 / γ) := by
    have hadd : R ^ ((1 - γ) * (1 / γ)) * R ^ (1 : ℝ) = R ^ ((1 - γ) * (1 / γ) + 1) :=
      (Real.rpow_add hR _ _).symm
    rw [Real.rpow_one] at hadd
    rw [← Real.rpow_mul hR.le, hadd, show (1 - γ) * (1 / γ) + 1 = 1 / γ by field_simp; ring]
  rw [Real.mul_rpow hβ (Real.rpow_nonneg hR.le _), mul_assoc, h1, ← Real.mul_rpow hβ hR.le]

/-- **A household that consumes a fixed share of cash on hand runs its assets down**, once
assets pass an explicit threshold. The share `ε` has to be large enough that `(1 - ε)(1 + r) < 1`
— with Ma and Toda's asymptotic MPC that is exactly `β(1 + r) < 1`. -/
theorem policy_lt_self_of_consumption_lower_bound {z : Z} {ε a : ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hlb : ε * (P.resources (a, z) - assetFloor) ≤ P.consumptionFn z a)
    (hgt : (1 - ε) * P.income z + ε * assetFloor
      < (1 - (1 - ε) * (1 + P.interest)) * a) :
    P.policy (a, z) < a := by
  have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
    simp only [resources, max_eq_right ha.1]
  have hpol : P.policy (a, z)
      = P.income z + (1 + P.interest) * a - P.consumptionFn z a := by
    simp only [consumptionFn, consumption, hres]; ring
  rw [hres] at hlb
  rw [hpol]
  have e1 : P.income z + (1 + P.interest) * a - P.consumptionFn z a
      ≤ (1 - ε) * P.income z + (1 - ε) * ((1 + P.interest) * a) + ε * assetFloor := by
    nlinarith [hlb]
  rw [show (1 - (1 - ε) * (1 + P.interest)) * a
      = a - (1 - ε) * ((1 + P.interest) * a) by ring] at hgt
  linarith

/-- **Every asset level above an explicit threshold declines**, given a linear lower bound on
consumption. This is the hypothesis `hdecl` of `exists_exhaust_of_decline`. -/
theorem exists_decline_of_consumption_lower_bound {z : Z} {ε : ℝ}
    (hε : (1 - ε) * (1 + P.interest) < 1)
    (hlb : ∀ a ∈ Icc assetFloor assetCap,
      ε * (P.resources (a, z) - assetFloor) ≤ P.consumptionFn z a) :
    ∃ ā : ℝ, ∀ a ∈ Icc assetFloor assetCap, ā < a → P.policy (a, z) < a := by
  refine ⟨((1 - ε) * P.income z + ε * assetFloor)
    / (1 - (1 - ε) * (1 + P.interest)), fun a ha hā => ?_⟩
  refine P.policy_lt_self_of_consumption_lower_bound ha (hlb a ha) ?_
  rw [div_lt_iff₀ (by linarith)] at hā
  linarith

end IncomeFluctuation

end LeanEconomics
