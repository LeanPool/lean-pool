/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationCrossRate

/-!
# The contraction, run on the compact region alone

The value function is a bounded continuous function on all of `ℝ × Z`, but the model only
ever lives on `[0, assetCap] × Z`, which is forward invariant: every feasible choice lands
back in it (`feasible_subset_region`). So the Bellman operator evaluated at a state of the
region never consults the continuation value anywhere else.

That has a consequence worth exploiting. The whole contraction estimate can be run with
suprema taken over the REGION rather than globally:

  sup_region |V_P - V_Q| ≤ (1 - β)⁻¹ * sup_region |bellman_P V_Q - V_Q|

so comparative statics in the interest rate never needs a global sup-norm estimate. Since
the agent distribution also lives on the region, this is all the equilibrium argument
requires. It needs no second programme on the subtype, and no transport: it is a direct
estimate on the objects already built.

The mechanism is that the reward cancels. Two continuation values fed to the same programme
give objectives differing only in the discounted expectation, and the expectation samples
the next asset level, which feasibility confines to the region.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- The region the model lives on. -/
def region (_P : IncomeFluctuation Z assetFloor assetCap) : Set (ℝ × Z) :=
  {s | s.1 ∈ Icc assetFloor assetCap}

theorem isCompact_region : IsCompact P.region := by
  have himg : P.region = (Icc assetFloor assetCap) ×ˢ (univ : Set Z) := by
    ext s; simp [region, Set.mem_prod]
  rw [himg]
  exact isCompact_Icc.prod isCompact_univ

theorem region_nonempty : P.region.Nonempty :=
  ⟨(assetFloor, Classical.ofNonempty), by simp [region, P.assetFloor_le_assetCap]⟩

/-- **The expectation only samples the region.** This is forward invariance in the form the
estimate needs. -/
theorem abs_expect_sub_le {v w : (ℝ × Z) →ᵇ ℝ} {c : ℝ}
    (hvw : ∀ t : ℝ × Z, t ∈ P.region → |v t - w t| ≤ c) {s : ℝ × Z} {a : ℝ}
    (ha : a ∈ P.toExtended.feasible s) :
    |P.toExtended.expect v (s, a) - P.toExtended.expect w (s, a)| ≤ c := by
  have htr : ∀ z' : Z, P.toExtended.transition z' (s, a) = (a, z') := fun _ => rfl
  have hreg : ∀ z' : Z, P.toExtended.transition z' (s, a) ∈ P.region := fun z' => by
    rw [htr z']; exact P.feasible_subset_region ha
  simp only [ExtendedStochasticProgram.expect, ← Finset.sum_sub_distrib, ← mul_sub]
  calc |∑ z', P.toExtended.prob z' (s, a)
          * (v (P.toExtended.transition z' (s, a)) - w (P.toExtended.transition z' (s, a)))|
      ≤ ∑ z', |P.toExtended.prob z' (s, a)
          * (v (P.toExtended.transition z' (s, a)) - w (P.toExtended.transition z' (s, a)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z' : Z, P.toExtended.prob z' (s, a) * c := by
        refine Finset.sum_le_sum fun z' _ => ?_
        rw [abs_mul, abs_of_nonneg (P.toExtended.prob_nonneg z' _)]
        exact mul_le_mul_of_nonneg_left (hvw _ (hreg z')) (P.toExtended.prob_nonneg z' _)
    _ = c := by rw [← Finset.sum_mul, P.toExtended.prob_sum, one_mul]

/-- **The operator contracts, measured on the region alone.** The reward cancels, so the two
objectives differ only in the discounted expectation, and the expectation samples the next
asset level, which feasibility confines to the region. -/
theorem abs_bellmanFn_sub_le_region {v w : (ℝ × Z) →ᵇ ℝ} {c : ℝ}
    (hvw : ∀ t : ℝ × Z, t ∈ P.region → |v t - w t| ≤ c) (s : ℝ × Z) :
    |P.toExtended.bellmanFn v s - P.toExtended.bellmanFn w s| ≤ P.discount * c := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have key : ∀ v w : (ℝ × Z) →ᵇ ℝ, (∀ t : ℝ × Z, t ∈ P.region → |v t - w t| ≤ c) →
      P.toExtended.bellmanFn v s ≤ P.toExtended.bellmanFn w s + P.discount * c := by
    intro v w hvw
    refine P.toExtended.bellmanFn_le v fun a ha => ?_
    have hstep : P.toExtended.objectiveE v s a
        ≤ P.toExtended.objectiveE w s a + ((P.discount * c : ℝ) : EReal) := by
      simp only [ExtendedStochasticProgram.objectiveE]
      rw [add_assoc, ← EReal.coe_add]
      refine add_le_add (le_refl _) ?_
      rw [EReal.coe_le_coe_iff]
      have hexp := P.abs_expect_sub_le hvw ha
      rw [abs_le] at hexp
      -- `toExtended.discount` and `discount` are defeq but distinct atoms to `linarith`
      rw [show (P.toExtended.discount : ℝ) = (P.discount : ℝ) from rfl]
      nlinarith [hexp.2, hβ]
    refine le_trans hstep ?_
    rw [EReal.coe_add]
    exact add_le_add (P.toExtended.le_bellmanFn w ha) (le_refl _)
  have hc : 0 ≤ c :=
    le_trans (abs_nonneg _)
      (hvw (assetFloor, Classical.ofNonempty) (by simp [region, P.assetFloor_le_assetCap]))
  have k1 := key v w hvw
  have k2 := key w v fun t ht => by rw [abs_sub_comm]; exact hvw t ht
  rw [abs_le]
  constructor <;> linarith

/-- **The bridge.** Two value functions differ on the region by at most the operator gap on
the region, amplified by `(1 - β)⁻¹`. Every norm here is taken over the COMPACT REGION, so
comparative statics in the interest rate never needs a global sup-norm estimate.

Since the agent distribution also lives on the region, this is all the equilibrium argument
requires. Note it needs no second programme on the compact state space and no transport --
it is a direct estimate on the objects already built. -/
theorem abs_valueFunction_sub_le_region {P Q : IncomeFluctuation Z assetFloor assetCap} {D : ℝ}
    (hD : ∀ t : ℝ × Z, t ∈ P.region →
      |P.toExtended.bellmanFn Q.toExtended.valueFunction t
        - Q.toExtended.valueFunction t| ≤ D)
    {s : ℝ × Z} (hs : s ∈ P.region) :
    |P.toExtended.valueFunction s - Q.toExtended.valueFunction s|
      ≤ D / (1 - P.discount) := by
  have hβ1 : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
  have hβ0 : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  set f : ℝ × Z → ℝ :=
    fun t => |P.toExtended.valueFunction t - Q.toExtended.valueFunction t| with hf
  have hcont : ContinuousOn f P.region :=
    ((P.toExtended.valueFunction.continuous.sub
      Q.toExtended.valueFunction.continuous).abs).continuousOn
  obtain ⟨t, htmem, htmax⟩ :=
    P.isCompact_region.exists_isMaxOn P.region_nonempty hcont
  have hCle : ∀ u : ℝ × Z, u ∈ P.region → f u ≤ f t := fun u hu => htmax hu
  -- the contraction, measured on the region
  have hstep : f t ≤ P.discount * f t + D := by
    have h1 : P.toExtended.valueFunction t
        = P.toExtended.bellmanFn P.toExtended.valueFunction t := by
      rw [← P.toExtended.bellman_apply, P.toExtended.bellman_valueFunction]
    have h2 := P.abs_bellmanFn_sub_le_region
      (v := P.toExtended.valueFunction) (w := Q.toExtended.valueFunction) (c := f t)
      (fun u hu => hCle u hu) t
    have h3 := hD t htmem
    have htri : |P.toExtended.bellmanFn P.toExtended.valueFunction t
          - Q.toExtended.valueFunction t|
        ≤ |P.toExtended.bellmanFn P.toExtended.valueFunction t
            - P.toExtended.bellmanFn Q.toExtended.valueFunction t|
          + |P.toExtended.bellmanFn Q.toExtended.valueFunction t
            - Q.toExtended.valueFunction t| := abs_sub_le _ _ _
    have h4 : f t = |P.toExtended.bellmanFn P.toExtended.valueFunction t
        - Q.toExtended.valueFunction t| := by rw [hf]; simp only [← h1]
    calc f t = |P.toExtended.bellmanFn P.toExtended.valueFunction t
          - Q.toExtended.valueFunction t| := h4
      _ ≤ |P.toExtended.bellmanFn P.toExtended.valueFunction t
            - P.toExtended.bellmanFn Q.toExtended.valueFunction t|
          + |P.toExtended.bellmanFn Q.toExtended.valueFunction t
            - Q.toExtended.valueFunction t| := htri
      _ ≤ P.discount * f t + D := add_le_add h2 h3
  have hC : f t ≤ D / (1 - P.discount) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hstep]
  exact le_trans (hCle s hs) hC

/-! ### The cutoff: actions worth keeping consume a bounded amount

The pointwise comparison the sup-norm estimate needs is false at actions that consume almost
nothing, because `u` falls to `-∞` there and two nearby rates can give utilities an arbitrary
distance apart. Such actions are dominated: saving nothing is always feasible and is worth at
least `loBound v = u minIncome - β‖v‖`, which the framework already places below the
supremum (`le_maxE`).

So it is enough to compare actions worth at least `loBound v`, and this section shows those
actions consume at least a fixed `δ > 0`. The `δ` depends on `u` and on `‖v‖` only — not on
the state and not on the interest rate, which is what the parametric argument needs. -/

theorem abs_expect_le (v : (ℝ × Z) →ᵇ ℝ) (p : (ℝ × Z) × ℝ) :
    |P.toExtended.expect v p| ≤ ‖v‖ := by
  calc |P.toExtended.expect v p|
      ≤ ∑ z', |P.toExtended.prob z' p * v (P.toExtended.transition z' p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z' : Z, P.toExtended.prob z' p * ‖v‖ := by
        refine Finset.sum_le_sum fun z' _ => ?_
        rw [abs_mul, abs_of_nonneg (P.toExtended.prob_nonneg z' _)]
        exact mul_le_mul_of_nonneg_left (v.norm_coe_le_norm _) (P.toExtended.prob_nonneg z' _)
    _ = ‖v‖ := by rw [← Finset.sum_mul, P.toExtended.prob_sum, one_mul]

/-- **Actions worth keeping consume a bounded amount**, for a cutoff `δ` given in advance.

Separating the choice of `δ` from its use is what makes the bound uniform across interest
rates: the hypothesis on `δ` mentions only `u`, `loBound v` and the discount factor, none of
which move with the rate, so a single `δ` serves every rate. -/
theorem le_consumption_of_cutoff (v : (ℝ × Z) →ᵇ ℝ) {δ : ℝ}
    (hspec : ∀ c ∈ P.dom, c < δ → P.u c < P.toExtended.loBound v - P.discount * ‖v‖)
    {s : ℝ × Z} (hs : s ∈ P.region) {a : ℝ} (ha : a ∈ P.toExtended.feasible s)
    (hL : ((P.toExtended.loBound v : ℝ) : EReal) ≤ P.toExtended.objectiveE v s a) :
    δ ≤ P.consumption s a := by
  set R : ℝ := P.toExtended.loBound v - P.discount * ‖v‖ with hR
  by_contra hlt
  rw [not_le] at hlt
  -- a reward of `⊥` would make the whole objective `⊥`, which is below the cutoff
  have hne : P.toExtended.reward (s, a) ≠ ⊥ := by
    intro hbot
    rw [ExtendedStochasticProgram.objectiveE, hbot, EReal.bot_add] at hL
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hL)
  have hc : P.consumption s a ∈ P.dom := P.consumption_mem_dom_of_ne_bot hs ha hne
  -- so the reward is real, and the objective is a real inequality
  have hrw := P.reward_eq_coe_dom hs ha hc
  rw [ExtendedStochasticProgram.objectiveE, hrw, ← EReal.coe_add, EReal.coe_le_coe_iff] at hL
  have hexp := P.abs_expect_le v (s, a)
  rw [abs_le] at hexp
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hdisc : (P.toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  rw [hdisc] at hL
  have hge : R ≤ P.u (P.consumption s a) := by
    rw [hR]
    nlinarith [hexp.2, hL]
  exact absurd (hspec _ hc hlt) (not_lt.mpr hge)

/-- A cutoff exists, and its defining property mentions only data that does not move with
the interest rate. -/
theorem exists_cutoff (hd : P.Unbounded) (v : (ℝ × Z) →ᵇ ℝ) :
    ∃ δ > 0, ∀ c ∈ P.dom, c < δ →
      P.u c < P.toExtended.loBound v - P.discount * ‖v‖ := by
  set R : ℝ := P.toExtended.loBound v - P.discount * ‖v‖ with hR
  have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), P.u c < R := P.tendsto_atBot_u hd (eventually_lt_atBot R)
  obtain ⟨δ, hδ, hsub⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  refine ⟨δ, hδ, fun c hc hcδ => hsub ⟨?_, hcδ⟩⟩
  rw [hd] at hc
  exact hc

/-- **Actions worth keeping consume a bounded amount.** -/
theorem exists_cutoff_consumption (hd : P.Unbounded) (v : (ℝ × Z) →ᵇ ℝ) :
    ∃ δ > 0, ∀ s : ℝ × Z, s ∈ P.region → ∀ a ∈ P.toExtended.feasible s,
      ((P.toExtended.loBound v : ℝ) : EReal) ≤ P.toExtended.objectiveE v s a →
      δ ≤ P.consumption s a := by
  obtain ⟨δ, hδ, hspec⟩ := P.exists_cutoff hd v
  exact ⟨δ, hδ, fun s hs a ha hL => P.le_consumption_of_cutoff v hspec hs ha hL⟩

/-! ### Uniform continuity

The two moduli the sup-norm estimate consumes. Both are uniform in the state, which is what
matters; neither is uniform in the interest rate, and neither needs to be, since the rate
enters only through the ARGUMENTS fed to `u` and to the continuation value, and those gaps
are already controlled by the cross-rate lemmas.

Note `Z` carries only a discrete topology, with no metric, so `ℝ × Z` is not a metric space
and uniform continuity of the continuation value cannot be taken there directly. It is taken
in the asset coordinate for each income state separately and the finitely many moduli
combined, which is legitimate exactly because `Z` is a `Fintype`. -/

/-- **Uniform continuity of utility**, away from zero consumption. The interval is compact and
sits inside `Ioi 0`, where `u` is assumed continuous; the cutoff is what puts consumption
there. -/
theorem exists_modulus_u {lo hi ε : ℝ} (hlo : 0 < lo) (hε : 0 < ε) :
    ∃ η > 0, ∀ c₁ ∈ Icc lo hi, ∀ c₂ ∈ Icc lo hi, |c₁ - c₂| < η → |P.u c₁ - P.u c₂| < ε := by
  have hsub : Icc lo hi ⊆ Ioi 0 := fun c hc => lt_of_lt_of_le hlo hc.1
  have hcont : ContinuousOn P.u (Icc lo hi) := P.continuousOn_u.mono hsub
  have huc : UniformContinuousOn P.u (Icc lo hi) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  obtain ⟨η, hη, hspec⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨η, hη, fun c₁ h₁ c₂ h₂ hd => ?_⟩
  have := hspec c₁ h₁ c₂ h₂ (by rwa [Real.dist_eq])
  rwa [Real.dist_eq] at this

omit [Fintype Z] [DiscreteTopology Z] in
/-- **Uniform continuity of the continuation value** in the asset coordinate, uniformly over
income states. The finiteness of `Z` is used in the PROOF, to combine the per-state moduli,
though it does not appear in the statement. -/
theorem exists_modulus_v [Finite Z] (v : (ℝ × Z) →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ z' : Z, ∀ a₁ ∈ Icc assetFloor assetCap, ∀ a₂ ∈ Icc assetFloor assetCap,
      |a₁ - a₂| < η → |v (a₁, z') - v (a₂, z')| < ε := by
  let _ := Fintype.ofFinite Z
  -- one modulus per income state
  have hslice : ∀ z' : Z, ∃ η > 0, ∀ a₁ ∈ Icc assetFloor assetCap, ∀ a₂ ∈ Icc assetFloor assetCap,
      |a₁ - a₂| < η → |v (a₁, z') - v (a₂, z')| < ε := by
    intro z'
    have hcont : ContinuousOn (fun a : ℝ => v (a, z')) (Icc assetFloor assetCap) :=
      (v.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    have huc : UniformContinuousOn (fun a : ℝ => v (a, z')) (Icc assetFloor assetCap) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hcont
    obtain ⟨η, hη, hspec⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
    refine ⟨η, hη, fun a₁ h₁ a₂ h₂ hd => ?_⟩
    have := hspec a₁ h₁ a₂ h₂ (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this
  choose η hη hspec using hslice
  -- `Z` is finite, so the moduli have a positive minimum
  have hne : (Finset.univ : Finset Z).Nonempty := ⟨Classical.ofNonempty, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne η, ?_, fun z' a₁ h₁ a₂ h₂ hd => ?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun z' _ => hη z'
  · exact hspec z' a₁ h₁ a₂ h₂
      (lt_of_lt_of_le hd (Finset.inf'_le _ (Finset.mem_univ z')))

end IncomeFluctuation

end LeanEconomics
