/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationConsumption
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationBounds
public import LeanPool.AiyagariEquilibrium.Models.CRRA

/-!
# A consumption floor from the margin, not from the level

`crra_pinch` traced the restriction `γ = 1` to `tendsto_atBot_u`, the requirement that utility
fall to `-∞` at zero consumption. This file replaces the use of that condition in the one place
where it does economic work — the uniform lower bound on consumption at the optimum — by a
condition on the MARGIN, which CRRA satisfies for every `γ > 0`, `γ < 1` included.

## Minimum income is necessary and not sufficient

A positive lower bound on income does not by itself keep consumption away from zero. It bounds
RESOURCES below, not consumption: `maxSaving = min assetCap resources`, so whenever the cap is
slack the household may save everything and consume nothing. Nothing about the income process
says it will not.

What minimum income does is make the CONTINUATION Lipschitz where the argument needs it. The
deviation argument compares the optimum with saving `h` less:

  `u (c + h) - u c ≤ β * (cont a - cont (a - h))`,

and the right-hand side has to be bounded by a multiple of `h`. The continuation is concave and
bounded, so its slope on `[0, x]` is at most `2‖V‖ / x` — which blows up as `x → 0`. Minimum
income kills that case: if consumption is small then saving is nearly all of resources, so
`a ≥ 3 minIncome / 4` and the slope constant is `4‖V‖ / minIncome`, depending on the state
through nothing at all. That is `contSlope_le`.

With a state-independent constant `L`, any consumption level whose marginal value beats `β L`
cannot be optimal, and `MarginalInada` supplies one. The floor is explicit:
`min δ (minIncome / 4)`.

## What this does NOT do, and why

The plan was to swap `tendsto_atBot_u` out of the structure. It cannot simply be swapped, and
the reason is worth recording. That condition does a SECOND job: `continuous_rewardFn` uses it
to make `extendBot u` continuous into `EReal`, and continuity of the reward is what Berge's
maximum theorem runs on. With `u (0⁺)` finite, `extendBot u` jumps from a finite limit down to
`⊥` at zero consumption — it is not even upper semicontinuous there, so the maximum is not
attained by the general argument and the whole `ExtendedStochasticProgram` apparatus lapses.

So admitting `γ < 1` needs the reward to stop being `extendBot u` and start being `u` itself,
real-valued and continuous on `[0, ∞)` — a different reward, hence a different structure, not a
different axiom. The floor proved here is what that structure will need and is stated so that it
transfers: it uses concavity and boundedness of the continuation and nothing else, and in
particular it never mentions `tendsto_atBot_u`.
-/

@[expose] public section

open Set Filter Topology

namespace LeanEconomics

/-- **Marginal Inada.** Consumption near zero has unboundedly large marginal value, measured by
secant slopes so that no derivative is needed. CRRA satisfies this for every `γ > 0`, including
the `γ < 1` range where utility itself stays bounded. -/
def MarginalInadaOn (D : Set ℝ) (u : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ δ > 0, ∀ c c' : ℝ, c ∈ D → c < c' → c' ≤ δ → M * (c' - c) ≤ u c' - u c

/-- The classical form, on the positives. -/
abbrev MarginalInada (u : ℝ → ℝ) : Prop := MarginalInadaOn (Ioi 0) u

/-- **A marginal lower bound near zero.** `MarginalInadaOn` is this for every `M`; a utility
with finite marginal value at zero -- CARA, or a shifted CRRA -- satisfies it for the `M` its
slope near zero allows, and the consumption floor then has to be earned by an inequality. -/
def MarginalBoundOn (D : Set ℝ) (u : ℝ → ℝ) (M : ℝ) : Prop :=
  ∃ δ > 0, ∀ c c' : ℝ, c ∈ D → c < c' → c' ≤ δ → M * (c' - c) ≤ u c' - u c

theorem marginalBoundOn_of_inada {D : Set ℝ} {u : ℝ → ℝ} (h : MarginalInadaOn D u) (M : ℝ) :
    MarginalBoundOn D u M := h M

/-- Marginal utility explodes at zero. -/
theorem tendsto_rpow_neg_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun c : ℝ => c ^ (-γ)) (𝓝[>] 0) atTop := by
  have hcont : Tendsto (fun c : ℝ => c ^ γ) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x ^ γ) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ γ)) :=
      (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).continuousWithinAt
    rwa [Real.zero_rpow hγ.ne'] at h
  have hwithin : Tendsto (fun c : ℝ => c ^ γ) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hcont
      (eventually_nhdsWithin_of_forall fun c hc => Real.rpow_pos_of_pos hc _)
  refine (tendsto_inv_nhdsGT_zero.comp hwithin).congr'
    (eventually_nhdsWithin_of_forall fun c hc => ?_)
  exact (Real.rpow_neg (le_of_lt hc) γ).symm

theorem rpow_neg_antitone {γ : ℝ} (hγ : 0 < γ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y ^ (-γ) ≤ x ^ (-γ) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.trans_le hxy).le]
  rw [inv_le_inv₀ (Real.rpow_pos_of_pos (hx.trans_le hxy) _) (Real.rpow_pos_of_pos hx _)]
  exact Real.rpow_le_rpow hx.le hxy hγ.le

/-- **CRRA has unbounded marginal value at zero for every `γ > 0`** — the `γ < 1` case included,
where the LEVEL condition `tendsto_atBot_u` fails. This is the whole point. -/
theorem marginalInada_crraUtility {γ : ℝ} (hγ : 0 < γ) : MarginalInada (crraUtility γ) := by
  intro M
  obtain ⟨δ, hδM, hδ0⟩ :=
    (((tendsto_rpow_neg_atTop hγ).eventually_ge_atTop M).and self_mem_nhdsWithin).exists
  refine ⟨δ, hδ0, fun c c' hc hcc' hc'δ => ?_⟩
  have hc' : 0 < c' := hc.trans hcc'
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (crraUtility γ)
    (fun x => x ^ (-γ)) hcc'
    ((continuousOn_crraUtility γ).mono fun x hx => lt_of_lt_of_le hc hx.1)
    (fun x hx => hasDerivAt_crraUtility γ (hc.trans hx.1))
  have hmono : M ≤ ξ ^ (-γ) :=
    hδM.trans (rpow_neg_antitone hγ (hc.trans hξ.1) (le_trans hξ.2.le hc'δ))
  rw [hslope, le_div_iff₀ (by linarith)] at hmono
  linarith

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-- The state-independent bound on the continuation's slope, which is where the positive income
floor does its work. -/
noncomputable def contSlopeConst : ℝ := 4 * ‖P.toExtended.valueFunction‖ / P.minConsumption

theorem contSlopeConst_nonneg : 0 ≤ P.contSlopeConst :=
  div_nonneg (by positivity) P.minConsumption_pos.le

theorem abs_cont_le (z : Z) (x : ℝ) : |P.cont z x| ≤ ‖P.toExtended.valueFunction‖ :=
  P.abs_expectation_le x z

/-- **The continuation's slope is bounded by a state-independent constant**, provided we stay
above `assetFloor + minConsumption / 2` in savings — which is exactly where the deviation
argument lives. -/
theorem cont_sub_le (z : Z) {x y : ℝ} (hx : assetFloor + P.minConsumption / 2 ≤ x) (hxy : x < y)
    (hy : y ∈ Icc assetFloor assetCap) :
    P.cont z y - P.cont z x ≤ P.contSlopeConst * (y - x) := by
  have hmin := P.minConsumption_pos
  have hx0 : assetFloor < x := by linarith
  have hxmem : x ∈ Icc assetFloor assetCap := ⟨hx0.le, le_trans hxy.le hy.2⟩
  have hslope := (P.concaveOn_cont z).slope_anti_adjacent
    (mem_Icc.mpr ⟨le_rfl, P.assetFloor_le_assetCap⟩) hy hx0 hxy
  have hb1 := abs_le.mp (P.abs_cont_le z x)
  have hb2 := abs_le.mp (P.abs_cont_le z assetFloor)
  have hhalf : P.contSlopeConst * (P.minConsumption / 2)
      = 2 * ‖P.toExtended.valueFunction‖ := by
    rw [contSlopeConst]; field_simp; ring
  have hbig : P.cont z x - P.cont z assetFloor ≤ P.contSlopeConst * (x - assetFloor) := by
    have hstep : P.contSlopeConst * (P.minConsumption / 2)
        ≤ P.contSlopeConst * (x - assetFloor) :=
      mul_le_mul_of_nonneg_left (by linarith) P.contSlopeConst_nonneg
    rw [hhalf] at hstep
    linarith [hb1.2, hb2.1]
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at hslope
  have hprod : (P.cont z y - P.cont z x) * (x - assetFloor)
      ≤ (P.contSlopeConst * (x - assetFloor)) * (y - x) := by
    nlinarith [hslope, hbig, (show (0 : ℝ) < y - x by linarith)]
  nlinarith [hprod, hx0]

/-- **A consumption floor from the margin.** No use is made of `tendsto_atBot_u`: the argument
runs on concavity and boundedness of the continuation, a positive income floor, and unbounded
marginal value at zero consumption. -/
theorem exists_consumption_floor_of_marginalInada (hu : MarginalInadaOn P.dom P.u) :
    ∃ δ > 0, ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → δ ≤ P.consumption s (P.policy s) := by
  have hmin := P.minConsumption_pos
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  obtain ⟨δ₀, hδ₀, hδ⟩ := hu (P.discount * P.contSlopeConst + 1)
  refine ⟨min δ₀ (P.minConsumption / 4), lt_min hδ₀ (by linarith), fun s hs => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  set d : ℝ := min δ₀ (P.minConsumption / 4) with hd
  set a : ℝ := P.policy s with hadef
  set c : ℝ := P.consumption s a with hcdef
  have hdδ : d ≤ δ₀ := min_le_left _ _
  have hd4 : d ≤ P.minConsumption / 4 := min_le_right _ _
  have hcmem : c ∈ P.dom := P.consumption_policy_mem_dom hs
  have hc0 : 0 ≤ c := P.nonneg_of_mem_dom hcmem
  have hres : P.minConsumption ≤ P.resources s - assetFloor :=
    P.minConsumption_le_consumption_floor s
  have hca : c = P.resources s - a := rfl
  -- consumption small forces saving large, which is what bounds the continuation's slope
  have ha : assetFloor + 3 * P.minConsumption / 4 ≤ a := by rw [hca] at hlt; linarith
  set h : ℝ := d - c with hhdef
  have hh0 : 0 < h := by rw [hhdef]; linarith
  have hhle : h ≤ P.minConsumption / 4 := by rw [hhdef]; linarith
  have hlow : assetFloor + P.minConsumption / 2 ≤ a - h := by linarith
  have hamem : a ∈ Icc assetFloor assetCap := P.policy_mem_region s
  -- the deviation is feasible and its consumption is `d`
  have hfeas : a - h ∈ P.toExtended.feasible s := by
    rw [P.feasible_eq]
    exact ⟨by linarith [hamem.1], by linarith [(P.policy_mem s).2]⟩
  have hcd : P.consumption s (a - h) = d := by
    simp only [consumption] at hca ⊢; linarith
  have hdpos : 0 < P.consumption s (a - h) := by rw [hcd]; linarith
  -- optimality of `a` against the deviation
  have hopt := P.objR_le_of_mem hs hfeas (P.mem_dom_of_pos hdpos)
  simp only [objR, hcd] at hopt
  -- the continuation cannot repay more than `L * h`
  have hslope := P.cont_sub_le s.2 hlow (by linarith) hamem
  rw [show a - (a - h) = h from by ring] at hslope
  have hscaled := mul_le_mul_of_nonneg_left hslope hβ
  have hutil : P.u d - P.u c ≤ (P.discount * P.contSlopeConst) * (d - c) := by
    have e : (P.discount : ℝ) * (P.contSlopeConst * h)
        = (P.discount * P.contSlopeConst) * (d - c) := by rw [hhdef]; ring
    linarith [hopt, hscaled, e.le, e.ge]
  -- but the marginal condition says it must repay strictly more
  have hmarg := hδ c d hcmem (by linarith) hdδ
  rw [show ((P.discount : ℝ) * P.contSlopeConst + 1) * (d - c)
      = (P.discount * P.contSlopeConst) * (d - c) + (d - c) from by ring] at hmarg
  rw [hhdef] at hh0
  linarith [hmarg, hutil, hh0]

/-- **The second route to positive consumption.** When utility is unbounded below the reward is
`⊥` at zero consumption and positivity is free; when it is bounded — CES with `γ < 1` — it has to
be earned, and this is where. The condition is on MARGINS, which is why it survives the loss of
the level condition. -/
theorem positiveConsumption_of_marginalInada (hu : MarginalInadaOn P.dom P.u) :
    P.PositiveConsumption := by
  obtain ⟨δ, hδ, hspec⟩ := P.exists_consumption_floor_of_marginalInada hu
  exact fun s hs => lt_of_lt_of_le hδ (hspec s hs)

end IncomeFluctuation

end LeanEconomics
