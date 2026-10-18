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
bounded, so its slope from `assetFloor` to `x` is at most `2‖V‖ / (x - assetFloor)`. The
positive sustainability bound `minConsumption` keeps the deviation away from that endpoint:
small consumption forces saving at least `assetFloor + 3 * minConsumption / 4`. The resulting
state-independent slope constant is `4‖V‖ / minConsumption`, as used by `cont_sub_le`.

With a state-independent constant `L`, any consumption level whose marginal value beats `β L`
cannot be optimal, and `MarginalInada` supplies one. The floor is explicit:
`min δ (minConsumption / 4)`.

## How the current bounded-domain model uses this result

Divergence at zero has two distinct roles in the unbounded-domain model: it makes
`extendBot u` continuous into `EReal` and excludes zero consumption at an optimum. The marginal
argument here replaces the latter role.

The current `IncomeFluctuation` structure has a utility-domain field.
`BoundedIncomeFluctuation` takes `dom = Ici 0`, where `extendDom` uses the finite value `u 0`
rather than `⊥`, and proves the needed reward continuity. Its marginal Inada argument then
establishes positive consumption separately. The floor results here fit that shared structure;
they do not require a new household type or a divergence assumption.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

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

/-- The slope constant an oscillation bound `G` gives. -/
noncomputable def oscSlopeConst (G : ℝ) : ℝ := 2 * G / P.minConsumption

theorem oscSlopeConst_nonneg {G : ℝ} (hG : 0 ≤ G) : 0 ≤ P.oscSlopeConst G :=
  div_nonneg (by linarith) P.minConsumption_pos.le

/-- **The continuation's slope, priced by its oscillation**, above
`assetFloor + minConsumption / 2`. -/
theorem contOf_sub_le_of_osc {v : (ℝ × Z) →ᵇ ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hv : ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap) fun a => v (a, z))
    (hosc : P.OscOn v G) (z : Z) {x y : ℝ}
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

/-- **The consumption floor, from a finite marginal bound.** -/
theorem exists_consumptionFnOf_floor_of_marginal {M G : ℝ}
    (hM : MarginalBoundOn P.dom P.u M) (hG : 0 ≤ G)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap) fun a => v (a, z))
    (hosc : P.OscOn v G)
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
  nlinarith only [hmarg, hutil, hh0, hlt]

/-- The state-independent bound on the continuation's slope, read against `v`. -/
noncomputable def contSlopeConstOf (v : (ℝ × Z) →ᵇ ℝ) : ℝ := 4 * ‖v‖ / P.minConsumption

theorem contSlopeConstOf_nonneg (v : (ℝ × Z) →ᵇ ℝ) : 0 ≤ P.contSlopeConstOf v :=
  div_nonneg (by positivity) P.minConsumption_pos.le

/-- **The continuation's slope is bounded by a state-independent constant**, above
`assetFloor + minConsumption / 2`, whatever the continuation. -/
theorem contOf_sub_le {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap) fun a => v (a, z)) (z : Z)
    {x y : ℝ} (hx : assetFloor + P.minConsumption / 2 ≤ x) (hxy : x < y)
    (hy : y ∈ Icc assetFloor assetCap) :
    P.contOf v z y - P.contOf v z x ≤ P.contSlopeConstOf v * (y - x) := by
  have h := P.contOf_sub_le_of_osc (by positivity) hv (P.oscOn_two_norm v) z hx hxy hy
  convert h using 1
  dsimp [oscSlopeConst, contSlopeConstOf]
  ring

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
  simpa only [cont, contOf, contSlopeConst, contSlopeConstOf] using
    P.contOf_sub_le P.concaveOn_valueFunction z hx hxy hy

/-- **A consumption floor from the margin, against an arbitrary continuation.** -/
theorem exists_consumptionFnOf_floor_of_marginalInada (hu : MarginalInadaOn P.dom P.u)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap) fun a => v (a, z)) :
    ∃ δ > 0, ∀ (z : Z), ∀ a ∈ Icc assetFloor assetCap, δ ≤ P.consumptionFnOf v z a := by
  refine P.exists_consumptionFnOf_floor_of_marginal
    (hu ((P.discount : ℝ) * P.oscSlopeConst (2 * ‖v‖) + 1))
    (by positivity) hv (P.oscOn_two_norm v) ?_
  linarith

/-- **A consumption floor from the margin.** No use is made of `tendsto_atBot_u`: the argument
runs on concavity and boundedness of the continuation, a positive income floor, and unbounded
marginal value at zero consumption. -/
theorem exists_consumption_floor_of_marginalInada (hu : MarginalInadaOn P.dom P.u) :
    ∃ δ > 0, ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → δ ≤ P.consumption s (P.policy s) := by
  obtain ⟨δ, hδ, hspec⟩ :=
    P.exists_consumptionFnOf_floor_of_marginalInada hu P.concaveOn_valueFunction
  exact ⟨δ, hδ, fun s hs => hspec s.2 s.1 hs⟩

/-- **A uniform bound on saving from a uniform marginal bound**, against any continuation. -/
theorem policyOf_le_of_marginal_bound {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap) fun a => v (a, z)) {m : ℝ} (hm : 0 < m)
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
  nlinarith only [hopt, hmg, mul_le_mul_of_nonneg_left hloss hβ]

/-- **The second route to positive consumption.** When utility is unbounded below the reward is
`⊥` at zero consumption and positivity is free; when it is bounded — CES with `γ < 1` — it has to
be earned, and this is where. The condition is on MARGINS, which is why it survives the loss of
the level condition. -/
theorem positiveConsumption_of_marginalInada (hu : MarginalInadaOn P.dom P.u) :
    P.PositiveConsumption := by
  obtain ⟨δ, hδ, hspec⟩ := P.exists_consumption_floor_of_marginalInada hu
  exact fun s hs => lt_of_lt_of_le hδ (hspec s hs)

/-- A power marginal bound prices the same proportional saving deviation for every utility. -/
theorem policyOf_le_mul_of_power_marginal {γ η θ G : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap) fun a => v (a, z))
    (hG : 0 ≤ G) (hosc : P.OscOn v G)
    (hmarg : ∀ c d : ℝ, c ∈ P.dom → c ≤ d → 0 < η + c →
      (η + d) ^ (-γ) * (d - c) ≤ P.u d - P.u c)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z)
    (hcpos : 0 < η + P.consumptionFnOf v z a) :
    P.policyOf v (a, z) - assetFloor
      ≤ ((P.discount : ℝ) * G / θ)
        * (η + P.consumptionFnOf v z a
            + (1 - θ) * (P.policyOf v (a, z) - assetFloor)) ^ γ := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  set b : ℝ := P.policyOf v (a, z) with hbdef
  set c : ℝ := P.consumptionFnOf v z a with hcdef
  have hbreg : b ∈ Icc assetFloor assetCap :=
    P.feasible_subset_region (P.policyOf_mem v (a, z))
  have hbase : (0 : ℝ) < η + c + (1 - θ) * (b - assetFloor) := by
    have := mul_nonneg (sub_pos.mpr hθ1).le (sub_nonneg.mpr hbreg.1)
    linarith
  have hrpow : (0 : ℝ) < (η + c + (1 - θ) * (b - assetFloor)) ^ γ :=
    Real.rpow_pos_of_pos hbase _
  rcases eq_or_lt_of_le hbreg.1 with hzero | hbpos
  · rw [← hzero, sub_self]
    positivity
  have hbf : (0 : ℝ) < b - assetFloor := sub_pos.mpr hbpos
  set w : ℝ := assetFloor + θ * (b - assetFloor) with hwdef
  have hw0 : assetFloor < w := by rw [hwdef]; nlinarith only [hθ0, hbf]
  have hwb : w < b := by rw [hwdef]; nlinarith only [hθ1, hbf]
  have hwmem : w ∈ Icc assetFloor assetCap := ⟨hw0.le, hwb.le.trans hbreg.2⟩
  have hfeas : w ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq]
    exact ⟨hw0.le, hwb.le.trans (P.policyOf_mem v (a, z)).2⟩
  have hcb : c = P.resources (a, z) - b := rfl
  have hcons : P.consumption (a, z) w = c + (1 - θ) * (b - assetFloor) := by
    simp only [consumption, hwdef]; rw [hcb]; ring
  have hdev : 0 < P.consumption (a, z) w := by
    rw [hcons]
    have hc : 0 ≤ c := P.nonneg_of_mem_dom (P.consumption_policyOf_mem_dom v ha)
    nlinarith only [hc, hθ1, hbf]
  have hopt := P.objROf_le_of_mem v ha hfeas (P.mem_dom_of_pos hdev)
  simp only [objROf, hcons] at hopt
  rw [show P.consumption (a, z) (P.policyOf v (a, z)) = c from rfl,
    show P.policyOf v (a, z) = b from rfl] at hopt
  have hslope := (P.concaveOn_contOf hv z).slope_anti_adjacent
    (mem_Icc.mpr ⟨le_rfl, P.assetFloor_le_assetCap⟩) hbreg hw0 hwb
  have hgap := P.contOf_sub_le_osc hosc hwmem
    (show assetFloor ∈ Icc assetFloor assetCap from ⟨le_rfl, P.assetFloor_le_assetCap⟩) z z
  have hbw : b - w = (1 - θ) * (b - assetFloor) := by rw [hwdef]; ring
  have hwf : w - assetFloor = θ * (b - assetFloor) := by rw [hwdef]; ring
  have hloss : P.contOf v z b - P.contOf v z w ≤ (1 - θ) / θ * G := by
    rw [div_le_div_iff₀ (sub_pos.mpr hwb) (sub_pos.mpr hw0), hbw, hwf] at hslope
    have h2 := hslope.trans (mul_le_mul_of_nonneg_right hgap
      (mul_nonneg (sub_pos.mpr hθ1).le hbf.le))
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ0]
    refine le_of_mul_le_mul_right (a := b - assetFloor) ?_ hbf
    convert h2 using 1 <;> ring
  have hmg : (η + c + (1 - θ) * (b - assetFloor)) ^ (-γ) * ((1 - θ) * (b - assetFloor))
      ≤ P.u (c + (1 - θ) * (b - assetFloor)) - P.u c := by
    have := hmarg c (c + (1 - θ) * (b - assetFloor))
      (P.consumption_policyOf_mem_dom v ha)
      (le_add_of_nonneg_right (mul_nonneg (sub_pos.mpr hθ1).le hbf.le)) hcpos
    simpa only [add_sub_cancel_left, add_assoc] using this
  have hmid : P.u (c + (1 - θ) * (b - assetFloor)) - P.u c
      ≤ (P.discount : ℝ) * (P.contOf v z b - P.contOf v z w) := by
    have hd : (P.discount : ℝ) * (P.contOf v z b - P.contOf v z w)
        = (P.discount : ℝ) * P.contOf v z b - (P.discount : ℝ) * P.contOf v z w := by ring
    linarith only [hopt, hd]
  have hkey := le_trans hmg (le_trans hmid (mul_le_mul_of_nonneg_left hloss hβ))
  rw [Real.rpow_neg hbase.le γ] at hkey
  have hexp : ((η + c + (1 - θ) * (b - assetFloor)) ^ γ)⁻¹ * ((1 - θ) * (b - assetFloor))
      = (1 - θ) * ((b - assetFloor) / (η + c + (1 - θ) * (b - assetFloor)) ^ γ) := by
    field_simp
  rw [hexp, show (P.discount : ℝ) * ((1 - θ) / θ * G)
      = (1 - θ) * ((P.discount : ℝ) * G / θ) from by ring] at hkey
  have hdiv := le_of_mul_le_mul_left hkey (sub_pos.mpr hθ1)
  rw [div_le_iff₀ hrpow] at hdiv
  exact hdiv

/-- A proportional power bound keeps saving below the cap under one primitive inequality. -/
theorem policyOf_lt_cap_of_power_bound {γ η θ K : ℝ} (hγ : 0 ≤ γ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hK : 0 ≤ K) {v : (ℝ × Z) →ᵇ ℝ}
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z)
    (hc : 0 ≤ η + P.consumptionFnOf v z a)
    (hbound : P.policyOf v (a, z) - assetFloor ≤ K *
      (η + P.consumptionFnOf v z a + (1 - θ) * (P.policyOf v (a, z) - assetFloor)) ^ γ)
    (hcap : K * (η + P.maxIncome + (1 + P.interest - θ) * assetCap
      - (1 - θ) * assetFloor) ^ γ < assetCap - assetFloor) :
    P.policyOf v (a, z) < assetCap := by
  by_contra hcon
  rw [not_lt] at hcon
  set b := P.policyOf v (a, z) with hbdef
  set c := P.consumptionFnOf v z a with hcdef
  have hbreg : b ∈ Icc assetFloor assetCap :=
    P.feasible_subset_region (P.policyOf_mem v (a, z))
  have hres : P.resources (a, z) - assetFloor ≤ P.maxConsumption :=
    P.consumption_le_maxConsumption (s := (a, z)) ha le_rfl
  have hsum : η + c + (1 - θ) * (b - assetFloor)
      = η + (P.resources (a, z) - assetFloor) - θ * (b - assetFloor) := by
    simp only [hcdef, consumptionFnOf, consumption, ← hbdef]; ring
  have hle : η + c + (1 - θ) * (b - assetFloor)
      ≤ η + P.maxIncome + (1 + P.interest - θ) * assetCap - (1 - θ) * assetFloor := by
    rw [hsum]
    have hθb : θ * (assetCap - assetFloor) ≤ θ * (b - assetFloor) :=
      mul_le_mul_of_nonneg_left (by linarith only [hcon]) hθ0
    simp only [maxConsumption] at hres
    nlinarith only [hres, hθb]
  have hnn : 0 ≤ η + c + (1 - θ) * (b - assetFloor) :=
    add_nonneg hc (mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr hbreg.1))
  have hmono := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnn hle hγ) hK
  exact (not_lt_of_ge hcon) (by linarith only [hbound, hmono, hcap])

end IncomeFluctuation

end LeanEconomics
