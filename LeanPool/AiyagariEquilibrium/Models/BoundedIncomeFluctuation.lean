/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.CRRA
public import LeanPool.AiyagariEquilibrium.Models.ConsumptionFloor
public import LeanPool.AiyagariEquilibrium.Distribution.Stationary
public import LeanPool.AiyagariEquilibrium.Equilibrium.PositiveCapital
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# CES with `γ < 1`: utility bounded below

`crra_pinch` showed that CRRA was confined to log: `tendsto_atBot_u` forced `γ ≥ 1`, and Light's
uniqueness condition forced `γ ≤ 1`. This file removes the first half of the pincer.

## What had to change, and where

The obstruction was never the axiom by itself. `tendsto_atBot_u` is what makes `extendBot u`
CONTINUOUS into `EReal`, and continuity of the reward is what Berge's maximum theorem runs on.
With `u (0⁺)` finite, `extendBot u` drops from a finite limit to `⊥` at zero consumption: not even
upper semicontinuous, so the maximum need not be attained. Deleting the axiom would have broken
`exists_optimal_action`, not weakened it.

`IncomeFluctuation` was therefore refactored over a utility DOMAIN, with `continuousOn_extendDom`
in place of `tendsto_atBot_u`. All that remains here is to take `dom = Ici 0` and check that CES
with `γ < 1` fits.

## Two things it costs

`continuousOn_extendDom` is discharged differently — `continuousOn_extendDom_Ici` below, where the
`⊥` branch is simply unreachable — and that part is free.

Positive consumption at the optimum is not. In the unbounded model it is a corollary of the reward
being `⊥` there. Here the reward at `c = 0` is `u 0`, a perfectly ordinary number, and the
household has to be shown not to want it. That is `MarginalInadaOn`: marginal utility explodes at
zero even though utility itself does not, and `positiveConsumption_of_marginalInada` turns it into
the `PositiveConsumption` the rest of the development asks for. Note that the condition has to
reach `c = 0` itself, which is why `MarginalInada` was generalised to a domain.

## What comes for free

Everything stated for `IncomeFluctuation`: the Bellman equation, uniqueness of the optimal action,
concavity and monotonicity of the value function, `policy_mono`, the Feller property, stationary
distributions, the Aiyagari equilibrium machinery. There is no second structure to carry them to.
-/

@[expose] public section

open scoped NNReal
open Set Filter Topology MeasureTheory

namespace LeanEconomics

/-! ### The domain `Ici 0` -/

/-- **The bounded case discharges the continuity requirement trivially.** On `Ici 0` the `⊥`
branch of `extendDom` is never taken, so what is left is continuity of `u` itself. -/
theorem continuousOn_extendDom_Ici {u : ℝ → ℝ} (hc : ContinuousOn u (Ici 0)) :
    ContinuousOn (extendDom (Ici 0) u) (Ici 0) :=
  (continuous_coe_real_ereal.comp_continuousOn hc).congr fun _ hx => extendDom_of_mem hx

/-! ### CES with `0 < γ < 1` -/

theorem continuousOn_crraUtility_Ici {γ : ℝ} (hγ1 : γ < 1) :
    ContinuousOn (crraUtility γ) (Ici 0) := by
  have he : crraUtility γ = fun c : ℝ => c ^ (1 - γ) / (1 - γ) :=
    funext (crraUtility_of_ne (by linarith))
  rw [he]
  refine ContinuousOn.div_const (fun x _ => ?_) _
  exact (Real.continuousAt_rpow_const x (1 - γ) (Or.inr (by linarith))).continuousWithinAt

theorem monotoneOn_crraUtility_Ici {γ : ℝ} (hγ1 : γ < 1) :
    MonotoneOn (crraUtility γ) (Ici 0) := by
  intro x hx y hy hxy
  rw [crraUtility_of_ne (by linarith), crraUtility_of_ne (by linarith)]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hx hxy (by linarith)) (by linarith)

theorem strictConcaveOn_crraUtility_Ici {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictConcaveOn ℝ (Ici 0) (crraUtility γ) := by
  have hpos : (0 : ℝ) < 1 - γ := by linarith
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have key := (Real.strictConcaveOn_rpow hpos (by linarith)).2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at key ⊢
  simp only [crraUtility_of_ne (show γ ≠ 1 by linarith)]
  rw [show a * (x ^ (1 - γ) / (1 - γ)) + b * (y ^ (1 - γ) / (1 - γ))
      = (a * x ^ (1 - γ) + b * y ^ (1 - γ)) / (1 - γ) from by ring]
  gcongr

theorem crraUtility_zero {γ : ℝ} (hγ1 : γ < 1) : crraUtility γ 0 = 0 := by
  rw [crraUtility_of_ne (by linarith), Real.zero_rpow (by linarith)]
  simp

/-- **CES with `γ < 1` has unbounded marginal value AT zero, not merely near it.** The level
condition `tendsto_atBot_u` fails here, and this is what replaces it: the household still refuses
to consume nothing, because the first unit of consumption is worth more than any bounded gain from
the saving it displaces. -/
theorem marginalInadaOn_Ici_crraUtility {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    MarginalInadaOn (Ici 0) (crraUtility γ) := by
  intro M
  obtain ⟨δ₁, hδ₁, hspec⟩ := marginalInada_crraUtility hγ0 M
  obtain ⟨δ₂, hδ₂M, hδ₂0⟩ :=
    (((tendsto_rpow_neg_atTop hγ0).eventually_ge_atTop M).and self_mem_nhdsWithin).exists
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂0, fun c c' hc hcc' hc'δ => ?_⟩
  rcases (mem_Ici.mp hc).lt_or_eq with hcpos | hc0
  · exact hspec c c' hcpos hcc' (le_trans hc'δ (min_le_left _ _))
  -- the new case: `c = 0`, where the classical condition has nothing to say
  have hc' : 0 < c' := hc0 ▸ hcc'
  have hM : M ≤ c' ^ (-γ) :=
    hδ₂M.trans (rpow_neg_antitone hγ0 hc' (le_trans hc'δ (min_le_right _ _)))
  have hmul : c' ^ (-γ) * c' = c' ^ (1 - γ) := by
    have hadd := Real.rpow_add hc' (-γ) 1
    rw [Real.rpow_one] at hadd
    rw [← hadd, show -γ + 1 = 1 - γ from by ring]
  have h1 : M * c' ≤ c' ^ (1 - γ) := by
    rw [← hmul]; exact mul_le_mul_of_nonneg_right hM hc'.le
  have h2 : (0 : ℝ) ≤ c' ^ (1 - γ) := (Real.rpow_pos_of_pos hc' _).le
  rw [← hc0, crraUtility_zero hγ1, crraUtility_of_ne (show γ ≠ 1 by linarith)]
  rw [sub_zero, sub_zero]
  rw [le_div_iff₀ (show (0 : ℝ) < 1 - γ by linarith)]
  nlinarith

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- Utility is bounded below: the domain is the closed half-line. -/
def Bounded : Prop := P.dom = Ici 0

/-- **Positive consumption in the bounded case.** The `⊥` at zero consumption is gone, so the
argument that used to be free is replaced by a marginal Inada condition. -/
theorem positiveConsumption_of_bounded_crra {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hb : P.Bounded) (hu : P.u = crraUtility γ) : P.PositiveConsumption := by
  refine P.positiveConsumption_of_marginalInada ?_
  rw [hb, hu]
  exact marginalInadaOn_Ici_crraUtility hγ0 hγ1

end IncomeFluctuation

/-! ### A CES economy with `γ = 1/2`

`crraUtility (1/2) c = 2 √c`, which is finite at `c = 0` and therefore inadmissible under the old
structure. The parameters are those of `dispersed`, so the two economies differ only in the
curvature of `u`. -/

/-- A household with CES utility at `γ = 1/2`: square-root utility, bounded below. -/
noncomputable def sqrtCES : IncomeFluctuation (Fin 2) 0 1 where
  income z := if z = 0 then 1 / 100 else 1
  transitionMatrix _ _ := 1 / 2
  interest := 0
  discount := 1 / 8
  u := crraUtility (1 / 2)
  minIncome := 1 / 100
  maxIncome := 1
  minIncome_pos := by norm_num
  minIncome_le z := by fin_cases z <;> norm_num
  le_maxIncome z := by fin_cases z <;> norm_num
  transitionMatrix_nonneg _ _ := by norm_num
  transitionMatrix_sum _ := by simp
  interest_gt_neg_one := by norm_num
  assetFloor_le_assetCap := by norm_num
  assetCap_nonneg := by norm_num
  minConsumption_pos := by norm_num
  minConsumption_le_floor := le_rfl
  discount_lt_one := by norm_num
  dom := Ici 0
  Ioi_subset_dom := Ioi_subset_Ici_self
  dom_subset_Ici := subset_rfl
  continuousOn_u_dom := continuousOn_crraUtility_Ici (by norm_num)
  monotoneOn_u_dom := monotoneOn_crraUtility_Ici (by norm_num)
  strictConcaveOn_u_dom := strictConcaveOn_crraUtility_Ici (by norm_num) (by norm_num)
  continuousOn_extendDom := continuousOn_extendDom_Ici (continuousOn_crraUtility_Ici (by norm_num))

@[simp] theorem sqrtCES_u : sqrtCES.u = crraUtility (1 / 2) := rfl

theorem sqrtCES_bounded : sqrtCES.Bounded := rfl

/-- Utility at zero consumption is finite. This is the fact the old structure forbade. -/
theorem sqrtCES_u_zero : sqrtCES.u 0 = 0 := crraUtility_zero (by norm_num)

/-- And it is not admissible under the level condition: `crra_pinch` rejected exactly this. -/
theorem sqrtCES_not_tendsto_atBot :
    ¬ Tendsto (crraUtility (1 / 2)) (𝓝[>] (0 : ℝ)) atBot :=
  not_tendsto_atBot_crraUtility (by norm_num)

/-- The reward is nonetheless real at zero consumption, so the household could in principle
choose it -- and `sqrtCES_positiveConsumption` is the proof that it does not. -/
theorem sqrtCES_not_unbounded : ¬ sqrtCES.Unbounded := by
  intro h
  have : (0 : ℝ) ∈ sqrtCES.dom := mem_Ici.mpr le_rfl
  rw [h] at this
  exact absurd this (by simp)

/-- **Positive consumption, earned from the margin.** -/
theorem sqrtCES_positiveConsumption : sqrtCES.PositiveConsumption :=
  sqrtCES.positiveConsumption_of_bounded_crra (by norm_num) (by norm_num) rfl rfl

/-! ### The whole development applies, unchanged -/

/-- The Bellman equation, with honest utility. -/
theorem sqrtCES_bellman {s : ℝ × Fin 2} (hs : s.1 ∈ Icc (0 : ℝ) 1) :
    ∃ a' ∈ Icc 0 (sqrtCES.maxSaving s), sqrtCES.consumption s a' ∈ sqrtCES.dom ∧
      sqrtCES.toExtended.valueFunction s
        = sqrtCES.u (sqrtCES.consumption s a')
          + sqrtCES.discount * ∑ z', sqrtCES.transitionMatrix s.2 z'
              * sqrtCES.toExtended.valueFunction (a', z') :=
  sqrtCES.exists_optimal_saving hs

/-- The optimal action is unique, from strict concavity on `Ici 0`. -/
theorem sqrtCES_optimal_action_unique {s : ℝ × Fin 2} (hs : s.1 ∈ Icc (0 : ℝ) 1) {a₀ a₁ : ℝ}
    (h₀ : a₀ ∈ sqrtCES.toExtended.feasible s) (h₁ : a₁ ∈ sqrtCES.toExtended.feasible s)
    (hm₀ : sqrtCES.toExtended.objectiveE sqrtCES.toExtended.valueFunction s a₀
      = ((sqrtCES.toExtended.bellmanFn sqrtCES.toExtended.valueFunction s : ℝ) : EReal))
    (hm₁ : sqrtCES.toExtended.objectiveE sqrtCES.toExtended.valueFunction s a₁
      = ((sqrtCES.toExtended.bellmanFn sqrtCES.toExtended.valueFunction s : ℝ) : EReal)) :
    a₀ = a₁ :=
  sqrtCES.optimal_action_unique hs h₀ h₁ hm₀ hm₁

/-- **Light's Theorem 1 holds for it**: the policy is increasing in assets. This is a result
about `IncomeFluctuation`, applied with no porting at all. -/
theorem sqrtCES_policy_mono {a a' : ℝ} {z : Fin 2} (ha : a ∈ Icc (0 : ℝ) 1)
    (ha' : a' ∈ Icc (0 : ℝ) 1) (hle : a ≤ a') :
    sqrtCES.policy (a, z) ≤ sqrtCES.policy (a', z) :=
  sqrtCES.policy_mono ha ha' hle

/-- Consumption is positive, and increasing in assets. -/
theorem sqrtCES_consumptionFn_pos {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 2) :
    0 < sqrtCES.consumptionFn z a :=
  sqrtCES.consumptionFn_pos sqrtCES_positiveConsumption ha z

theorem sqrtCES_monotoneOn_consumptionFn (z : Fin 2) :
    MonotoneOn (sqrtCES.consumptionFn z) (Icc 0 1) :=
  sqrtCES.monotoneOn_consumptionFn z

/-- **A stationary agent distribution exists**, by Krylov-Bogolyubov, with aggregate capital
equal to mean saving. The distribution half of the development needs no porting either. -/
theorem sqrtCES_exists_isStationary (μ₀ : ProbabilityMeasure sqrtCES.State) :
    ∃ μ : ProbabilityMeasure sqrtCES.State, sqrtCES.IsStationary μ :=
  sqrtCES.exists_isStationary μ₀

theorem sqrtCES_aggregateCapital_eq_integral_policy {μ : ProbabilityMeasure sqrtCES.State}
    (hμ : sqrtCES.IsStationary μ) :
    sqrtCES.aggregateCapital μ
      = ∫ s, sqrtCES.policy (sqrtCES.incl s) ∂(μ : Measure sqrtCES.State) :=
  sqrtCES.aggregateCapital_eq_integral_policy hμ

end LeanEconomics
