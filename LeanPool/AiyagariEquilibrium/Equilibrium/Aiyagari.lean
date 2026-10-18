/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Distribution.Uniqueness

/-!
# Aiyagari stationary equilibrium

An interest rate at which the capital households choose to hold equals the capital firms
want to employ.

Aggregation is the easy half and is done here in full: mean assets under the agent
distribution is the integral of the asset coordinate, which is a BOUNDED CONTINUOUS function
on the compact state space, so aggregate capital is weakly continuous in the distribution.
That is the one place the compactness of the state space pays off directly, and it means no
separate uniform-integrability argument is needed.

The firm side is left abstract: any continuous capital demand schedule `D` will do, so a
Cobb-Douglas firm with depreciation is one instance among many, and nothing here depends on
which.

What is assumed rather than proved is that capital supply moves continuously with the
interest rate. That is the remaining gap, and it is a real one -- see the note at the end of
this file.
-/

@[expose] public section

open scoped NNReal ENNReal
open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### Aggregation -/

theorem continuous_assetCoord : Continuous fun s : P.State => (s.1 : ℝ) :=
  continuous_subtype_val.comp continuous_fst

theorem norm_assetCoord_le (s : P.State) : ‖(s.1 : ℝ)‖ ≤ |assetFloor| + |assetCap| :=
  abs_le.mpr ⟨by linarith [s.1.2.1, neg_abs_le assetFloor, abs_nonneg assetCap],
    by linarith [s.1.2.2, le_abs_self assetCap, abs_nonneg assetFloor]⟩

/-- The asset coordinate, as a bounded continuous function. Boundedness is exactly the asset
cap, and continuity is immediate; together they are what make aggregate capital behave well
under weak convergence. -/
noncomputable def assetCoord : P.State →ᵇ ℝ :=
  ofNormedAddCommGroup (fun s => (s.1 : ℝ)) P.continuous_assetCoord (|assetFloor| + |assetCap|)
    P.norm_assetCoord_le

@[simp]
theorem assetCoord_apply (s : P.State) : P.assetCoord s = (s.1 : ℝ) := rfl

variable [MeasurableSpace Z] [BorelSpace Z]

/-- **Aggregate capital**: mean assets under an agent distribution. -/
noncomputable def aggregateCapital (μ : ProbabilityMeasure P.State) : ℝ :=
  ∫ s, P.assetCoord s ∂(μ : Measure P.State)

/-- **Aggregation is weakly continuous.** The asset coordinate is bounded and continuous, so
this is exactly what the weak topology is designed to give. -/
theorem continuous_aggregateCapital : Continuous P.aggregateCapital :=
  P.continuous_integral_bcf P.assetCoord

end IncomeFluctuation

/-! ### Equilibrium -/

section Equilibrium

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z] {assetFloor assetCap : ℝ}

/-- **An Aiyagari stationary equilibrium** at interest rate `r`: the household problem
`Pf r` has a stationary agent distribution whose aggregate capital equals the capital
demanded at that rate. -/
def IsAiyagariEquilibrium (Pf : ℝ → IncomeFluctuation Z assetFloor assetCap) (D : ℝ → ℝ)
    (r : ℝ) : Prop :=
  ∃ μ : ProbabilityMeasure (Pf r).State,
    (Pf r).IsStationary μ ∧ (Pf r).aggregateCapital μ = D r

/-- **Existence of an Aiyagari stationary equilibrium.**

Given a capital supply schedule `S` that is realised by a stationary distribution at every
interest rate and is continuous, and any continuous capital demand schedule `D`, a rate at
which the two agree exists as soon as excess demand changes sign across the interval.

Uniqueness of the stationary distribution is what makes `S` a FUNCTION of `r` rather than a
correspondence, and that is what allows the intermediate value theorem to close the argument
in place of a fixed point theorem for correspondences -- Mathlib has no Kakutani. -/
theorem exists_aiyagari_equilibrium
    {Pf : ℝ → IncomeFluctuation Z assetFloor assetCap} {D S : ℝ → ℝ} {rlo rhi : ℝ} (hle : rlo ≤ rhi)
    (hS : ∀ r, ∃ μ : ProbabilityMeasure (Pf r).State,
      (Pf r).IsStationary μ ∧ (Pf r).aggregateCapital μ = S r)
    (hScont : ContinuousOn S (Icc rlo rhi)) (hDcont : ContinuousOn D (Icc rlo rhi))
    (hlo : S rlo ≤ D rlo) (hhi : D rhi ≤ S rhi) :
    ∃ r ∈ Icc rlo rhi, IsAiyagariEquilibrium Pf D r := by
  have hcont : ContinuousOn (fun r => S r - D r) (Icc rlo rhi) := hScont.sub hDcont
  have hmem : (0 : ℝ) ∈ Icc (S rlo - D rlo) (S rhi - D rhi) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hle hcont hmem
  refine ⟨r, hr, ?_⟩
  obtain ⟨μ, hstat, hagg⟩ := hS r
  exact ⟨μ, hstat, by rw [hagg]; linarith [sub_eq_zero.mp hr0]⟩

end Equilibrium

end LeanEconomics

/-!
## What remains

`exists_aiyagari_equilibrium` takes continuity of capital supply `S` as a hypothesis. The
pieces already proved discharge part of it and identify exactly what is missing.

Given a family of household problems indexed by the interest rate:

1. `continuousAt_fixedPoint` (in `DynamicProgramming/Parametric.lean`) reduces continuity of
   `r ↦ valueFunction r` to continuity of `r ↦ bellman r v₀` at the SINGLE function
   `v₀ = valueFunction r₀`, in sup norm. The Blackwell contraction modulus is the discount
   factor, which does not vary with `r`, so the common-modulus hypothesis is free.
2. From a continuous value function, continuity of the policy in `r` would follow by the same
   Berge argument that already gives continuity in the state, since the maximiser is unique.
3. From a continuous policy, `r ↦ push r` is weakly continuous, so the set of stationary
   distributions has closed graph; with UNIQUENESS (`stationary_unique_of_exhausts`) a
   convergent subnet argument on the compact space of probability measures gives continuity
   of `r ↦ μ r`.
4. `continuous_aggregateCapital` then gives continuity of `S`, since the asset coordinate is
   bounded and continuous. This step is proved.

Step 1 is the substantial one: it needs a sup-norm (not pointwise) estimate, uniform over the
state space, and the extended-real reward makes it delicate near zero consumption, where
utility falls to `-∞`. The estimate is true -- the optimum keeps consumption bounded away
from zero because the value is finite -- but proving it uniformly in `r` is real work.

A second obstacle is structural rather than mathematical: `assetCap` is a FIELD of
`IncomeFluctuation`, so `(Pf r).State` is a different type for each `r`. Any statement
quantifying over the family across rates has to either fix the cap across the family or carry
transports. That is why the theorem above quantifies the distribution inside an existential,
where the dependence causes no trouble.
-/
