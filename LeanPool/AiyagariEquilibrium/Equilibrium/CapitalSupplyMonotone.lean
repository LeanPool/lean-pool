/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Distribution.Uniqueness
public import LeanPool.AiyagariEquilibrium.Equilibrium.Uniqueness


/-!
# Light (2018) Theorem 2: aggregate savings rise with the interest rate

`Equilibrium.Uniqueness` proves single crossing — Light's Theorem 3 — but carries MONOTONE
CAPITAL SUPPLY as a hypothesis, with nothing in the development connecting that hypothesis to
the household side. This file supplies the connection. Given that every household saves more at
the higher rate, aggregate capital is larger there, so the hypothesis of `equilibriumRate_unique`
follows from the conclusion of Light's Theorem 1.

That leaves the whole uniqueness argument resting on one thing: Theorem 1, itself reduced to the
Carroll and Kimball step in `IncomeFluctuationCarrollKimball`.

## The argument

Aggregate capital is mean assets under the stationary distribution, so what has to be compared
is two distributions, not two numbers. The comparison is first-order stochastic dominance in the
asset coordinate, `Dominates`, tested against bounded continuous functions that rise with assets
at each income state.

Three facts do the work, and they are the three things a dominance argument always needs.

* The Markov operator PRESERVES the test class: `markovOp` of a function rising in assets rises
  in assets, because the policy does (`policy_mono`). Note where the income chain enters — it
  does not. The probabilities depend on today's income state alone, so comparing two asset
  levels at a FIXED income state leaves them untouched.
* A uniformly larger policy gives a larger operator, on the test class.
* Dominance survives weak limits, since the test functions are bounded and continuous.

Then run both economies forward from the SAME initial distribution. They stay ordered at every
date by the first two facts, and each converges to its own stationary distribution by
`tendsto_pushProb_iterate` — the Doeblin convergence proved for step 4 of the roadmap, which has
had no consumer until now. The third fact passes the order to the limit.

The Doeblin data appears as hypotheses at both rates. It is the same minorisation the uniqueness
theorem runs on: an atom at the borrowing constraint.
-/

@[expose] public section

open scoped NNReal
open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetFloor assetCap : ℝ}

/-! ### Stochastic dominance in the asset coordinate -/

omit [Fintype Z] [Nonempty Z] [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z] in
/-- Bounded continuous functions that rise with assets, at each income state separately. These
are the test functions of first-order stochastic dominance in the asset coordinate. -/
def MonoAsset (h : (↥(Icc assetFloor assetCap) × Z) →ᵇ ℝ) : Prop :=
  ∀ (z : Z) (a b : ↥(Icc assetFloor assetCap)), a ≤ b → h (a, z) ≤ h (b, z)

/-- **First-order stochastic dominance in assets.** -/
def Dominates (μ ν : ProbabilityMeasure (↥(Icc assetFloor assetCap) × Z)) : Prop :=
  ∀ h : (↥(Icc assetFloor assetCap) × Z) →ᵇ ℝ, MonoAsset h →
    ∫ s, h s ∂(μ : Measure _) ≤ ∫ s, h s ∂(ν : Measure _)

omit [Fintype Z] [Nonempty Z] [DiscreteTopology Z] [BorelSpace Z] in
theorem Dominates.refl (μ : ProbabilityMeasure (↥(Icc assetFloor assetCap) × Z)) :
    Dominates μ μ := fun _ _ => le_rfl

omit [Fintype Z] [Nonempty Z] in
/-- **Dominance survives weak limits**, because the test functions are bounded and
continuous. -/
theorem Dominates.of_tendsto [Finite Z]
    {μs νs : ℕ → ProbabilityMeasure (↥(Icc assetFloor assetCap) × Z)}
    {μ ν : ProbabilityMeasure (↥(Icc assetFloor assetCap) × Z)}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hd : ∀ n, Dominates (μs n) (νs n)) : Dominates μ ν := by
  let _ := Fintype.ofFinite Z
  exact fun h hh => le_of_tendsto_of_tendsto
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ h)
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν h)
    (Eventually.of_forall fun n => hd n h hh)

/-! ### The operator preserves the test class, and respects a larger policy -/

variable (P Q : IncomeFluctuation Z assetFloor assetCap)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The Markov operator preserves the test class.** The expected value tomorrow of a payoff
that rises with assets itself rises with assets, because the policy does. -/
theorem monoAsset_markovOp {h : P.State →ᵇ ℝ} (hh : MonoAsset h) :
    MonoAsset (P.markovOp h) := by
  intro z a b hab
  simp only [markovOp_apply]
  refine Finset.sum_le_sum fun z' _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (P.prob_nonneg _ _)
  exact hh z' _ _ (P.policy_mono a.2 b.2 hab)

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **A uniformly larger policy gives a larger operator**, on the test class. -/
theorem markovOp_le_of_policy_le
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s ≤ Q.policy s)
    {h : P.State →ᵇ ℝ} (hh : MonoAsset h) (s : P.State) :
    P.markovOp h s ≤ Q.markovOp h s := by
  simp only [markovOp_apply]
  refine Finset.sum_le_sum fun z' _ => ?_
  rw [show P.prob s z' = Q.prob s z' from hprob _ _]
  refine mul_le_mul_of_nonneg_left ?_ (Q.prob_nonneg _ _)
  exact hh z' _ _ (hpol (P.incl s) (P.incl_mem s))

/-- **One period preserves dominance.** -/
theorem Dominates.pushProb
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s ≤ Q.policy s)
    {μ ν : ProbabilityMeasure P.State} (hd : Dominates μ ν) :
    Dominates (P.pushProb μ) (Q.pushProb ν) := by
  intro h hh
  rw [coe_pushProb, coe_pushProb, P.integral_push _ h, Q.integral_push _ h]
  refine le_trans (integral_mono ((P.markovOp h).integrable _)
    ((Q.markovOp h).integrable _) ?_) (hd _ (Q.monoAsset_markovOp hh))
  exact fun s => markovOp_le_of_policy_le P Q hprob hpol hh s

/-! ### Theorem 2 -/

/-- **Stationary distributions are ordered when policies are.** Both economies are run forward
from the same starting distribution and stay ordered at every date, so their limits are ordered.

Convergence is the hypothesis rather than the Doeblin data, because that is all the argument
uses; `dominates_stationary_of_policy_le` supplies it from the minorisation. -/
theorem dominates_of_policy_le
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s ≤ Q.policy s)
    {μ₀ μ ν : ProbabilityMeasure P.State}
    (hP : Tendsto (fun m => P.pushProb^[m] μ₀) atTop (𝓝 μ))
    (hQ : Tendsto (fun m => Q.pushProb^[m] μ₀) atTop (𝓝 ν)) :
    Dominates μ ν := by
  refine Dominates.of_tendsto hP hQ fun n => ?_
  induction n with
  | zero => exact Dominates.refl μ₀
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ih.pushProb P Q hprob hpol

/-- The same, with convergence supplied by the Doeblin minorisation at each rate — the atom at
the borrowing constraint that `Distribution.Uniqueness` runs on. -/
theorem dominates_stationary_of_policy_le
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s ≤ Q.policy s)
    {zP : Z} {sP : P.State} {pP : ℝ} {NP : ℕ} (hpP0 : 0 < pP)
    (hpP : ∀ s : P.State, pP ≤ P.prob s zP) (hbadP : ∀ s, (P.badStep zP)^[NP] s = sP)
    {zQ : Z} {sQ : Q.State} {pQ : ℝ} {NQ : ℕ} (hpQ0 : 0 < pQ)
    (hpQ : ∀ s : Q.State, pQ ≤ Q.prob s zQ) (hbadQ : ∀ s, (Q.badStep zQ)^[NQ] s = sQ)
    {μ ν : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) (hν : Q.IsStationary ν) :
    Dominates μ ν := by
  obtain ⟨s₀⟩ : Nonempty P.State := inferInstance
  exact dominates_of_policy_le P Q hprob hpol
    (μ₀ := ⟨Measure.dirac s₀, inferInstance⟩)
    (P.tendsto_pushProb_iterate hpP0 hpP hbadP _ hμ)
    (Q.tendsto_pushProb_iterate hpQ0 hpQ hbadQ _ hν)

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem monoAsset_assetCoord : MonoAsset P.assetCoord := fun _ _ _ hab => hab

/-- **Light (2018) Theorem 2.** If every household saves at least as much in the second economy
as in the first, aggregate capital is at least as large. -/
theorem aggregateCapital_le_of_policy_le
    (hprob : ∀ z z' : Z, P.transitionMatrix z z' = Q.transitionMatrix z z')
    (hpol : ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → P.policy s ≤ Q.policy s)
    {zP : Z} {sP : P.State} {pP : ℝ} {NP : ℕ} (hpP0 : 0 < pP)
    (hpP : ∀ s : P.State, pP ≤ P.prob s zP) (hbadP : ∀ s, (P.badStep zP)^[NP] s = sP)
    {zQ : Z} {sQ : Q.State} {pQ : ℝ} {NQ : ℕ} (hpQ0 : 0 < pQ)
    (hpQ : ∀ s : Q.State, pQ ≤ Q.prob s zQ) (hbadQ : ∀ s, (Q.badStep zQ)^[NQ] s = sQ)
    {μ ν : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) (hν : Q.IsStationary ν) :
    P.aggregateCapital μ ≤ Q.aggregateCapital ν :=
  dominates_stationary_of_policy_le P Q hprob hpol hpP0 hpP hbadP hpQ0 hpQ hbadQ hμ hν
    P.assetCoord (monoAsset_assetCoord P)

/-- **Capital supply is monotone in the interest rate** whenever the household policy is.

This is exactly the hypothesis `hS` of `equilibriumRate_unique`, so with Light's Theorem 1 in
hand — the policy rising in the rate — the equilibrium rate is unique. Theorem 1 is the only
thing still missing, and `IncomeFluctuationCarrollKimball` has reduced it to one step. -/
theorem monotoneOn_capitalSupply_of_policy_mono {rlo rhi : ℝ}
    (Pf : ℝ → IncomeFluctuation Z assetFloor assetCap)
    (hprob : ∀ r r' : ℝ, ∀ z z' : Z,
      (Pf r).transitionMatrix z z' = (Pf r').transitionMatrix z z')
    (hpol : ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap → (Pf r).policy s ≤ (Pf r').policy s)
    (μ₀ : ProbabilityMeasure P.State) (ν : ℝ → ProbabilityMeasure P.State)
    (hconv : ∀ r ∈ Icc rlo rhi, Tendsto (fun m => (Pf r).pushProb^[m] μ₀) atTop (𝓝 (ν r))) :
    MonotoneOn (fun r => P.aggregateCapital (ν r)) (Icc rlo rhi) := fun r hr r' hr' hrr =>
  dominates_of_policy_le (Pf r) (Pf r') (hprob r r') (hpol r hr r' hr' hrr)
    (hconv r hr) (hconv r' hr') P.assetCoord (monoAsset_assetCoord P)

/-- **Capital supply is ordered when the policies are**, across two FAMILIES of economies rather
than across two rates of one. The patience comparative static consumes this: a more patient
population saves more at every rate, so its supply schedule lies above. -/
theorem capitalSupply_le_of_policy_le {rlo rhi : ℝ}
    (Pf Qf : ℝ → IncomeFluctuation Z assetFloor assetCap)
    (hprob : ∀ r : ℝ, ∀ z z' : Z, (Pf r).transitionMatrix z z' = (Qf r).transitionMatrix z z')
    (hpol : ∀ r ∈ Icc rlo rhi, ∀ s : ℝ × Z, s.1 ∈ Icc assetFloor assetCap →
      (Pf r).policy s ≤ (Qf r).policy s)
    (μ₀ : ProbabilityMeasure P.State) (ν ρ : ℝ → ProbabilityMeasure P.State)
    (hconvP : ∀ r ∈ Icc rlo rhi, Tendsto (fun m => (Pf r).pushProb^[m] μ₀) atTop (𝓝 (ν r)))
    (hconvQ : ∀ r ∈ Icc rlo rhi, Tendsto (fun m => (Qf r).pushProb^[m] μ₀) atTop (𝓝 (ρ r)))
    {r : ℝ} (hr : r ∈ Icc rlo rhi) :
    P.aggregateCapital (ν r) ≤ P.aggregateCapital (ρ r) :=
  dominates_of_policy_le (Pf r) (Qf r) (hprob r) (hpol r hr) (hconvP r hr) (hconvQ r hr)
    P.assetCoord (monoAsset_assetCoord P)

end IncomeFluctuation

end LeanEconomics
