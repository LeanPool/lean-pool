/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.DynamicProgramming.Bellman

/-!
# Stochastic dynamic programming with finitely many shocks

The Bellman operator

  `T v s = sup { r (s, a) + β * ∑ z, p z (s, a) * v (g z (s, a)) | a ∈ Γ s }`

where a shock `z` is drawn from a finite set with probabilities `p z (s, a)` and leads to
the state `g z (s, a)`. This is the deterministic operator of
`LeanEconomics.DynamicProgramming.Bellman` with the successor state replaced by an
expectation over successors.

## Why this is a new structure rather than a reuse

The deterministic program's continuation is `v` evaluated at one point. Here it is a convex
combination of `v` at several points, which is not of that form, so the operator has to be
rebuilt. Everything above the operator is reused unchanged: the same Blackwell conditions
give the contraction, and the same Berge theorem gives continuity. Only the two facts about
the expectation are new, and they are exactly the two properties of a probability
distribution:

* `p ≥ 0` gives **monotonicity** -- a larger continuation value cannot lower the average;
* `∑ p = 1` gives **discounting** -- adding a constant to the continuation value adds
  exactly that constant to the average, not more.

Shock probabilities may depend on the state and the action, which covers a Markov chain on
a component of the state as the special case where they depend on that component alone.

## Main results

* `LeanEconomics.StochasticDynamicProgram.blackwell` : the operator is a contraction.
* `LeanEconomics.StochasticDynamicProgram.exists_optimal_policy` : the value function
  satisfies the stochastic Bellman equation, and the maximum is attained.
-/

@[expose] public section

open scoped NNReal
open Filter Topology BoundedContinuousFunction

namespace LeanEconomics

variable {S A Z : Type*} [TopologicalSpace S] [TopologicalSpace A] [Fintype Z]

/-- A **stochastic dynamic program** with finitely many shocks. -/
structure StochasticDynamicProgram (S A Z : Type*) [TopologicalSpace S] [TopologicalSpace A]
    [Fintype Z] where
  /-- The actions available at each state. -/
  feasible : S → Set A
  isCompact_feasible : ∀ s, IsCompact (feasible s)
  feasible_nonempty : ∀ s, (feasible s).Nonempty
  upperHemicontinuous_feasible : UpperHemicontinuous feasible
  lowerHemicontinuous_feasible : LowerHemicontinuous feasible
  /-- The one-period reward. -/
  reward : (S × A) →ᵇ ℝ
  /-- The state reached when shock `z` occurs. -/
  transition : Z → C(S × A, S)
  /-- The probability that shock `z` occurs. -/
  prob : Z → C(S × A, ℝ)
  prob_nonneg : ∀ z p, 0 ≤ prob z p
  prob_sum : ∀ p, ∑ z, prob z p = 1
  /-- The factor applied to next-period value. -/
  discount : ℝ≥0
  discount_lt_one : discount < 1

namespace StochasticDynamicProgram

variable (D : StochasticDynamicProgram S A Z)

/-- The expected continuation value of `v` after choosing `a` at `s`. -/
noncomputable def expectation (v : S →ᵇ ℝ) (p : S × A) : ℝ :=
  ∑ z, D.prob z p * v (D.transition z p)

/-- Current reward plus the discounted expected continuation value. -/
noncomputable def objective (v : S →ᵇ ℝ) (s : S) (a : A) : ℝ :=
  D.reward (s, a) + D.discount * D.expectation v (s, a)

theorem continuous_expectation (v : S →ᵇ ℝ) : Continuous (D.expectation v) :=
  continuous_finsetSum _ fun z _ =>
    (D.prob z).continuous.mul (v.continuous.comp (D.transition z).continuous)

theorem continuous_uncurry_objective (v : S →ᵇ ℝ) : Continuous ↿(D.objective v) :=
  D.reward.continuous.add (continuous_const.mul (D.continuous_expectation v))

/-- An average of values of `v` is no larger than the size of `v`. This is where `p ≥ 0`
and `∑ p = 1` first do their work. -/
theorem abs_expectation_le (v : S →ᵇ ℝ) (p : S × A) : |D.expectation v p| ≤ ‖v‖ := by
  calc |D.expectation v p| ≤ ∑ z, |D.prob z p * v (D.transition z p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, D.prob z p * |v (D.transition z p)| := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [abs_mul, abs_of_nonneg (D.prob_nonneg z p)]
    _ ≤ ∑ z, D.prob z p * ‖v‖ := by
        refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (D.prob_nonneg z p)
        simpa [Real.norm_eq_abs] using v.norm_coe_le_norm (D.transition z p)
    _ = ‖v‖ := by rw [← Finset.sum_mul, D.prob_sum, one_mul]

theorem abs_objective_le (v : S →ᵇ ℝ) (s : S) (a : A) :
    |D.objective v s a| ≤ ‖D.reward‖ + D.discount * ‖v‖ := by
  have h₁ : |D.reward (s, a)| ≤ ‖D.reward‖ := by
    simpa [Real.norm_eq_abs] using D.reward.norm_coe_le_norm (s, a)
  have h₂ := D.abs_expectation_le v (s, a)
  have hβ : (0 : ℝ) ≤ D.discount := D.discount.coe_nonneg
  rw [abs_le] at h₁ h₂
  simp only [objective, abs_le]
  constructor <;>
    nlinarith [h₁.1, h₁.2, h₂.1, h₂.2, mul_le_mul_of_nonneg_left h₂.1 hβ,
      mul_le_mul_of_nonneg_left h₂.2 hβ]

/-- The Bellman operator as a bare function. -/
noncomputable def bellmanFn (v : S →ᵇ ℝ) (s : S) : ℝ :=
  maxValue (D.objective v) D.feasible s

theorem le_bellmanFn (v : S →ᵇ ℝ) {s : S} {a : A} (ha : a ∈ D.feasible s) :
    D.objective v s a ≤ D.bellmanFn v s :=
  le_maxValue (D.continuous_uncurry_objective v) (D.isCompact_feasible s) ha

theorem bellmanFn_le (v : S →ᵇ ℝ) {s : S} {c : ℝ}
    (h : ∀ a ∈ D.feasible s, D.objective v s a ≤ c) : D.bellmanFn v s ≤ c :=
  maxValue_le (D.feasible_nonempty s) h

theorem abs_bellmanFn_le (v : S →ᵇ ℝ) (s : S) :
    |D.bellmanFn v s| ≤ ‖D.reward‖ + D.discount * ‖v‖ := by
  obtain ⟨a, ha⟩ := D.feasible_nonempty s
  rw [abs_le]
  refine ⟨?_, D.bellmanFn_le v fun b _ => (le_abs_self _).trans (D.abs_objective_le v s b)⟩
  exact le_trans (neg_le_of_abs_le (D.abs_objective_le v s a)) (D.le_bellmanFn v ha)

/-- The **stochastic Bellman operator** on bounded continuous functions. -/
noncomputable def bellman (v : S →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (D.bellmanFn v)
    (continuous_maxValue (D.continuous_uncurry_objective v) D.feasible_nonempty
      D.isCompact_feasible D.upperHemicontinuous_feasible D.lowerHemicontinuous_feasible)
    (‖D.reward‖ + D.discount * ‖v‖)
    fun s => by simpa [Real.norm_eq_abs] using D.abs_bellmanFn_le v s

@[simp]
theorem bellman_apply (v : S →ᵇ ℝ) (s : S) :
    D.bellman v s = maxValue (D.objective v) D.feasible s := rfl

/-- **Blackwell's conditions hold.** Monotonicity is `prob_nonneg`: averaging with
nonnegative weights preserves order. Discounting is `prob_sum`: the weights sum to one, so
raising the continuation value by `c` raises the average by exactly `c`, and the objective
by `β * c`. -/
theorem blackwell : Blackwell D.discount D.bellman where
  monotone := by
    intro v w hvw s
    have hβ : (0 : ℝ) ≤ D.discount := D.discount.coe_nonneg
    have key : ∀ a ∈ D.feasible s, D.objective v s a ≤ D.bellmanFn w s := by
      intro a ha
      refine le_trans ?_ (D.le_bellmanFn w ha)
      have hsum : D.expectation v (s, a) ≤ D.expectation w (s, a) := by
        refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (D.prob_nonneg z _)
        simpa using hvw (D.transition z (s, a))
      simp only [objective]
      nlinarith
    exact D.bellmanFn_le v key
  discounting := by
    intro v c _ s
    have key : ∀ a ∈ D.feasible s, D.objective (v + const S c) s a
        ≤ D.bellmanFn v s + D.discount * c := by
      intro a ha
      have hterm : ∀ z : Z, D.prob z (s, a) * (v + const S c) (D.transition z (s, a))
          = D.prob z (s, a) * v (D.transition z (s, a)) + D.prob z (s, a) * c := fun z => by
        simp only [coe_add, const_apply, Pi.add_apply]; ring
      have hsum : D.expectation (v + const S c) (s, a) = D.expectation v (s, a) + c := by
        simp only [expectation]
        rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_add_distrib,
          ← Finset.sum_mul, D.prob_sum, one_mul]
      have h : D.objective (v + const S c) s a = D.objective v s a + D.discount * c := by
        simp only [objective, hsum]; ring
      rw [h]
      have := D.le_bellmanFn v (s := s) ha
      linarith
    exact D.bellmanFn_le (v + const S c) key

/-- The supremum is attained: an optimal action exists at every state. -/
theorem exists_optimal_action (v : S →ᵇ ℝ) (s : S) :
    ∃ a ∈ D.feasible s, D.bellman v s = D.objective v s a ∧
      ∀ b ∈ D.feasible s, D.objective v s b ≤ D.objective v s a := by
  obtain ⟨a, ha, hmax⟩ :=
    argmax_nonempty (D.continuous_uncurry_objective v) (D.feasible_nonempty s)
      (D.isCompact_feasible s)
  exact ⟨a, ha,
    maxValue_eq (D.continuous_uncurry_objective v) (D.isCompact_feasible s) ⟨ha, hmax⟩,
    fun b hb => isMaxOn_iff.mp hmax b hb⟩

section ValueFunction

/-- The **value function** of the stochastic program. -/
noncomputable def valueFunction : S →ᵇ ℝ := D.blackwell.valueFunction D.discount_lt_one

theorem bellman_valueFunction : D.bellman D.valueFunction = D.valueFunction :=
  D.blackwell.isFixedPt_valueFunction D.discount_lt_one

theorem eq_valueFunction {v : S →ᵇ ℝ} (hv : D.bellman v = v) : v = D.valueFunction :=
  D.blackwell.eq_valueFunction D.discount_lt_one hv

theorem tendsto_iterate_valueFunction (v : S →ᵇ ℝ) :
    Tendsto (fun n => D.bellman^[n] v) atTop (𝓝 D.valueFunction) :=
  D.blackwell.tendsto_iterate_valueFunction D.discount_lt_one v

theorem norm_iterate_sub_valueFunction_le (v : S →ᵇ ℝ) (n : ℕ) :
    ‖D.bellman^[n] v - D.valueFunction‖
      ≤ (D.discount : ℝ) ^ n / (1 - D.discount) * ‖D.bellman v - v‖ :=
  D.blackwell.norm_iterate_sub_valueFunction_le D.discount_lt_one v n

/-- **The stochastic Bellman equation.** At every state there is an optimal action, and the
value is the reward it earns plus the discounted expected value of the successor state. -/
theorem exists_optimal_policy (s : S) :
    ∃ a ∈ D.feasible s, D.valueFunction s
      = D.reward (s, a)
        + D.discount * ∑ z, D.prob z (s, a) * D.valueFunction (D.transition z (s, a)) := by
  obtain ⟨a, ha, heq, -⟩ := D.exists_optimal_action D.valueFunction s
  rw [D.bellman_valueFunction] at heq
  exact ⟨a, ha, heq⟩

end ValueFunction

end StochasticDynamicProgram

end LeanEconomics
