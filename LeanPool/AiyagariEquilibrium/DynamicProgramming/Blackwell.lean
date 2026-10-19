/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Blackwell's sufficient conditions

An operator on bounded continuous functions that is *monotone* and *discounts* is a
contraction. This is the standard route to showing that a Bellman operator has a unique
fixed point: verifying monotonicity and discounting is elementary, whereas verifying the
contraction property directly is not.

The setting is the space `S →ᵇ ℝ` of bounded continuous real-valued functions on a state
space `S`, with the supremum norm. It is already a complete metric space, which is what
the Banach fixed point theorem needs.

## Main definitions

* `LeanEconomics.Blackwell β T` : `T` is monotone and discounts at rate `β`.
* `LeanEconomics.Blackwell.valueFunction` : the unique fixed point of `T`.

## Main results

* `LeanEconomics.Blackwell.contractingWith` : Blackwell's conditions imply `T` is a
  `β`-contraction.
* `LeanEconomics.Blackwell.isFixedPt_valueFunction`,
  `LeanEconomics.Blackwell.eq_valueFunction` : the value function is the unique solution
  of the fixed point equation `T v = v`.
* `LeanEconomics.Blackwell.tendsto_iterate_valueFunction` : value function iteration
  converges to it, from any starting guess.
* `LeanEconomics.Blackwell.norm_iterate_sub_valueFunction_le` : the geometric error bound
  `‖Tⁿ v - v*‖ ≤ βⁿ / (1 - β) * ‖T v - v‖`, which is the stopping rule used in practice.

## Examples

* `LeanEconomics.Blackwell.affine` : the affine operator `v ↦ f + β • v` satisfies the
  conditions. This is the degenerate case of a Bellman operator in which the agent has no
  choice to make, and it witnesses that the hypotheses are consistent.

## References

* Stokey, Lucas and Prescott, *Recursive Methods in Economic Dynamics*.
* Blackwell, *Discounted dynamic programming*, Ann. Math. Statist. 36 (1965).
-/

@[expose] public section

open scoped NNReal
open Filter Topology

namespace BoundedContinuousFunction

variable {S : Type*} [TopologicalSpace S]

/-- Any bounded continuous function is dominated by any other one shifted up by the
distance between them. -/
theorem le_add_const_norm_sub (v w : S →ᵇ ℝ) : v ≤ w + const S ‖v - w‖ := by
  rw [← sub_le_iff_le_add']
  exact sub_nonneg.mp (norm_sub_nonneg (v - w))

end BoundedContinuousFunction

namespace LeanEconomics

open BoundedContinuousFunction

variable {S : Type*} [TopologicalSpace S]

/-- **Blackwell's sufficient conditions** for an operator on bounded continuous functions
to be a contraction of modulus `β`.

`monotone` says a pointwise larger continuation value cannot lower the operator's value;
`discounting` says that raising the continuation value everywhere by a constant `c` raises
the operator's value by at most `β * c`. For a Bellman operator both are immediate: the
first because the objective is increasing in the continuation value, the second because
the continuation value enters multiplied by the discount factor. -/
structure Blackwell (β : ℝ≥0) (T : (S →ᵇ ℝ) → (S →ᵇ ℝ)) : Prop where
  /-- A pointwise larger continuation value gives a pointwise larger image. -/
  monotone : Monotone T
  /-- Adding a constant `c ≥ 0` to the continuation value raises the image by at most
  `β * c`. -/
  discounting : ∀ (v : S →ᵇ ℝ) (c : ℝ), 0 ≤ c → T (v + const S c) ≤ T v + const S (β * c)

namespace Blackwell

variable {β : ℝ≥0} {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)}

/-- The one-sided bound at the heart of Blackwell's argument: `T v` cannot exceed `T w`
by more than `β` times the distance between `v` and `w`. -/
theorem apply_le_add_const (h : Blackwell β T) (v w : S →ᵇ ℝ) :
    T v ≤ T w + const S (β * ‖v - w‖) :=
  (h.monotone (le_add_const_norm_sub v w)).trans (h.discounting w _ (norm_nonneg _))

/-- Blackwell's conditions make `T` Lipschitz with constant `β` in the supremum norm. -/
theorem norm_sub_le (h : Blackwell β T) (v w : S →ᵇ ℝ) : ‖T v - T w‖ ≤ β * ‖v - w‖ := by
  rw [norm_le (by positivity)]
  intro x
  have h₁ : T v x ≤ T w x + β * ‖v - w‖ := by simpa using h.apply_le_add_const v w x
  have h₂ : T w x ≤ T v x + β * ‖w - v‖ := by simpa using h.apply_le_add_const w v x
  rw [norm_sub_rev w v] at h₂
  rw [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem lipschitzWith (h : Blackwell β T) : LipschitzWith β T :=
  LipschitzWith.of_dist_le_mul fun v w => by
    simpa only [dist_eq_norm] using h.norm_sub_le v w

/-- **Blackwell's theorem**: a monotone operator that discounts at rate `β < 1` is a
contraction of modulus `β`. -/
theorem contractingWith (h : Blackwell β T) (hβ : β < 1) : ContractingWith β T :=
  ⟨hβ, h.lipschitzWith⟩

section ValueFunction

variable (h : Blackwell β T) (hβ : β < 1)

/-- The **value function**: the unique fixed point of an operator satisfying Blackwell's
conditions, obtained from the Banach fixed point theorem. -/
noncomputable def valueFunction : S →ᵇ ℝ :=
  ContractingWith.fixedPoint T (h.contractingWith hβ)

/-- The value function solves the fixed point equation. -/
theorem isFixedPt_valueFunction : T (h.valueFunction hβ) = h.valueFunction hβ :=
  (h.contractingWith hβ).fixedPoint_isFixedPt

/-- The value function is the *only* solution of the fixed point equation. -/
theorem eq_valueFunction {v : S →ᵇ ℝ} (hv : T v = v) : v = h.valueFunction hβ :=
  (h.contractingWith hβ).fixedPoint_unique hv

/-- **Value function iteration converges**, from any starting guess. -/
theorem tendsto_iterate_valueFunction (v : S →ᵇ ℝ) :
    Tendsto (fun n => T^[n] v) atTop (𝓝 (h.valueFunction hβ)) :=
  (h.contractingWith hβ).tendsto_iterate_fixedPoint v

/-- The geometric error bound for value function iteration: after `n` iterations from a
guess `v`, the distance to the value function is at most `βⁿ / (1 - β)` times the size of
the first update. This is the a priori bound behind the usual stopping rule. -/
theorem norm_iterate_sub_valueFunction_le (v : S →ᵇ ℝ) (n : ℕ) :
    ‖T^[n] v - h.valueFunction hβ‖ ≤ (β : ℝ) ^ n / (1 - β) * ‖T v - v‖ := by
  have key := (h.contractingWith hβ).apriori_dist_iterate_fixedPoint_le v n
  rw [dist_eq_norm, dist_eq_norm, norm_sub_rev v (T v)] at key
  calc ‖T^[n] v - h.valueFunction hβ‖ ≤ ‖T v - v‖ * (β : ℝ) ^ n / (1 - β) := key
    _ = (β : ℝ) ^ n / (1 - β) * ‖T v - v‖ := by ring

end ValueFunction

/-- The affine operator `v ↦ f + β • v`, a dynamic program with a single feasible action,
satisfies Blackwell's conditions. -/
theorem affine (f : S →ᵇ ℝ) (β : ℝ≥0) :
    Blackwell β (fun v => f + (β : ℝ) • v) where
  monotone := by
    intro v w hvw x
    have hx : v x ≤ w x := by simpa using hvw x
    have hβ : (0 : ℝ) ≤ β := β.coe_nonneg
    have : f x + (β : ℝ) * v x ≤ f x + (β : ℝ) * w x := by nlinarith
    simpa using this
  discounting := by
    intro v c _
    refine le_of_eq ?_
    ext x
    simp only [coe_add, coe_smul, const_apply, Pi.add_apply, smul_eq_mul]
    ring

end Blackwell

/-- **A dominated operator has a dominated fixed point.** If one Bellman operator never returns
more than another, its value function never does either.

This is the workhorse of comparative statics: to compare two economies one only has to compare
their operators at a COMMON continuation value, which is a one-period calculation, and the
comparison of the infinite-horizon values follows. The two need not share a discount factor.
No policy comparison, no differentiability,
nothing about argmaxes -- the whole content is that value function iteration started from the
same place stays ordered. -/
theorem Blackwell.valueFunction_le {β₁ β₂ : ℝ≥0} {T₁ T₂ : (S →ᵇ ℝ) → (S →ᵇ ℝ)}
    (h₁ : Blackwell β₁ T₁) (h₂ : Blackwell β₂ T₂) (hβ₁ : β₁ < 1) (hβ₂ : β₂ < 1)
    (hle : ∀ v : S →ᵇ ℝ, ⇑(T₁ v) ≤ ⇑(T₂ v)) (s : S) :
    h₁.valueFunction hβ₁ s ≤ h₂.valueFunction hβ₂ s := by
  have hiter : ∀ n : ℕ, ⇑(T₁^[n] (0 : S →ᵇ ℝ)) ≤ ⇑(T₂^[n] (0 : S →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact le_trans (hle _) (h₂.monotone ih)
  have hl₁ := h₁.tendsto_iterate_valueFunction hβ₁ (0 : S →ᵇ ℝ)
  have hl₂ := h₂.tendsto_iterate_valueFunction hβ₂ (0 : S →ᵇ ℝ)
  have hp₁ : Filter.Tendsto (fun n => T₁^[n] (0 : S →ᵇ ℝ) s) Filter.atTop
      (𝓝 (h₁.valueFunction hβ₁ s)) :=
    ((BoundedContinuousFunction.evalCLM ℝ s).continuous.tendsto _).comp hl₁
  have hp₂ : Filter.Tendsto (fun n => T₂^[n] (0 : S →ᵇ ℝ) s) Filter.atTop
      (𝓝 (h₂.valueFunction hβ₂ s)) :=
    ((BoundedContinuousFunction.evalCLM ℝ s).continuous.tendsto _).comp hl₂
  exact le_of_tendsto_of_tendsto hp₁ hp₂ (Filter.Eventually.of_forall fun n => hiter n s)

/-! ### Monotonicity of the value function

If the operator preserves monotone functions then so does its fixed point, because the
monotone functions are a *closed* subset of `S →ᵇ ℝ` and value function iteration converges
in norm. Nothing about the fixed point itself is needed, only that the property is closed
and preserved. This is the standard route to comparative statics. -/

section Monotone

variable [Preorder S]

/-- The monotone bounded continuous functions form a closed set: a supremum-norm limit of
monotone functions is monotone, since evaluation at a point is continuous. -/
theorem isClosed_monotone : IsClosed {v : S →ᵇ ℝ | Monotone ⇑v} := by
  have heq : {v : S →ᵇ ℝ | Monotone ⇑v}
      = ⋂ (x : S) (y : S) (_ : x ≤ y), {v : S →ᵇ ℝ | v x ≤ v y} := by
    ext v; simp [Monotone]
  rw [heq]
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ => ?_
  exact isClosed_le (BoundedContinuousFunction.lipschitz_eval_const x).continuous
    (BoundedContinuousFunction.lipschitz_eval_const y).continuous

/-- **The value function is monotone** whenever the operator preserves monotonicity. -/
theorem Blackwell.monotone_valueFunction {β : ℝ≥0} {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)}
    (h : Blackwell β T) (hβ : β < 1)
    (hT : ∀ v : S →ᵇ ℝ, Monotone ⇑v → Monotone ⇑(T v)) :
    Monotone ⇑(h.valueFunction hβ) := by
  have hiter : ∀ n : ℕ, Monotone ⇑(T^[n] (0 : S →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => intro x y _; simp
    | succ k ih => rw [Function.iterate_succ_apply']; exact hT _ ih
  exact isClosed_monotone.mem_of_tendsto (h.tendsto_iterate_valueFunction hβ 0)
    (Filter.Eventually.of_forall hiter)

end Monotone

/-! ### Concavity of the value function

The same closed-set argument as for monotonicity, and the reason it is wanted is the agent
distribution. Defining a distribution over states needs the optimal policy to be a
*function*, and `exists_optimal_action` only gives existence of a maximiser. Uniqueness
comes from strict concavity of the objective in the action, which needs the continuation
value to be concave -- that is, the value function. So this is the first link in the chain
from the value function to the stationary distribution. -/

section Concave

variable {S : Type*} [TopologicalSpace S] [AddCommMonoid S] [Module ℝ S]

/-- The functions concave on a fixed convex set form a closed set.

Stated on a set rather than the whole space deliberately. The household models clamp assets
with `max 0 a`, which is convex and so breaks concavity globally -- but `max 0 a = a` on
`[0, ā]`, so concavity does hold on the compact convex region the economics lives in, and
that is the region the agent distribution will be supported on. -/
theorem isClosed_concaveOn {s : Set S} (hs : Convex ℝ s) :
    IsClosed {v : S →ᵇ ℝ | ConcaveOn ℝ s ⇑v} := by
  have heq : {v : S →ᵇ ℝ | ConcaveOn ℝ s ⇑v}
      = ⋂ (p : S × S × ℝ × ℝ) (_ : p.1 ∈ s ∧ p.2.1 ∈ s ∧ 0 ≤ p.2.2.1 ∧ 0 ≤ p.2.2.2 ∧
            p.2.2.1 + p.2.2.2 = 1),
          {v : S →ᵇ ℝ | p.2.2.1 • v p.1 + p.2.2.2 • v p.2.1
            ≤ v (p.2.2.1 • p.1 + p.2.2.2 • p.2.1)} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · rintro ⟨-, hv⟩ p ⟨hx, hy, ha, hb, hab⟩
      exact hv hx hy ha hb hab
    · intro hv
      exact ⟨hs, fun x hx y hy a b ha hb hab => hv (x, y, a, b) ⟨hx, hy, ha, hb, hab⟩⟩
  rw [heq]
  refine isClosed_iInter fun p => isClosed_iInter fun _ => ?_
  exact isClosed_le
    ((((BoundedContinuousFunction.lipschitz_eval_const p.1).continuous).const_smul p.2.2.1).add
      (((BoundedContinuousFunction.lipschitz_eval_const p.2.1).continuous).const_smul p.2.2.2))
    (BoundedContinuousFunction.lipschitz_eval_const
      (p.2.2.1 • p.1 + p.2.2.2 • p.2.1)).continuous

/-- **The value function is concave on `s`** whenever the operator preserves concavity
on `s`. -/
theorem Blackwell.concaveOn_valueFunction {β : ℝ≥0} {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)} {s : Set S}
    (hs : Convex ℝ s) (h : Blackwell β T) (hβ : β < 1)
    (hT : ∀ v : S →ᵇ ℝ, ConcaveOn ℝ s ⇑v → ConcaveOn ℝ s ⇑(T v)) :
    ConcaveOn ℝ s ⇑(h.valueFunction hβ) := by
  have hiter : ∀ n : ℕ, ConcaveOn ℝ s ⇑(T^[n] (0 : S →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact ⟨hs, fun x _ y _ a b _ _ _ => by simp⟩
    | succ k ih => rw [Function.iterate_succ_apply']; exact hT _ ih
  exact (isClosed_concaveOn hs).mem_of_tendsto (h.tendsto_iterate_valueFunction hβ 0)
    (Filter.Eventually.of_forall hiter)

end Concave

/-! ### Concavity along slices

A stochastic household's state is a pair `(assets, income state)`, and that is not a module
over `ℝ` -- there is no sensible convex combination of income states. So concavity cannot be
stated on the state space itself. What is wanted, and what is true, is concavity in assets
for each fixed income state, which is concavity along a family of slices. It is still a
closed condition, so the same argument applies. -/

section ConcaveSlice

variable {ι : Type*} {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- Concavity along every slice is a closed condition. -/
theorem isClosed_forall_concaveOn {s : Set E} (hs : Convex ℝ s) (g : ι → E → S) :
    IsClosed {v : S →ᵇ ℝ | ∀ i, ConcaveOn ℝ s fun e => v (g i e)} := by
  have heq : {v : S →ᵇ ℝ | ∀ i, ConcaveOn ℝ s fun e => v (g i e)}
      = ⋂ (p : ι × E × E × ℝ × ℝ)
          (_ : p.2.1 ∈ s ∧ p.2.2.1 ∈ s ∧ 0 ≤ p.2.2.2.1 ∧ 0 ≤ p.2.2.2.2 ∧
            p.2.2.2.1 + p.2.2.2.2 = 1),
          {v : S →ᵇ ℝ | p.2.2.2.1 • v (g p.1 p.2.1) + p.2.2.2.2 • v (g p.1 p.2.2.1)
            ≤ v (g p.1 (p.2.2.2.1 • p.2.1 + p.2.2.2.2 • p.2.2.1))} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hv p ⟨hx, hy, ha, hb, hab⟩
      exact (hv p.1).2 hx hy ha hb hab
    · intro hv i
      exact ⟨hs, fun x hx y hy a b ha hb hab => hv (i, x, y, a, b) ⟨hx, hy, ha, hb, hab⟩⟩
  rw [heq]
  refine isClosed_iInter fun p => isClosed_iInter fun _ => ?_
  exact isClosed_le
    (((BoundedContinuousFunction.lipschitz_eval_const
          (g p.1 p.2.1)).continuous.const_smul p.2.2.2.1).add
      ((BoundedContinuousFunction.lipschitz_eval_const
          (g p.1 p.2.2.1)).continuous.const_smul p.2.2.2.2))
    (BoundedContinuousFunction.lipschitz_eval_const
      (g p.1 (p.2.2.2.1 • p.2.1 + p.2.2.2.2 • p.2.2.1))).continuous

/-- **The value function is concave along every slice** whenever the operator preserves
that. -/
theorem Blackwell.forall_concaveOn_valueFunction {β : ℝ≥0} {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)}
    {s : Set E} (hs : Convex ℝ s) (g : ι → E → S) (h : Blackwell β T) (hβ : β < 1)
    (hT : ∀ v : S →ᵇ ℝ, (∀ i, ConcaveOn ℝ s fun e => v (g i e)) →
      ∀ i, ConcaveOn ℝ s fun e => (T v) (g i e)) :
    ∀ i, ConcaveOn ℝ s fun e => (h.valueFunction hβ) (g i e) := by
  have hiter : ∀ n : ℕ, ∀ i, ConcaveOn ℝ s fun e => (T^[n] (0 : S →ᵇ ℝ)) (g i e) := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨hs, fun x _ y _ a b _ _ _ => by simp⟩
    | succ k ih => rw [Function.iterate_succ_apply']; exact hT _ ih
  exact (isClosed_forall_concaveOn hs g).mem_of_tendsto (h.tendsto_iterate_valueFunction hβ 0)
    (Filter.Eventually.of_forall hiter)

end ConcaveSlice

section Lipschitz

/-!
### Lipschitz value functions

The third closed class, after monotone and concave. A value function that is Lipschitz in one
coordinate is what lets a marginal argument run without derivatives: it bounds the marginal
value of that coordinate uniformly, which is what a corner condition needs.

As with concavity, the property is stated along a family of slices `g i`, since the state
space need not be a metric space in the coordinate of interest.
-/

variable {S : Type*} [TopologicalSpace S] {ι : Type*}

theorem isClosed_forall_lipschitzOn (t : Set ℝ) (L : ℝ) (g : ι → ℝ → S) :
    IsClosed {v : S →ᵇ ℝ | ∀ i, ∀ x ∈ t, ∀ y ∈ t, |v (g i x) - v (g i y)| ≤ L * |x - y|} := by
  have heq : {v : S →ᵇ ℝ | ∀ i, ∀ x ∈ t, ∀ y ∈ t, |v (g i x) - v (g i y)| ≤ L * |x - y|}
      = ⋂ (p : ι × ℝ × ℝ) (_ : p.2.1 ∈ t ∧ p.2.2 ∈ t),
          {v : S →ᵇ ℝ | |v (g p.1 p.2.1) - v (g p.1 p.2.2)| ≤ L * |p.2.1 - p.2.2|} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun hv p hp => hv p.1 p.2.1 hp.1 p.2.2 hp.2, fun hv i x hx y hy => hv (i, x, y) ⟨hx, hy⟩⟩
  rw [heq]
  refine isClosed_iInter fun p => isClosed_iInter fun _ => ?_
  exact isClosed_le
    (((BoundedContinuousFunction.lipschitz_eval_const (g p.1 p.2.1)).continuous.sub
      (BoundedContinuousFunction.lipschitz_eval_const (g p.1 p.2.2)).continuous).abs)
    continuous_const

/-- **The value function is Lipschitz along the slices** whenever the operator preserves that
property. The nonnegativity of `L` is what makes the zero function a valid starting point for
the iteration. -/
theorem Blackwell.forall_lipschitzOn_valueFunction {β : ℝ≥0} {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)}
    (h : Blackwell β T) (hβ : β < 1) {t : Set ℝ} {L : ℝ} (hL : 0 ≤ L) {g : ι → ℝ → S}
    (hT : ∀ v : S →ᵇ ℝ,
      (∀ i, ∀ x ∈ t, ∀ y ∈ t, |v (g i x) - v (g i y)| ≤ L * |x - y|) →
      ∀ i, ∀ x ∈ t, ∀ y ∈ t, |T v (g i x) - T v (g i y)| ≤ L * |x - y|) :
    ∀ i, ∀ x ∈ t, ∀ y ∈ t,
      |h.valueFunction hβ (g i x) - h.valueFunction hβ (g i y)| ≤ L * |x - y| := by
  have hiter : ∀ n : ℕ, ∀ i, ∀ x ∈ t, ∀ y ∈ t,
      |(T^[n] (0 : S →ᵇ ℝ)) (g i x) - (T^[n] (0 : S →ᵇ ℝ)) (g i y)| ≤ L * |x - y| := by
    intro n
    induction n with
    | zero =>
        intro i x _ y _
        simpa using mul_nonneg hL (abs_nonneg _)
    | succ k ih => rw [Function.iterate_succ_apply']; exact hT _ ih
  exact isClosed_forall_lipschitzOn t L g |>.mem_of_tendsto
    (h.tendsto_iterate_valueFunction hβ 0) (Filter.Eventually.of_forall hiter)

end Lipschitz

section IncreasingDifferences

/-!
### Increasing differences

The fourth closed class, after monotone, concave and Lipschitz.

A function of two real coordinates has increasing differences when raising the second
coordinate raises the increment in the first. For a value function whose coordinates are
assets and the interest rate, that says the marginal value of wealth rises with the rate --
and that is the derivative-free form of the condition driving Light (2018) Theorem 1, where
it appears as `f'(·, R₂) ≥ f'(·, R₁)` and is obtained from the envelope theorem.

Stating it as increments rather than derivatives is what makes it expressible here at all,
since nothing in this development differentiates anything. Its natural home is the augmented
programme of `Models/IncomeFluctuationAugmented.lean`, where the rate is a state coordinate,
so the property is about a single function rather than a family.

Whether the Bellman operator preserves it is a separate question and is NOT settled here;
Light's argument for the derivative version compares different asset levels across rates via
a rescaling, so it does not transcribe.
-/

variable {S : Type*} [TopologicalSpace S] {ι : Type*}

theorem isClosed_forall_increasingDifferences (s t : Set ℝ) (g : ι → ℝ → ℝ → S) :
    IsClosed {v : S →ᵇ ℝ | ∀ i, ∀ a₁ ∈ s, ∀ a₂ ∈ s, ∀ r₁ ∈ t, ∀ r₂ ∈ t, a₁ ≤ a₂ → r₁ ≤ r₂ →
      v (g i a₂ r₁) - v (g i a₁ r₁) ≤ v (g i a₂ r₂) - v (g i a₁ r₂)} := by
  have heq : {v : S →ᵇ ℝ | ∀ i, ∀ a₁ ∈ s, ∀ a₂ ∈ s, ∀ r₁ ∈ t, ∀ r₂ ∈ t, a₁ ≤ a₂ → r₁ ≤ r₂ →
        v (g i a₂ r₁) - v (g i a₁ r₁) ≤ v (g i a₂ r₂) - v (g i a₁ r₂)}
      = ⋂ (p : ι × ℝ × ℝ × ℝ × ℝ)
          (_ : p.2.1 ∈ s ∧ p.2.2.1 ∈ s ∧ p.2.2.2.1 ∈ t ∧ p.2.2.2.2 ∈ t ∧
            p.2.1 ≤ p.2.2.1 ∧ p.2.2.2.1 ≤ p.2.2.2.2),
          {v : S →ᵇ ℝ |
            v (g p.1 p.2.2.1 p.2.2.2.1) - v (g p.1 p.2.1 p.2.2.2.1)
              ≤ v (g p.1 p.2.2.1 p.2.2.2.2) - v (g p.1 p.2.1 p.2.2.2.2)} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun hv p hp => hv p.1 p.2.1 hp.1 p.2.2.1 hp.2.1 p.2.2.2.1 hp.2.2.1 p.2.2.2.2 hp.2.2.2.1
        hp.2.2.2.2.1 hp.2.2.2.2.2,
      fun hv i a₁ h1 a₂ h2 r₁ h3 r₂ h4 h5 h6 => hv (i, a₁, a₂, r₁, r₂) ⟨h1, h2, h3, h4, h5, h6⟩⟩
  rw [heq]
  refine isClosed_iInter fun p => isClosed_iInter fun _ => ?_
  exact isClosed_le
    ((BoundedContinuousFunction.lipschitz_eval_const _).continuous.sub
      (BoundedContinuousFunction.lipschitz_eval_const _).continuous)
    ((BoundedContinuousFunction.lipschitz_eval_const _).continuous.sub
      (BoundedContinuousFunction.lipschitz_eval_const _).continuous)

/-- **The value function has increasing differences** whenever the operator preserves the
property. The zero function has it trivially, which is what lets the iteration start. -/
theorem Blackwell.forall_increasingDifferences_valueFunction {β : ℝ≥0}
    {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)} (h : Blackwell β T) (hβ : β < 1) {s t : Set ℝ} {g : ι → ℝ → ℝ → S}
    (hT : ∀ v : S →ᵇ ℝ,
      (∀ i, ∀ a₁ ∈ s, ∀ a₂ ∈ s, ∀ r₁ ∈ t, ∀ r₂ ∈ t, a₁ ≤ a₂ → r₁ ≤ r₂ →
        v (g i a₂ r₁) - v (g i a₁ r₁) ≤ v (g i a₂ r₂) - v (g i a₁ r₂)) →
      ∀ i, ∀ a₁ ∈ s, ∀ a₂ ∈ s, ∀ r₁ ∈ t, ∀ r₂ ∈ t, a₁ ≤ a₂ → r₁ ≤ r₂ →
        T v (g i a₂ r₁) - T v (g i a₁ r₁) ≤ T v (g i a₂ r₂) - T v (g i a₁ r₂)) :
    ∀ i, ∀ a₁ ∈ s, ∀ a₂ ∈ s, ∀ r₁ ∈ t, ∀ r₂ ∈ t, a₁ ≤ a₂ → r₁ ≤ r₂ →
      h.valueFunction hβ (g i a₂ r₁) - h.valueFunction hβ (g i a₁ r₁)
        ≤ h.valueFunction hβ (g i a₂ r₂) - h.valueFunction hβ (g i a₁ r₂) := by
  have hiter : ∀ n : ℕ, ∀ i, ∀ a₁ ∈ s, ∀ a₂ ∈ s, ∀ r₁ ∈ t, ∀ r₂ ∈ t, a₁ ≤ a₂ → r₁ ≤ r₂ →
      (T^[n] (0 : S →ᵇ ℝ)) (g i a₂ r₁) - (T^[n] (0 : S →ᵇ ℝ)) (g i a₁ r₁)
        ≤ (T^[n] (0 : S →ᵇ ℝ)) (g i a₂ r₂) - (T^[n] (0 : S →ᵇ ℝ)) (g i a₁ r₂) := by
    intro n
    induction n with
    | zero => intro i a₁ _ a₂ _ r₁ _ r₂ _ _ _; simp
    | succ k ih => rw [Function.iterate_succ_apply']; exact hT _ ih
  exact isClosed_forall_increasingDifferences s t g |>.mem_of_tendsto
    (h.tendsto_iterate_valueFunction hβ 0) (Filter.Eventually.of_forall hiter)

end IncreasingDifferences

end LeanEconomics
