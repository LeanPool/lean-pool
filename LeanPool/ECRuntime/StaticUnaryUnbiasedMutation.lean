/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

public import LeanPool.ECRuntime.Transition

/-!
# Static Unary Unbiased Mutation

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/--
A static unary-unbiased mutation law on bit strings of dimension `n`.

The law is represented directly on mutation masks.  `card_invariant` is the finite
hypercube characterization of unary unbiasedness needed by the runtime development:
masks with the same Hamming radius have the same probability.  Together with
normalization this is equivalent to first choosing a radius and then choosing a mask of
that radius uniformly.
-/
structure StaticUnaryUnbiasedMutation (n : ℕ) where
  /-- Probability mass assigned to a mutation mask. -/
  weight : MutationMask n → ℝ
  weight_nonneg : ∀ mask, 0 ≤ weight mask
  weight_sum : (∑ mask : MutationMask n, weight mask) = 1
  card_invariant : ∀ {mask₁ mask₂ : MutationMask n},
    mask₁.card = mask₂.card → weight mask₁ = weight mask₂

namespace StaticUnaryUnbiasedMutation

/-- Probability mass assigned to mutation radius `k`. -/
def radiusMass {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (k : ℕ) : ℝ :=
  ∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), law.weight mask

/-- Every mutation-radius mass is nonnegative. -/
theorem radiusMass_nonneg {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (k : ℕ) :
    0 ≤ law.radiusMass k := by
  unfold radiusMass
  exact Finset.sum_nonneg (fun mask _hmask => law.weight_nonneg mask)

/-- Radii larger than the dimension carry no mass. -/
theorem radiusMass_eq_zero_of_lt {n k : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (hkn : n < k) :
    law.radiusMass k = 0 := by
  unfold radiusMass
  have hcard : (Finset.univ : Finset (Fin n)).card < k := by
    simpa using hkn
  rw [Finset.powersetCard_eq_empty.mpr hcard]
  simp

/-- The derived radius masses form a probability distribution on `0, ..., n`. -/
theorem sum_radiusMass_eq_one {n : ℕ} (law : StaticUnaryUnbiasedMutation n) :
    (∑ k ∈ Finset.range (n + 1), law.radiusMass k) = 1 := by
  have hdecomp :=
    Finset.sum_powerset (Finset.univ : Finset (Fin n)) law.weight
  have hsplit :
      (∑ k ∈ Finset.range (n + 1), law.radiusMass k) =
        ∑ mask : MutationMask n, law.weight mask := by
    simpa [radiusMass] using hdecomp.symm
  exact hsplit.trans law.weight_sum

/-- The principal runtime parameter: probability that the mutation flips exactly one bit. -/
def oneBitMass {n : ℕ} (law : StaticUnaryUnbiasedMutation n) : ℝ :=
  law.radiusMass 1

/-- The one-bit mutation mass is nonnegative. -/
theorem oneBitMass_nonneg {n : ℕ} (law : StaticUnaryUnbiasedMutation n) :
    0 ≤ law.oneBitMass := by
  exact law.radiusMass_nonneg 1

/--
All singleton masks have the same weight, and their aggregate weight is `n` times the
weight of any specified singleton.
-/
theorem oneBitMass_eq_n_mul_singleton {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (i : Fin n) :
    law.oneBitMass = (n : ℝ) * law.weight ({i} : MutationMask n) := by
  unfold oneBitMass radiusMass
  calc
    (∑ mask ∈ Finset.powersetCard 1 (Finset.univ : Finset (Fin n)), law.weight mask) =
        ∑ _mask ∈ Finset.powersetCard 1 (Finset.univ : Finset (Fin n)),
          law.weight ({i} : MutationMask n) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      have hcard : mask.card = 1 := (Finset.mem_powersetCard.mp hmask).2
      have hsingleton : ({i} : MutationMask n).card = 1 := by simp
      exact law.card_invariant (hcard.trans hsingleton.symm)
    _ = ((Finset.powersetCard 1 (Finset.univ : Finset (Fin n))).card : ℝ) *
        law.weight ({i} : MutationMask n) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (n : ℝ) * law.weight ({i} : MutationMask n) := by
      simp

/-- In positive dimension, a specified one-bit flip has probability `p₁ / n`. -/
theorem singletonWeight_eq_oneBitMass_div {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n) (i : Fin n) :
    law.weight ({i} : MutationMask n) = law.oneBitMass / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  apply (eq_div_iff hn0).2
  simpa [mul_comm] using (law.oneBitMass_eq_n_mul_singleton i).symm

/-- Expected Hamming radius of one mutation, corresponding to the literature parameter `χ`. -/
def meanRadius {n : ℕ} (law : StaticUnaryUnbiasedMutation n) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (k : ℝ) * law.radiusMass k

/-- The expected mutation radius is nonnegative. -/
theorem meanRadius_nonneg {n : ℕ} (law : StaticUnaryUnbiasedMutation n) :
    0 ≤ law.meanRadius := by
  unfold meanRadius
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (Nat.cast_nonneg k) (law.radiusMass_nonneg k)

/--
Aggregate weight of the elementary improving events that flip one currently-zero bit
and no other coordinate.
-/
def singleZeroFlipWeight {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (x : BitString n) : ℝ :=
  ∑ i ∈ zeroPositions x, law.weight ({i} : MutationMask n)

/--
For a static unary-unbiased mutation law, the elementary one-bit improvement mass is
exactly `zeroCount(x) * p₁ / n`.
-/
theorem singleZeroFlipWeight_eq {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n) (x : BitString n) :
    law.singleZeroFlipWeight x =
      (zeroCount x : ℝ) * (law.oneBitMass / (n : ℝ)) := by
  unfold singleZeroFlipWeight
  simp_rw [law.singletonWeight_eq_oneBitMass_div hn]
  rw [Finset.sum_const, nsmul_eq_mul, zeroPositions_card]

/-- Independent bit mutation is a static unary-unbiased mutation law. -/
def independentBitLaw {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    StaticUnaryUnbiasedMutation n where
  weight := mutationMaskWeight p
  weight_nonneg := mutationMaskWeight_nonneg hp0 hp1
  weight_sum := mutationMaskWeight_sum n p
  card_invariant := by
    intro mask₁ mask₂ hcard
    unfold mutationMaskWeight
    rw [hcard]

/-- The one-bit mass of independent bit mutation is `n p (1-p)^(n-1)`. -/
theorem independentBitLaw_oneBitMass {n : ℕ} (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (independentBitLaw (n := n) p hp0 hp1).oneBitMass =
      (n : ℝ) * (p * (1 - p) ^ (n - 1)) := by
  unfold oneBitMass radiusMass independentBitLaw
  calc
    (∑ mask ∈ Finset.powersetCard 1 (Finset.univ : Finset (Fin n)),
        mutationMaskWeight p mask) =
        ∑ _mask ∈ Finset.powersetCard 1 (Finset.univ : Finset (Fin n)),
          p * (1 - p) ^ (n - 1) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      have hcard : mask.card = 1 := (Finset.mem_powersetCard.mp hmask).2
      simp [mutationMaskWeight, hcard]
    _ = ((Finset.powersetCard 1 (Finset.univ : Finset (Fin n))).card : ℝ) *
        (p * (1 - p) ^ (n - 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (n : ℝ) * (p * (1 - p) ^ (n - 1)) := by
      simp

/-- Elitist `(1+1)` transition induced by a static unary-unbiased mutation law. -/
noncomputable def transition {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (fitness : BitString n → ℝ) :
    TransitionMatrix (BitString n) :=
  finiteRandomTransition
    (fun _parent mask => law.weight mask)
    (selectedAfterMask fitness)

/-- Independent bit mutation induces exactly the existing `(1+1)`-EA transition. -/
theorem independentBitLaw_transition_eq_onePlusOneTransition {n : ℕ}
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (fitness : BitString n → ℝ) :
    (independentBitLaw p hp0 hp1).transition fitness =
      onePlusOneTransition p fitness := by
  rw [onePlusOneTransition_eq_finiteRandomTransition]
  rfl

/-- The static unary-unbiased transition is stochastic. -/
theorem transition_stochastic {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (fitness : BitString n → ℝ) :
    IsStochastic (law.transition fitness) := by
  unfold transition
  apply finiteRandomTransition_stochastic
  · intro parent mask
    exact law.weight_nonneg mask
  · intro parent
    exact law.weight_sum

end StaticUnaryUnbiasedMutation

end ECRuntime
