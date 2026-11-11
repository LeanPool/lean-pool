/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.BellmanGeometricExactRuntime
public import LeanPool.ECRuntime.FitnessLevel
public import LeanPool.ECRuntime.LinearPotential
public import LeanPool.ECRuntime.OneMaxUnaryHarmonic
public import LeanPool.ECRuntime.RLSFiniteSurvivalCouponBound
public import LeanPool.ECRuntime.RLSOneBitSupport
public import LeanPool.ECRuntime.UniformOneBitMutation
public import LeanPool.ECRuntime.UnrestrictedRuntime

/-!
Exact coupon-collector expectations for one-bit RLS on positive linear
objectives. Singleton acceptance depends only on the sign of its coordinate
weight, so no sorting or reordering assumption on the weights is required.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ECRuntime

/-- Exact transition-level reduction of the full expected RLS runtime to
OneMax. The remaining hard task is the OneMax coupon-collector identity. -/
private theorem candidate_rlsLinear_runtimeSup_reduce_to_oneMax
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (x : BitString n) :
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w)) ({allOnes n} : Set (BitString n)) x =
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        oneMaxReal) ({allOnes n} : Set (BitString n)) x := by
  rw [candidate_rls_linear_transition_eq_oneMax hn w hw]

/-- Existing harmonic bounds prove that RLS on a positive linear objective
hits the all-one optimum in finite expected time. Thus the remaining gap in
the *exact* coupon-collector theorem is Bellman uniqueness, not integrability. -/
private theorem candidate_rlsLinear_runtimeSup_ne_top
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (x : BitString n) :
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w)) ({allOnes n} : Set (BitString n)) x ≠ ⊤ := by
  let law := StaticUnaryUnbiasedMutation.uniformOneBitLaw hn
  have hp : 0 < law.oneBitMass := by
    change 0 < (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).oneBitMass
    rw [StaticUnaryUnbiasedMutation.uniformOneBitLaw_oneBitMass hn]
    norm_num
  have hbound := StaticUnaryUnbiasedMutation.oneMaxUnary_runtimeSup_le_harmonic
    law hn hp x
  have htarget : oneMaxTarget n = ({allOnes n} : Set (BitString n)) :=
    oneMaxTarget_eq_singleton n
  have hcongr := runtimeSup_congr_target (law.transition oneMaxReal)
    (oneMaxTarget n) ({allOnes n} : Set (BitString n)) htarget x
  rw [candidate_rls_linear_transition_eq_oneMax hn w hw]
  change runtimeSup (law.transition oneMaxReal) ({allOnes n} : Set (BitString n)) x ≠ ⊤
  rw [← hcongr]
  exact ne_top_of_le_ne_top (by simp) hbound

/-- Bellman equality of the proposed coupon-collector runtime certificate.
This has equality (not only super-solution inequality). -/
theorem rlsLinear_harmonic_bellman
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w)
    (x : BitString n) :
    (if x = allOnes n then (0 : Real)
      else 1 + expectedValueAfter
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          (linearFitness w))
        (fun y : BitString n =>
          (n : Real) * harmonicReal (zeroCount y)) x) =
      (n : Real) * harmonicReal (zeroCount x) := by
  rw [candidate_rls_linear_transition_eq_oneMax hn w hw,
    candidate_rlsOneMax_harmonic_one_step hn x]
  by_cases hx : x = allOnes n
  · simp [hx]
  · have hz : zeroCount x ≠ 0 := by
      intro hzero
      exact hx ((zeroCount_eq_zero_iff_allOnes x).mp hzero)
    simp [hx, hz]

/-- Exact unrestricted expected number of RLS iterations to the optimum. -/
theorem rlsLinear_runtimeSup_eq_harmonic
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w)
    (x : BitString n) :
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w))
      ({allOnes n} : Set (BitString n)) x =
      ENNReal.ofReal ((n : Real) * harmonicReal (zeroCount x)) := by
  classical
  let law := StaticUnaryUnbiasedMutation.uniformOneBitLaw hn
  let P : TransitionMatrix (BitString n) := law.transition (linearFitness w)
  let R : BitString n → Real :=
    fun y => (n : Real) * harmonicReal (zeroCount y)
  have hnpos : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hnge : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hq0 : 0 ≤ (1 : Real) - 1 / (n : Real) := by
    have hdiv : (1 : Real) / (n : Real) ≤ 1 :=
      (div_le_iff₀ hnpos).mpr (by linarith)
    linarith
  have hq1 : (1 : Real) - 1 / (n : Real) < 1 := by
    have hdiv : 0 < (1 : Real) / (n : Real) := by positivity
    linarith
  have hP : IsStochastic P := by
    exact law.transition_stochastic (linearFitness w)
  have hRnonneg : ∀ y : BitString n, 0 ≤ R y := by
    intro y
    exact mul_nonneg (Nat.cast_nonneg _) (harmonicReal_nonneg _)
  have hRzero : ∀ y : BitString n,
      y ∈ ({allOnes n} : Set (BitString n)) → R y = 0 := by
    intro y hy
    have heq : y = allOnes n := by simpa using hy
    simp [R, heq, zeroCount_allOnes]
  have hRbellman : ∀ y : BitString n,
      y ∉ ({allOnes n} : Set (BitString n)) →
        R y = 1 + expectedValueAfter P R y := by
    intro y hy
    have hyne : y ≠ allOnes n := by simpa using hy
    have h := rlsLinear_harmonic_bellman hn w hw y
    simp only [ite_eq_right hyne] at h
    exact h.symm
  have hRbound : ∀ y : BitString n,
      R y ≤ (n : Real) * harmonicReal n := by
    intro y
    exact mul_le_mul_of_nonneg_left
      (harmonicReal_mono (zeroCount_le y)) (Nat.cast_nonneg n)
  have hsurvival : ∀ t : Nat, ∀ y : BitString n,
      finiteLevelSurvival P ({allOnes n} : Set (BitString n))ᶜ t y ≤
        (n : Real) * (1 - 1 / (n : Real)) ^ t := by
    intro t y
    have hone := proposed_rlsOneMax_finiteSurvival_couponBound hn y t
    have hnat : (zeroCount y : Real) ≤ (n : Real) := by
      exact_mod_cast zeroCount_le y
    have hmult :
        (zeroCount y : Real) * (1 - 1 / (n : Real)) ^ t ≤
          (n : Real) * (1 - 1 / (n : Real)) ^ t :=
      mul_le_mul_of_nonneg_right hnat (pow_nonneg hq0 _)
    have htransfer :
        finiteLevelSurvival P ({allOnes n} : Set (BitString n))ᶜ t y ≤
          (zeroCount y : Real) * (1 - 1 / (n : Real)) ^ t := by
      simpa only [P, law,
        candidate_rls_linear_transition_eq_oneMax hn w hw,
        ← oneMaxTarget_eq_singleton n] using hone
    exact htransfer.trans hmult
  change runtimeSup P ({allOnes n} : Set (BitString n)) x =
    ENNReal.ofReal (R x)
  exact proposed_exactRuntime_of_bellmanAndGeometricSurvival P
    ({allOnes n} : Set (BitString n)) hP R
    hRnonneg hRzero hRbellman
    ((n : Real) * harmonicReal n) (n : Real)
    (1 - 1 / (n : Real)) hRbound
    (Nat.cast_nonneg n) hq0 hq1 hsurvival x

end ECRuntime
