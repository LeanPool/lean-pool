/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.BellmanGeometricExactRuntime
public import LeanPool.ECRuntime.OneMaxRLSHarmonicStep
public import LeanPool.ECRuntime.RLSFiniteSurvivalCouponBound
public import LeanPool.ECRuntime.StrictMonotoneRLSKernelSupport

/-!
Exact one-bit RLS runtime for strictly coordinate-monotone Boolean
landscapes. The singleton kernel bridge reduces the Bellman certificate
and survival estimate to OneMax.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
namespace ECRuntime

/-- Strict coordinatewise monotonicity identifies RLS with OneMax RLS. -/
theorem candidateStrictMonotoneRLS_transition_eq_oneMax
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness) :
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness =
      (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal := by
  exact support_strictMonotoneRLS_transition_eq_oneMax hn fitness hf

/-- Reduction of the monotone-function runtime question to OneMax RLS.
The reduction is independent of the subsequent harmonic expectation calculation. -/
private theorem candidateStrictMonotoneRLS_runtimeSup_reduce_to_oneMax
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (x : BitString n) :
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      ({allOnes n} : Set (BitString n)) x =
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      ({allOnes n} : Set (BitString n)) x := by
  rw [candidateStrictMonotoneRLS_transition_eq_oneMax hn fitness hf]

/-- A strictly coordinate-monotone RLS chain inherits the exact
OneMax harmonic Bellman identity, independently of its fitness magnitudes. -/
private theorem stage119_strictMonotone_harmonic_one_step
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (x : BitString n) :
    expectedValueAfter
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      (fun y : BitString n => (n : Real) * harmonicReal (zeroCount y)) x =
      if zeroCount x = 0 then 0 else
        (n : Real) * harmonicReal (zeroCount x) - 1 := by
  rw [candidateStrictMonotoneRLS_transition_eq_oneMax hn fitness hf]
  exact proposed_oneMaxRLS_harmonic_one_step hn x

/-- Exact coupon-collector expectation for the broader monotone class. -/
theorem candidateStrictMonotoneRLS_runtimeSup_eq_harmonic
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (x : BitString n) :
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      ({allOnes n} : Set (BitString n)) x =
      ENNReal.ofReal ((n : Real) * harmonicReal (zeroCount x)) := by
  classical
  let law := StaticUnaryUnbiasedMutation.uniformOneBitLaw hn
  let P : TransitionMatrix (BitString n) := law.transition fitness
  let R : BitString n → Real :=
    fun y => (n : Real) * harmonicReal (zeroCount y)
  have hnpos : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hq0 : 0 ≤ (1 : Real) - 1 / (n : Real) := by
    have hnge : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
    have hdiv : (1 : Real) / (n : Real) ≤ 1 :=
      (div_le_iff₀ hnpos).mpr (by linarith)
    linarith
  have hq1 : (1 : Real) - 1 / (n : Real) < 1 := by
    have hdiv : 0 < (1 : Real) / (n : Real) := by positivity
    linarith
  have hP : IsStochastic P := law.transition_stochastic fitness
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
    have hz : zeroCount y ≠ 0 := by
      intro hzero
      exact hyne ((zeroCount_eq_zero_iff_allOnes y).mp hzero)
    have h := stage119_strictMonotone_harmonic_one_step hn fitness hf y
    simp only [ite_eq_right hz] at h
    change expectedValueAfter P R y = R y - 1 at h
    linarith
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
        candidateStrictMonotoneRLS_transition_eq_oneMax hn fitness hf,
        ← oneMaxTarget_eq_singleton n] using hone
    exact htransfer.trans hmult
  change runtimeSup P ({allOnes n} : Set (BitString n)) x =
    ENNReal.ofReal (R x)
  exact candidate_geometricBellman_runtime_eq P
    ({allOnes n} : Set (BitString n)) hP R
    hRnonneg hRzero hRbellman
    ((n : Real) * harmonicReal n) (n : Real)
    (1 - 1 / (n : Real)) hRbound
    (Nat.cast_nonneg n) hq0 hq1 hsurvival x

end ECRuntime
