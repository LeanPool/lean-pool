/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.BellmanGeometricExactRuntime
public import LeanPool.ECRuntime.OneMaxRLSHarmonicStep
public import LeanPool.ECRuntime.RLSFiniteSurvivalCouponBound

/-!
# Exact OneMax RLS expectation

The harmonic Bellman certificate and geometric survival bound determine the
expected first-hitting time. Linear and strictly coordinate-monotone objectives
transfer this shared result through their equality with the OneMax kernel.

Extracted from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ECRuntime

/-- Exact expected number of one-bit OneMax RLS iterations from any initial string. -/
theorem oneMaxRLS_runtimeSup_eq_harmonic
    {n : Nat} (hn : 0 < n)
    (x : BitString n) :
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      ({allOnes n} : Set (BitString n)) x =
      ENNReal.ofReal ((n : Real) * harmonicReal (zeroCount x)) := by
  classical
  let law := StaticUnaryUnbiasedMutation.uniformOneBitLaw hn
  let P : TransitionMatrix (BitString n) := law.transition oneMaxReal
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
  have hP : IsStochastic P := law.transition_stochastic oneMaxReal
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
    have h := proposed_oneMaxRLS_harmonic_one_step hn y
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
