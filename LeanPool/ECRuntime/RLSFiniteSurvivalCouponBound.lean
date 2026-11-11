/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.LevelExitTail
public import LeanPool.ECRuntime.OneMax
public import LeanPool.ECRuntime.RLSZeroCountOneStep
public import LeanPool.ECRuntime.UniformOneBitMutation

/-!
A finite-budget survival bound for one-bit elitist OneMax RLS.
The proof inducts on the exact one-step zero-count contraction; it does
not assume that the different coordinates evolve independently.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/-- Starting with `k` zero bits, the probability that RLS has not optimized
OneMax by step `t` is at most `k(1-1/n)^t`. -/
theorem proposed_rlsOneMax_finiteSurvival_couponBound
    {n : Nat} (hn : 0 < n) (x : BitString n) (t : Nat) :
    finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      (oneMaxTarget n)ᶜ t x ≤
    (zeroCount x : Real) * (1 - 1 / (n : Real)) ^ t := by
  classical
  let P : TransitionMatrix (BitString n) :=
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal
  let q : Real := 1 - 1 / (n : Real)
  have hP : IsStochastic P :=
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition_stochastic oneMaxReal
  have hnreal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hone : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hq : 0 ≤ q := by
    have hdiv : 1 / (n : Real) ≤ 1 :=
      (div_le_iff₀ hnreal).2 (by linarith)
    dsimp [q]
    linarith
  have hstep (y : BitString n) :
      expectedValueAfter P (fun z : BitString n => (zeroCount z : Real)) y =
        q * (zeroCount y : Real) := by
    exact proposed_rlsOneMax_expectedZeroCount_oneStep hn y
  have hall : ∀ s (y : BitString n),
      finiteLevelSurvival P (oneMaxTarget n)ᶜ s y ≤
        (zeroCount y : Real) * q ^ s := by
    intro s
    induction s with
    | zero =>
        intro y
        by_cases hy : y ∈ (oneMaxTarget n)ᶜ
        · have hyne : y ≠ allOnes n := by
            intro heq
            apply hy
            rw [heq]
            exact allOnes_mem_oneMaxTarget n
          have hzero : 0 < zeroCount y := by
            by_contra hz
            have hz0 : zeroCount y = 0 := by omega
            exact hyne ((zeroCount_eq_zero_iff_allOnes y).mp hz0)
          have hnat : 1 ≤ zeroCount y := by omega
          have hreal : (1 : Real) ≤ (zeroCount y : Real) := by
            exact_mod_cast hnat
          rw [finiteLevelSurvival_zero_of_mem P (oneMaxTarget n)ᶜ y hy]
          simpa only [pow_zero, mul_one] using hreal
        · rw [finiteLevelSurvival_zero_of_not_mem P (oneMaxTarget n)ᶜ y hy]
          simpa only [pow_zero, mul_one] using
            (Nat.cast_nonneg (zeroCount y) : (0 : Real) ≤ _)
    | succ s ih =>
        intro y
        by_cases hy : y ∈ (oneMaxTarget n)ᶜ
        · rw [finiteLevelSurvival_succ_of_mem P (oneMaxTarget n)ᶜ s y hy]
          have hmono := expectedValueAfter_mono P hP
            (finiteLevelSurvival P (oneMaxTarget n)ᶜ s)
            (fun z : BitString n => (zeroCount z : Real) * q ^ s)
            (fun z => ih z) y
          have hfactor :
              expectedValueAfter P
                (fun z : BitString n => (zeroCount z : Real) * q ^ s) y =
              q ^ s * expectedValueAfter P
                (fun z : BitString n => (zeroCount z : Real)) y := by
            unfold expectedValueAfter
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            ring
          calc
            (∑ z, P y z * finiteLevelSurvival P (oneMaxTarget n)ᶜ s z) =
                expectedValueAfter P
                  (finiteLevelSurvival P (oneMaxTarget n)ᶜ s) y := rfl
            _ ≤ expectedValueAfter P
                  (fun z : BitString n => (zeroCount z : Real) * q ^ s) y := hmono
            _ = q ^ s * expectedValueAfter P
                  (fun z : BitString n => (zeroCount z : Real)) y := hfactor
            _ = q ^ s * (q * (zeroCount y : Real)) := by rw [hstep]
            _ = (zeroCount y : Real) * q ^ (s + 1) := by rw [pow_succ]; ring
        · rw [finiteLevelSurvival_succ_of_not_mem P (oneMaxTarget n)ᶜ s y hy]
          exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _)
  change finiteLevelSurvival P (oneMaxTarget n)ᶜ t x ≤
    (zeroCount x : Real) * q ^ t
  exact hall t x

end ECRuntime
