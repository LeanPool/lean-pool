/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RLSLinearExact
public import LeanPool.ECRuntime.RLSRandomStart

/-!
The uniform-start mean number of one-bit RLS mutation iterations on a
positive linear objective. The statewise harmonic expectation is combined
with the exact binomial distribution of the initial zero count.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/-- Uniform-start exact RLS expected runtime, averaged over all `2^n`
bitstrings and expressed as a binomial harmonic sum. -/
theorem proposed_rlsLinear_uniformInitial_runtimeAverage
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal) /
        (2 : Real) ^ n =
      ((n : Real) / (2 : Real) ^ n) *
        (Finset.sum (Finset.range (n + 1))
          (fun k => (Nat.choose n k : Real) * harmonicReal k))) := by
  classical
  have hsum :
      (Finset.univ.sum (fun x : BitString n =>
          (runtimeSup
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
              (linearFitness w))
            ({allOnes n} : Set (BitString n)) x).toReal)) =
        Finset.univ.sum (fun x : BitString n =>
          (n : Real) * harmonicReal (zeroCount x)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [rlsLinear_runtimeSup_eq_harmonic hn w hw x]
    exact ENNReal.toReal_ofReal
      (mul_nonneg (Nat.cast_nonneg n) (harmonicReal_nonneg (zeroCount x)))
  rw [hsum]
  exact rlsLinear_uniformInitial_harmonic_average n

end ECRuntime
