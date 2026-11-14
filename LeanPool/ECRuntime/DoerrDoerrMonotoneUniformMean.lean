/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.BinomialHarmonicAverageClosedForm
public import LeanPool.ECRuntime.RLSRandomStart
public import LeanPool.ECRuntime.StrictMonotoneRLS

/-!
Uniform-start one-bit RLS on strictly coordinate-monotone functions.
The exact statewise harmonic expectation is averaged over all Boolean strings
and evaluated using the binomial-harmonic transform. This is the RLS setting
of Doerr and Doerr, Collecting Coupons with Random Initial Stake, Section 2.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ECRuntime

/-- Uniformly averaged number of one-bit RLS mutation iterations needed to
reach `allOnes` on a given fitness function. The initial fitness evaluation is
not counted. The definition makes no claim that the supplied kernel converges. -/
noncomputable def strictMonotoneRLSUniformInitialMean
    {n : ℕ} (hn : 0 < n) (fitness : BitString n → ℝ) : ℝ :=
  (Finset.univ.sum (fun x : BitString n =>
    (runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : ℝ) ^ n

/-- OneMax satisfies strict coordinate monotonicity in every dimension. -/
theorem oneMaxReal_coordinateStrictMonotonicity (n : Nat) :
    CandidateCoordinateStrictMonotonicity (oneMaxReal (n := n)) := by
  intro x i hi
  change (oneMax x : Real) <
    (oneMax (mutateWithMask x ({i} : MutationMask n)) : Real)
  exact_mod_cast oneMax_single_zero_flip_improves x i hi

/-- Proposed full-uniform-start monotone RLS mean identity. It is stronger
in objective scope than the currently public positive-linear identity,
but does not assert any other algorithmic result from the source paper. -/
theorem proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection
    {n : ℕ} (hn : 0 < n)
    (fitness : BitString n → ℝ)
    (hf : CandidateCoordinateStrictMonotonicity fitness) :
    strictMonotoneRLSUniformInitialMean hn fitness =
      (n : ℝ) *
        (harmonicReal n -
          (Finset.Icc 1 n).sum (fun j =>
            (1 : ℝ) / ((j : ℝ) * (2 : ℝ) ^ j))) := by
  classical
  unfold strictMonotoneRLSUniformInitialMean
  have hsum :
      (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          ({allOnes n} : Set (BitString n)) x).toReal)) =
        Finset.univ.sum (fun x : BitString n =>
          (n : ℝ) * harmonicReal (zeroCount x)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [candidateStrictMonotoneRLS_runtimeSup_eq_harmonic hn fitness hf x]
    exact ENNReal.toReal_ofReal
      (mul_nonneg (Nat.cast_nonneg n) (harmonicReal_nonneg (zeroCount x)))
  rw [hsum]
  calc
    ((Finset.univ.sum (fun x : BitString n =>
        (n : ℝ) * harmonicReal (zeroCount x))) / (2 : ℝ) ^ n) =
      ((n : ℝ) / (2 : ℝ) ^ n) *
        (Finset.sum (Finset.range (n + 1)) (fun k =>
          (Nat.choose n k : ℝ) * harmonicReal k)) := by
            exact rlsLinear_uniformInitial_harmonic_average n
    _ = (n : ℝ) *
          (harmonicReal n -
            (Finset.Icc 1 n).sum (fun j =>
              (1 : ℝ) / ((j : ℝ) * (2 : ℝ) ^ j))) := by
            rw [← proposed_binomialHarmonicAverage_closedForm n]
            ring

end ECRuntime
