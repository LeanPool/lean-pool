/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Positive traces of operator series

The sum here is the actual operator-norm sum on the full Hilbert space.
Its positive trace commutes with an arbitrary-index positive series,
including when the resulting extended trace is infinite. The proof uses
continuous evaluation for each diagonal entry and nonnegative Tonelli.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

omit [CompleteSpace E] in
theorem hasSum_operator_diagonal {A : ι → E →L[ℂ] E} {T : E →L[ℂ] E}
    (hA : HasSum A T) (x : E) :
    HasSum (fun i => (inner ℂ x (A i x)).re) (inner ℂ x (T x)).re := by
  exact Complex.hasSum_re ((hA.mapL (ContinuousLinearMap.apply ℂ E x)).mapL
    (innerSL ℂ x))

theorem positiveTrace_tsum {A : ι → E →L[ℂ] E}
    (hA : ∀ i, 0 ≤ A i) (hs : Summable A) :
    positiveTrace (∑' i, A i) = ∑' i, positiveTrace (A i) := by
  obtain ⟨κ, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  have hsum : 0 ≤ ∑' i, A i := tsum_nonneg hA
  have hdiag (j : κ) :
      ENNReal.ofReal ((inner ℂ (b j) ((∑' i, A i) (b j))).re) =
        ∑' i, ENNReal.ofReal ((inner ℂ (b j) (A i (b j))).re) := by
    have hd := hasSum_operator_diagonal hs.hasSum (b j)
    rw [← hd.tsum_eq]
    apply ENNReal.ofReal_tsum_of_nonneg
    · intro i
      simpa only [RCLike.re_eq_complex_re] using
        (ContinuousLinearMap.nonneg_iff_isPositive.mp (hA i)).re_inner_nonneg_right (b j)
    · exact hd.summable
  calc
    positiveTrace (∑' i, A i) =
        ∑' j, ENNReal.ofReal ((inner ℂ (b j) ((∑' i, A i) (b j))).re) :=
      positiveTrace_eq_tsum_diagonal b hsum
    _ = ∑' j, ∑' i, ENNReal.ofReal ((inner ℂ (b j) (A i (b j))).re) :=
      tsum_congr hdiag
    _ = ∑' i, ∑' j, ENNReal.ofReal ((inner ℂ (b j) (A i (b j))).re) :=
      tsum_comm
    _ = ∑' i, positiveTrace (A i) :=
      tsum_congr fun i => (positiveTrace_eq_tsum_diagonal b (hA i)).symm

theorem isPositiveTraceClass_tsum {A : ι → E →L[ℂ] E}
    (hA : ∀ i, 0 ≤ A i) (hs : Summable A)
    (htrace : (∑' i, positiveTrace (A i)) < ∞) :
    IsPositiveTraceClass (∑' i, A i) := by
  refine ⟨tsum_nonneg hA, ?_⟩
  rwa [positiveTrace_tsum hA hs]

end VacuumBellSeparation.Gaussian
