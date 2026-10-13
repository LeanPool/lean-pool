/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.LargeCubeW1Inf

/-!
# StreamDerivativeSum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The corrected full-range stream derivative sum

This module exposes the literal shell-derivative sum in corrected
`e.W.1.inf.bound`.  It is a source-facing provider over the already proved
large-cube derivative gauge estimate; the internal gauge is unfolded in the
conclusion.

Source: ABK26 `l.km.kn.Lp.estimates`, with inputs.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The corrected full-range `Gamma_2` bound for the weighted first- and
second-derivative shell sum.  The positive constant is chosen from the
dimension before the model and all scales. -/
theorem stream_derivative_sum_bound_provider (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (l m n : ℤ), n ≤ min m l →
        IndependentSums.IsBigOWith
          M.P.toMeasure
          (IndependentSums.gammaSigma 2)
          (fun omega : ShellSeq d =>
            ∑ k ∈ Finset.Ioc n m,
              ((3 : ℝ) ^ k * localCubeDerivNorm l (omega k) +
                (3 : ℝ) ^ (2 * k) * localCubeSecondDerivNorm l (omega k)))
          (C * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
            min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
  refine ⟨streamW1InfSumConst d, streamW1InfSumConst_pos d, ?_⟩
  intro M l m n hrange
  have hnm : n ≤ m := hrange.trans (min_le_left _ _)
  simpa only [largeCubeDerivGauge] using
    (isBigOWith_gammaSigma_largeCubeDerivGaugeSum M (l := l) hnm)

end

end Algsuperdiff.Section3.Provider.Stream
