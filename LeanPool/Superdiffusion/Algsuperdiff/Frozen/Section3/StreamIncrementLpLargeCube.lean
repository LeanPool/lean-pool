/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLp
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedLargeAllP

/-!
# StreamIncrementLpLargeCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.stream_increment_lp_large_cube_bound
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (p : ℝ), 1 ≤ p →
        ∀ l m n : ℤ, n < m → m ≤ l →
          Probability.IsDeterministicShiftOneSidedOrlicz
            M.P.toMeasure
            (HCPolySupport.IndependentSums.gammaSigma (2 / p))
            (Provider.Stream.streamIncrementLpMass p l n m)
            ((C * p) ^ (p / 2) *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                  (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2))
            ((C * p) ^ (p / 2) *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                  (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.Stream.stream_increment_lp_large_cube_bound_provider d
