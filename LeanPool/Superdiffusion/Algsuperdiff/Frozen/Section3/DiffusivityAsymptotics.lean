/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Scales
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripRemainder

/-!
# DiffusivityAsymptotics

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
  (diffusivity_asymptotics_proved)

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory



-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.diffusivity_asymptotics
    (d : ℕ) :
    ∃ Cflow : ℝ, 0 < Cflow ∧
      ∀ (M : ABKModel d) (m0 : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        mStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ m : ℤ, m ≤ m0 →
          |(Annealed.sigmaBar M m : ℝ) -
              Real.sqrt
                (M.nu ^ 2 +
                  Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
            ≤ Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (Annealed.sigmaBar M m : ℝ)) ∧
        (1 / 4 : ℝ) *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2)
          ≤ (Annealed.sigmaBar M m0 : ℝ) ^ 2 ∧
        (Annealed.sigmaBar M m0 : ℝ) ^ 2
          ≤ 4 *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2)
-- FROZEN-STATEMENT-END
    := by
  by_cases hd : 2 ≤ d
  · have : NeZero d := ⟨by omega⟩
    -- The provider export is gated at `mStarStar`; the frozen gate
    -- `mStar M < m0` is the stronger one, so the composition is a fortiori.
    obtain ⟨Cflow, hCflow, hmain⟩ :=
      diffusivity_asymptotics_proved
        d hd
    exact ⟨Cflow, hCflow, fun M m0 E hm0 =>
      hmain M m0 E (lt_of_le_of_lt (Provider.Scales.mStarStar_le_mStar M) hm0)⟩
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension hd⟩
