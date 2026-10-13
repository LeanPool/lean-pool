/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ErrorMoment

/-!
# S5ErrorMomentBoundProvider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Moment bound for the localized error

This module packages the localized-error estimate with one constant serving
both its moment amplitude and the admissible exponent range.
-/

namespace Algsuperdiff.Section4.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section5.Support
open _root_.HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

/-- The localized error has the generator-renormalization moment profile at
every scale and centre. -/
theorem s5_error_moment_bound_provider
    (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ (p : ℝ) (n : ℤ) (y : Vec d), 1 ≤ p →
          p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
          (∫⁻ omega, localizedError M n y omega ^ p ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
            ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
              Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p := by
  classical
  by_cases hmodel : Nonempty (ABKModel d)
  · obtain ⟨M⟩ := hmodel
    exact Algsuperdiff.Section5.Provider.localizedError_moment_bound
      d cstar M.shellPrefix.dimension hcstar
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro M
    exact (hmodel ⟨M⟩).elim

end

end Algsuperdiff.Section4.Provider
