/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Definition

/-!
# Characterization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Characterization of the running diffusivity

This file exposes the complete unique-choice characterization of `sigmaBar`:
positivity, convergence of the genuine unnormalized cutoff law's annealed
full-block matrices, and uniqueness among positive scalars with that limit.

## Main result

* `sigmaBar_characterization`: the full limit and uniqueness theorem.
-/

namespace Algsuperdiff.Section3.Annealed

open Filter HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The running diffusivity is positive, gives the genuine cutoff law's
infinite-volume isotropic block limit, and is the unique positive scalar with
that property. -/
theorem sigmaBar_characterization (M : ABKModel d) (m : ℤ) :
    0 < (sigmaBar M m : ℝ) ∧
      Tendsto
        (fun n : ℕ =>
          toFullBlockMat
            (Ch04.annealedBlockMatrixAtScale
              (coefficientCutoffLaw M m) (n : ℤ)))
        atTop
        (nhds (toFullBlockMat (Ch02.blockDiag
          ((sigmaBar M m : ℝ) • (1 : Mat d))
          ((sigmaBar M m : ℝ)⁻¹ • (1 : Mat d))))) ∧
      ∀ other : ℝ,
        0 < other →
        Tendsto
          (fun n : ℕ =>
            toFullBlockMat
              (Ch04.annealedBlockMatrixAtScale
                (coefficientCutoffLaw M m) (n : ℤ)))
          atTop
          (nhds (toFullBlockMat (Ch02.blockDiag
            (other • (1 : Mat d)) (other⁻¹ • (1 : Mat d))))) →
        other = (sigmaBar M m : ℝ) := by
  have hspec := Classical.choose_spec (existsUnique_sigmaBar M m)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [sigmaBar] using hspec.1.1
  · simpa only [sigmaBar] using hspec.1.2
  · intro other hother_pos hother_limit
    simpa only [sigmaBar] using
      hspec.2 other ⟨hother_pos, hother_limit⟩

end


end Algsuperdiff.Section3.Annealed
