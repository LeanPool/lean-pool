/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivityBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.NormalizedP4
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.NormalizedStructuralLaw

/-!
# WellDefinedness

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Well-definedness of the running diffusivity

This file proves existence and uniqueness of the positive scalar describing the
infinite-volume annealed full-block limit of the genuine coefficient cutoff.
The proof consumes the verified law carrier, normalized structural law, and
direct normalized `(P4)` package.  None of those proof ingredients appears as a
hypothesis of the public theorem.

## Main result

* `existsUnique_sigmaBar`: the exact no-extra-premise well-definedness theorem
  for the Section 3 running diffusivity.
-/

namespace Algsuperdiff.Section3.Annealed

open Filter HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- There is a unique positive scalar whose isotropic block diagonal is the
infinite-volume annealed full-block limit of the genuine cutoff law. -/
theorem existsUnique_sigmaBar (M : ABKModel d) (m : ℤ) :
    ∃! sigma : ℝ,
      0 < sigma ∧
        Tendsto
          (fun n : ℕ =>
            toFullBlockMat
              (Ch04.annealedBlockMatrixAtScale
                (coefficientCutoffLaw M m) (n : ℤ)))
          atTop
          (nhds (toFullBlockMat (Ch02.blockDiag
            (sigma • (1 : Mat d)) (sigma⁻¹ • (1 : Mat d))))) := by
  let : NeZero d := ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  exact existsUnique_pos_annealedFullBlockMatrixAtScale_limit_of_scaleNormalized_P4
    (coefficientCutoffLaw_lawCarrier M m)
    (cutoffNormalizationDepth d m)
    (cutoffNormalization_structuralLaw M m)
    (cutoffNormalization_quantitativeCoarseGrainedEllipticity M m)

end


end Algsuperdiff.Section3.Annealed
