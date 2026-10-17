/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Support.HighContrast.Corridor.PhaseComparison.Averaging

/-!
# AveragingUniform

Ported from scottnarmstrong/CoarseGraining at c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Uniform-constant grid-phase averaging

The shared proof of `exists_gridPhase_meanSq_le_uniform` lives in
`Corridor/PhaseComparison/Averaging.lean`.
The existential interface specializes its field-independent constant. This module
preserves the public import path for consumers of the uniform theorem.
-/
