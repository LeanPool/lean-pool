/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceInclusion
public import LeanPool.VacuumBellSeparation.Gaussian.SourceGram

/-!
# Literal statement construction extracted from FreeField/ComplexSource

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

open MeasureTheory ClosedSubmodule

namespace VacuumBellSeparation

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- The actual complex Hilbert space obtained from the completed real sources. -/
abbrev ComplexSourceHilbert := Gaussian.HilbertComplexification (SourceHilbert hm U)

/-- Complex-linear extension of the physical source embedding. -/
noncomputable def complexSourceMap :
    ComplexSourceHilbert hm U →L[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  Gaussian.sourceMap (sourceEmbedding hm U)

/-- Componentwise extension of the actual real commutation operator. -/
noncomputable def complexSourceCommutation :
    ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U :=
  Gaussian.complexCommutation (sourceEmbedding hm U)

/-- The physical Gram operator, defined by the map and its genuine Hilbert adjoint. -/
noncomputable def sourceGram : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U :=
  (complexSourceMap hm U).adjoint.comp (complexSourceMap hm U)


end VacuumBellSeparation
