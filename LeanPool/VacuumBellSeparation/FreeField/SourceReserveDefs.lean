/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceGramStrictness
public import LeanPool.VacuumBellSeparation.Gaussian.NormalizedCommutation

/-!
# Literal statement construction extracted from FreeField/SourceReserve

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- Continuous linear map for the conjugate source gram, of type `ComplexSourceHilbert hm U →L[ℂ]
ComplexSourceHilbert hm U`. -/
noncomputable def conjugateSourceGram :
    ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U :=
  Gaussian.conjugateOperator (sourceGram hm U)

/-- Continuous linear map for the source reserve, of type `ComplexSourceHilbert hm U →L[ℂ]
ComplexSourceHilbert hm U`. -/
noncomputable def sourceReserve :
    ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U :=
  CFC.sqrt (sourceGram hm U * conjugateSourceGram hm U)


end VacuumBellSeparation
