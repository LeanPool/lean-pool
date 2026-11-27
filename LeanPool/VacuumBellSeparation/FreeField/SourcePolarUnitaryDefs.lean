/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PolarUnitary
public import LeanPool.VacuumBellSeparation.FreeField.StandardSourceSpace

/-!
# Literal statement construction extracted from FreeField/SourcePolarUnitary

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- Linear isometry equivalence for the source polar unitary, of type `ComplexSourceHilbert hm U
≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def sourcePolarUnitary (hU : Bornology.IsBounded U)
    (hopen : IsOpen U) (hne : U.Nonempty) :
    ComplexSourceHilbert hm U ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  polarUnitary (complexSourceMap hm U) (complexSourceMap_injective hm U hU)
    (complexSourceMap_denseRange_of_open hm U hopen hne)


end VacuumBellSeparation
