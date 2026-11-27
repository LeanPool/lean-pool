/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroSymplecticNondegenerate
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Literal statement construction extracted from FreeField/CanonicalSourceHull

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- A canonical system retains the actual local test pairs and symplectic form. -/
def IsCanonicalSourceSystem (U : Set (EuclideanSpace ℝ (Fin 3)))
    (S : Submodule ℝ TimeZeroSource) : Prop :=
  FiniteDimensional ℝ S ∧ S ≤ localizedTimeZeroSources U ∧
    ∀ u ∈ S, (∀ v ∈ S, timeZeroSymplectic u v = 0) → u = 0


end VacuumBellSeparation
