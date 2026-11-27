/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Tactic.TypeStar

/-!
# Statement seed extracted from FreeField/CanonicalContractionExhaustion

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology
open scoped InnerProductSpace

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Vacuum complex covariance given by `⟪Ω, (A * B) Ω⟫_ℂ - ⟪Ω, A Ω⟫_ℂ * ⟪Ω, B Ω⟫_ℂ`. -/
noncomputable def vacuumComplexCovariance (Ω : H) (A B : H →L[ℂ] H) : ℂ :=
  ⟪Ω, (A * B) Ω⟫_ℂ - ⟪Ω, A Ω⟫_ℂ * ⟪Ω, B Ω⟫_ℂ


end VacuumBellSeparation
