/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroDefs

/-!
# Primitive time-zero Weyl and local-algebra definitions

A source is selected by its literal pointwise physical κ predicate. The
existence and representation independence of such a source are proved in
TimeZeroWeyl, separately from these definitions. Thus the statement closure
of the time-slice identity contains no local existence theorem.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- A purely specified representative; the predicate is satisfied by the
proved actual reverse time-slice construction at positive mass. -/
noncomputable def timeZeroSpacetimeRepresentative {m : ℝ} (_hm : 0 < m)
    (u : TimeZeroSource) : RealTestFunction := by
  letI : Nonempty RealTestFunction :=
    ⟨⟨0, contDiff_const, HasCompactSupport.zero⟩⟩
  exact Classical.epsilon (fun F : RealTestFunction =>
    ∀ p, oneParticle m F p = timeZeroOneParticle m u p)

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuous linear map for the time zero Weyl, of type `H →L[ℂ] H`. -/
noncomputable def FreeFieldVacuum.timeZeroWeyl (V : FreeFieldVacuum m H)
    (hm : 0 < m) (u : TimeZeroSource) : H →L[ℂ] H :=
  V.weyl (timeZeroSpacetimeRepresentative hm u)

/-- Time-zero localization uses the literal compact supports of both real
test functions and operators acting in the existing vacuum Hilbert space. -/
noncomputable def timeZeroLocalAlgebra (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) : VonNeumannAlgebra H :=
  generatedVNA {T | ∃ u : TimeZeroSource,
    tsupport u.1.1 ⊆ U ∧ tsupport u.2.1 ⊆ U ∧ T = V.timeZeroWeyl hm u}

end VacuumBellSeparation
