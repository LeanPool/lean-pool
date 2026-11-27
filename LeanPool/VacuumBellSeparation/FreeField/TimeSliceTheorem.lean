/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ForwardTimeSliceClosure

/-!
# The actual local-algebra time-slice identity

Both algebras act in the original physical vacuum Hilbert space. The
reverse inclusion uses actual compact spacetime representatives. The
forward inclusion uses actual localized time-zero approximants, physical
one-particle convergence, proved strong Weyl continuity and strong closure
of the original double commutant. No time-slice or cyclicity premise is
added to the vacuum model.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem FreeFieldVacuum.weyl_mem_timeZeroLocalAlgebra_of_mem_closure
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (F : RealTestFunction)
    (hF : oneParticleL2 hm F ∈ closure (Set.range (sourceTestMap hm U))) :
    V.weyl F ∈ timeZeroLocalAlgebra V hm U := by
  obtain ⟨us, hlim⟩ := exists_sourceTestSequence_of_mem_closure hm U (oneParticleL2 hm F) hF
  apply mem_vonNeumannAlgebra_of_strong_tendsto (timeZeroLocalAlgebra V hm U)
    (Ts := fun n => V.timeZeroWeyl hm (us n).1) (l := atTop)
  · exact Eventually.of_forall fun n =>
      V.timeZeroWeyl_mem_timeZeroLocalAlgebra hm (us n).1 (us n).2.1 (us n).2.2
  · intro x
    apply V.tendsto_weyl_of_oneParticleL2 hm
    simpa only [oneParticleL2_timeZeroSpacetimeRepresentative] using hlim

/-- Forward time-slice inclusion for the genuine spacetime local algebra. -/
theorem localAlgebra_doubleCone_le_timeZeroLocalAlgebra (V : FreeFieldVacuum m H)
    (hm : 0 < m) {R : ℝ} (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3)) :
    localAlgebra V (doubleCone (0, x₀) R) ≤
      timeZeroLocalAlgebra V hm (Metric.ball x₀ R) := by
  apply generatedVNA_le_of_subset
  rintro T ⟨F, hF, rfl⟩
  exact V.weyl_mem_timeZeroLocalAlgebra_of_mem_closure hm _ F
    (oneParticleL2_mem_closure_sourceTestMap hm hR x₀ F hF)

/-- Manuscript (2.3), in every actual positive-mass vacuum representation
and for every positive-radius spatial ball and its double cone. -/
theorem localAlgebra_doubleCone_eq_timeZeroLocalAlgebra (V : FreeFieldVacuum m H)
    (hm : 0 < m) {R : ℝ} (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3)) :
    localAlgebra V (doubleCone (0, x₀) R) =
      timeZeroLocalAlgebra V hm (Metric.ball x₀ R) :=
  le_antisymm (localAlgebra_doubleCone_le_timeZeroLocalAlgebra V hm hR x₀)
    (timeZeroLocalAlgebra_ball_le V hm hR x₀)

end VacuumBellSeparation
