/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeSliceBall
public import LeanPool.VacuumBellSeparation.FreeField.StrongContinuity
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroWeylDefs

/-!
# Actual time-zero Weyl operators in the physical vacuum representation

The spacetime representative exists by the proved reverse time-slice
construction. Equality of its actual one-particle vector makes the resulting
operator independent of the chosen representative. Localization uses a
separate, locally constructed witness in the same representation.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

theorem oneParticle_timeZeroSpacetimeRepresentative {m : ℝ} (hm : 0 < m)
    (u : TimeZeroSource) (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (timeZeroSpacetimeRepresentative hm u) p = timeZeroOneParticle m u p := by
  let : Nonempty RealTestFunction := ⟨0⟩
  exact Classical.epsilon_spec (exists_spacetimeSource_of_timeZeroSource_any hm u) p

theorem oneParticleL2_timeZeroSpacetimeRepresentative {m : ℝ} (hm : 0 < m)
    (u : TimeZeroSource) :
    oneParticleL2 hm (timeZeroSpacetimeRepresentative hm u) = timeZeroL2 hm u :=
  oneParticleL2_eq_timeZeroL2_of_eq hm _ u (oneParticle_timeZeroSpacetimeRepresentative hm u)

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem FreeFieldVacuum.timeZeroWeyl_eq_weyl (V : FreeFieldVacuum m H)
    (hm : 0 < m) (u : TimeZeroSource) (F : RealTestFunction)
    (hF : oneParticleL2 hm F = timeZeroL2 hm u) :
    V.timeZeroWeyl hm u = V.weyl F :=
  V.weyl_eq_of_oneParticleL2_eq hm
    ((oneParticleL2_timeZeroSpacetimeRepresentative hm u).trans hF.symm)

theorem FreeFieldVacuum.timeZeroWeyl_mem_unitary (V : FreeFieldVacuum m H)
    (hm : 0 < m) (u : TimeZeroSource) :
    V.timeZeroWeyl hm u ∈ unitary (H →L[ℂ] H) :=
  V.weyl_mem_unitary _

theorem oneParticleInner_timeZeroSpacetimeRepresentative (hm : 0 < m)
    (u v : TimeZeroSource) :
    oneParticleInner m (timeZeroSpacetimeRepresentative hm u)
      (timeZeroSpacetimeRepresentative hm v) = timeZeroOneParticleInner m u v := by
  rw [← inner_oneParticleL2 hm, oneParticleL2_timeZeroSpacetimeRepresentative,
    oneParticleL2_timeZeroSpacetimeRepresentative, inner_timeZeroL2]

theorem FreeFieldVacuum.timeZeroWeyl_mul (V : FreeFieldVacuum m H)
    (hm : 0 < m) (u v : TimeZeroSource) :
    V.timeZeroWeyl hm u * V.timeZeroWeyl hm v =
      Complex.exp (-(Complex.I * ((timeZeroOneParticleInner m u v).im : ℂ))) •
        V.timeZeroWeyl hm (u + v) := by
  have hadd : oneParticleL2 hm
      (timeZeroSpacetimeRepresentative hm u + timeZeroSpacetimeRepresentative hm v) =
      timeZeroL2 hm (u + v) := by
    rw [oneParticleL2_add, oneParticleL2_timeZeroSpacetimeRepresentative,
      oneParticleL2_timeZeroSpacetimeRepresentative, timeZeroL2_add]
  change V.weyl _ * V.weyl _ = _
  rw [V.weyl_mul, oneParticleInner_timeZeroSpacetimeRepresentative,
    ← V.timeZeroWeyl_eq_weyl hm (u + v) _ hadd]

theorem FreeFieldVacuum.vacuum_timeZeroWeyl (V : FreeFieldVacuum m H)
    (hm : 0 < m) (u : TimeZeroSource) :
    ⟪V.vacuum, V.timeZeroWeyl hm u V.vacuum⟫_ℂ =
      ((Real.exp (-(timeZeroFourierCovariance m u u / 2)) : ℝ) : ℂ) := by
  change ⟪V.vacuum, V.weyl _ V.vacuum⟫_ℂ = _
  rw [V.vacuum_weyl, oneParticleInner_timeZeroSpacetimeRepresentative,
    timeZeroOneParticleInner_re hm]

/-- The time-zero test pair gives an operator in the original spacetime
double-cone algebra, with no new representation or localization axiom. -/
theorem FreeFieldVacuum.timeZeroWeyl_mem_localAlgebra (V : FreeFieldVacuum m H)
    (hm : 0 < m) {R : ℝ} (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3))
    (u : TimeZeroSource)
    (hf : tsupport u.1.1 ⊆ Metric.ball x₀ R)
    (hg : tsupport u.2.1 ⊆ Metric.ball x₀ R) :
    V.timeZeroWeyl hm u ∈ localAlgebra V (doubleCone (0, x₀) R) := by
  obtain ⟨F, hs, heq⟩ := exists_spacetimeSourceL2_of_timeZeroSource_ball hm hR x₀ u hf hg
  rw [V.timeZeroWeyl_eq_weyl hm u F heq]
  exact V.weyl_mem_localAlgebra F hs

end VacuumBellSeparation
