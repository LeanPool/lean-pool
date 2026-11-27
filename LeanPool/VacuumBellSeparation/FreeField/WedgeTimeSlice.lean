/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeCompactExhaustion
public import LeanPool.VacuumBellSeparation.FreeField.TimeSliceBall
public import LeanPool.VacuumBellSeparation.FreeField.ForwardTimeSliceClosure
public import LeanPool.VacuumBellSeparation.FreeField.SourceInclusion

/-!
# Time-slice equality for the actual halfspace and spacetime wedge

Compact exhaustion by contained tangent double cones lets the established
ball time-slice construction apply to every wedge test source. Both sides
use the original massive mass-shell Hilbert space and original source maps.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m) (ℓ : ℝ)

theorem exists_spacetimeSourceL2_of_timeZeroSource_leftWedge
    (u : TimeZeroSource)
    (hf : tsupport u.1.1 ⊆ leftWedgeTimeZero ℓ)
    (hg : tsupport u.2.1 ⊆ leftWedgeTimeZero ℓ) :
    ∃ F : RealTestFunction, tsupport F.1 ⊆ leftWedge ℓ ∧
      oneParticleL2 hm F = timeZeroL2 hm u := by
  have hK : IsCompact (tsupport u.1.1 ∪ tsupport u.2.1) := u.1.2.2.union u.2.2.2
  obtain ⟨L, hL, hs⟩ := IsCompact.exists_tangent_ball hK (Set.union_subset hf hg)
  obtain ⟨F, hF, heq⟩ := exists_spacetimeSourceL2_of_timeZeroSource_ball hm hL
    ((ℓ - L) • e₁) u (Set.subset_union_left.trans hs) (Set.subset_union_right.trans hs)
  exact ⟨F, hF.trans (tangent_doubleCone_subset_leftWedge ℓ L), heq⟩

theorem oneParticleL2_mem_sourceRealSpace_leftWedge
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ leftWedge ℓ) :
    oneParticleL2 hm F ∈ sourceRealSpace hm (leftWedgeTimeZero ℓ) := by
  obtain ⟨L, hL, hs⟩ := IsCompact.exists_tangent_doubleCone F.2.2 hF
  exact sourceRealSpace_mono hm (tangent_ball_subset_leftWedgeTimeZero ℓ L)
    (oneParticleL2_mem_sourceRealSpace hm hL ((ℓ - L) • e₁) F hs)

/-- Wedge spacetime test vectors with membership specified by `{z | ∃ F : RealTestFunction,
tsupport F.1 ⊆ leftWedge ℓ ∧ oneParticleL2 hm F = z}`. -/
def wedgeSpacetimeTestVectors : Set (Lp ℂ 2 (oneParticleMeasure m)) :=
  {z | ∃ F : RealTestFunction, tsupport F.1 ⊆ leftWedge ℓ ∧ oneParticleL2 hm F = z}

/-- Equality of real closed source sets, with no bounded-wedge hypothesis. -/
theorem closure_wedgeSpacetimeTestVectors :
    closure (wedgeSpacetimeTestVectors hm ℓ) =
      (sourceRealSpace hm (leftWedgeTimeZero ℓ) : Set (Lp ℂ 2 (oneParticleMeasure m))) := by
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ (sourceRealSpace hm (leftWedgeTimeZero ℓ)).isClosed'
    rintro _ ⟨F, hF, rfl⟩
    exact oneParticleL2_mem_sourceRealSpace_leftWedge hm ℓ F hF
  · change Set.range (sourceEmbedding hm (leftWedgeTimeZero ℓ)) ⊆ _
    rw [range_sourceEmbedding_eq_closure]
    apply closure_mono
    rintro _ ⟨u, rfl⟩
    exact exists_spacetimeSourceL2_of_timeZeroSource_leftWedge hm ℓ u.1 u.2.1 u.2.2

end VacuumBellSeparation
