/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpacetimeSlicePairing
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Topology.Sequences

/-!
# Actual forward time-slice inclusion in the real local source closure

Every real orthogonal annihilator of the local time-zero source range
annihilates each actual evolved slice. The proved scalar Fubini identity
therefore puts κF in the real norm closure. This is enough for the local
von Neumann algebra statement and makes no local cyclicity assertion.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology
open scoped InnerProductSpace

theorem oneParticleL2_mem_closure_sourceTestMap {m R : ℝ}
    (hm : 0 < m) (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3))
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ doubleCone (0, x₀) R) :
    oneParticleL2 hm F ∈ closure (Set.range (sourceTestMap hm (Metric.ball x₀ R))) := by
  let K : Submodule ℝ (Lp ℂ 2 (oneParticleMeasure m)) :=
    (sourceTestMap hm (Metric.ball x₀ R)).range
  change oneParticleL2 hm F ∈ K.topologicalClosure
  rw [← K.orthogonal_orthogonal_eq_closure]
  apply ((Kᗮ).mem_orthogonal _).mpr
  intro ψ hψ
  rw [real_inner_oneParticleL2_eq_integral_timeZeroL2]
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun t => by
    apply (K.mem_orthogonal' ψ).mp hψ
    exact ⟨⟨evolvedSpatialSource hm t (spacetimeSpatialSlice F t),
      evolvedSpatialSource_spacetimeSlice_mem_ball_of_doubleCone hm hR x₀ F hF t⟩, rfl⟩

theorem oneParticleL2_mem_sourceRealSpace {m R : ℝ}
    (hm : 0 < m) (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3))
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ doubleCone (0, x₀) R) :
    oneParticleL2 hm F ∈ sourceRealSpace hm (Metric.ball x₀ R) := by
  change oneParticleL2 hm F ∈ Set.range (sourceEmbedding hm (Metric.ball x₀ R))
  rw [range_sourceEmbedding_eq_closure]
  exact oneParticleL2_mem_closure_sourceTestMap hm hR x₀ F hF

/-- The approximants are actual local compact test pairs, rather than
arbitrary elements of the completed or complexified source space. -/
theorem exists_sourceTestSequence_of_mem_closure {m : ℝ} (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (z : Lp ℂ 2 (oneParticleMeasure m))
    (hz : z ∈ closure (Set.range (sourceTestMap hm U))) :
    ∃ us : ℕ → SourceTestSpace hm U,
      Tendsto (fun n => timeZeroL2 hm (us n).1) atTop (𝓝 z) := by
  obtain ⟨xs, hxs, hlim⟩ := mem_closure_iff_seq_limit.mp hz
  have hw : ∀ n, ∃ u : SourceTestSpace hm U, sourceTestMap hm U u = xs n := hxs
  choose us hus using hw
  refine ⟨us, ?_⟩
  have heq : (fun n => timeZeroL2 hm (us n).1) = xs := funext hus
  rwa [heq]

end VacuumBellSeparation
