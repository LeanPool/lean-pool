/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeTimeSlice
public import LeanPool.VacuumBellSeparation.FreeField.SourceTomitaTestCore
public import LeanPool.VacuumBellSeparation.FreeField.ShellBoostMeasure

/-!
# A boost-invariant spacetime test core for the actual wedge Tomita graph

The graph pairs are formed from original real compact spacetime sources.
Time-slice equality identifies their full graph closure, and the literal
inverse-label boost action preserves this test graph at wedge position zero.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Gaussian.HilbertComplexification

variable {m : ℝ} (hm : 0 < m)

/-- Wedge spacetime Tomita test graph. -/
def wedgeSpacetimeTomitaTestGraph (ℓ : ℝ) :
    Set (Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m)) :=
  {p | ∃ F G : RealTestFunction,
    tsupport F.1 ⊆ leftWedge ℓ ∧ tsupport G.1 ⊆ leftWedge ℓ ∧
      p = (oneParticleL2 hm F + Complex.I • oneParticleL2 hm G,
        oneParticleL2 hm F - Complex.I • oneParticleL2 hm G)}

theorem wedgeSpacetimeTomitaTestGraph_subset (ℓ : ℝ) :
    wedgeSpacetimeTomitaTestGraph hm ℓ ⊆ sourceTomitaGraph hm (leftWedgeTimeZero ℓ) := by
  rintro _ ⟨F, G, hF, hG, rfl⟩
  obtain ⟨u, hu⟩ := oneParticleL2_mem_sourceRealSpace_leftWedge hm ℓ F hF
  obtain ⟨v, hv⟩ := oneParticleL2_mem_sourceRealSpace_leftWedge hm ℓ G hG
  change sourceEmbedding hm (leftWedgeTimeZero ℓ) u = oneParticleL2 hm F at hu
  change sourceEmbedding hm (leftWedgeTimeZero ℓ) v = oneParticleL2 hm G at hv
  refine ⟨mk u v, ?_, ?_⟩
  · change sourceEmbedding hm (leftWedgeTimeZero ℓ) u +
      Complex.I • sourceEmbedding hm (leftWedgeTimeZero ℓ) v = _
    rw [hu, hv]
  · change sourceEmbedding hm (leftWedgeTimeZero ℓ) u +
      Complex.I • sourceEmbedding hm (leftWedgeTimeZero ℓ) (-v) = _
    rw [map_neg, smul_neg, hu, hv, sub_eq_add_neg]

theorem sourceTomitaTestGraph_subset_wedgeSpacetime (ℓ : ℝ) :
    sourceTomitaTestGraph hm (leftWedgeTimeZero ℓ) ⊆ wedgeSpacetimeTomitaTestGraph hm ℓ := by
  rintro _ ⟨u, v, rfl⟩
  obtain ⟨F, hF, heqF⟩ := exists_spacetimeSourceL2_of_timeZeroSource_leftWedge
    hm ℓ u.1 u.2.1 u.2.2
  obtain ⟨G, hG, heqG⟩ := exists_spacetimeSourceL2_of_timeZeroSource_leftWedge
    hm ℓ v.1 v.2.1 v.2.2
  exact ⟨F, G, hF, hG, by rw [heqF, heqG]⟩

theorem closure_wedgeSpacetimeTomitaTestGraph (ℓ : ℝ) :
    closure (wedgeSpacetimeTomitaTestGraph hm ℓ) =
      sourceTomitaGraph hm (leftWedgeTimeZero ℓ) := by
  apply Set.Subset.antisymm
  · exact closure_minimal (wedgeSpacetimeTomitaTestGraph_subset hm ℓ)
      (sourceTomitaGraph_isClosed hm (leftWedgeTimeZero ℓ))
  · rw [← closure_sourceTomitaTestGraph]
    exact closure_mono (sourceTomitaTestGraph_subset_wedgeSpacetime hm ℓ)

theorem oneParticleBoostIsometry_oneParticleL2 (η : ℝ) (F : RealTestFunction) :
    oneParticleBoostIsometry hm η (oneParticleL2 hm F) =
      oneParticleL2 hm (F.compCLE (boost (-η))) := by
  apply Lp.ext
  have hpull := (measurePreserving_shellBoost hm (-η)).quasiMeasurePreserving.ae_eq_comp
    (coeFn_oneParticleL2 hm F)
  filter_upwards [oneParticleBoostIsometry_ae hm η (oneParticleL2 hm F), hpull,
    coeFn_oneParticleL2 hm (F.compCLE (boost (-η)))] with p hU hF hboost
  exact hU.trans (hF.trans (hboost.trans (oneParticle_boost m (-η) F p)).symm)

theorem tsupport_compCLE_boost_subset_leftWedge_zero (η : ℝ) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) :
    tsupport (F.compCLE (boost η)).1 ⊆ leftWedge 0 := by
  rw [RealTestFunction.tsupport_compCLE]
  intro x hx
  exact (boost_mem_leftWedge_zero_iff η x).mp (hF hx)

/-- Both coordinates of the literal smooth graph core transform by the same
physical unitary. The inverse-label sign is retained in the test functions. -/
theorem wedgeSpacetimeTomitaTestGraph_boost_invariant (η : ℝ)
    {p : Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m)}
    (hp : p ∈ wedgeSpacetimeTomitaTestGraph hm 0) :
    (oneParticleBoostIsometry hm η p.1, oneParticleBoostIsometry hm η p.2) ∈
      wedgeSpacetimeTomitaTestGraph hm 0 := by
  obtain ⟨F, G, hF, hG, rfl⟩ := hp
  refine ⟨F.compCLE (boost (-η)), G.compCLE (boost (-η)),
    tsupport_compCLE_boost_subset_leftWedge_zero (-η) F hF,
    tsupport_compCLE_boost_subset_leftWedge_zero (-η) G hG, ?_⟩
  simp only [map_add, map_sub, map_smul, oneParticleBoostIsometry_oneParticleL2]

end VacuumBellSeparation
