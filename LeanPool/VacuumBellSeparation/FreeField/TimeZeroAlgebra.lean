/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroWeyl

/-!
# Time-zero local algebras inside the original spacetime algebras

The generators are actual time-zero Weyl operators in the same physical
vacuum representation. The inclusion is the proved reverse time-slice
direction. Equality still requires the forward time-slice direction.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem generatedVNA_coe (A : VonNeumannAlgebra H) :
    generatedVNA (A : Set (H →L[ℂ] H)) = A := by
  change A.commutant.commutant = A
  exact A.commutant_commutant

theorem generatedVNA_le_of_subset {S : Set (H →L[ℂ] H)} (A : VonNeumannAlgebra H)
    (hS : S ⊆ A) : generatedVNA S ≤ A := by
  rw [← generatedVNA_coe A]
  exact generatedVNA_mono hS

variable {m : ℝ}

theorem timeZeroLocalAlgebra_mono (V : FreeFieldVacuum m H) (hm : 0 < m)
    {U U' : Set (EuclideanSpace ℝ (Fin 3))} (h : U ⊆ U') :
    timeZeroLocalAlgebra V hm U ≤ timeZeroLocalAlgebra V hm U' := by
  apply generatedVNA_mono
  rintro T ⟨u, hf, hg, rfl⟩
  exact ⟨u, hf.trans h, hg.trans h, rfl⟩

theorem FreeFieldVacuum.timeZeroWeyl_mem_timeZeroLocalAlgebra
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (u : TimeZeroSource)
    (hf : tsupport u.1.1 ⊆ U) (hg : tsupport u.2.1 ⊆ U) :
    V.timeZeroWeyl hm u ∈ timeZeroLocalAlgebra V hm U :=
  subset_generatedVNA _ ⟨u, hf, hg, rfl⟩

/-- The actual time-zero ball algebra embeds in the original double-cone
algebra, in every physical vacuum representation. -/
theorem timeZeroLocalAlgebra_ball_le (V : FreeFieldVacuum m H) (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3)) :
    timeZeroLocalAlgebra V hm (Metric.ball x₀ R) ≤
      localAlgebra V (doubleCone (0, x₀) R) := by
  apply generatedVNA_le_of_subset
  rintro T ⟨u, hf, hg, rfl⟩
  exact V.timeZeroWeyl_mem_localAlgebra hm hR x₀ u hf hg

/-- Strong continuity depends on the actual physical time-zero norm. -/
theorem FreeFieldVacuum.tendsto_timeZeroWeyl (V : FreeFieldVacuum m H)
    (hm : 0 < m) {α : Type*} {l : Filter α}
    {us : α → TimeZeroSource} {u : TimeZeroSource}
    (hu : Tendsto (fun i => timeZeroL2 hm (us i)) l (𝓝 (timeZeroL2 hm u)))
    (x : H) : Tendsto (fun i => V.timeZeroWeyl hm (us i) x) l
      (𝓝 (V.timeZeroWeyl hm u x)) := by
  apply V.tendsto_weyl_of_oneParticleL2 hm
  simpa only [oneParticleL2_timeZeroSpacetimeRepresentative] using hu

end VacuumBellSeparation
