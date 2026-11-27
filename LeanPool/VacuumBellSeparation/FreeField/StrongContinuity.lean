/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Weyl.StrongContinuity
public import LeanPool.VacuumBellSeparation.FreeField.Uniqueness
public import LeanPool.VacuumBellSeparation.FreeField.Isotony
public import LeanPool.VacuumBellSeparation.Bell.StrongClosure

/-!
# Strong continuity in every free-field vacuum representation

An explicit Gaussian-kernel vacuum model transports the actual strong
continuity theorem to any `FreeFieldVacuum` by the proved GNS uniqueness
theorem. Thus convergence in the physical mass-shell L² norm is sufficient.
The local-algebra corollary states a genuine sufficient approximation
criterion; the time-slice identity (2.3) is proved without it, in
`FreeField/TimeSliceTheorem.lean` (`localAlgebra_doubleCone_eq_timeZeroLocalAlgebra`).
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology
open scoped InnerProductSpace

variable {m : ℝ}

/-- The explicit kernel model, rather than a chosen witness of existence. -/
noncomputable def canonicalFreeFieldVacuum (hm : 0 < m) :
    FreeFieldVacuum m (WeylSpace (oneParticleL2 hm)) where
  weyl := weylCLM (oneParticleL2 hm) (oneParticleL2_add hm)
  vacuum := weylVec (oneParticleL2 hm) 0
  weyl_mem_unitary := weylCLM_mem_unitary (oneParticleL2 hm) (oneParticleL2_add hm)
  weyl_mul F G := by
    rw [← inner_oneParticleL2 hm F G]
    exact weylCLM_mul (oneParticleL2 hm) (oneParticleL2_add hm) F G
  vacuum_norm := norm_weylVec_zero (oneParticleL2 hm) (oneParticleL2_add hm)
  vacuum_weyl F := by
    rw [← norm_oneParticleL2_sq hm F]
    exact weyl_vacuum (oneParticleL2 hm) (oneParticleL2_add hm) F
  cyclic := weyl_cyclic (oneParticleL2 hm) (oneParticleL2_add hm)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Norm convergence of the actual one-particle vectors gives strong
convergence of the Weyl operators in every vacuum representation. -/
theorem FreeFieldVacuum.tendsto_weyl_of_oneParticleL2 (V : FreeFieldVacuum m H)
    (hm : 0 < m) {α : Type*} {l : Filter α}
    {Fs : α → RealTestFunction} {F : RealTestFunction}
    (hF : Tendsto (fun i => oneParticleL2 hm (Fs i)) l (𝓝 (oneParticleL2 hm F)))
    (x : H) : Tendsto (fun i => V.weyl (Fs i) x) l (𝓝 (V.weyl F x)) := by
  obtain ⟨U, hΩ, hW⟩ := V.exists_unitary_equiv (canonicalFreeFieldVacuum hm)
  have ht := U.symm.continuous.continuousAt.tendsto.comp
    (tendsto_weylCLM_strong (oneParticleL2 hm) (oneParticleL2_add hm) hF (U x))
  change Tendsto (fun i => U.symm ((canonicalFreeFieldVacuum hm).weyl (Fs i) (U x))) l
    (𝓝 (U.symm ((canonicalFreeFieldVacuum hm).weyl F (U x)))) at ht
  simpa only [← hW, U.symm_apply_apply] using ht

theorem FreeFieldVacuum.weyl_eq_of_oneParticleL2_eq (V : FreeFieldVacuum m H)
    (hm : 0 < m) {F G : RealTestFunction}
    (hFG : oneParticleL2 hm F = oneParticleL2 hm G) : V.weyl F = V.weyl G := by
  apply ContinuousLinearMap.ext
  intro x
  have ht := V.tendsto_weyl_of_oneParticleL2 hm
    (l := atTop) (Fs := fun _ : ℕ => F) (F := G)
    (by rw [hFG]; exact tendsto_const_nhds) x
  exact tendsto_nhds_unique tendsto_const_nhds ht

theorem subset_generatedVNA (S : Set (H →L[ℂ] H)) : S ⊆ generatedVNA S := by
  intro T hT
  change T ∈ (commutantOf S).commutant
  rw [VonNeumannAlgebra.mem_commutant_iff]
  intro B hB
  have hb := mem_commutantOf_iff.mp hB
  exact (Set.mem_centralizer_iff.mp hb T (Set.mem_union_left _ hT)).symm

theorem FreeFieldVacuum.weyl_mem_localAlgebra (V : FreeFieldVacuum m H)
    {O : Set Spacetime} (F : RealTestFunction) (hF : tsupport F.1 ⊆ O) :
    V.weyl F ∈ localAlgebra V O :=
  subset_generatedVNA _ ⟨F, hF, rfl⟩

/-- The local algebra contains any Weyl operator whose actual one-particle
vector is a limit of vectors of sources supported in that region. -/
theorem FreeFieldVacuum.weyl_mem_localAlgebra_of_oneParticleL2_tendsto
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    {α : Type*} {l : Filter α} [l.NeBot] {O : Set Spacetime}
    {Fs : α → RealTestFunction} {F : RealTestFunction}
    (hsupp : ∀ᶠ i in l, tsupport (Fs i).1 ⊆ O)
    (hF : Tendsto (fun i => oneParticleL2 hm (Fs i)) l (𝓝 (oneParticleL2 hm F))) :
    V.weyl F ∈ localAlgebra V O := by
  apply mem_vonNeumannAlgebra_of_strong_tendsto (localAlgebra V O)
    (l := l) (Ts := fun i => V.weyl (Fs i))
  · exact hsupp.mono fun i hi => V.weyl_mem_localAlgebra (Fs i) hi
  · exact V.tendsto_weyl_of_oneParticleL2 hm hF

end VacuumBellSeparation
