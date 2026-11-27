/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CanonicalSourcePair
public import LeanPool.VacuumBellSeparation.FreeField.CanonicalSourceAlgebra
public import LeanPool.VacuumBellSeparation.FreeField.Microcausality.Algebra

/-!
# Commutation of the actual time-zero source algebras

The literal source symplectic form is the imaginary one-particle pairing.
Its vanishing gives commutation of the original spacetime representatives,
then of their actual generated von Neumann algebras.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {m : ℝ} (hm : 0 < m) {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (V : FreeFieldVacuum m H)

theorem timeZeroWeyl_mul_comm_of_symplectic_zero {u v : TimeZeroSource}
    (huv : timeZeroSymplectic u v = 0) :
    V.timeZeroWeyl hm u * V.timeZeroWeyl hm v = V.timeZeroWeyl hm v * V.timeZeroWeyl hm u := by
  change V.weyl (timeZeroSpacetimeRepresentative hm u) * V.weyl
    (timeZeroSpacetimeRepresentative hm v) = _
  apply V.weyl_mul_comm_of_im_eq_zero
  rw [oneParticleInner_timeZeroSpacetimeRepresentative, ← inner_timeZeroL2 hm,
    inner_timeZeroL2_gram]
  simp [huv]

theorem commuting_canonicalSourceAlgebras (S T : Submodule ℝ TimeZeroSource)
    (hST : ∀ u ∈ S, ∀ v ∈ T, timeZeroSymplectic u v = 0) :
    Commuting (canonicalSourceAlgebra V hm S) (canonicalSourceAlgebra V hm T) := by
  apply commuting_generatedVNA_of_commute
  apply commute_union_star_of_subset_unitary
  · rintro A ⟨u, hu, rfl⟩
    exact V.timeZeroWeyl_mem_unitary hm u
  · rintro B ⟨v, hv, rfl⟩
    exact V.timeZeroWeyl_mem_unitary hm v
  · rintro A ⟨u, hu, rfl⟩ B ⟨v, hv, rfl⟩
    exact timeZeroWeyl_mul_comm_of_symplectic_zero hm V (hST u hu v hv)

/-- Actual local time-zero algebras commute for arbitrary disjoint regions. -/
theorem commuting_timeZeroLocalAlgebras_of_disjoint
    {U W : Set (EuclideanSpace ℝ (Fin 3))} (hUW : Disjoint U W) :
    Commuting (timeZeroLocalAlgebra V hm U) (timeZeroLocalAlgebra V hm W) := by
  apply commuting_generatedVNA_of_commute
  apply commute_union_star_of_subset_unitary
  · rintro A ⟨u, hu, h'u, rfl⟩
    exact V.timeZeroWeyl_mem_unitary hm u
  · rintro B ⟨v, hv, h'v, rfl⟩
    exact V.timeZeroWeyl_mem_unitary hm v
  · rintro A ⟨u, hu, h'u, rfl⟩ B ⟨v, hv, h'v, rfl⟩
    exact timeZeroWeyl_mul_comm_of_symplectic_zero hm V
      (timeZeroSymplectic_eq_zero_of_disjoint hUW ⟨hu, h'u⟩ ⟨hv, h'v⟩)

end VacuumBellSeparation
