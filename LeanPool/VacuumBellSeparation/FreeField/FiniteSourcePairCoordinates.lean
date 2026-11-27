/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CanonicalSourcePair
public import LeanPool.VacuumBellSeparation.FreeField.FiniteGaussianObservables
public import Mathlib.LinearAlgebra.Projection

/-!
# Literal regional label subspaces in a joint finite physical system

Pulling source subspaces back through the actual basis coordinates retains
their exact Weyl algebras. A disjoint direct sum of source systems gives
complementary label subspaces, and its actual symplectic cross form vanishes.
These are algebraic complementary subspaces, not assumed covariance-orthogonal.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped Matrix

variable {m : ℝ} (hm : 0 < m) (R : Submodule ℝ TimeZeroSource)
  [FiniteDimensional ℝ R] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (FiniteSourceSpace hm R))

omit [DecidableEq ι] [FiniteDimensional ℝ R] in
theorem finiteSourceCoordinates_injective : Function.Injective
  (finiteSourceCoordinates hm R b) := by
  intro x y h
  apply b.equivFun.symm.injective
  exact Subtype.ext h

/-- Coordinate vectors whose corresponding physical source belongs to the indicated subspace. -/
noncomputable def finiteSourceLabelSubspace (S : Submodule ℝ TimeZeroSource) : Submodule ℝ (ι
  → ℝ) :=
  S.comap (finiteSourceCoordinates hm R b)

omit [DecidableEq ι] [FiniteDimensional ℝ R] [Fintype ι] in
theorem finiteSourceCovarianceMatrix_isHermitian :
  (finiteSourceCovarianceMatrix hm R b).IsHermitian := by
  change (finiteSourceCovarianceMatrix hm R b)ᴴ = finiteSourceCovarianceMatrix hm R b
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, finiteSourceCovarianceMatrix]
  rw [← finiteSourceSpace_inner hm R, ← finiteSourceSpace_inner hm R, real_inner_comm]

omit [DecidableEq ι] [FiniteDimensional ℝ ↥R] in
theorem finiteSourceLabelSubspace_isCompl {S T : Submodule ℝ TimeZeroSource}
    (hR : R = S ⊔ T) (hST : Disjoint S T) :
    IsCompl (finiteSourceLabelSubspace hm R b S) (finiteSourceLabelSubspace hm R b T) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hy
    apply finiteSourceCoordinates_injective hm R b
    rw [map_zero]
    exact Submodule.disjoint_def.mp hST _ hx hy
  · apply codisjoint_iff.mpr
    apply top_unique
    intro x hx
    have hRS : R ≤ S ⊔ T := le_of_eq hR
    have hc : finiteSourceCoordinates hm R b x ∈ S ⊔ T :=
      hRS (finiteSourceCoordinates_mem hm R b x)
    obtain ⟨s, hs, t, ht, he⟩ := Submodule.mem_sup.mp hc
    have hsR : s ∈ Set.range (finiteSourceCoordinates hm R b) := by
      rw [range_finiteSourceCoordinates, hR]
      exact Submodule.mem_sup_left hs
    have htR : t ∈ Set.range (finiteSourceCoordinates hm R b) := by
      rw [range_finiteSourceCoordinates, hR]
      exact Submodule.mem_sup_right ht
    obtain ⟨y, hy⟩ := hsR
    obtain ⟨z, hz⟩ := htR
    apply Submodule.mem_sup.mpr
    refine ⟨y, ?_, z, ?_, ?_⟩
    · change finiteSourceCoordinates hm R b y ∈ S
      rwa [hy]
    · change finiteSourceCoordinates hm R b z ∈ T
      rwa [hz]
    · apply finiteSourceCoordinates_injective hm R b
      rw [map_add, hy, hz]
      exact he

omit [DecidableEq ι] [FiniteDimensional ℝ R] in
theorem generatedVNA_finiteSourceLabelSubspace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : FreeFieldVacuum m H) (S : Submodule ℝ TimeZeroSource) (hSR : S ≤ R) :
    generatedVNA (finitePhysicalWeyl hm R b V '' (finiteSourceLabelSubspace hm R b S : Set (ι
      → ℝ))) =
      canonicalSourceAlgebra V hm S := by
  congr 1
  ext A
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨finiteSourceCoordinates hm R b x, hx, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    have hr : u ∈ Set.range (finiteSourceCoordinates hm R b) := by
      rw [range_finiteSourceCoordinates]
      exact hSR hu
    obtain ⟨x, hx⟩ := hr
    refine ⟨x, ?_, ?_⟩
    · change finiteSourceCoordinates hm R b x ∈ S
      rwa [hx]
    · change V.timeZeroWeyl hm (finiteSourceCoordinates hm R b x) = V.timeZeroWeyl hm u
      rw [hx]

theorem finiteSourceLabelSubspace_symplectic_cross {n : ℕ}
    (c : Module.Basis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm R))
    (hσ : finiteSourceSymplecticMatrix hm R c = modeSymplecticForm)
    (S T : Submodule ℝ TimeZeroSource)
    (hST : ∀ u ∈ S, ∀ v ∈ T, timeZeroSymplectic u v = 0)
    {x y : Fin n × Fin 2 → ℝ}
    (hx : x ∈ finiteSourceLabelSubspace hm R c S)
    (hy : y ∈ finiteSourceLabelSubspace hm R c T) :
    x ⬝ᵥ (modeSymplecticForm *ᵥ y) = 0 := by
  rw [← hσ, ← finiteSourceCoordinates_symplectic hm R c]
  exact hST _ hx _ hy

end VacuumBellSeparation
