/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CanonicalSourceAlgebra
public import LeanPool.VacuumBellSeparation.Bell.DirectedAlgebraUnion
public import LeanPool.VacuumBellSeparation.Bell.BicommutantSelfAdjoint

/-!
# The actual canonical union as a functional-calculus closed star algebra

The zero canonical hull supplies a stage even in an empty region. Directedness
supplies common stages for addition and multiplication. Selfadjoint finite
approximation is then instantiated for the original physical local algebra.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuous linear map for the canonical union ⋆-algebra, of type `StarSubalgebra ℂ (H →L[ℂ]
H)`. -/
noncomputable def canonicalUnionStarAlgebra (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) : StarSubalgebra ℂ (H →L[ℂ] H) := by
  letI : Nonempty {S : Submodule ℝ TimeZeroSource // IsCanonicalSourceSystem U S} :=
    ⟨⟨canonicalSourceHull ∅, canonicalSourceHull_isCanonical Set.finite_empty (Set.empty_subset _)⟩⟩
  exact directedAlgebraUnion (fun S : {S // IsCanonicalSourceSystem U S} =>
    canonicalSourceAlgebra V hm S.1) (by
      intro S T
      obtain ⟨R, hR, hSR, hTR⟩ := canonicalSourceAlgebras_directed V hm S.2 T.2
      exact ⟨⟨R, hR⟩, hSR, hTR⟩)

theorem mem_canonicalUnionStarAlgebra_iff (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (A : H →L[ℂ] H) :
    A ∈ canonicalUnionStarAlgebra V hm U ↔
      ∃ S : Submodule ℝ TimeZeroSource, IsCanonicalSourceSystem U S ∧
        A ∈ canonicalSourceAlgebra V hm S := by
  change (∃ S : {S // IsCanonicalSourceSystem U S}, A ∈ canonicalSourceAlgebra V hm S.1) ↔ _
  constructor
  · rintro ⟨⟨S, hS⟩, hA⟩
    exact ⟨S, hS, hA⟩
  · rintro ⟨S, hS, hA⟩
    exact ⟨⟨S, hS⟩, hA⟩

theorem coe_canonicalUnionStarAlgebra (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) :
    (canonicalUnionStarAlgebra V hm U : Set (H →L[ℂ] H)) = canonicalAlgebraUnion V hm U := by
  ext A
  exact mem_canonicalUnionStarAlgebra_iff V hm U A

theorem cfc_mem_canonicalUnionStarAlgebra (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (f : ℝ → ℝ) {A : H →L[ℂ] H}
    (hA : A ∈ canonicalUnionStarAlgebra V hm U) : cfc f A ∈ canonicalUnionStarAlgebra V hm U := by
  obtain ⟨S, hS, hA⟩ := (mem_canonicalUnionStarAlgebra_iff V hm U A).mp hA
  exact (mem_canonicalUnionStarAlgebra_iff V hm U _).mpr
    ⟨S, hS, cfc_mem_vonNeumannAlgebra _ f hA⟩

theorem generatedVNA_canonicalUnionStarAlgebra (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) :
    generatedVNA (canonicalUnionStarAlgebra V hm U : Set (H →L[ℂ] H)) =
      timeZeroLocalAlgebra V hm U := by
  rw [coe_canonicalUnionStarAlgebra, generatedVNA_canonicalAlgebraUnion]

/-- Actual selfadjoint local observables admit finite canonical approximants on
every finite family of vectors; no operator-norm bound is asserted yet. -/
theorem local_selfAdjoint_finite_canonical_approximation
    (V : FreeFieldVacuum m H) (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
    {T : H →L[ℂ] H} (hT : T ∈ timeZeroLocalAlgebra V hm U) (hsa : IsSelfAdjoint T)
    {ι : Type*} [Finite ι] (x : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Submodule ℝ TimeZeroSource, IsCanonicalSourceSystem U S ∧
      ∃ A ∈ canonicalSourceAlgebra V hm S, IsSelfAdjoint A ∧
        ∀ i, ‖T (x i) - A (x i)‖ < ε := by
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [← generatedVNA_canonicalUnionStarAlgebra V hm U] at hT
  obtain ⟨A, hA, hself, hdist⟩ := selfAdjoint_bicommutant_approximate_finite_family
    (canonicalUnionStarAlgebra V hm U) hT hsa x hε
  obtain ⟨S, hS, hA⟩ := (mem_canonicalUnionStarAlgebra_iff V hm U A).mp hA
  exact ⟨S, hS, A, hA, hself, hdist⟩

end VacuumBellSeparation
