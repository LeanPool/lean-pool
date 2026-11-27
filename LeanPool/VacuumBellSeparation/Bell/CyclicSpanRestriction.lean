/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.ClosedCyclicSpan
public import LeanPool.VacuumBellSeparation.Bell.ReducingCompression

/-!
# The literal cyclic Hilbert subspace

The original generating vectors, considered in their actual closed span,
are dense there. Its subtype isometry has exactly the usual orthogonal
projection, so the preceding reducing-compression results apply without
any replacement Hilbert space or density assumption.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A generating vector viewed as an element of its closed cyclic span. -/
def cyclicSpanVector {ι : Type*} (v : ι → H) (i : ι) : closedCyclicSpan v :=
  ⟨v i, mem_closedCyclicSpan v i⟩

omit [CompleteSpace H] in
theorem cyclicSpanVector_dense {ι : Type*} (v : ι → H) :
    (Submodule.span ℂ (Set.range (cyclicSpanVector v))).topologicalClosure = ⊤ := by
  let K := closedCyclicSpan v
  have hmap : (Submodule.span ℂ (Set.range (cyclicSpanVector v))).map K.subtype =
      Submodule.span ℂ (Set.range v) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  apply top_unique
  intro x hx
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp x.property ε hε
  rw [← hmap] at hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  exact ⟨z, hz, hdist⟩

theorem imageProjection_subtype (K : Submodule ℂ H) [CompleteSpace K] :
    imageProjection K.subtypeₗᵢ = K.starProjection := by
  simp only [imageProjection, Submodule.subtypeₗᵢ_toContinuousLinearMap,
    K.adjoint_subtypeL, Submodule.starProjection]

/-- Compression is literally restriction on an invariant closed subspace. -/
theorem compression_subtype_apply (K : Submodule ℂ H) [CompleteSpace K]
    (A : H →L[ℂ] H) (hA : ∀ x ∈ K, A x ∈ K) (x : K) :
    compression K.subtypeₗᵢ A x = ⟨A x, hA x x.property⟩ := by
  change K.subtypeₗᵢ.toContinuousLinearMap.adjoint (A x) = _
  exact adjoint_embedding_apply K.subtypeₗᵢ ⟨A x, hA x x.property⟩

/-- The full original generated algebra restricts into the algebra generated
by its compressed generators on the genuine reducing cyclic subspace. -/
theorem compression_subtype_mem_generatedVNA (K : Submodule ℂ H) [CompleteSpace K]
    (S : Set (H →L[ℂ] H))
    (hS : ∀ A ∈ S, (∀ x ∈ K, A x ∈ K) ∧ (∀ x ∈ K, star A x ∈ K))
    {T : H →L[ℂ] H} (hT : T ∈ generatedVNA S) :
    compression K.subtypeₗᵢ T ∈ generatedVNA (compression K.subtypeₗᵢ '' S) := by
  apply compression_mem_generatedVNA _ _ ?_ hT
  intro A hA
  rw [imageProjection_subtype]
  exact starProjection_commutes_of_invariant_pair K A (hS A hA).1 (hS A hA).2

end VacuumBellSeparation
