/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.BicommutantOrbit

/-!
# Closed cyclic spans and actual reducing subspaces

These lemmas use the literal closed span of a family of vectors. Invariance
of the generators and their adjoints makes its orthogonal projection commute
with the generated von Neumann algebra. No cyclicity assumption is inserted.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Closure of the complex linear span of the given vectors. -/
def closedCyclicSpan {ι : Type*} (v : ι → H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range v)).topologicalClosure

omit [CompleteSpace H] in
theorem mem_closedCyclicSpan {ι : Type*} (v : ι → H) (i : ι) :
    v i ∈ closedCyclicSpan v :=
  (Submodule.span ℂ (Set.range v)).le_topologicalClosure (Submodule.subset_span ⟨i, rfl⟩)

omit [CompleteSpace H] in
theorem closedCyclicSpan_invariant {ι : Type*} (v : ι → H) (A : H →L[ℂ] H)
    (hA : ∀ i, A (v i) ∈ closedCyclicSpan v) {x : H} (hx : x ∈ closedCyclicSpan v) :
    A x ∈ closedCyclicSpan v := by
  have hs : Submodule.span ℂ (Set.range v) ≤ (closedCyclicSpan v).comap A.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hA i
  exact closure_minimal hs
    ((Submodule.span ℂ (Set.range v)).isClosed_topologicalClosure.preimage A.continuous) hx

/-- A subspace invariant under an operator and its adjoint is genuinely reducing. -/
theorem starProjection_commutes_of_invariant_pair (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (A : H →L[ℂ] H)
    (hA : ∀ x ∈ K, A x ∈ K) (hstar : ∀ x ∈ K, star A x ∈ K) :
    A * K.starProjection = K.starProjection * A := by
  have hfix (B : H →L[ℂ] H) (hB : ∀ x ∈ K, B x ∈ K) :
      K.starProjection * B * K.starProjection = B * K.starProjection := by
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr (hB _ (K.starProjection_apply_mem x))
  have hleft : K.starProjection * A * K.starProjection = K.starProjection * A := by
    have h := congrArg star (hfix (star A) hstar)
    simpa only [star_mul, star_star, (isSelfAdjoint_starProjection K).star_eq,
      mul_assoc] using h
  exact (hfix A hA).symm.trans hleft

/-- Generator invariance and adjoint invariance imply invariance under the
actual double commutant, using its commutation with the subspace projection. -/
theorem generatedVNA_invariant_of_reducing (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (S : Set (H →L[ℂ] H))
    (hS : ∀ A ∈ S, (∀ x ∈ K, A x ∈ K) ∧ (∀ x ∈ K, star A x ∈ K))
    {T : H →L[ℂ] H} (hT : T ∈ generatedVNA S) {x : H} (hx : x ∈ K) :
    T x ∈ K := by
  have hP : K.starProjection ∈ commutantOf S := by
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro A hA
    refine ⟨starProjection_commutes_of_invariant_pair K A (hS A hA).1 (hS A hA).2, ?_⟩
    apply starProjection_commutes_of_invariant_pair K (star A) (hS A hA).2
    simpa only [star_star] using (hS A hA).1
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp hT K.starProjection hP
  apply Submodule.starProjection_eq_self_iff.mp
  simpa only [mul_apply_eq_comp, Submodule.starProjection_eq_self_iff.mpr hx] using
    congrArg (fun B : H →L[ℂ] H => B x) hc

end VacuumBellSeparation
