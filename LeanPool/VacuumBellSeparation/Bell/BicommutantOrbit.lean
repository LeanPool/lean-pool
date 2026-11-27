/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Isotony
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The one-vector double-commutant approximation lemma

The orbit of a unital complex star algebra is a linear subspace. Its
closed orbit is reducing, so its orthogonal projection belongs to the
commutant. This gives actual norm approximation on one vector for every
operator in the double commutant.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The orbit of a finite vector family under the simultaneous action of operators in the
algebra. -/
def operatorOrbit (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) : Submodule ℂ H where
  carrier := {y | ∃ A ∈ S, A x = y}
  zero_mem' := ⟨0, S.zero_mem, by simp⟩
  add_mem' := by
    rintro y z ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    exact ⟨A + B, S.add_mem hA hB, by simp⟩
  smul_mem' := by
    rintro c y ⟨A, hA, rfl⟩
    exact ⟨c • A, S.smul_mem hA c, by simp⟩

theorem operatorOrbit_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H)
    {A : H →L[ℂ] H} (hA : A ∈ S) {y : H} (hy : y ∈ operatorOrbit S x) :
    A y ∈ operatorOrbit S x := by
  obtain ⟨B, hB, rfl⟩ := hy
  exact ⟨A * B, S.mul_mem hA hB, rfl⟩

theorem closedOperatorOrbit_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H)
    {A : H →L[ℂ] H} (hA : A ∈ S) {y : H}
    (hy : y ∈ (operatorOrbit S x).topologicalClosure) :
    A y ∈ (operatorOrbit S x).topologicalClosure := by
  have hs : (operatorOrbit S x : Set H) ⊆
      A ⁻¹' ((operatorOrbit S x).topologicalClosure : Set H) := by
    intro z hz
    exact (operatorOrbit S x).le_topologicalClosure (operatorOrbit_invariant S x hA hz)
  exact closure_minimal hs
    ((operatorOrbit S x).isClosed_topologicalClosure.preimage A.continuous) hy

/-- Reducing subspaces have projections commuting with every algebra element. -/
theorem starProjection_commutes_of_invariant
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection]
    (hinv : ∀ A ∈ S, ∀ y ∈ K, A y ∈ K) {A : H →L[ℂ] H} (hA : A ∈ S) :
    A * K.starProjection = K.starProjection * A := by
  have hfix : ∀ B ∈ S, K.starProjection * B * K.starProjection = B * K.starProjection := by
    intro B hB
    ext y
    exact Submodule.starProjection_eq_self_iff.mpr
      (hinv B hB _ (K.starProjection_apply_mem y))
  have hleft : K.starProjection * A * K.starProjection = K.starProjection * A := by
    have h := congrArg star (hfix (star A) (star_mem hA))
    simpa only [star_mul, star_star,
      (isSelfAdjoint_starProjection K).star_eq, mul_assoc] using h
  exact (hfix A hA).symm.trans hleft

theorem closedOperatorOrbit_projection_mem_commutant
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) :
    (operatorOrbit S x).topologicalClosure.starProjection ∈ commutantOf (S : Set (H →L[ℂ] H)) := by
  rw [mem_commutantOf_iff, StarMemClass.star_coe_eq, Set.union_self]
  apply Set.mem_centralizer_iff.mpr
  intro A hA
  exact starProjection_commutes_of_invariant S _
    (fun B hB y hy => closedOperatorOrbit_invariant S x hB hy) hA

/-- Every double-commutant operator sends a vector into its actual closed orbit. -/
theorem bicommutant_apply_mem_closedOrbit
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ generatedVNA (S : Set (H →L[ℂ] H))) (x : H) :
    T x ∈ (operatorOrbit S x).topologicalClosure := by
  let K := (operatorOrbit S x).topologicalClosure
  have hx : x ∈ K := (operatorOrbit S x).le_topologicalClosure ⟨1, S.one_mem, by simp⟩
  have hc := (VonNeumannAlgebra.mem_commutant_iff.mp hT)
    K.starProjection (closedOperatorOrbit_projection_mem_commutant S x)
  apply Submodule.starProjection_eq_self_iff.mp
  have he := congrArg (fun A : H →L[ℂ] H => A x) hc
  simpa only [mul_apply_eq_comp,
    Submodule.starProjection_eq_self_iff.mpr hx] using he

/-- Actual approximation on one vector, with no operator-norm bound yet. -/
theorem bicommutant_approximate_one_vector
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ generatedVNA (S : Set (H →L[ℂ] H))) (x : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ S, ‖T x - A x‖ < ε := by
  obtain ⟨y, ⟨A, hA, rfl⟩, hy⟩ := Metric.mem_closure_iff.mp
    (bicommutant_apply_mem_closedOrbit S hT x) ε hε
  exact ⟨A, hA, by simpa only [dist_eq_norm] using hy⟩

end VacuumBellSeparation
