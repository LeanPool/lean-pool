/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.Defs

/-!
# Range projections in a von Neumann algebra

For a bounded operator `T` on a Hilbert space `H`, `rangeProjection T` is the orthogonal
projection onto the closure of the range of `T`.  The main result, `rangeProjection_mem`,
states that the range projection of an element of a von Neumann algebra `M` belongs to `M`
(double-commutant argument: the projection commutes with every element of the commutant).
-/

@[expose] public section

namespace VacuumBellSeparation

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closure of the range of `T`, as a closed subspace. -/
def rangeClosure (T : H →L[ℂ] H) : Submodule ℂ H :=
  (LinearMap.range T.toLinearMap).topologicalClosure

instance rangeClosure_completeSpace (T : H →L[ℂ] H) : CompleteSpace (rangeClosure T) := by
  first
    | (unfold rangeClosure; infer_instance)


instance rangeClosure_hasOrthogonalProjection (T : H →L[ℂ] H) :
    (rangeClosure T).HasOrthogonalProjection := by
  first
    | infer_instance


/-- The orthogonal projection onto the closure of the range of `T`, as an element of `B(H)`. -/
def rangeProjection (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (rangeClosure T).starProjection

omit [CompleteSpace H] in
/-- If `S` commutes with `T`, then `S` maps the closure of the range of `T` into itself. -/
theorem map_mem_rangeClosure_of_commute {T S : H →L[ℂ] H} (h : S * T = T * S) {x : H}
    (hx : x ∈ rangeClosure T) : S x ∈ rangeClosure T := by
  have hcomm : ∀ z : H, S (T z) = T (S z) := fun z => by
    first
      | exact DFunLike.congr_fun h z
  have hle : (LinearMap.range T.toLinearMap).topologicalClosure ≤
      Submodule.comap S.toLinearMap (LinearMap.range T.toLinearMap).topologicalClosure := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · intro y hy
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
      have hmem : S (T z) ∈ LinearMap.range T.toLinearMap :=
        LinearMap.mem_range.mpr ⟨S z, (hcomm z).symm⟩
      first
        | exact Submodule.mem_comap.mpr (Submodule.le_topologicalClosure _ hmem)
    · exact (Submodule.isClosed_topologicalClosure _).preimage S.continuous
  first
    | exact hle hx


/-- A subspace `K` (with an orthogonal projection) that is invariant under `S` and under
its adjoint `star S` has an orthogonal projection commuting with `S`. -/
theorem commute_projection_of_invariant (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (S : H →L[ℂ] H) (hS : ∀ x ∈ K, S x ∈ K) (hS' : ∀ x ∈ K, (star S) x ∈ K) :
    K.starProjection * S = S * K.starProjection := by
  refine ContinuousLinearMap.ext fun x => ?_
  change K.starProjection (S x) = S (K.starProjection x)
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hS _ (Submodule.starProjection_apply_mem K x)) ?_
  intro w hw
  have hw' : (ContinuousLinearMap.adjoint S) w ∈ K := by
    first
      | exact hS' w hw
  have h0 := Submodule.starProjection_inner_eq_zero x _ hw'
  rw [ContinuousLinearMap.adjoint_inner_right, map_sub] at h0
  exact h0

/-- The orthogonal projection onto the closure of the range of an element of a von Neumann
algebra belongs to the algebra. -/
theorem rangeProjection_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T ∈ M) :
    rangeProjection T ∈ M := by
  have key : rangeProjection T ∈ M.commutant.commutant := by
    refine VonNeumannAlgebra.mem_commutant_iff.mpr fun S hS => ?_
    have h1 : S * T = T * S := by
      have h := VonNeumannAlgebra.mem_commutant_iff.mp hS T hT
      first
        | exact h.symm
    have h2 : star S * T = T * star S := by
      have h := VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hS) T hT
      first
        | exact h.symm
    have hc : (rangeClosure T).starProjection * S = S * (rangeClosure T).starProjection :=
      commute_projection_of_invariant (rangeClosure T) S
        (fun x hx => map_mem_rangeClosure_of_commute h1 hx)
        (fun x hx => map_mem_rangeClosure_of_commute h2 hx)
    first
      | exact hc.symm
  first
    | (rw [VonNeumannAlgebra.commutant_commutant] at key; exact key)


end

end VacuumBellSeparation
