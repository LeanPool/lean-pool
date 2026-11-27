/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.CyclicGramEquivalence
public import LeanPool.VacuumBellSeparation.Bell.CyclicSpanRestriction

/-!
# Cyclic equivalence from genuine projective representation data

Identical multiplication phases, adjoint labels and vector characteristics
give equal orbit Gram matrices. Density in the literal source cyclic
subspace is proved; target density remains explicit in this generic lemma.
The oscillator instantiation supplies it using faithful purification.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap
open scoped InnerProductSpace

variable {Z H K : Type*} [AddGroup Z]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
theorem projective_closedOrbit_invariant (W : Z → H →L[ℂ] H)
    (c : Z → Z → ℂ) (hmul : ∀ x y, W x * W y = c x y • W (x + y))
    (v : H) (z : Z) {x : H} (hx : x ∈ closedCyclicSpan (fun y => W y v)) :
    W z x ∈ closedCyclicSpan (fun y => W y v) := by
  apply closedCyclicSpan_invariant _ _ ?_ hx
  intro y
  rw [← mul_apply_eq_comp, hmul, smul_apply]
  exact (closedCyclicSpan _).smul_mem _ (mem_closedCyclicSpan _ (z + y))

theorem projective_closedOrbit_reducing (W : Z → H →L[ℂ] H)
    (c : Z → Z → ℂ) (hmul : ∀ x y, W x * W y = c x y • W (x + y))
    (hstar : ∀ x, star (W x) = W (-x)) (v : H)
    (A : H →L[ℂ] H) (hA : A ∈ Set.range W) :
    (∀ x ∈ closedCyclicSpan (fun y => W y v), A x ∈ closedCyclicSpan (fun y => W y v)) ∧
    (∀ x ∈ closedCyclicSpan (fun y => W y v), star A x ∈ closedCyclicSpan (fun y => W y v)) := by
  obtain ⟨z, rfl⟩ := hA
  refine ⟨fun x hx => projective_closedOrbit_invariant W c hmul v z hx, ?_⟩
  intro x hx
  rw [hstar]
  exact projective_closedOrbit_invariant W c hmul v (-z) hx

theorem projective_orbit_gram (W : Z → H →L[ℂ] H) (c : Z → Z → ℂ)
    (hmul : ∀ x y, W x * W y = c x y • W (x + y))
    (hstar : ∀ x, star (W x) = W (-x)) (v : H) (x y : Z) :
    ⟪W x v, W y v⟫_ℂ = c (-x) y * ⟪v, W (-x + y) v⟫_ℂ := by
  rw [← adjoint_inner_right, ← star_eq_adjoint, ← mul_apply_eq_comp,
    hstar, hmul, smul_apply, inner_smul_right]

local instance closedOrbit_complete (W : Z → H →L[ℂ] H) (v : H) :
    CompleteSpace (closedCyclicSpan (fun x => W x v)) := by
  unfold closedCyclicSpan
  infer_instance

/-- A concrete unitary on the actual source cyclic subspace, obtained from
matching projective relations and vector characteristics. -/
theorem exists_projective_cyclic_unitary
    (W : Z → H →L[ℂ] H) (W' : Z → K →L[ℂ] K) (c : Z → Z → ℂ)
    (hmul : ∀ x y, W x * W y = c x y • W (x + y))
    (hmul' : ∀ x y, W' x * W' y = c x y • W' (x + y))
    (hstar : ∀ x, star (W x) = W (-x))
    (hstar' : ∀ x, star (W' x) = W' (-x)) (v : H) (v' : K)
    (hd : closedCyclicSpan (fun x => W' x v') = ⊤)
    (hchar : ∀ x, ⟪v, W x v⟫_ℂ = ⟪v', W' x v'⟫_ℂ) :
    ∃ U : closedCyclicSpan (fun x => W x v) ≃ₗᵢ[ℂ] K,
      (∀ x, U (cyclicSpanVector (fun x => W x v) x) = W' x v') ∧
      (∀ z, U.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (compression (closedCyclicSpan (fun x => W x v)).subtypeₗᵢ (W z)) =
          (W' z).comp U.toContinuousLinearEquiv.toContinuousLinearMap) := by
  have hgram (x y : Z) :
      ⟪cyclicSpanVector (fun x => W x v) x, cyclicSpanVector (fun x => W x v) y⟫_ℂ =
        ⟪W' x v', W' y v'⟫_ℂ := by
    change ⟪W x v, W y v⟫_ℂ = _
    rw [projective_orbit_gram W c hmul hstar, projective_orbit_gram W' c hmul' hstar', hchar]
  obtain ⟨U, hU⟩ := exists_unitary_equiv_of_dense_gram
    (cyclicSpanVector (fun x => W x v)) (fun x => W' x v')
    (cyclicSpanVector_dense _) hd hgram
  refine ⟨U, hU, fun z => ?_⟩
  refine cyclic_unitary_intertwines
    (cyclicSpanVector (fun x => W x v))
    (cyclicSpanVector_dense (fun x => W x v)) U
    (compression (closedCyclicSpan (fun x => W x v)).subtypeₗᵢ (W z)) (W' z) ?_
  intro x
  have hr : compression (closedCyclicSpan (fun x => W x v)).subtypeₗᵢ (W z)
      (cyclicSpanVector (fun x => W x v) x) =
        c z x • cyclicSpanVector (fun x => W x v) (z + x) := by
    rw [compression_subtype_apply _ _
      (fun y hy => projective_closedOrbit_invariant W c hmul v z hy)]
    apply Subtype.ext
    exact congrArg (fun A : H →L[ℂ] H => A v) (hmul z x)
  rw [hr, map_smul, hU, hU, ← mul_apply_eq_comp, hmul', smul_apply]

end VacuumBellSeparation
