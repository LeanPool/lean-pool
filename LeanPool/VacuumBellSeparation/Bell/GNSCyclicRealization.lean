/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.CyclicGramEquivalence
public import LeanPool.VacuumBellSeparation.Bell.GNSDominatedCommutant

/-!
# Actual unitary realization of a cyclic GNS representation

The unitary is constructed from equality of the actual cyclic Gram forms
and density of the given orbit. It intertwines every original algebra
element on the whole completed Hilbert space. In particular a positive
functional dominated by the reference functional has a representing vector
in any such concrete cyclic realization. Arbitrary normal functionals are
not assumed to be dominated or represented.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open scoped InnerProductSpace ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem dense_span_of_dense_orbit {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (v : ι → E) (hv : DenseRange v) :
    (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mp
  exact Dense.mono (fun _ hx => Submodule.subset_span hx) hv

/-- Equality of vector expectation and cyclicity construct the unitary;
normality, faithfulness and a pre-existing representation equivalence are
not premises. Neither reference functional nor vector must be normalized. -/
theorem exists_gns_cyclic_unitary (φ : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (hφ : ∀ a : A, φ a = inner ℂ Ω (π a Ω))
    (hcyclic : DenseRange (fun a : A => π a Ω)) :
    ∃ U : φ.GNS ≃ₗᵢ[ℂ] H, U (gnsUnitVector φ) = Ω ∧
      ∀ (a : A) (x : φ.GNS), U (φ.gnsStarAlgHom a x) = π a (U x) := by
  have hgram (a b : A) :
      inner ℂ (φ.gnsStarAlgHom a (gnsUnitVector φ))
        (φ.gnsStarAlgHom b (gnsUnitVector φ)) = inner ℂ (π a Ω) (π b Ω) := by
    calc
      _ = φ (star a * b) := by
        simpa only [map_one, one_apply_eq_self, one_mul, mul_one] using
          gns_matrix_coefficient φ a 1 b
      _ = _ := by
        rw [hφ, map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
          mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
  obtain ⟨U, hU⟩ := exists_unitary_equiv_of_dense_gram
    (fun a : A => φ.gnsStarAlgHom a (gnsUnitVector φ)) (fun a : A => π a Ω)
    (dense_span_of_dense_orbit _ (gnsUnitVector_dense_orbit φ))
    (dense_span_of_dense_orbit _ hcyclic) hgram
  refine ⟨U, ?_, ?_⟩
  · simpa only [map_one, one_apply_eq_self] using hU (1 : A)
  · intro a x
    have he := (gnsUnitVector_dense_orbit φ).equalizer
      (U.continuous.comp (φ.gnsStarAlgHom a).continuous)
      ((π a).continuous.comp U.continuous)
      (by
        funext b
        change U (φ.gnsStarAlgHom a (φ.gnsStarAlgHom b (gnsUnitVector φ))) =
          π a (U (φ.gnsStarAlgHom b (gnsUnitVector φ)))
        rw [← mul_apply_eq_comp, ← map_mul, hU, hU, map_mul, mul_apply_eq_comp])
    exact congrFun he x

/-- Domination produces an actual vector in the supplied concrete cyclic
Hilbert space, with the exact unnormalized mass of the positive functional. -/
theorem exists_dominated_vector_in_cyclic_representation (φ ψ : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (hφ : ∀ a : A, φ a = inner ℂ Ω (π a Ω))
    (hcyclic : DenseRange (fun a : A => π a Ω))
    (C : ℝ) (hC : 0 ≤ C) (hdom : ∀ a : A, 0 ≤ a → ψ a ≤ C • φ a) :
    ∃ ξ : H, ‖ξ‖ = Real.sqrt (ψ 1).re ∧
      ∀ a : A, inner ℂ ξ (π a ξ) = ψ a := by
  obtain ⟨U, _, hintertwine⟩ := exists_gns_cyclic_unitary φ π Ω hφ hcyclic
  let ξ := dominatedGNSVector φ ψ C hC hdom
  refine ⟨U ξ, ?_, ?_⟩
  · rw [U.norm_map]
    exact dominatedGNSVector_norm φ ψ C hC hdom
  · intro a
    rw [← hintertwine a ξ, U.inner_map_map]
    exact dominatedGNSVector_expectation φ ψ C hC hdom a

theorem exists_dominated_unit_vector_in_cyclic_representation (φ ψ : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (hφ : ∀ a : A, φ a = inner ℂ Ω (π a Ω))
    (hcyclic : DenseRange (fun a : A => π a Ω))
    (C : ℝ) (hC : 0 ≤ C) (hdom : ∀ a : A, 0 ≤ a → ψ a ≤ C • φ a)
    (hψ : ψ 1 = 1) :
    ∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ a : A, inner ℂ ξ (π a ξ) = ψ a := by
  obtain ⟨ξ, hξ, hrepr⟩ :=
    exists_dominated_vector_in_cyclic_representation φ ψ π Ω hφ hcyclic C hC hdom
  refine ⟨ξ, ?_, hrepr⟩
  simpa only [hψ, Complex.one_re, Real.sqrt_one] using hξ

end VacuumBellSeparation
