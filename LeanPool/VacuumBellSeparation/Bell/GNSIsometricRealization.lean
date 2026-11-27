/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GNSCyclicRealization

/-!
A vector functional's GNS space embeds isometrically in the original H.
No cyclicity in all of H is required: the image is allowed to be proper.
Consequently a positive functional dominated by this vector functional has
an actual representing vector in H even in a noncyclic representation.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open scoped InnerProductSpace ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_gns_isometry_in_representation (φ : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (hφ : ∀ a : A, φ a = inner ℂ Ω (π a Ω)) :
    ∃ U : φ.GNS →ₗᵢ[ℂ] H, U (gnsUnitVector φ) = Ω ∧
      ∀ (a : A) (x : φ.GNS), U (φ.gnsStarAlgHom a x) = π a (U x) := by
  let v : A → φ.GNS := fun a => φ.gnsStarAlgHom a (gnsUnitVector φ)
  let w : A → H := fun a => π a Ω
  have hgram (a b : A) : inner ℂ (v a) (v b) = inner ℂ (w a) (w b) := by
    calc
      _ = φ (star a * b) := by
        simpa only [v, map_one, one_apply_eq_self, one_mul, mul_one] using
          gns_matrix_coefficient φ a 1 b
      _ = _ := by
        rw [hφ, map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
          mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
  have hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mp
    exact Dense.mono (fun _ hx => Submodule.subset_span hx) (gnsUnitVector_dense_orbit φ)
  have hd := denseRange_linearCombination_of_dense_span v hv
  have hn (c : A →₀ ℂ) :
      ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖ := by
    have he := inner_linearCombination_eq_of_inner_eq v w hgram c c
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), he]
  let U : φ.GNS →ₗᵢ[ℂ] H := (Finsupp.linearCombination ℂ w).extendOfIsometry hd hn
  have hU (a : A) : U (v a) = w a := by
    simpa only [Finsupp.linearCombination_single, one_smul] using
      LinearMap.extendOfIsometry_eq (Finsupp.linearCombination ℂ w) hd hn (Finsupp.single a 1)
  refine ⟨U, ?_, ?_⟩
  · simpa only [v, w, map_one, one_apply_eq_self] using hU (1 : A)
  · intro a x
    have he := (gnsUnitVector_dense_orbit φ).equalizer
      (U.continuous.comp (φ.gnsStarAlgHom a).continuous)
      ((π a).continuous.comp U.continuous)
      (by
        funext b
        change U (φ.gnsStarAlgHom a (v b)) = π a (U (v b))
        change U (φ.gnsStarAlgHom a (φ.gnsStarAlgHom b (gnsUnitVector φ))) =
          π a (U (v b))
        rw [← mul_apply_eq_comp, ← map_mul, hU, hU]
        simp only [w, map_mul, mul_apply_eq_comp])
    exact congrFun he x

/-- Actual bounded vector-Radon--Nikodym realization, without ambient cyclicity. -/
theorem exists_dominated_vector_in_representation (φ ψ : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (hφ : ∀ a : A, φ a = inner ℂ Ω (π a Ω))
    (C : ℝ) (hC : 0 ≤ C) (hdom : ∀ a : A, 0 ≤ a → ψ a ≤ C • φ a) :
    ∃ ξ : H, ‖ξ‖ = Real.sqrt (ψ 1).re ∧
      ∀ a : A, inner ℂ ξ (π a ξ) = ψ a := by
  obtain ⟨U, _, hi⟩ := exists_gns_isometry_in_representation φ π Ω hφ
  let ξ := dominatedGNSVector φ ψ C hC hdom
  refine ⟨U ξ, ?_, ?_⟩
  · rw [U.norm_map]
    exact dominatedGNSVector_norm φ ψ C hC hdom
  · intro a
    rw [← hi a ξ, U.inner_map_map]
    exact dominatedGNSVector_expectation φ ψ C hC hdom a

end VacuumBellSeparation
