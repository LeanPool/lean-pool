/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalFunctionalDominatedCorner
public import LeanPool.VacuumBellSeparation.Bell.GNSIsometricRealization
public import LeanPool.VacuumBellSeparation.Bell.PositiveStateCompression

/-!
Every nonzero corner contains a nonzero subcorner on which an arbitrary
positive order-normal functional is represented by an original-H vector.
The stronger conclusion represents the p-compression on every original
algebra element. No normal representation theorem is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance vectorCorner_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- Corner domination is transported to actual compression on the full
algebra, so the bounded vector-RN theorem applies without a new corner carrier. -/
theorem exists_vector_of_supported_corner_domination (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (η : H)
    (hd : ∀ a : M.toStarSubalgebra, 0 ≤ a → p * a = a →
      (φ a).re ≤ (vectorPositiveLinearMap M η a).re) :
    ∃ ξ : H, (p : H →L[ℂ] H) ξ = ξ ∧ ‖ξ‖ = Real.sqrt (φ p).re ∧
      ∀ a : M.toStarSubalgebra,
        vectorFunctional M ξ a = φ (p * a * p) := by
  let ψ := compressionFunctional φ p
  let Ω := (p : H →L[ℂ] H) η
  let χ := vectorPositiveLinearMap M Ω
  have hdom (a : M.toStarSubalgebra) (ha : 0 ≤ a) : ψ a ≤ (1 : ℝ) • χ a := by
    have hq : 0 ≤ star p * a * p := star_left_conjugate_nonneg ha p
    have hpq : p * (star p * a * p) = star p * a * p := by
      rw [hp.isSelfAdjoint.star_eq]
      simp only [← mul_assoc, hp.isIdempotentElem.eq]
    have he : vectorPositiveLinearMap M η (star p * a * p) = χ a := by
      change inner ℂ η (((p : H →L[ℂ] H).adjoint * (a : H →L[ℂ] H) *
        (p : H →L[ℂ] H)) η) = inner ℂ Ω ((a : H →L[ℂ] H) Ω)
      rw [mul_apply_eq_comp, mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
    rw [one_smul]
    apply Complex.le_def.mpr
    refine ⟨?_, ?_⟩
    · simpa only [ψ, compressionFunctional_apply, he] using hd _ hq hpq
    · exact ((Complex.nonneg_iff.mp (ψ.map_nonneg ha)).2).symm.trans
        (Complex.nonneg_iff.mp (χ.map_nonneg ha)).2
  obtain ⟨ξ, hn, hv⟩ := exists_dominated_vector_in_representation χ ψ
    M.toStarSubalgebra.subtype Ω (fun _ => rfl) 1 (by norm_num) hdom
  have hrepr (a : M.toStarSubalgebra) : vectorFunctional M ξ a = φ (p * a * p) := by
    change inner ℂ ξ ((a : H →L[ℂ] H) ξ) = φ (p * a * p)
    simpa only [StarSubalgebra.subtype_apply, ψ, compressionFunctional_apply,
      hp.isSelfAdjoint.star_eq] using hv a
  have hezero : vectorFunctional M ξ (1 - p) = 0 := by
    rw [hrepr, hp.mul_one_sub_self, zero_mul, map_zero]
  have heproj : IsStarProjection ((1 - p : M.toStarSubalgebra) : H →L[ℂ] H) :=
    hp.one_sub.map M.toStarSubalgebra.subtype
  have heξ : ((1 - p : M.toStarSubalgebra) : H →L[ℂ] H) ξ = 0 := by
    apply norm_eq_zero.mp
    have hh := re_inner_projection_apply _ heproj ξ
    rw [inner_re_symm (𝕜 := ℂ)] at hh
    change (vectorFunctional M ξ (1 - p)).re = ‖_‖ ^ 2 at hh
    rw [hezero, Complex.zero_re] at hh
    nlinarith [norm_nonneg (((1 - p : M.toStarSubalgebra) : H →L[ℂ] H) ξ)]
  have hpξ : (p : H →L[ℂ] H) ξ = ξ := by
    change ξ - (p : H →L[ℂ] H) ξ = 0 at heξ
    exact (sub_eq_zero.mp heξ).symm
  refine ⟨ξ, hpξ, ?_, hrepr⟩
  simpa only [ψ, compressionFunctional_apply, mul_one,
    hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using hn

/-- Actual original-H vector realization on a nonzero subprojection of every
prescribed nonzero projection, for arbitrary positive order-normal phi. -/
theorem exists_nonzero_vector_realized_subcorner (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ)
    (r : M.toStarSubalgebra) (hr : IsStarProjection r) (hne : r ≠ 0) :
    ∃ (p : M.toStarSubalgebra) (ξ : H), IsStarProjection p ∧ p ≠ 0 ∧ p ≤ r ∧
      (p : H →L[ℂ] H) ξ = ξ ∧ ‖ξ‖ = Real.sqrt (φ p).re ∧
      ∀ a : M.toStarSubalgebra, vectorFunctional M ξ a = φ (p * a * p) := by
  obtain ⟨p, η, hp, hpne, hpr, _, hd⟩ :=
    exists_nonzero_vector_dominated_subcorner M φ hn r hr hne
  obtain ⟨ξ, hpξ, hnξ, hv⟩ := exists_vector_of_supported_corner_domination M φ p hp η hd
  exact ⟨p, ξ, hp, hpne, hpr, hpξ, hnξ, hv⟩

end VacuumBellSeparation.Bipartite
