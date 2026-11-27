/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-! The literal unit vector and dense orbit of the pinned GNS construction.
This does not identify the image as a von Neumann algebra or prove normality. -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open scoped InnerProductSpace ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The additive norm inherited from the uniform completion of the pre-GNS space. -/
noncomputable instance gnsNormedAddCommGroup (φ : A →ₚ[ℂ] ℂ) :
    NormedAddCommGroup φ.GNS :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion φ.PreGNS))

/-- The scalar product on the completion extending the pre-GNS scalar product. -/
noncomputable instance gnsInnerProductSpace (φ : A →ₚ[ℂ] ℂ) : InnerProductSpace ℂ φ.GNS :=
  inferInstanceAs (InnerProductSpace ℂ (UniformSpace.Completion φ.PreGNS))

/-- Completeness of the completed GNS representation space. -/
instance gnsCompleteSpace (φ : A →ₚ[ℂ] ℂ) : CompleteSpace φ.GNS :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion φ.PreGNS))

/-- GNS unit vector. -/
def gnsUnitVector (φ : A →ₚ[ℂ] ℂ) : φ.GNS :=
  ((φ.toPreGNS 1 : φ.PreGNS) : φ.GNS)

theorem gns_apply_unitVector (φ : A →ₚ[ℂ] ℂ) (a : A) :
    φ.gnsStarAlgHom a (gnsUnitVector φ) = ((φ.toPreGNS a : φ.PreGNS) : φ.GNS) := by
  change φ.gnsNonUnitalStarAlgHom a ((φ.toPreGNS 1 : φ.PreGNS) : φ.GNS) = _
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  congr 1
  change φ.toPreGNS (a * 1) = φ.toPreGNS a
  rw [mul_one]

theorem gnsUnitVector_norm (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) :
    ‖gnsUnitVector φ‖ = 1 := by
  rw [gnsUnitVector, UniformSpace.Completion.norm_coe, PositiveLinearMap.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, hφ,
    Complex.one_re, Real.sqrt_one]

theorem gnsUnitVector_expectation (φ : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪gnsUnitVector φ, φ.gnsStarAlgHom a (gnsUnitVector φ)⟫_ℂ = φ a := by
  rw [gns_apply_unitVector]
  change ⟪((φ.toPreGNS 1 : φ.PreGNS) : φ.GNS),
    ((φ.toPreGNS a : φ.PreGNS) : φ.GNS)⟫_ℂ = _
  rw [UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul]

theorem gnsUnitVector_dense_orbit (φ : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => φ.gnsStarAlgHom a (gnsUnitVector φ)) := by
  have hr : Set.range (fun a : A => φ.gnsStarAlgHom a (gnsUnitVector φ)) =
      Set.range ((↑) : φ.PreGNS → φ.GNS) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨φ.toPreGNS a, (gns_apply_unitVector φ a).symm⟩
    · rintro ⟨a, rfl⟩
      refine ⟨φ.ofPreGNS a, ?_⟩
      change φ.gnsStarAlgHom (φ.ofPreGNS a) (gnsUnitVector φ) = _
      rw [gns_apply_unitVector, PositiveLinearMap.toPreGNS_ofPreGNS]
  change Dense (Set.range (fun a : A => φ.gnsStarAlgHom a (gnsUnitVector φ)))
  rw [hr]
  exact UniformSpace.Completion.denseRange_coe

theorem gns_apply_unitVector_norm_sq (φ : A →ₚ[ℂ] ℂ) (a : A) :
    ((‖φ.gnsStarAlgHom a (gnsUnitVector φ)‖ ^ 2 : ℝ) : ℂ) = φ (star a * a) := by
  rw [gns_apply_unitVector, UniformSpace.Completion.norm_coe]
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, Complex.ofReal_pow] using
    φ.preGNS_norm_sq (φ.toPreGNS a)

/-- Faithfulness is the actual vanishing condition on each positive square.
The result concerns the concrete GNS representation, not an assumed isomorphism. -/
theorem gnsStarAlgHom_injective_of_faithful (φ : A →ₚ[ℂ] ℂ)
    (hfaithful : ∀ a : A, φ (star a * a) = 0 → a = 0) :
    Function.Injective φ.gnsStarAlgHom := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hfaithful (a - b)
  have hv : φ.gnsStarAlgHom (a - b) (gnsUnitVector φ) = 0 := by
    rw [map_sub, hab, sub_self]
    rfl
  calc
    φ (star (a - b) * (a - b)) =
        ((‖φ.gnsStarAlgHom (a - b) (gnsUnitVector φ)‖ ^ 2 : ℝ) : ℂ) :=
      (gns_apply_unitVector_norm_sq φ (a - b)).symm
    _ = 0 := by rw [hv]; norm_num

end VacuumBellSeparation
