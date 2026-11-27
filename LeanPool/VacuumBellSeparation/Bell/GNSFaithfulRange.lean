/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GNSMatrixCoefficients
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The faithful GNS image with its actual norm and order

The image here is only the literal star-subalgebra range. Norm closure and
order reflection are derived; neither means that this range is a VNA.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open scoped InnerProductSpace ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- GNS faithful range equivalence defined as `StarAlgEquiv.ofInjective φ.gnsStarAlgHom
(gnsStarAlgHom_injective_of_faithful φ hf)`. -/
def gnsFaithfulRangeEquiv (φ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, φ (star a * a) = 0 → a = 0) :
    A ≃⋆ₐ[ℂ] φ.gnsStarAlgHom.range :=
  StarAlgEquiv.ofInjective φ.gnsStarAlgHom (gnsStarAlgHom_injective_of_faithful φ hf)

theorem gnsStarAlgHom_isometry_of_faithful (φ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, φ (star a * a) = 0 → a = 0) : Isometry φ.gnsStarAlgHom :=
  NonUnitalStarAlgHom.isometry φ.gnsStarAlgHom (gnsStarAlgHom_injective_of_faithful φ hf)

theorem gnsStarAlgHom_norm_of_faithful (φ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, φ (star a * a) = 0 → a = 0) (a : A) :
    ‖φ.gnsStarAlgHom a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map φ.gnsStarAlgHom (gnsStarAlgHom_injective_of_faithful φ hf) a

theorem gnsStarAlgHom_le_iff_of_faithful (φ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, φ (star a * a) = 0 → a = 0) {a b : A} :
    φ.gnsStarAlgHom a ≤ φ.gnsStarAlgHom b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff φ.gnsStarAlgHom
    (gnsStarAlgHom_injective_of_faithful φ hf)

theorem gnsStarAlgHom_nonneg_iff_of_faithful (φ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, φ (star a * a) = 0 → a = 0) (a : A) :
    0 ≤ φ.gnsStarAlgHom a ↔ 0 ≤ a := by
  simpa only [map_zero] using (gnsStarAlgHom_le_iff_of_faithful φ hf (a := 0) (b := a))

theorem gns_range_norm_closed_of_faithful (φ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, φ (star a * a) = 0 → a = 0) :
    IsClosed (Set.range φ.gnsStarAlgHom) :=
  (gnsStarAlgHom_isometry_of_faithful φ hf).isClosedEmbedding.isClosed_range

/-- Separation is proved on the literal image, not its double commutant. -/
theorem gns_unitVector_separates_range_of_faithful (φ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, φ (star a * a) = 0 → a = 0)
    (T : φ.GNS →L[ℂ] φ.GNS) (hT : T ∈ φ.gnsStarAlgHom.range)
    (hz : T (gnsUnitVector φ) = 0) : T = 0 := by
  obtain ⟨a, rfl⟩ := hT
  have ha := (gns_apply_unitVector_eq_zero_iff_of_faithful φ hf a).mp hz
  simp only [ha, map_zero]

/-- Ambient least-upper-bound comparisons reflect to the original algebra.
No normality of a yet-unconstructed inverse VNA map is postulated. -/
theorem gns_isLUB_reflects_of_faithful (φ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, φ (star a * a) = 0 → a = 0)
    {s : Set A} {X : A} (hX : IsLUB (φ.gnsStarAlgHom '' s) (φ.gnsStarAlgHom X)) :
    IsLUB s X := by
  constructor
  · intro T hT
    exact (gnsStarAlgHom_le_iff_of_faithful φ hf).mp (hX.1 ⟨T, hT, rfl⟩)
  · intro Y hY
    apply (gnsStarAlgHom_le_iff_of_faithful φ hf).mp
    apply hX.2
    rintro _ ⟨T, hT, rfl⟩
    exact gnsStarAlgHom_monotone φ (hY hT)

end VacuumBellSeparation
